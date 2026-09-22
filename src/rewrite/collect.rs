use std::collections::{BTreeMap, BTreeSet};

use syn::{
    Attribute, Expr, ExprClosure, ExprPath, ExprStruct, File, FnArg, ImplItemFn, Item, ItemFn,
    ItemImpl, ItemMod, ItemUse, Local, Macro, Pat, PatStruct, PatTupleStruct, Path as SynPath,
    QSelf, Signature, Token, TraitBound, TraitItemFn, TypePath,
    parse::Parser,
    punctuated::Punctuated,
    spanned::Spanned,
    visit::{self, Visit, visit_pat},
};

use super::{
    attrs::extract_cfg,
    consts::{DEFAULT_INDENT_WIDTH, FMT_MACROS, PRIMITIVES},
    defs::collect_defs,
    source::Lines,
    use_tree::{
        collect_idents, collect_mappings, has_glob_import, has_super_glob, is_internal, path_str,
        resolve_path,
    },
};

#[derive(Clone)]
pub(super) struct Occurrence {
    pub(super) path: String,
    pub(super) span: (usize, usize),
    pub(super) scope: String,
    pub(super) cfg: Vec<String>,
    pub(super) suffix: String,
    pub(super) binding: Option<usize>,
    /// Locals visible at the call site (union over the enclosing
    /// function/closure frames). A short-name import for this occurrence must
    /// not collide with any of these names.
    pub(super) locals: BTreeSet<String>,
}

pub(super) struct ScopeInfo {
    pub(super) pos: usize,
    pub(super) imports: BTreeSet<String>,
    pub(super) indent: String,
    pub(super) has_glob: bool,
    pub(super) mappings: BTreeMap<String, String>,
    pub(super) defs: BTreeSet<String>,
    /// Names mentioned inside macro bodies whose grammar we do not understand.
    /// New imports must not capture these names.
    pub(super) opaque_names: BTreeSet<String>,
}

pub(super) struct Collector<'a> {
    pub(super) occs: Vec<Occurrence>,
    ignore: &'a BTreeSet<String>,
    scope: Vec<String>,
    pub(super) scopes: BTreeMap<String, ScopeInfo>,
    lines: &'a Lines<'a>,
    mappings: BTreeMap<String, String>,
    binding_ids: BTreeMap<String, usize>,
    next_binding_id: usize,
    pub(super) protected_bindings: BTreeSet<usize>,
    internal: BTreeSet<String>,
    cfg: BTreeSet<String>,
    /// Stack of locals introduced by the enclosing function/closure frames.
    fn_locals: Vec<BTreeSet<String>>,
}

fn path_byte_span(path: &SynPath, lines: &Lines<'_>) -> Option<(usize, usize)> {
    let first = path.segments.first()?;
    let last = path.segments.last()?;
    let st = first.ident.span().start();
    let en = last.ident.span().end();
    Some((lines.to_byte(st.line, st.column)?, lines.to_byte(en.line, en.column)?))
}

impl<'a> Collector<'a> {
    pub(super) fn new(ignore: &'a BTreeSet<String>, lines: &'a Lines<'a>) -> Self {
        Self {
            occs: Vec::new(),
            ignore,
            scope: Vec::new(),
            scopes: BTreeMap::new(),
            lines,
            mappings: BTreeMap::new(),
            binding_ids: BTreeMap::new(),
            next_binding_id: 0,
            protected_bindings: BTreeSet::new(),
            internal: BTreeSet::new(),
            cfg: BTreeSet::new(),
            fn_locals: Vec::new(),
        }
    }

    fn alloc_binding(&mut self) -> usize {
        let id = self.next_binding_id;
        self.next_binding_id += 1;
        id
    }

    fn install_scope_mappings(
        &mut self,
        raw: BTreeMap<String, String>,
        inherited: BTreeMap<String, (String, usize)>,
    ) {
        let mut combined: BTreeMap<String, String> = inherited
            .iter()
            .map(|(name, (target, _))| (name.clone(), target.clone()))
            .collect();
        combined.extend(raw.clone());
        let snapshot = combined.clone();
        let mut cache = BTreeMap::new();
        let resolved: BTreeMap<_, _> = raw
            .into_iter()
            .map(|(name, target)| {
                let target = resolve_path(&target, &snapshot, &mut cache, 0);
                (name, target)
            })
            .collect();

        self.mappings = inherited
            .iter()
            .map(|(name, (target, _))| (name.clone(), target.clone()))
            .collect();
        self.binding_ids = inherited.into_iter().map(|(name, (_, id))| (name, id)).collect();
        for (name, target) in resolved {
            let id = self.alloc_binding();
            self.mappings.insert(name.clone(), target);
            self.binding_ids.insert(name, id);
        }
    }

    fn cur_cfg(&self) -> Vec<String> {
        self.cfg.iter().cloned().collect()
    }

    fn cur_scope(&self) -> String {
        self.scope.join("::")
    }

    fn add_local(&mut self, name: String) {
        if let Some(top) = self.fn_locals.last_mut() {
            top.insert(name);
        }
    }

    fn cur_locals(&self) -> BTreeSet<String> {
        self.fn_locals.iter().flatten().cloned().collect()
    }

    fn expand(&self, first: &str, rest: &[String]) -> Option<String> {
        self.mappings.get(first).and_then(|base| {
            (base.split("::").next()? != first || rest.is_empty()).then(|| {
                if rest.is_empty() { base.clone() } else { format!("{base}::{}", rest.join("::")) }
            })
        })
    }

    fn with_cfg<F: FnOnce(&mut Self)>(&mut self, attrs: &[Attribute], f: F) {
        let added: Vec<_> = extract_cfg(attrs)
            .into_iter()
            .filter(|c| self.cfg.insert(c.clone()))
            .collect();
        f(self);
        added.iter().for_each(|c| {
            self.cfg.remove(c);
        });
    }

    /// Run `f` inside a fresh function/closure frame: `mappings` and
    /// `internal` are saved and restored, and `locals` becomes the new
    /// top entry on the locals stack. Frame depth is implied by
    /// `fn_locals.len()`.
    fn with_frame<F: FnOnce(&mut Self)>(&mut self, locals: BTreeSet<String>, f: F) {
        let saved_mappings = self.mappings.clone();
        let saved_binding_ids = self.binding_ids.clone();
        let saved_internal = self.internal.clone();
        self.fn_locals.push(locals);
        f(self);
        self.fn_locals.pop();
        self.mappings = saved_mappings;
        self.binding_ids = saved_binding_ids;
        self.internal = saved_internal;
    }

    fn with_fn<F: FnOnce(&mut Self)>(&mut self, sig: &Signature, f: F) {
        let mut locals = BTreeSet::new();
        sig.inputs
            .iter()
            .filter_map(|i| match i {
                FnArg::Typed(t) => Some(&t.pat),
                _ => None,
            })
            .for_each(|p| collect_pat(p, &mut locals));
        self.with_frame(locals, f);
    }

    fn record_path(&mut self, path: &SynPath, is_type: bool) {
        if path.segments.len() < 2 {
            return;
        }
        // Skip paths with turbofish generics on non-last segments.
        // The byte span covers the full text between first and last idents,
        // so generics like `::<YAML>` between segments would be lost in the replacement.
        let has_inner_generics = path
            .segments
            .iter()
            .rev()
            .skip(1)
            .any(|s| !matches!(s.arguments, syn::PathArguments::None));
        if has_inner_generics {
            return;
        }
        if let Some(span) = path_byte_span(path, self.lines) {
            self.record(path, span, is_type);
        }
    }

    /// Record `path` only when it is not behind a `<T as Trait>::…` qualified
    /// self — the qself form rebinds the leading segments and the simple
    /// name-based dequalification doesn't apply.
    fn record_if_unqual(&mut self, qself: Option<&QSelf>, path: &SynPath, is_type: bool) {
        if qself.is_none() {
            self.record_path(path, is_type);
        }
    }

    fn record(&mut self, path: &SynPath, span: (usize, usize), is_type: bool) {
        let segs = &path.segments;
        if segs.len() < 2 {
            return;
        }
        let first = segs[0].ident.to_string();
        if self.internal.contains(&first) {
            return;
        }
        let binding = self.binding_ids.get(&first).copied();

        let rest: Vec<String> = segs.iter().skip(1).map(|s| s.ident.to_string()).collect();
        let (full, eff) = match self.expand(&first, &rest) {
            Some(e) => {
                let eff = e.split("::").next().unwrap_or(&first).to_string();
                (e, eff)
            }
            None => (path_str(path), first.clone()),
        };

        let starts_upper = eff.chars().next().is_some_and(char::is_uppercase);
        if eff == "Self" || starts_upper || self.ignore.contains(&eff) {
            return;
        }

        let parts: Vec<&str> = full.split("::").collect();
        if !is_type {
            let parent = parts.get(parts.len().saturating_sub(2)).unwrap_or(&"");
            let is_type_method = parent.chars().next().is_some_and(char::is_uppercase);
            if PRIMITIVES.contains(parent) {
                return;
            }
            if is_type_method {
                let type_path = parts[..parts.len() - 1].join("::");
                let suffix = parts[parts.len() - 1..].join("::");
                self.occs.push(Occurrence {
                    path: type_path,
                    span,
                    scope: self.cur_scope(),
                    cfg: self.cur_cfg(),
                    suffix,
                    binding,
                    locals: self.cur_locals(),
                });
                return;
            }
        } else if PRIMITIVES.contains(&rest.last().unwrap().as_str()) {
            return;
        }

        self.occs.push(Occurrence {
            path: full,
            span,
            scope: self.cur_scope(),
            cfg: self.cur_cfg(),
            suffix: String::new(),
            binding,
            locals: self.cur_locals(),
        });
    }

    fn visit_fmt_args(&mut self, m: &Macro) -> bool {
        if let Ok(args) = Punctuated::<Expr, Token![,]>::parse_terminated.parse2(m.tokens.clone()) {
            args.into_iter().skip(1).for_each(|a| self.visit_expr(&a));
            true
        } else {
            false
        }
    }
}

impl Visit<'_> for Collector<'_> {
    fn visit_item_use(&mut self, n: &ItemUse) {
        if !self.fn_locals.is_empty() {
            let mut raw = BTreeMap::new();
            collect_mappings(&n.tree, &mut raw);
            let mut combined = self.mappings.clone();
            combined.extend(raw.clone());
            let mut cache = BTreeMap::new();
            for (name, target) in raw {
                let target = resolve_path(&target, &combined, &mut cache, 0);
                let id = self.alloc_binding();
                self.mappings.insert(name.clone(), target);
                self.binding_ids.insert(name, id);
            }
            if is_internal(&n.tree) {
                collect_idents(&n.tree, &mut self.internal);
            }
        }
        visit::visit_item_use(self, n);
    }

    fn visit_item_fn(&mut self, n: &ItemFn) {
        self.with_cfg(&n.attrs, |s| s.with_fn(&n.sig, |s| visit::visit_item_fn(s, n)));
    }

    fn visit_impl_item_fn(&mut self, n: &ImplItemFn) {
        self.with_cfg(&n.attrs, |s| s.with_fn(&n.sig, |s| visit::visit_impl_item_fn(s, n)));
    }

    fn visit_trait_item_fn(&mut self, n: &TraitItemFn) {
        self.with_cfg(&n.attrs, |s| s.with_fn(&n.sig, |s| visit::visit_trait_item_fn(s, n)));
    }

    fn visit_expr_closure(&mut self, n: &ExprClosure) {
        let mut locals = BTreeSet::new();
        for i in &n.inputs {
            collect_pat(i, &mut locals);
        }
        self.with_frame(locals, |s| visit::visit_expr_closure(s, n));
    }

    fn visit_local(&mut self, n: &Local) {
        self.with_cfg(&n.attrs, |s| {
            if let Some(init) = &n.init {
                s.visit_expr(&init.expr);
                if let Some((_, e)) = &init.diverge {
                    s.visit_expr(e);
                }
            }
            let mut locals = BTreeSet::new();
            collect_pat(&n.pat, &mut locals);
            locals.into_iter().for_each(|name| s.add_local(name));
            visit_pat(s, &n.pat);
        });
    }

    fn visit_item_impl(&mut self, n: &ItemImpl) {
        self.with_cfg(&n.attrs, |s| {
            if let Some((_, path, _)) = &n.trait_ {
                s.record_path(path, true);
            }
            visit::visit_item_impl(s, n);
        });
    }

    fn visit_expr_path(&mut self, n: &ExprPath) {
        self.record_if_unqual(n.qself.as_ref(), &n.path, false);
        visit::visit_expr_path(self, n);
    }

    fn visit_expr_struct(&mut self, n: &ExprStruct) {
        self.record_if_unqual(n.qself.as_ref(), &n.path, true);
        visit::visit_expr_struct(self, n);
    }

    fn visit_item_mod(&mut self, n: &ItemMod) {
        let Some((brace, items)) = &n.content else {
            visit::visit_item_mod(self, n);
            return;
        };
        let saved_mappings = self.mappings.clone();
        let saved_binding_ids = self.binding_ids.clone();
        let saved_cfg = std::mem::take(&mut self.cfg);
        self.scope.push(n.ident.to_string());
        let scope = self.cur_scope();
        let acc = accumulate_uses(items);
        let inherited = if acc.super_glob {
            saved_mappings
                .iter()
                .filter_map(|(name, target)| {
                    saved_binding_ids
                        .get(name)
                        .map(|id| (name.clone(), (target.clone(), *id)))
                })
                .collect()
        } else {
            BTreeMap::new()
        };
        self.install_scope_mappings(acc.mappings.clone(), inherited);
        let defs = collect_defs(items);
        let indent = items.first().map_or_else(
            || " ".repeat(DEFAULT_INDENT_WIDTH * self.scope.len()),
            |i| " ".repeat(i.span().start().column),
        );
        let pos = acc
            .last_use_line
            .map_or_else(|| self.lines.end(brace.span.open().end().line), |l| self.lines.end(l));
        self.scopes.insert(
            scope,
            ScopeInfo {
                pos,
                imports: acc.imports,
                indent,
                has_glob: acc.has_glob,
                mappings: self.mappings.clone(),
                defs,
                opaque_names: BTreeSet::new(),
            },
        );
        visit::visit_item_mod(self, n);
        self.scope.pop();
        self.mappings = saved_mappings;
        self.binding_ids = saved_binding_ids;
        self.cfg = saved_cfg;
    }

    fn visit_macro(&mut self, n: &Macro) {
        self.record_path(&n.path, false);
        let is_fmt = n.path.segments.len() == 1
            && n.path
                .segments
                .first()
                .is_some_and(|s| FMT_MACROS.contains(&s.ident.to_string().as_str()));
        let parsed = is_fmt && self.visit_fmt_args(n);
        if !parsed {
            let names = collect_token_names(n.tokens.clone());
            if let Some(info) = self.scopes.get_mut(&self.cur_scope()) {
                info.opaque_names.extend(names.iter().cloned());
            }
            names
                .iter()
                .filter_map(|name| self.binding_ids.get(name))
                .for_each(|id| {
                    self.protected_bindings.insert(*id);
                });
        }
        visit::visit_macro(self, n);
    }

    fn visit_type_path(&mut self, n: &TypePath) {
        self.record_if_unqual(n.qself.as_ref(), &n.path, true);
        visit::visit_type_path(self, n);
    }

    fn visit_trait_bound(&mut self, n: &TraitBound) {
        // TraitBound carries a bare `Path` (not a `TypePath`), so generic
        // constraints like `T: std::fmt::Display` and `where T: ...` would
        // otherwise be skipped.
        self.record_path(&n.path, true);
        visit::visit_trait_bound(self, n);
    }

    fn visit_pat_struct(&mut self, n: &PatStruct) {
        // is_type=false so an enum struct-variant `Foo::Bar { x }` imports
        // `Foo` and keeps the call site `Foo::Bar { x }`, consistent with the
        // tuple-struct and unit-variant forms.
        self.record_if_unqual(n.qself.as_ref(), &n.path, false);
        visit::visit_pat_struct(self, n);
    }

    fn visit_pat_tuple_struct(&mut self, n: &PatTupleStruct) {
        // is_type=false so the type-method split treats `Foo::Bar(x)` as
        // importing `Foo` and rewriting to `Foo::Bar(x)`, matching how the
        // call form `Foo::Bar(x)` is handled in expression position.
        self.record_if_unqual(n.qself.as_ref(), &n.path, false);
        visit::visit_pat_tuple_struct(self, n);
    }
}

fn collect_pat(pat: &Pat, out: &mut BTreeSet<String>) {
    match pat {
        Pat::Ident(p) => {
            out.insert(p.ident.to_string());
        }
        Pat::Tuple(t) => t.elems.iter().for_each(|p| collect_pat(p, out)),
        Pat::Struct(s) => s.fields.iter().for_each(|f| collect_pat(&f.pat, out)),
        Pat::TupleStruct(t) => t.elems.iter().for_each(|p| collect_pat(p, out)),
        Pat::Slice(s) => s.elems.iter().for_each(|p| collect_pat(p, out)),
        Pat::Reference(r) => collect_pat(&r.pat, out),
        Pat::Or(o) => o.cases.iter().for_each(|p| collect_pat(p, out)),
        _ => {}
    }
}

pub(super) fn collect_occurrences<'a>(
    ast: &File,
    lines: &'a Lines<'a>,
    ignore: &'a BTreeSet<String>,
) -> Collector<'a> {
    let mut c = Collector::new(ignore, lines);
    let mut root = file_scope(ast, lines);
    c.install_scope_mappings(root.mappings.clone(), BTreeMap::new());
    root.mappings = c.mappings.clone();
    c.scopes.insert(String::new(), root);
    Visit::visit_file(&mut c, ast);
    c
}

fn collect_token_names(tokens: proc_macro2::TokenStream) -> BTreeSet<String> {
    use proc_macro2::TokenTree;

    tokens.into_iter().fold(BTreeSet::new(), |mut names, token| {
        match token {
            TokenTree::Ident(ident) => {
                names.insert(ident.to_string());
            }
            TokenTree::Group(group) => {
                names.extend(collect_token_names(group.stream()));
            }
            _ => {}
        }
        names
    })
}

fn file_scope(ast: &File, lines: &Lines<'_>) -> ScopeInfo {
    let acc = accumulate_uses(&ast.items);
    // Default below any inner attributes (`#![…]`) and module doc comments
    // (`//! …`, lowered to `#![doc = "…"]`) so a fresh import is never
    // inserted above them — which would be invalid Rust.
    let attr_end = ast
        .attrs
        .iter()
        .map(|a| lines.end(a.span().end().line))
        .max()
        .unwrap_or(0);
    let pos = acc.last_use_line.map_or(attr_end, |l| lines.end(l));
    ScopeInfo {
        pos,
        imports: acc.imports,
        indent: String::new(),
        has_glob: acc.has_glob,
        mappings: acc.mappings,
        defs: collect_defs(&ast.items),
        opaque_names: BTreeSet::new(),
    }
}

struct UseAccumulator {
    imports: BTreeSet<String>,
    has_glob: bool,
    super_glob: bool,
    mappings: BTreeMap<String, String>,
    last_use_line: Option<usize>,
}

fn accumulate_uses(items: &[Item]) -> UseAccumulator {
    let mut acc = UseAccumulator {
        imports: BTreeSet::new(),
        has_glob: false,
        super_glob: false,
        mappings: BTreeMap::new(),
        last_use_line: None,
    };
    items
        .iter()
        .filter_map(|i| match i {
            Item::Use(u) => Some(u),
            _ => None,
        })
        .for_each(|u| {
            acc.last_use_line = Some(u.span().end().line);
            collect_idents(&u.tree, &mut acc.imports);
            acc.has_glob |= has_glob_import(&u.tree);
            acc.super_glob |= has_super_glob(&u.tree);
            collect_mappings(&u.tree, &mut acc.mappings);
        });
    acc
}
