use std::collections::{BTreeMap, BTreeSet};

use syn::{
    Attribute, Expr, ExprCall, ExprClosure, ExprStruct, ImplItemFn, Item, ItemFn, ItemImpl,
    ItemMod, ItemUse, Local, Macro, Pat, Path as SynPath, Signature, TypePath,
    spanned::Spanned,
    visit::{self, Visit, visit_pat},
};

use super::{
    attrs::extract_cfg,
    consts::{FMT_MACROS, PRIMITIVES},
    defs::collect_defs,
    source::Lines,
    use_tree::{collect_idents, collect_mappings, has_glob_import, is_internal, path_str},
};

#[derive(Clone)]
pub(super) struct Occurrence {
    pub(super) path: String,
    pub(super) span: (usize, usize),
    pub(super) scope: String,
    pub(super) cfg: Vec<String>,
    pub(super) suffix: String,
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
}

pub(super) struct Collector<'a> {
    pub(super) occs: Vec<Occurrence>,
    ignore: &'a BTreeSet<String>,
    scope: Vec<String>,
    pub(super) scopes: BTreeMap<String, ScopeInfo>,
    lines: &'a Lines<'a>,
    pub(super) mappings: BTreeMap<String, String>,
    internal: BTreeSet<String>,
    depth: usize,
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
            internal: BTreeSet::new(),
            depth: 0,
            cfg: BTreeSet::new(),
            fn_locals: Vec::new(),
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
        let mut out = BTreeSet::new();
        for f in &self.fn_locals {
            out.extend(f.iter().cloned());
        }
        out
    }

    fn expand(&self, first: &str, rest: &[String]) -> Option<String> {
        self.mappings.get(first).and_then(|base| {
            (base.split("::").next()? != first || rest.is_empty()).then(|| {
                if rest.is_empty() { base.clone() } else { format!("{base}::{}", rest.join("::")) }
            })
        })
    }

    fn with_cfg<F: FnOnce(&mut Self)>(&mut self, attrs: &[Attribute], f: F) {
        let cfgs = extract_cfg(attrs);
        let added: Vec<_> = cfgs.into_iter().filter(|c| self.cfg.insert(c.clone())).collect();
        f(self);
        for c in added {
            self.cfg.remove(&c);
        }
    }

    /// Run `f` inside a fresh function/closure frame: `mappings` and
    /// `internal` are saved and restored, depth is bumped, and `locals`
    /// becomes the new top entry on the locals stack.
    fn with_frame<F: FnOnce(&mut Self)>(&mut self, locals: BTreeSet<String>, f: F) {
        self.depth += 1;
        let saved_mappings = self.mappings.clone();
        let saved_internal = self.internal.clone();
        self.fn_locals.push(locals);
        f(self);
        self.fn_locals.pop();
        self.mappings = saved_mappings;
        self.internal = saved_internal;
        self.depth -= 1;
    }

    fn with_fn<F: FnOnce(&mut Self)>(&mut self, sig: &Signature, f: F) {
        let mut locals = BTreeSet::new();
        for i in &sig.inputs {
            if let syn::FnArg::Typed(t) = i {
                collect_pat(&t.pat, &mut locals);
            }
        }
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

    fn record(&mut self, path: &SynPath, span: (usize, usize), is_type: bool) {
        let segs = &path.segments;
        if segs.len() < 2 {
            return;
        }
        let first = segs[0].ident.to_string();
        if self.internal.contains(&first) {
            return;
        }

        let rest: Vec<String> = segs.iter().skip(1).map(|s| s.ident.to_string()).collect();
        let (full, eff) = self
            .expand(&first, &rest)
            .map(|e| (e.clone(), e.split("::").next().unwrap_or(&first).to_string()))
            .unwrap_or_else(|| (path_str(path), first));

        let starts_upper = eff.chars().next().is_some_and(|c| c.is_uppercase());
        if eff == "Self" || starts_upper || self.ignore.contains(&eff) {
            return;
        }

        let parts: Vec<&str> = full.split("::").collect();
        if !is_type {
            let parent = parts.get(parts.len().saturating_sub(2)).unwrap_or(&"");
            let is_type_method = parent.chars().next().is_some_and(|c| c.is_uppercase());
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
                    locals: self.cur_locals(),
                });
                return;
            }
        } else {
            let last = segs.last().map(|s| s.ident.to_string()).unwrap_or_default();
            if PRIMITIVES.contains(&last.as_str()) {
                return;
            }
        }

        self.occs.push(Occurrence {
            path: full,
            span,
            scope: self.cur_scope(),
            cfg: self.cur_cfg(),
            suffix: String::new(),
            locals: self.cur_locals(),
        });
    }

    fn visit_fmt_args(&mut self, m: &Macro) {
        use syn::{Token, parse::Parser, punctuated::Punctuated};
        if let Ok(args) = Punctuated::<Expr, Token![,]>::parse_terminated.parse2(m.tokens.clone()) {
            for a in args.into_iter().skip(1) {
                self.visit_expr(&a);
            }
        }
    }
}

impl Visit<'_> for Collector<'_> {
    fn visit_item_use(&mut self, n: &ItemUse) {
        collect_mappings(&n.tree, &mut self.mappings);
        if self.depth > 0 && is_internal(&n.tree) {
            collect_idents(&n.tree, &mut self.internal);
        }
        visit::visit_item_use(self, n);
    }

    fn visit_item_fn(&mut self, n: &ItemFn) {
        self.with_cfg(&n.attrs, |s| s.with_fn(&n.sig, |s| visit::visit_item_fn(s, n)));
    }

    fn visit_impl_item_fn(&mut self, n: &ImplItemFn) {
        self.with_cfg(&n.attrs, |s| s.with_fn(&n.sig, |s| visit::visit_impl_item_fn(s, n)));
    }

    fn visit_expr_closure(&mut self, n: &ExprClosure) {
        let mut locals = BTreeSet::new();
        for i in &n.inputs {
            collect_pat(i, &mut locals);
        }
        self.with_frame(locals, |s| visit::visit_expr_closure(s, n));
    }

    fn visit_local(&mut self, n: &Local) {
        if let Some(init) = &n.init {
            self.visit_expr(&init.expr);
            if let Some((_, e)) = &init.diverge {
                self.visit_expr(e);
            }
        }
        let mut b = BTreeSet::new();
        collect_pat(&n.pat, &mut b);
        for name in b {
            self.add_local(name);
        }
        visit_pat(self, &n.pat);
    }

    fn visit_item_impl(&mut self, n: &ItemImpl) {
        self.with_cfg(&n.attrs, |s| {
            if let Some((_, path, _)) = &n.trait_ {
                s.record_path(path, true);
            }
            visit::visit_item_impl(s, n)
        });
    }

    fn visit_expr_call(&mut self, n: &ExprCall) {
        if let syn::Expr::Path(p) = &*n.func
            && p.qself.is_none()
        {
            self.record_path(&p.path, false);
        }
        visit::visit_expr_call(self, n);
    }

    fn visit_expr_struct(&mut self, n: &ExprStruct) {
        if n.qself.is_none() {
            self.record_path(&n.path, true);
        }
        visit::visit_expr_struct(self, n);
    }

    fn visit_item_mod(&mut self, n: &ItemMod) {
        self.with_cfg(&n.attrs, |s| {
            let Some((brace, items)) = &n.content else {
                visit::visit_item_mod(s, n);
                return;
            };
            s.scope.push(n.ident.to_string());
            let scope = s.cur_scope();
            let mut last_use = None;
            let mut imports = BTreeSet::new();
            let mut has_glob = false;
            let mut mappings = BTreeMap::new();
            for u in items.iter().filter_map(|i| match i {
                Item::Use(u) => Some(u),
                _ => None,
            }) {
                last_use = Some(u.span().end().line);
                collect_idents(&u.tree, &mut imports);
                has_glob |= has_glob_import(&u.tree);
                collect_mappings(&u.tree, &mut mappings);
            }
            let defs = collect_defs(items);
            let indent = items
                .first()
                .map(|i| " ".repeat(i.span().start().column))
                .unwrap_or_else(|| " ".repeat(4 * s.scope.len()));
            let pos = last_use
                .map(|l| s.lines.end(l))
                .unwrap_or_else(|| s.lines.end(brace.span.open().end().line));
            s.scopes
                .insert(scope, ScopeInfo { pos, imports, indent, has_glob, mappings, defs });
            visit::visit_item_mod(s, n);
            s.scope.pop();
        });
    }

    fn visit_macro(&mut self, n: &Macro) {
        self.record_path(&n.path, false);
        let is_fmt = n.path.segments.len() == 1
            && n.path
                .segments
                .first()
                .is_some_and(|s| FMT_MACROS.contains(&s.ident.to_string().as_str()));
        if is_fmt {
            self.visit_fmt_args(n);
        }
        visit::visit_macro(self, n);
    }

    fn visit_type_path(&mut self, n: &TypePath) {
        if n.qself.is_none() {
            self.record_path(&n.path, true);
        }
        visit::visit_type_path(self, n);
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
