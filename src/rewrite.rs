use std::{
    cmp::Reverse,
    collections::{BTreeMap, BTreeSet},
    fs::{read_to_string, write},
    path::Path,
};

use anyhow::{Context, Result};
use similar::{ChangeTag, TextDiff};
use syn::{
    Attribute, Expr, ExprCall, ExprClosure, File, ImplItemFn, Item, ItemConst, ItemEnum, ItemFn,
    ItemImpl, ItemMod, ItemStatic, ItemStruct, ItemTrait, ItemType, ItemUnion, ItemUse, Local,
    Macro, Pat, Path as SynPath, Signature, TypePath, UseTree, parse_file,
    spanned::Spanned,
    visit::{self, Visit, visit_pat},
};

const PRIMITIVES: &[&str] = &[
    "bool", "char", "str", "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64",
    "u128", "usize", "f32", "f64",
];
const PRELUDE: &[&str] = &["Option", "Result", "Box", "String", "Vec"];
const FMT_MACROS: &[&str] = &[
    "println",
    "print",
    "eprintln",
    "eprint",
    "format",
    "format_args",
    "write",
    "writeln",
    "panic",
    "unreachable",
    "todo",
    "unimplemented",
    "trace",
    "debug",
    "info",
    "warn",
    "error",
];

#[derive(Clone)]
struct Occurrence {
    path: String,
    span: (usize, usize),
    scope: String,
    cfg: Vec<String>,
}

struct ScopeInfo {
    pos: usize,
    imports: BTreeSet<String>,
    indent: String,
    locals: BTreeSet<String>,
}

struct Collector<'a> {
    occs: Vec<Occurrence>,
    ignore: &'a BTreeSet<String>,
    scope: Vec<String>,
    scopes: BTreeMap<String, ScopeInfo>,
    lines: &'a Lines,
    mappings: BTreeMap<String, String>,
    internal: BTreeSet<String>,
    depth: usize,
    cfg: BTreeSet<String>,
}

fn path_byte_span(path: &SynPath, lines: &Lines) -> Option<(usize, usize)> {
    let first = path.segments.first()?;
    let last = path.segments.last()?;
    let st = first.ident.span().start();
    let en = last.ident.span().end();
    Some((lines.to_byte(st.line, st.column)?, lines.to_byte(en.line, en.column)?))
}

impl<'a> Collector<'a> {
    fn new(ignore: &'a BTreeSet<String>, lines: &'a Lines) -> Self {
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
        }
    }

    fn cur_cfg(&self) -> Vec<String> {
        self.cfg.iter().cloned().collect()
    }
    fn cur_scope(&self) -> String {
        self.scope.join("::")
    }
    fn add_local(&mut self, name: String) {
        let scope = self.cur_scope();
        if let Some(info) = self.scopes.get_mut(&scope) {
            info.locals.insert(name);
        }
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

    fn with_fn<F: FnOnce(&mut Self)>(&mut self, sig: &Signature, f: F) {
        self.depth += 1;
        let mut b = BTreeSet::new();
        for i in &sig.inputs {
            if let syn::FnArg::Typed(t) = i {
                collect_pat(&t.pat, &mut b);
            }
        }
        for name in b {
            self.add_local(name);
        }
        f(self);
        self.depth -= 1;
    }

    fn record_path(&mut self, path: &SynPath, is_type: bool) {
        if path.segments.len() < 2 {
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
            if is_type_method || PRIMITIVES.contains(parent) {
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
        self.depth += 1;
        let mut b = BTreeSet::new();
        for i in &n.inputs {
            collect_pat(i, &mut b);
        }
        for name in b {
            self.add_local(name);
        }
        visit::visit_expr_closure(self, n);
        self.depth -= 1;
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

    fn visit_item_mod(&mut self, n: &ItemMod) {
        self.with_cfg(&n.attrs, |s| {
            if let Some((brace, items)) = &n.content {
                s.scope.push(n.ident.to_string());
                let scope = s.cur_scope();
                let mut last_use = None;
                let mut imports = BTreeSet::new();
                for i in items {
                    if let Item::Use(u) = i {
                        last_use = Some(u.span().end().line);
                        collect_idents(&u.tree, &mut imports);
                    }
                }
                let indent = items
                    .first()
                    .map(|i| " ".repeat(i.span().start().column))
                    .unwrap_or(" ".repeat(4 * s.scope.len()));
                let pos = last_use
                    .map(|l| s.lines.end(l))
                    .unwrap_or_else(|| s.lines.end(brace.span.open().end().line));
                s.scopes
                    .insert(scope, ScopeInfo { pos, imports, indent, locals: BTreeSet::new() });
                visit::visit_item_mod(s, n);
                s.scope.pop();
            } else {
                visit::visit_item_mod(s, n);
            }
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

fn extract_cfg(attrs: &[Attribute]) -> Vec<String> {
    attrs
        .iter()
        .filter_map(|a| {
            a.path()
                .is_ident("cfg")
                .then(|| a.meta.require_list().ok().map(|l| format!("cfg({})", l.tokens)))?
        })
        .collect()
}

#[derive(Clone)]
struct Strategy {
    full: String,
    segs: Vec<String>,
    len: usize,
    exists: bool,
}

impl Strategy {
    fn new(p: &str) -> Self {
        let segs: Vec<_> = p.split("::").map(String::from).collect();
        Self {
            full: p.into(),
            len: segs.len(),
            segs,
            exists: false,
        }
    }
    fn ident(&self) -> &str {
        &self.segs[self.len - 1]
    }
    fn up(&mut self) -> bool {
        if self.len > 1 {
            self.len -= 1;
            true
        } else {
            false
        }
    }
    fn same(&self) -> bool {
        self.len == 1
    }
    fn use_stmt(&self) -> Option<String> {
        (!self.exists).then(|| format!("use {};", self.segs[..self.len].join("::")))
    }
    fn repl(&self) -> String {
        if self.len == self.segs.len() {
            self.segs.last().unwrap().clone()
        } else {
            format!("{}::{}", self.segs[self.len - 1], self.segs[self.len..].join("::"))
        }
    }
}

fn resolve(
    paths: &[String],
    existing: &BTreeSet<String>,
    mappings: &BTreeMap<String, String>,
) -> BTreeMap<String, Strategy> {
    let mut strats: Vec<_> = paths.iter().map(|p| Strategy::new(p)).collect();
    for s in &mut strats {
        if mappings.get(s.segs.last().unwrap()).is_some_and(|m| m == &s.full) {
            s.exists = true;
        }
    }
    loop {
        let mut groups: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        for (i, s) in strats.iter().enumerate() {
            if !s.same() && !s.exists {
                groups.entry(s.ident().into()).or_default().push(i);
            }
        }
        let mut changed = false;
        for v in groups.values().filter(|v| v.len() > 1) {
            for &i in v {
                changed |= strats[i].up();
            }
        }
        if !changed {
            break;
        }
    }
    loop {
        let mut changed = false;
        for s in &mut strats {
            if !s.same() && !s.exists && existing.contains(s.ident()) {
                changed |= s.up();
            }
        }
        if !changed {
            break;
        }
    }
    let mut used = BTreeSet::new();
    let mut res = BTreeMap::new();
    for s in strats {
        if !s.same() && used.insert(s.ident().to_string()) {
            res.insert(s.full.clone(), s);
        }
    }
    res
}

enum Edit {
    Ins(usize, String),
    Rep(usize, usize, String),
}
impl Edit {
    fn pos(&self) -> usize {
        match self {
            Edit::Ins(p, _) => *p,
            Edit::Rep(s, _, _) => *s,
        }
    }
}

pub fn process_file(path: &Path, ignore: &[String], dry: bool) -> Result<Option<String>> {
    let src = read_to_string(path).with_context(|| format!("read {}", path.display()))?;
    let ast: File = parse_file(&src).with_context(|| format!("parse {}", path.display()))?;
    let lines = Lines::new(&src);
    let ignore: BTreeSet<_> = ignore.iter().cloned().collect();

    let (c, file_imports) = collect_occurrences(&ast, &lines, &ignore);
    if c.occs.is_empty() {
        return Ok(None);
    }

    let edits = build_edits(&c, &ast, &file_imports);
    if edits.is_empty() {
        return Ok(None);
    }

    apply_edits(path, &src, edits, dry)
}

fn collect_occurrences<'a>(
    ast: &File,
    lines: &'a Lines,
    ignore: &'a BTreeSet<String>,
) -> (Collector<'a>, BTreeSet<String>) {
    let mut c = Collector::new(ignore, lines);
    let (pos, file_imports) = collect_file_context(ast, lines);
    c.scopes.insert(
        String::new(),
        ScopeInfo {
            pos,
            imports: file_imports.clone(),
            indent: String::new(),
            locals: BTreeSet::new(),
        },
    );
    c.visit_file(ast);

    let mut cache = BTreeMap::new();
    let mappings_snap = c.mappings.clone();
    for v in c.mappings.values_mut() {
        *v = resolve_path(v, &mappings_snap, &mut cache, 0);
    }
    for o in &mut c.occs {
        o.path = resolve_path(&o.path, &c.mappings, &mut cache, 0);
    }

    (c, file_imports)
}

fn build_edits(c: &Collector, ast: &File, file_imports: &BTreeSet<String>) -> Vec<Edit> {
    let prelude = collect_prelude(ast);
    let defs = collect_defs(ast);
    let mut by_scope: BTreeMap<&str, Vec<&Occurrence>> = BTreeMap::new();
    for o in &c.occs {
        by_scope.entry(&o.scope).or_default().push(o);
    }

    let mut edits = Vec::new();
    for (scope, occs) in &by_scope {
        let info = c.scopes.get(*scope).unwrap_or_else(|| c.scopes.get("").unwrap());
        let mut existing = file_imports.clone();
        existing.extend(info.imports.clone());
        existing.extend(prelude.clone());
        existing.extend(defs.clone());
        existing.extend(info.locals.clone());

        let scope_paths: Vec<_> = occs
            .iter()
            .map(|o| o.path.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let strats = resolve(&scope_paths, &existing, &c.mappings);

        let mut by_cfg: BTreeMap<Vec<String>, BTreeSet<String>> = BTreeMap::new();
        for o in occs {
            if let Some(s) = strats.get(&o.path) {
                if let Some(u) = s.use_stmt() {
                    by_cfg.entry(o.cfg.clone()).or_default().insert(u);
                }
                edits.push(Edit::Rep(o.span.0, o.span.1, s.repl()));
            }
        }

        if !by_cfg.is_empty() {
            let ind = &info.indent;
            let mut blocks = Vec::new();
            for (cfg, stmts) in &by_cfg {
                if cfg.is_empty() {
                    blocks.extend(stmts.iter().map(|s| format!("{ind}{s}")));
                } else {
                    let pre: String = cfg.iter().map(|c| format!("{ind}#[{c}]\n")).collect();
                    blocks.extend(stmts.iter().map(|s| format!("{pre}{ind}{s}")));
                }
            }
            if !blocks.is_empty() {
                edits.push(Edit::Ins(info.pos, format!("\n{}\n", blocks.join("\n"))));
            }
        }
    }
    edits
}

fn apply_edits(path: &Path, src: &str, mut edits: Vec<Edit>, dry: bool) -> Result<Option<String>> {
    edits.sort_by_key(|e| Reverse(e.pos()));
    let mut out = src.to_string();
    for e in edits {
        match e {
            Edit::Ins(p, t) => out.insert_str(p, &t),
            Edit::Rep(s, e, t) => out.replace_range(s..e, &t),
        }
    }
    if out == src {
        return Ok(None);
    }
    if dry {
        return Ok(Some(diff(path, src, &out)));
    }
    write(path, &out).with_context(|| format!("write {}", path.display()))?;
    Ok(Some(String::new()))
}

fn path_str(p: &SynPath) -> String {
    p.segments
        .iter()
        .map(|s| s.ident.to_string())
        .collect::<Vec<_>>()
        .join("::")
}

struct Lines(Vec<usize>);
impl Lines {
    fn new(src: &str) -> Self {
        let mut starts = vec![0];
        for (i, c) in src.char_indices() {
            if c == '\n' {
                starts.push(i + 1);
            }
        }
        Self(starts)
    }
    fn to_byte(&self, line: usize, col: usize) -> Option<usize> {
        if line == 0 || line > self.0.len() {
            return None;
        }
        Some(self.0[line - 1] + col)
    }
    fn end(&self, line: usize) -> usize {
        if line == 0 || line > self.0.len() {
            return 0;
        }
        if line < self.0.len() { self.0[line] - 1 } else { self.0[line - 1] }
    }
}

fn collect_file_context(ast: &File, lines: &Lines) -> (usize, BTreeSet<String>) {
    let mut imports = BTreeSet::new();
    let mut pos = 0;
    for i in &ast.items {
        if let Item::Use(u) = i {
            pos = lines.end(u.span().end().line);
            collect_idents(&u.tree, &mut imports);
        }
    }
    (pos, imports)
}

fn walk_use_tree<F: FnMut(&[String], &UseTree)>(
    tree: &UseTree,
    prefix: &mut Vec<String>,
    f: &mut F,
) {
    match tree {
        UseTree::Path(p) => {
            prefix.push(p.ident.to_string());
            walk_use_tree(&p.tree, prefix, f);
            prefix.pop();
        }
        UseTree::Group(g) => g.items.iter().for_each(|t| walk_use_tree(t, prefix, f)),
        leaf => f(prefix, leaf),
    }
}

fn collect_idents(tree: &UseTree, out: &mut BTreeSet<String>) {
    walk_use_tree(tree, &mut Vec::new(), &mut |prefix, leaf| match leaf {
        UseTree::Name(n) => {
            let name = n.ident.to_string();
            if name == "self" {
                if let Some(p) = prefix.last() {
                    out.insert(p.clone());
                }
            } else {
                out.insert(name);
            }
        }
        UseTree::Rename(r) => {
            out.insert(r.rename.to_string());
        }
        _ => {}
    });
}

fn is_internal(tree: &UseTree) -> bool {
    match tree {
        UseTree::Path(p) => matches!(p.ident.to_string().as_str(), "crate" | "self" | "super"),
        UseTree::Group(g) => g.items.iter().all(is_internal),
        _ => false,
    }
}

fn resolve_path(
    path: &str,
    mappings: &BTreeMap<String, String>,
    cache: &mut BTreeMap<String, String>,
    depth: usize,
) -> String {
    if depth > 20 {
        return path.to_string(); // cycle protection
    }
    if let Some(resolved) = cache.get(path) {
        return resolved.clone();
    }

    let segs: Vec<&str> = path.split("::").collect();
    let first = segs.first().copied().unwrap_or("");

    let result = if let Some(base) = mappings.get(first) {
        if base.split("::").next().unwrap_or("") != first {
            let resolved_base = resolve_path(base, mappings, cache, depth + 1);
            let mut n: Vec<&str> = resolved_base.split("::").collect();
            n.extend(segs.iter().skip(1));
            n.join("::")
        } else {
            path.to_string()
        }
    } else {
        path.to_string()
    };

    cache.insert(path.to_string(), result.clone());
    result
}

fn collect_mappings(tree: &UseTree, out: &mut BTreeMap<String, String>) {
    walk_use_tree(tree, &mut Vec::new(), &mut |prefix, leaf| {
        let full = |name: &str| {
            let mut p = prefix.to_vec();
            p.push(name.into());
            p.join("::")
        };
        match leaf {
            UseTree::Name(n) => {
                let name = n.ident.to_string();
                if name == "self" {
                    if let Some(l) = prefix.last() {
                        out.insert(l.clone(), prefix.join("::"));
                    }
                } else {
                    out.insert(name.clone(), full(&name));
                }
            }
            UseTree::Rename(r) => {
                let (alias, orig) = (r.rename.to_string(), r.ident.to_string());
                if orig == "self" {
                    out.insert(alias, prefix.join("::"));
                } else {
                    out.insert(alias, full(&orig));
                }
            }
            _ => {}
        }
    });
}

fn collect_defs(ast: &File) -> BTreeSet<String> {
    let mut s = BTreeSet::new();
    for i in &ast.items {
        match i {
            Item::Fn(f) => {
                s.insert(f.sig.ident.to_string());
            }
            Item::Struct(ItemStruct { ident, .. })
            | Item::Enum(ItemEnum { ident, .. })
            | Item::Union(ItemUnion { ident, .. })
            | Item::Trait(ItemTrait { ident, .. })
            | Item::Type(ItemType { ident, .. })
            | Item::Mod(ItemMod { ident, .. }) => {
                s.insert(ident.to_string());
            }
            Item::Static(ItemStatic { ident, .. }) | Item::Const(ItemConst { ident, .. }) => {
                s.insert(ident.to_string());
            }
            Item::Impl(ItemImpl { items, .. }) => {
                for ii in items {
                    if let syn::ImplItem::Fn(f) = ii {
                        s.insert(f.sig.ident.to_string());
                    }
                }
            }
            _ => {}
        }
    }
    s
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

fn collect_prelude(ast: &File) -> BTreeSet<String> {
    struct V(BTreeSet<String>);
    impl<'a> Visit<'a> for V {
        fn visit_type_path(&mut self, n: &'a TypePath) {
            if n.qself.is_none() && n.path.segments.len() == 1 {
                let id = n.path.segments[0].ident.to_string();
                if PRELUDE.contains(&id.as_str()) {
                    self.0.insert(id);
                }
            }
            visit::visit_type_path(self, n);
        }
    }
    let mut v = V(BTreeSet::new());
    v.visit_file(ast);
    v.0
}

fn diff(path: &Path, old: &str, new: &str) -> String {
    use std::fmt::Write;
    let d = TextDiff::from_lines(old, new);
    let mut out = String::new();
    writeln!(out, "--- {}", path.display()).unwrap();
    writeln!(out, "+++ {}", path.display()).unwrap();
    for h in d.unified_diff().context_radius(3).iter_hunks() {
        writeln!(out, "{}", h.header()).unwrap();
        for c in h.iter_changes() {
            write!(
                out,
                "{}{c}",
                match c.tag() {
                    ChangeTag::Delete => "-",
                    ChangeTag::Insert => "+",
                    ChangeTag::Equal => " ",
                }
            )
            .unwrap();
            if c.missing_newline() {
                writeln!(out).unwrap();
            }
        }
    }
    out
}
