use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};

use anyhow::{Context, Result};
use fs::{read_to_string, write};
use proc_macro2::Span;
use quote::quote;
use syn::{
    ExprCall, File, Ident, Item, ItemConst, ItemEnum, ItemFn, ItemImpl, ItemMod, ItemStatic,
    ItemStruct, ItemTrait, ItemType, ItemUnion, ItemUse, Pat, Path as SynPath, UseTree, parse_file,
    parse_quote,
    visit_mut::{self, VisitMut},
};
use visit_mut::{visit_local_mut, visit_pat_ident_mut};
#[doc = " Information about a fully-qualified function path we want to shorten."]
#[derive(Clone)]
struct PathInfo {
    full: SynPath,
    last_ident: Ident,
    line: usize,
}
impl std::fmt::Debug for PathInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PathInfo")
            .field("full", &path_to_string(&self.full))
            .field("last_ident", &self.last_ident.to_string())
            .field("line", &self.line)
            .finish()
    }
}
#[doc = " Collect all candidate fully-qualified paths from function calls."]
#[derive(Default)]
struct PathCollector {
    paths: BTreeMap<String, PathInfo>,
    ignore_roots: BTreeSet<String>,
}
impl PathCollector {
    fn new(ignore_roots: &[String]) -> Self {
        Self {
            paths: BTreeMap::new(),
            ignore_roots: ignore_roots.iter().cloned().collect(),
        }
    }
}
impl VisitMut for PathCollector {
    fn visit_expr_call_mut(&mut self, node: &mut ExprCall) {
        if let syn::Expr::Path(expr_path) = &*node.func
            && expr_path.qself.is_none()
        {
            let path = &expr_path.path;
            let segments = &path.segments;
            if segments.len() >= 2 {
                let first_ident = &segments[0].ident;
                let first_name = first_ident.to_string();
                let first_char = first_name.chars().next().unwrap_or('a');
                if first_name != "Self"
                    && !first_char.is_uppercase()
                    && !self.ignore_roots.contains(&first_name)
                {
                    let last_segment = segments.last().unwrap().clone();
                    let last_ident = last_segment.ident.clone();
                    let line = first_ident.span().start().line;
                    let full_str = path_to_string(path);
                    self.paths.entry(full_str.clone()).or_insert(PathInfo {
                        full: path.clone(),
                        last_ident,
                        line,
                    });
                }
            }
        }
        visit_mut::visit_expr_call_mut(self, node);
    }
}
#[doc = " Rewrite fully-qualified paths in function calls to their last segment,"]
#[doc = " but deal correctly with conflicts."]
struct PathRewriter {
    by_string: BTreeMap<String, PathInfo>,
    imported_idents: BTreeSet<String>,
    local_idents: BTreeSet<String>,
    file_path: String,
    alias_on_conflict: bool,
    aliases: BTreeMap<String, Ident>,
}
impl PathRewriter {
    fn new(
        file_path: &Path,
        paths: BTreeMap<String, PathInfo>,
        imported_idents: BTreeSet<String>,
        local_idents: BTreeSet<String>,
        alias_on_conflict: bool,
    ) -> Self {
        Self {
            by_string: paths,
            imported_idents,
            local_idents,
            file_path: file_path.display().to_string(),
            alias_on_conflict,
            aliases: BTreeMap::new(),
        }
    }
    fn has_conflict(&self, ident: &str) -> bool {
        self.imported_idents.contains(ident) || self.local_idents.contains(ident)
    }
    #[doc = " Get or create an alias identifier for a conflicting full path."]
    fn alias_for(&mut self, full: &SynPath) -> Ident {
        let key = path_to_string(full);
        if let Some(id) = self.aliases.get(&key) {
            return id.clone();
        }
        let base = full
            .segments
            .iter()
            .map(|s| s.ident.to_string())
            .collect::<Vec<_>>()
            .join("_");
        let mut candidate = base.clone();
        let mut idx = 1;
        while self.imported_idents.contains(&candidate) || self.local_idents.contains(&candidate) {
            candidate = format!("{base}_{idx}");
            idx += 1;
        }
        let ident = Ident::new(&candidate, Span::call_site());
        self.aliases.insert(key, ident.clone());
        ident
    }
}
impl VisitMut for PathRewriter {
    fn visit_expr_call_mut(&mut self, node: &mut ExprCall) {
        if let syn::Expr::Path(expr_path) = &mut *node.func
            && expr_path.qself.is_none()
        {
            let path = &expr_path.path;
            if path.segments.len() >= 2 {
                let key = path_to_string(path);
                if let Some(info) = self.by_string.get(&key).cloned() {
                    let last_name = info.last_ident.to_string();
                    if self.has_conflict(&last_name) {
                        if self.alias_on_conflict {
                            let alias_ident = self.alias_for(&info.full);
                            expr_path.path.segments.clear();
                            expr_path.path.segments.push(alias_ident.into());
                        } else {
                            eprintln!(
                                "conflict in {}:{}: identifier `{}` is already \
                                 defined/imported; skipping rewrite of `{}`",
                                self.file_path, info.line, last_name, key
                            );
                        }
                    } else {
                        let last_segment = path.segments.last().unwrap().clone();
                        expr_path.path.segments.clear();
                        expr_path.path.segments.push(last_segment);
                    }
                }
            }
        }
        visit_mut::visit_expr_call_mut(self, node);
    }
}
#[doc = " Process a single file."]
#[doc = " Returns true if the file would be / was changed."]
pub fn process_file(
    path: &Path,
    ignore_roots: &[String],
    dry_run: bool,
    alias_on_conflict: bool,
) -> Result<bool> {
    let src = read_to_string(path).with_context(|| format!("failed to read {}", path.display()))?;
    let mut ast: File =
        parse_file(&src).with_context(|| format!("failed to parse {}", path.display()))?;
    let mut collector = PathCollector::new(ignore_roots);
    collector.visit_file_mut(&mut ast);
    if collector.paths.is_empty() {
        return Ok(false);
    }
    let imported_idents = collect_imported_idents(&ast);
    let local_idents = collect_local_idents(&ast);
    let mut ast_for_rewrite = ast.clone();
    let mut rewriter = PathRewriter::new(
        path,
        collector.paths.clone(),
        imported_idents.clone(),
        local_idents.clone(),
        alias_on_conflict,
    );
    rewriter.visit_file_mut(&mut ast_for_rewrite);
    let aliases = rewriter.aliases.clone();
    let mut ast_final = ast_for_rewrite;
    inject_uses(
        &mut ast_final,
        &collector.paths,
        &imported_idents,
        &local_idents,
        path,
        alias_on_conflict,
        &aliases,
    );
    let new_src = quote ! (# ast_final).to_string();
    if new_src == src {
        return Ok(false);
    }
    if dry_run {
        println!("would modify: {}", path.display());
        return Ok(true);
    }
    write(path, new_src).with_context(|| format!("failed to write {}", path.display()))?;
    Ok(true)
}
fn path_to_string(path: &SynPath) -> String {
    path.segments
        .iter()
        .map(|s| s.ident.to_string())
        .collect::<Vec<_>>()
        .join("::")
}
#[doc = " Collect the identifiers that are already imported into the file via `use`."]
fn collect_imported_idents(ast: &File) -> BTreeSet<String> {
    let mut idents = BTreeSet::new();
    for item in &ast.items {
        if let Item::Use(item_use) = item {
            collect_use_idents(&item_use.tree, &mut idents);
        }
    }
    idents
}
fn collect_use_idents(tree: &UseTree, out: &mut BTreeSet<String>) {
    match tree {
        UseTree::Name(n) => {
            out.insert(n.ident.to_string());
        }
        UseTree::Rename(r) => {
            out.insert(r.rename.to_string());
        }
        UseTree::Path(p) => {
            collect_use_idents(&p.tree, out);
        }
        UseTree::Group(g) => {
            for t in &g.items {
                collect_use_idents(t, out);
            }
        }
        UseTree::Glob(_g) => {}
    }
}
#[doc = " Collect local identifiers in the file to detect potential conflicts."]
#[doc = " This is conservative: we just gather all names we see in common binding positions."]
fn collect_local_idents(ast: &File) -> BTreeSet<String> {
    let mut set = BTreeSet::new();
    for item in &ast.items {
        match item {
            Item::Fn(ItemFn { sig, .. }) => {
                set.insert(sig.ident.to_string());
                for input in &sig.inputs {
                    if let syn::FnArg::Typed(pat_ty) = input {
                        collect_pattern_idents(&pat_ty.pat, &mut set);
                    }
                }
            }
            Item::Struct(ItemStruct { ident, .. })
            | Item::Enum(ItemEnum { ident, .. })
            | Item::Union(ItemUnion { ident, .. })
            | Item::Trait(ItemTrait { ident, .. })
            | Item::Type(ItemType { ident, .. })
            | Item::Mod(ItemMod { ident, .. }) => {
                set.insert(ident.to_string());
            }
            Item::Static(ItemStatic { ident, .. }) | Item::Const(ItemConst { ident, .. }) => {
                set.insert(ident.to_string());
            }
            Item::Impl(ItemImpl { items, .. }) => {
                for impl_item in items {
                    if let syn::ImplItem::Fn(f) = impl_item {
                        set.insert(f.sig.ident.to_string());
                    }
                }
            }
            _ => {}
        }
    }
    struct LocalBindingCollector<'a> {
        set: &'a mut BTreeSet<String>,
    }
    impl<'a> VisitMut for LocalBindingCollector<'a> {
        fn visit_local_mut(&mut self, node: &mut syn::Local) {
            collect_pattern_idents(&node.pat, self.set);
            visit_local_mut(self, node);
        }
        fn visit_pat_ident_mut(&mut self, node: &mut syn::PatIdent) {
            self.set.insert(node.ident.to_string());
            visit_pat_ident_mut(self, node);
        }
    }
    let mut ast_clone = ast.clone();
    let mut collector = LocalBindingCollector { set: &mut set };
    collector.visit_file_mut(&mut ast_clone);
    set
}
fn collect_pattern_idents(pat: &Pat, out: &mut BTreeSet<String>) {
    match pat {
        Pat::Ident(p) => {
            out.insert(p.ident.to_string());
        }
        Pat::Tuple(tuple) => {
            for p in &tuple.elems {
                collect_pattern_idents(p, out);
            }
        }
        Pat::Struct(s) => {
            for field in &s.fields {
                collect_pattern_idents(&field.pat, out);
            }
        }
        Pat::TupleStruct(ts) => {
            for p in &ts.elems {
                collect_pattern_idents(p, out);
            }
        }
        Pat::Slice(slice) => {
            for p in &slice.elems {
                collect_pattern_idents(p, out);
            }
        }
        Pat::Reference(r) => {
            collect_pattern_idents(&r.pat, out);
        }
        Pat::Or(or) => {
            for p in &or.cases {
                collect_pattern_idents(p, out);
            }
        }
        _ => {}
    }
}
#[doc = " Inject `use path::to::func;` for each shortened path:"]
#[doc = " - If no conflict: `use foo::bar::baz;`"]
#[doc = " - If conflict and alias_on_conflict: `use foo::bar::baz as foo_bar_baz;`"]
#[doc = " - If conflict and !alias_on_conflict: skip + warn (call site kept FQ)."]
fn inject_uses(
    ast: &mut File,
    paths: &BTreeMap<String, PathInfo>,
    imported_idents: &BTreeSet<String>,
    local_idents: &BTreeSet<String>,
    file_path: &Path,
    alias_on_conflict: bool,
    aliases: &BTreeMap<String, Ident>,
) {
    let mut new_uses: Vec<Item> = Vec::new();
    let file_path_str = file_path.display().to_string();
    for (key, info) in paths {
        let ident_name = info.last_ident.to_string();
        let has_conflict =
            imported_idents.contains(&ident_name) || local_idents.contains(&ident_name);
        if has_conflict && !alias_on_conflict {
            eprintln!(
                "conflict in {}:{}: identifier `{}` is already defined/imported; \
                 skipping import of `use {}`;",
                file_path_str,
                info.line,
                ident_name,
                path_to_string(&info.full)
            );
            continue;
        }
        let full_path = &info.full;
        let use_item: ItemUse = if has_conflict && alias_on_conflict {
            let alias_ident = aliases.get(key).expect("alias should exist for conflicting path");
            parse_quote! { use # full_path as # alias_ident ; }
        } else {
            parse_quote! { use # full_path ; }
        };
        new_uses.push(Item::Use(use_item));
    }
    if new_uses.is_empty() {
        return;
    }
    let mut insert_idx = 0usize;
    for (idx, item) in ast.items.iter().enumerate() {
        if let Item::Use(_) = item {
            insert_idx = idx + 1;
        }
    }
    ast.items.splice(insert_idx..insert_idx, new_uses);
}
