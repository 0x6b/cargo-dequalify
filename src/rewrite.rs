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
    Macro, Pat, Path as SynPath, TypePath, UseTree, parse_file,
    spanned::Spanned,
    visit::{Visit, self},
};

const PRIMITIVE_TYPES: &[&str] = &[
    "bool", "char", "str", "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64",
    "u128", "usize", "f32", "f64",
];

const PRELUDE_TYPES: &[&str] = &["Option", "Result", "Box", "String", "Vec"];

const FORMAT_MACROS: &[&str] = &[
    "println", "print", "eprintln", "eprint", "format", "format_args", "write", "writeln",
    "panic", "unreachable", "todo", "unimplemented", "trace", "debug", "info", "warn", "error",
];

#[derive(Clone, Debug)]
struct PathOccurrence {
    full_path_str: String,
    start_line: usize,
    start_col: usize,
    end_line: usize,
    end_col: usize,
    scope: String,
    cfg_attrs: Vec<String>,
    local_bindings: BTreeSet<String>,
}

#[derive(Debug)]
struct ScopeInfo {
    insert_pos: usize,
    imported_idents: BTreeSet<String>,
    indent: String,
}

struct PathCollector<'a> {
    paths: BTreeSet<String>,
    occurrences: Vec<PathOccurrence>,
    ignore_roots: &'a BTreeSet<String>,
    scope_stack: Vec<String>,
    scope_infos: BTreeMap<String, ScopeInfo>,
    line_offsets: &'a LineOffsets,
    import_mappings: BTreeMap<String, String>,
    locally_imported_internal_names: BTreeSet<String>,
    block_depth: usize,
    cfg_stack: Vec<String>,
    local_binding_stack: Vec<BTreeSet<String>>,
}

impl<'a> PathCollector<'a> {
    fn new(ignore_roots: &'a BTreeSet<String>, line_offsets: &'a LineOffsets) -> Self {
        Self {
            paths: BTreeSet::new(),
            occurrences: Vec::new(),
            ignore_roots,
            scope_stack: Vec::new(),
            scope_infos: BTreeMap::new(),
            line_offsets,
            import_mappings: BTreeMap::new(),
            locally_imported_internal_names: BTreeSet::new(),
            block_depth: 0,
            cfg_stack: Vec::new(),
            local_binding_stack: Vec::new(),
        }
    }

    fn current_cfg_attrs(&self) -> Vec<String> {
        let mut attrs: Vec<_> = self.cfg_stack.iter().cloned().collect();
        attrs.sort();
        attrs.dedup();
        attrs
    }

    fn current_scope(&self) -> String {
        self.scope_stack.join("::")
    }

    fn current_local_bindings(&self) -> BTreeSet<String> {
        self.local_binding_stack.iter().flatten().cloned().collect()
    }

    fn add_local_binding(&mut self, name: String) {
        if let Some(current) = self.local_binding_stack.last_mut() {
            current.insert(name);
        }
    }

    fn expand_path(&self, first_segment: &str, remaining: &[String]) -> Option<String> {
        self.import_mappings.get(first_segment).and_then(|base| {
            let base_first = base.split("::").next().unwrap_or("");
            if base_first == first_segment && !remaining.is_empty() {
                return None;
            }
            Some(if remaining.is_empty() {
                base.clone()
            } else {
                format!("{base}::{}", remaining.join("::"))
            })
        })
    }

    fn with_cfg_attrs<F>(&mut self, attrs: &[Attribute], f: F)
    where
        F: FnOnce(&mut Self),
    {
        let cfg_attrs = extract_cfg_attrs(attrs);
        let cfg_count = cfg_attrs.len();
        self.cfg_stack.extend(cfg_attrs);
        f(self);
        self.cfg_stack.truncate(self.cfg_stack.len() - cfg_count);
    }

    fn with_fn_scope<F>(&mut self, sig: &syn::Signature, f: F)
    where
        F: FnOnce(&mut Self),
    {
        self.block_depth += 1;
        let mut bindings = BTreeSet::new();
        for input in &sig.inputs {
            if let syn::FnArg::Typed(pat_ty) = input {
                collect_pattern_idents(&pat_ty.pat, &mut bindings);
            }
        }
        self.local_binding_stack.push(bindings);
        f(self);
        self.local_binding_stack.pop();
        self.block_depth -= 1;
    }

    fn record_qualified_path(
        &mut self,
        path: &SynPath,
        start_line: usize,
        start_col: usize,
        end_line: usize,
        end_col: usize,
        is_type: bool,
    ) {
        let segments = &path.segments;
        if segments.len() < 2 {
            return;
        }

        let first_name = segments[0].ident.to_string();

        if self.locally_imported_internal_names.contains(&first_name) {
            return;
        }

        let remaining: Vec<String> = segments.iter().skip(1).map(|s| s.ident.to_string()).collect();
        let (full_str, effective_first) = match self.expand_path(&first_name, &remaining) {
            Some(expanded) => {
                let ef = expanded.split("::").next().unwrap_or(&first_name).to_string();
                (expanded, ef)
            }
            None => (path_to_string(path), first_name),
        };

        let first_char = effective_first.chars().next().unwrap_or('a');
        if effective_first == "Self" || first_char.is_uppercase() {
            return;
        }
        if self.ignore_roots.contains(&effective_first) {
            return;
        }

        let expanded_segments: Vec<&str> = full_str.split("::").collect();

        if !is_type {
            let second_to_last = expanded_segments
                .get(expanded_segments.len().saturating_sub(2))
                .unwrap_or(&"");
            let stl_char = second_to_last.chars().next().unwrap_or('a');
            if stl_char.is_uppercase() || PRIMITIVE_TYPES.contains(second_to_last) {
                return;
            }
        } else {
            let last = segments.last().map(|s| s.ident.to_string()).unwrap_or_default();
            if PRIMITIVE_TYPES.contains(&last.as_str()) {
                return;
            }
        }

        self.paths.insert(full_str.clone());
        self.occurrences.push(PathOccurrence {
            full_path_str: full_str,
            start_line,
            start_col,
            end_line,
            end_col,
            scope: self.current_scope(),
            cfg_attrs: self.current_cfg_attrs(),
            local_bindings: self.current_local_bindings(),
        });
    }

    fn visit_format_macro_args(&mut self, node: &Macro) {
        use syn::parse::Parser;
        use syn::punctuated::Punctuated;
        use syn::Token;

        let parser = Punctuated::<Expr, Token![,]>::parse_terminated;
        if let Ok(args) = parser.parse2(node.tokens.clone()) {
            for arg in args.into_iter().skip(1) {
                self.visit_expr(&arg);
            }
        }
    }
}

impl Visit<'_> for PathCollector<'_> {
    fn visit_item_use(&mut self, node: &ItemUse) {
        collect_use_mappings(&node.tree, &[], &mut self.import_mappings);
        if self.block_depth > 0 && is_internal_use_tree(&node.tree) {
            collect_use_idents(&node.tree, &mut self.locally_imported_internal_names);
        }
        visit::visit_item_use(self, node);
    }

    fn visit_item_fn(&mut self, node: &syn::ItemFn) {
        self.with_cfg_attrs(&node.attrs, |this| {
            this.with_fn_scope(&node.sig, |this| visit::visit_item_fn(this, node));
        });
    }

    fn visit_impl_item_fn(&mut self, node: &ImplItemFn) {
        self.with_cfg_attrs(&node.attrs, |this| {
            this.with_fn_scope(&node.sig, |this| visit::visit_impl_item_fn(this, node));
        });
    }

    fn visit_expr_closure(&mut self, node: &ExprClosure) {
        self.block_depth += 1;
        let mut bindings = BTreeSet::new();
        for input in &node.inputs {
            collect_pattern_idents(input, &mut bindings);
        }
        self.local_binding_stack.push(bindings);
        visit::visit_expr_closure(self, node);
        self.local_binding_stack.pop();
        self.block_depth -= 1;
    }

    fn visit_local(&mut self, node: &Local) {
        if let Some(init) = &node.init {
            self.visit_expr(&init.expr);
            if let Some((_, else_branch)) = &init.diverge {
                self.visit_expr(else_branch);
            }
        }
        let mut bindings = BTreeSet::new();
        collect_pattern_idents(&node.pat, &mut bindings);
        for name in bindings {
            self.add_local_binding(name);
        }
        visit::visit_pat(self, &node.pat);
    }

    fn visit_item_impl(&mut self, node: &ItemImpl) {
        self.with_cfg_attrs(&node.attrs, |this| visit::visit_item_impl(this, node));
    }

    fn visit_expr_call(&mut self, node: &ExprCall) {
        if let syn::Expr::Path(expr_path) = &*node.func {
            if expr_path.qself.is_none() {
                let span = expr_path.span();
                let start = span.start();
                let end = span.end();
                self.record_qualified_path(
                    &expr_path.path,
                    start.line,
                    start.column,
                    end.line,
                    end.column,
                    false,
                );
            }
        }
        visit::visit_expr_call(self, node);
    }

    fn visit_item_mod(&mut self, node: &ItemMod) {
        self.with_cfg_attrs(&node.attrs, |this| {
            if let Some((brace, items)) = &node.content {
                let mod_name = node.ident.to_string();
                this.scope_stack.push(mod_name);
                let current_scope = this.current_scope();

                let mut last_use_line: Option<usize> = None;
                let mut imported_idents = BTreeSet::new();
                for item in items {
                    if let Item::Use(item_use) = item {
                        last_use_line = Some(item_use.span().end().line);
                        collect_use_idents(&item_use.tree, &mut imported_idents);
                    }
                }

                let indent = items
                    .first()
                    .map(|i| " ".repeat(i.span().start().column))
                    .unwrap_or_else(|| " ".repeat(4 * this.scope_stack.len()));

                let insert_pos = last_use_line
                    .map(|line| this.line_offsets.line_end_byte(line))
                    .unwrap_or_else(|| this.line_offsets.line_end_byte(brace.span.open().end().line));

                this.scope_infos.insert(current_scope, ScopeInfo { insert_pos, imported_idents, indent });
                visit::visit_item_mod(this, node);
                this.scope_stack.pop();
            } else {
                visit::visit_item_mod(this, node);
            }
        });
    }

    fn visit_macro(&mut self, node: &Macro) {
        let segments = &node.path.segments;
        if segments.len() >= 2 {
            let span = node.path.segments.span();
            let start = span.start();
            let end = span.end();
            self.record_qualified_path(&node.path, start.line, start.column, end.line, end.column, false);
        }
        if segments.len() == 1 {
            let macro_name = segments[0].ident.to_string();
            if FORMAT_MACROS.contains(&macro_name.as_str()) {
                self.visit_format_macro_args(node);
            }
        }
        visit::visit_macro(self, node);
    }

    fn visit_type_path(&mut self, node: &TypePath) {
        if node.qself.is_none() && node.path.segments.len() >= 2 {
            let start = node.path.segments.first().unwrap().ident.span().start();
            let end = node.path.segments.last().unwrap().ident.span().end();
            self.record_qualified_path(&node.path, start.line, start.column, end.line, end.column, true);
        }
        visit::visit_type_path(self, node);
    }
}

fn extract_cfg_attrs(attrs: &[Attribute]) -> Vec<String> {
    attrs
        .iter()
        .filter_map(|attr| {
            attr.path().is_ident("cfg").then(|| {
                attr.meta.require_list().ok().map(|list| format!("cfg({})", list.tokens))
            })?
        })
        .collect()
}

#[derive(Clone)]
struct ImportStrategy {
    full_path: String,
    segments: Vec<String>,
    import_len: usize,
    already_imported: bool,
}

impl ImportStrategy {
    fn new(full_path: &str) -> Self {
        let segments: Vec<String> = full_path.split("::").map(String::from).collect();
        let import_len = segments.len();
        Self { full_path: full_path.to_string(), segments, import_len, already_imported: false }
    }

    fn import_ident(&self) -> &str {
        &self.segments[self.import_len - 1]
    }

    fn go_up(&mut self) -> bool {
        if self.import_len > 1 {
            self.import_len -= 1;
            true
        } else {
            false
        }
    }

    fn is_same_as_original(&self) -> bool {
        self.import_len == 1
    }

    fn use_statement(&self) -> Option<String> {
        (!self.already_imported).then(|| format!("use {};", self.segments[..self.import_len].join("::")))
    }

    fn replacement(&self) -> String {
        if self.import_len == self.segments.len() {
            self.segments.last().unwrap().clone()
        } else {
            format!("{}::{}", self.segments[self.import_len - 1], self.segments[self.import_len..].join("::"))
        }
    }
}

fn resolve_all_imports(
    paths: &[String],
    existing_idents: &BTreeSet<String>,
    import_mappings: &BTreeMap<String, String>,
) -> BTreeMap<String, ImportStrategy> {
    let mut strategies: Vec<ImportStrategy> = paths.iter().map(|p| ImportStrategy::new(p)).collect();

    for strategy in &mut strategies {
        let short_name = strategy.segments.last().unwrap();
        if import_mappings.get(short_name).is_some_and(|mapped| mapped == &strategy.full_path) {
            strategy.already_imported = true;
        }
    }

    loop {
        let mut groups: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        for (idx, strategy) in strategies.iter().enumerate() {
            if !strategy.is_same_as_original() && !strategy.already_imported {
                groups.entry(strategy.import_ident().to_string()).or_default().push(idx);
            }
        }

        let mut has_conflict = false;
        for indices in groups.values().filter(|v| v.len() > 1) {
            for &idx in indices {
                has_conflict |= strategies[idx].go_up();
            }
        }
        if !has_conflict {
            break;
        }
    }

    loop {
        let mut has_conflict = false;
        for strategy in &mut strategies {
            if !strategy.is_same_as_original()
                && !strategy.already_imported
                && existing_idents.contains(strategy.import_ident())
            {
                has_conflict |= strategy.go_up();
            }
        }
        if !has_conflict {
            break;
        }
    }

    let mut used_idents: BTreeSet<String> = BTreeSet::new();
    let mut result = BTreeMap::new();
    for strategy in strategies {
        if strategy.is_same_as_original() {
            continue;
        }
        let import_ident = strategy.import_ident().to_string();
        if used_idents.insert(import_ident) {
            result.insert(strategy.full_path.clone(), strategy);
        }
    }
    result
}

#[derive(Debug)]
enum Edit {
    Insert { pos: usize, text: String },
    Replace { start: usize, end: usize, text: String },
}

impl Edit {
    fn sort_position(&self) -> usize {
        match self {
            Edit::Insert { pos, .. } => *pos,
            Edit::Replace { start, .. } => *start,
        }
    }
}

pub fn process_file(path: &Path, ignore_roots: &[String], dry_run: bool) -> Result<Option<String>> {
    let src = read_to_string(path).with_context(|| format!("failed to read {}", path.display()))?;
    let ast: File = parse_file(&src).with_context(|| format!("failed to parse {}", path.display()))?;

    let line_offsets = LineOffsets::new(&src);
    let ignore_set: BTreeSet<String> = ignore_roots.iter().cloned().collect();
    let mut collector = PathCollector::new(&ignore_set, &line_offsets);

    let file_level_imported = collect_imported_idents(&ast);
    let file_level_insert_pos = find_use_insert_position(&ast, &line_offsets);
    collector.scope_infos.insert(
        String::new(),
        ScopeInfo { insert_pos: file_level_insert_pos, imported_idents: file_level_imported.clone(), indent: String::new() },
    );

    collector.visit_file(&ast);

    for _ in 0..10 {
        let snapshot = collector.import_mappings.clone();
        let mut changed = false;
        for full_path in collector.import_mappings.values_mut() {
            let normalized = normalize_path(full_path.clone(), &snapshot);
            if &normalized != full_path {
                *full_path = normalized;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    collector.paths = collector.paths.iter().map(|p| normalize_path(p.clone(), &collector.import_mappings)).collect();
    for occ in &mut collector.occurrences {
        occ.full_path_str = normalize_path(occ.full_path_str.clone(), &collector.import_mappings);
    }

    if collector.paths.is_empty() {
        return Ok(None);
    }

    let used_prelude_types = collect_unqualified_prelude_usages(&ast);
    let file_level_defs = collect_file_level_definitions(&ast);

    let mut occ_by_scope: BTreeMap<&str, Vec<&PathOccurrence>> = BTreeMap::new();
    for occ in &collector.occurrences {
        occ_by_scope.entry(&occ.scope).or_default().push(occ);
    }

    let mut edits: Vec<Edit> = Vec::new();

    for (scope, occurrences) in &occ_by_scope {
        let scope_info = collector.scope_infos.get(*scope).unwrap_or_else(|| collector.scope_infos.get("").unwrap());

        let mut existing_idents: BTreeSet<String> = file_level_imported.clone();
        existing_idents.extend(scope_info.imported_idents.clone());
        existing_idents.extend(used_prelude_types.clone());
        existing_idents.extend(file_level_defs.clone());
        for occ in occurrences {
            existing_idents.extend(occ.local_bindings.clone());
        }

        let scope_paths: Vec<String> = occurrences.iter().map(|o| o.full_path_str.clone()).collect::<BTreeSet<_>>().into_iter().collect();
        let strategies = resolve_all_imports(&scope_paths, &existing_idents, &collector.import_mappings);

        let mut use_by_cfg: BTreeMap<Vec<String>, BTreeSet<String>> = BTreeMap::new();

        for occ in occurrences {
            if let Some(strategy) = strategies.get(&occ.full_path_str) {
                if let Some(use_stmt) = strategy.use_statement() {
                    use_by_cfg.entry(occ.cfg_attrs.clone()).or_default().insert(use_stmt);
                }

                if let (Some(start), Some(end)) = (
                    line_offsets.line_col_to_byte(occ.start_line, occ.start_col),
                    line_offsets.line_col_to_byte(occ.end_line, occ.end_col),
                ) {
                    edits.push(Edit::Replace { start, end, text: strategy.replacement() });
                }
            }
        }

        if !use_by_cfg.is_empty() {
            let indent = &scope_info.indent;
            let mut use_blocks: Vec<String> = Vec::new();

            for (cfg_attrs, use_stmts) in &use_by_cfg {
                if cfg_attrs.is_empty() {
                    use_blocks.extend(use_stmts.iter().map(|s| format!("{indent}{s}")));
                } else {
                    let cfg_prefix: String = cfg_attrs.iter().map(|cfg| format!("{indent}#[{cfg}]\n")).collect();
                    use_blocks.extend(use_stmts.iter().map(|s| format!("{cfg_prefix}{indent}{s}")));
                }
            }

            if !use_blocks.is_empty() {
                edits.push(Edit::Insert { pos: scope_info.insert_pos, text: format!("\n{}\n", use_blocks.join("\n")) });
            }
        }
    }

    if edits.is_empty() {
        return Ok(None);
    }

    edits.sort_by_key(|e| Reverse(e.sort_position()));

    let mut new_src = src.clone();
    for edit in edits {
        match edit {
            Edit::Insert { pos, text } => new_src.insert_str(pos, &text),
            Edit::Replace { start, end, text } => new_src.replace_range(start..end, &text),
        }
    }

    if new_src == src {
        return Ok(None);
    }

    if dry_run {
        return Ok(Some(format_diff(path, &src, &new_src)));
    }

    write(path, &new_src).with_context(|| format!("failed to write {}", path.display()))?;
    Ok(Some(String::new()))
}

fn path_to_string(path: &SynPath) -> String {
    path.segments.iter().map(|s| s.ident.to_string()).collect::<Vec<_>>().join("::")
}

struct LineOffsets {
    lines: Vec<(usize, Vec<usize>)>,
}

impl LineOffsets {
    fn new(src: &str) -> Self {
        let mut lines = Vec::new();
        let mut current_char_offsets = Vec::new();
        let mut line_start_byte = 0;

        for (byte_idx, ch) in src.char_indices() {
            if ch == '\n' {
                lines.push((line_start_byte, current_char_offsets));
                current_char_offsets = Vec::new();
                line_start_byte = byte_idx + 1;
            } else {
                current_char_offsets.push(byte_idx - line_start_byte);
            }
        }
        lines.push((line_start_byte, current_char_offsets));
        Self { lines }
    }

    fn line_col_to_byte(&self, line: usize, col: usize) -> Option<usize> {
        if line == 0 || line > self.lines.len() {
            return None;
        }
        let (line_start, char_offsets) = &self.lines[line - 1];
        if col >= char_offsets.len() {
            return Some(line_start + char_offsets.last().map_or(0, |&o| o + 1));
        }
        Some(line_start + char_offsets[col])
    }

    fn line_end_byte(&self, line: usize) -> usize {
        if line == 0 || line > self.lines.len() {
            return 0;
        }
        if line < self.lines.len() {
            self.lines[line].0 - 1
        } else {
            let (line_start, char_offsets) = &self.lines[line - 1];
            line_start + char_offsets.last().map_or(0, |&o| o + 1)
        }
    }
}

fn find_use_insert_position(ast: &File, line_offsets: &LineOffsets) -> usize {
    ast.items
        .iter()
        .filter_map(|item| match item {
            Item::Use(item_use) => Some(line_offsets.line_end_byte(item_use.span().end().line)),
            _ => None,
        })
        .last()
        .unwrap_or(0)
}

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
    collect_use_idents_impl(tree, None, out);
}

fn collect_use_idents_impl(tree: &UseTree, parent: Option<&str>, out: &mut BTreeSet<String>) {
    match tree {
        UseTree::Name(n) => {
            let name = n.ident.to_string();
            if name == "self" {
                if let Some(p) = parent {
                    out.insert(p.to_string());
                }
            } else {
                out.insert(name);
            }
        }
        UseTree::Rename(r) => {
            out.insert(r.rename.to_string());
        }
        UseTree::Path(p) => {
            let ident = p.ident.to_string();
            collect_use_idents_impl(&p.tree, Some(&ident), out);
        }
        UseTree::Group(g) => {
            for t in &g.items {
                collect_use_idents_impl(t, parent, out);
            }
        }
        UseTree::Glob(_) => {}
    }
}

fn is_internal_use_tree(tree: &UseTree) -> bool {
    match tree {
        UseTree::Path(p) => {
            let first = p.ident.to_string();
            first == "crate" || first == "self" || first == "super"
        }
        UseTree::Group(g) => g.items.iter().all(is_internal_use_tree),
        _ => false,
    }
}

fn normalize_path(full: String, mappings: &BTreeMap<String, String>) -> String {
    let segments: Vec<&str> = full.split("::").collect();
    if let Some(&first) = segments.first() {
        if let Some(base) = mappings.get(first) {
            let base_first = base.split("::").next().unwrap_or("");
            if base_first != first {
                let mut new_segments: Vec<&str> = base.split("::").collect();
                new_segments.extend(segments.iter().skip(1));
                return new_segments.join("::");
            }
        }
    }
    full
}

fn collect_use_mappings(tree: &UseTree, prefix: &[String], out: &mut BTreeMap<String, String>) {
    match tree {
        UseTree::Name(n) => {
            let name = n.ident.to_string();
            if name == "self" {
                if let Some(local_name) = prefix.last() {
                    let full = normalize_path(prefix.join("::"), out);
                    out.insert(local_name.clone(), full);
                }
            } else {
                let mut parts = prefix.to_vec();
                parts.push(name.clone());
                let full = normalize_path(parts.join("::"), out);
                out.insert(name, full);
            }
        }
        UseTree::Rename(r) => {
            let alias = r.rename.to_string();
            let original = r.ident.to_string();
            if original == "self" {
                let full = normalize_path(prefix.join("::"), out);
                out.insert(alias, full);
            } else {
                let mut parts = prefix.to_vec();
                parts.push(original);
                let full = normalize_path(parts.join("::"), out);
                out.insert(alias, full);
            }
        }
        UseTree::Path(p) => {
            let mut new_prefix = prefix.to_vec();
            new_prefix.push(p.ident.to_string());
            collect_use_mappings(&p.tree, &new_prefix, out);
        }
        UseTree::Group(g) => {
            for t in &g.items {
                collect_use_mappings(t, prefix, out);
            }
        }
        UseTree::Glob(_) => {}
    }
}

fn collect_file_level_definitions(ast: &File) -> BTreeSet<String> {
    let mut set = BTreeSet::new();
    for item in &ast.items {
        match item {
            Item::Fn(ItemFn { sig, .. }) => {
                set.insert(sig.ident.to_string());
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

fn collect_unqualified_prelude_usages(ast: &File) -> BTreeSet<String> {
    struct PreludeCollector(BTreeSet<String>);

    impl<'ast> Visit<'ast> for PreludeCollector {
        fn visit_type_path(&mut self, node: &'ast TypePath) {
            if node.qself.is_none() && node.path.segments.len() == 1 {
                let ident = node.path.segments[0].ident.to_string();
                if PRELUDE_TYPES.contains(&ident.as_str()) {
                    self.0.insert(ident);
                }
            }
            visit::visit_type_path(self, node);
        }
    }

    let mut collector = PreludeCollector(BTreeSet::new());
    collector.visit_file(ast);
    collector.0
}

fn format_diff(path: &Path, old: &str, new: &str) -> String {
    use std::fmt::Write;
    let diff = TextDiff::from_lines(old, new);
    let mut output = String::new();
    writeln!(output, "--- {}", path.display()).unwrap();
    writeln!(output, "+++ {}", path.display()).unwrap();
    for hunk in diff.unified_diff().context_radius(3).iter_hunks() {
        writeln!(output, "{}", hunk.header()).unwrap();
        for change in hunk.iter_changes() {
            let sign = match change.tag() {
                ChangeTag::Delete => "-",
                ChangeTag::Insert => "+",
                ChangeTag::Equal => " ",
            };
            write!(output, "{sign}{change}").unwrap();
            if change.missing_newline() {
                writeln!(output).unwrap();
            }
        }
    }
    output
}
