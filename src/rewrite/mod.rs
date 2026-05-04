mod attrs;
mod collect;
mod consts;
mod defs;
mod diff;
mod edits;
mod resolve;
mod source;
mod use_tree;

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::read_to_string,
    path::Path,
};

use anyhow::{Context, Result};
use collect::{Collector, ScopeInfo};
use defs::collect_defs;
use edits::{apply_edits, build_edits};
use source::Lines;
use syn::{File, Item, parse_file, spanned::Spanned, visit::Visit};
use use_tree::{collect_idents, collect_mappings, has_glob_import, resolve_path};

/// Configuration for [`process_file`].
#[derive(Debug, Clone, Default)]
pub struct Options {
    /// Top-level path roots whose qualified uses should be left alone
    /// (e.g. `"std"`, `"core"`, `"alloc"`).
    pub ignore_roots: Vec<String>,
    /// If true, do not write the file; produce a unified diff string instead.
    pub dry_run: bool,
}

/// Outcome of running [`process_file`] on a single file.
#[derive(Debug)]
pub enum Change {
    /// The file needs no changes.
    None,
    /// The file was modified on disk (only possible when `dry_run` is false).
    Written,
    /// The file would change; the unified diff is enclosed
    /// (only produced when `dry_run` is true).
    Pending(String),
}

pub fn process_file(path: &Path, options: &Options) -> Result<Change> {
    let src = read_to_string(path).with_context(|| format!("read {}", path.display()))?;
    let ast: File = parse_file(&src).with_context(|| format!("parse {}", path.display()))?;
    let lines = Lines::new(&src);
    let ignore: BTreeSet<_> = options.ignore_roots.iter().cloned().collect();

    let c = collect_occurrences(&ast, &lines, &ignore);
    if c.occs.is_empty() {
        return Ok(Change::None);
    }

    let edits = build_edits(&c, &ast);
    if edits.is_empty() {
        return Ok(Change::None);
    }

    apply_edits(path, &src, edits, options.dry_run)
}

fn collect_occurrences<'a>(
    ast: &File,
    lines: &'a Lines<'a>,
    ignore: &'a BTreeSet<String>,
) -> Collector<'a> {
    let mut c = Collector::new(ignore, lines);
    let (pos, file_imports, has_glob, file_mappings, file_defs) = collect_file_context(ast, lines);
    c.scopes.insert(
        String::new(),
        ScopeInfo {
            pos,
            imports: file_imports,
            indent: String::new(),
            has_glob,
            mappings: file_mappings,
            defs: file_defs,
        },
    );
    Visit::visit_file(&mut c, ast);

    let mut cache = BTreeMap::new();
    resolve_mappings(&mut c.mappings, &mut cache);
    for o in &mut c.occs {
        o.path = resolve_path(&o.path, &c.mappings, &mut cache, 0);
    }
    for info in c.scopes.values_mut() {
        resolve_mappings(&mut info.mappings, &mut cache);
    }

    c
}

/// Rewrite each value of `map` so its first segment is no longer an alias
/// of another mapping (i.e. fold chains like `A -> B -> C` into `A -> C`).
fn resolve_mappings(
    map: &mut BTreeMap<String, String>,
    cache: &mut BTreeMap<String, String>,
) {
    let snap = map.clone();
    for v in map.values_mut() {
        *v = resolve_path(v, &snap, cache, 0);
    }
}

fn collect_file_context(
    ast: &File,
    lines: &Lines<'_>,
) -> (usize, BTreeSet<String>, bool, BTreeMap<String, String>, BTreeSet<String>) {
    let mut imports = BTreeSet::new();
    let mut pos = 0;
    let mut has_glob = false;
    let mut mappings = BTreeMap::new();
    for i in &ast.items {
        if let Item::Use(u) = i {
            pos = lines.end(u.span().end().line);
            collect_idents(&u.tree, &mut imports);
            has_glob |= has_glob_import(&u.tree);
            collect_mappings(&u.tree, &mut mappings);
        }
    }
    let defs = collect_defs(&ast.items);
    (pos, imports, has_glob, mappings, defs)
}
