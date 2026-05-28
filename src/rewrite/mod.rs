mod attrs;
mod collect;
mod consts;
mod defs;
mod diff;
mod edits;
mod resolve;
mod source;
mod use_tree;

use std::{collections::BTreeSet, fs::read_to_string, path::Path};

use anyhow::{Context, Result};
use collect::collect_occurrences;
use edits::{apply_edits, build_edits};
use source::Lines;
use syn::{File, parse_file};

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

    let edits = build_edits(&c, &ast, &src);
    if edits.is_empty() {
        return Ok(Change::None);
    }

    apply_edits(path, &src, edits, options.dry_run)
}
