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
    collections::BTreeSet,
    fs::{read_to_string, write},
    path::Path,
};

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
    /// The file would change; the unified diff is enclosed. Produced in dry-run
    /// mode, or when a batch write is aborted because another file failed planning.
    Pending(String),
}

pub(crate) enum RewritePlan {
    Unchanged,
    Changed { before: String, after: String },
}

pub(crate) fn plan_file(path: &Path, options: &Options) -> Result<RewritePlan> {
    let src = read_to_string(path).with_context(|| format!("read {}", path.display()))?;
    let ast: File = parse_file(&src).with_context(|| format!("parse {}", path.display()))?;
    let lines = Lines::new(&src);
    let ignore: BTreeSet<_> = options.ignore_roots.iter().cloned().collect();

    let c = collect_occurrences(&ast, &lines, &ignore);
    if c.occs.is_empty() {
        return Ok(RewritePlan::Unchanged);
    }

    let edits = build_edits(&c, &ast, &src);
    if edits.is_empty() {
        return Ok(RewritePlan::Unchanged);
    }

    let after = apply_edits(&src, edits);
    if after == src {
        Ok(RewritePlan::Unchanged)
    } else {
        Ok(RewritePlan::Changed { before: src, after })
    }
}

pub(crate) fn apply_plan(path: &Path, plan: RewritePlan, dry_run: bool) -> Result<Change> {
    let RewritePlan::Changed { before, after } = plan else {
        return Ok(Change::None);
    };
    if dry_run {
        return Ok(Change::Pending(diff::diff(path, &before, &after)));
    }
    write(path, after).with_context(|| format!("write {}", path.display()))?;
    Ok(Change::Written)
}

pub fn process_file(path: &Path, options: &Options) -> Result<Change> {
    apply_plan(path, plan_file(path, options)?, options.dry_run)
}
