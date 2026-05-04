use std::{
    cmp::Reverse,
    collections::{BTreeMap, BTreeSet},
    fs::write,
    path::Path,
};

use anyhow::{Context, Result};
use syn::File;

use super::Change;
use super::collect::{Collector, Occurrence};
use super::defs::{collect_prelude, collect_unqualified_names};
use super::diff::diff;
use super::resolve::resolve;

pub(super) enum Edit {
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

    /// Used as a tiebreaker so that, when an `Ins` and a `Rep` share the
    /// same byte position, the `Rep` is applied first (in reverse-position
    /// order this means the `Ins` lands strictly before the replaced range,
    /// not in the middle of freshly inserted text).
    fn kind_rank(&self) -> u8 {
        match self {
            Edit::Ins(_, _) => 0,
            Edit::Rep(_, _, _) => 1,
        }
    }
}

pub(super) fn build_edits(c: &Collector, ast: &File) -> Vec<Edit> {
    let prelude = collect_prelude(ast);
    let unqualified = collect_unqualified_names(ast);
    let mut by_scope: BTreeMap<&str, Vec<&Occurrence>> = BTreeMap::new();
    for o in &c.occs {
        by_scope.entry(&o.scope).or_default().push(o);
    }

    let mut edits = Vec::new();
    for (scope, occs) in &by_scope {
        let info = c.scopes.get(*scope).unwrap_or_else(|| c.scopes.get("").unwrap());
        let mut existing = info.imports.clone();
        existing.extend(prelude.clone());
        existing.extend(info.defs.clone());
        // Pessimistically include every local visible at any occurrence in this
        // scope: a single import line serves all occurrences, so the chosen
        // short name must avoid collision in any of them.
        for o in occs {
            existing.extend(o.locals.iter().cloned());
        }
        if info.has_glob {
            existing.extend(unqualified.iter().cloned());
        }

        let scope_paths: Vec<_> = occs
            .iter()
            .map(|o| o.path.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let strats = resolve(&scope_paths, &existing, &info.mappings);

        let mut by_cfg: BTreeMap<Vec<String>, BTreeSet<String>> = BTreeMap::new();
        for o in occs {
            if let Some(s) = strats.get(&o.path) {
                if let Some(u) = s.use_stmt() {
                    by_cfg.entry(o.cfg.clone()).or_default().insert(u);
                }
                let repl = if o.suffix.is_empty() {
                    s.repl()
                } else {
                    format!("{}::{}", s.repl(), o.suffix)
                };
                edits.push(Edit::Rep(o.span.0, o.span.1, repl));
            }
        }

        let ind = &info.indent;
        let blocks: Vec<String> = by_cfg
            .iter()
            .flat_map(|(cfg, stmts)| {
                let pre: String = cfg.iter().map(|c| format!("{ind}#[{c}]\n")).collect();
                stmts.iter().map(move |s| format!("{pre}{ind}{s}"))
            })
            .collect();
        if !blocks.is_empty() {
            edits.push(Edit::Ins(info.pos, format!("\n{}\n", blocks.join("\n"))));
        }
    }
    edits
}

pub(super) fn apply_edits(
    path: &Path,
    src: &str,
    mut edits: Vec<Edit>,
    dry: bool,
) -> Result<Change> {
    // Apply edits from the end of the file backwards so positions in earlier
    // edits remain valid. When two edits share a byte position, apply the
    // `Rep` first so the `Ins` is not swallowed by the replacement range.
    edits.sort_by_key(|e| (Reverse(e.pos()), Reverse(e.kind_rank())));
    let mut out = src.to_string();
    for e in edits {
        match e {
            Edit::Ins(p, t) => out.insert_str(p, &t),
            Edit::Rep(s, e, t) => out.replace_range(s..e, &t),
        }
    }
    if out == src {
        return Ok(Change::None);
    }
    if dry {
        return Ok(Change::Pending(diff(path, src, &out)));
    }
    write(path, &out).with_context(|| format!("write {}", path.display()))?;
    Ok(Change::Written)
}
