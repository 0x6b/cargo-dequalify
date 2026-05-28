use std::{
    cmp::Reverse,
    collections::{BTreeMap, BTreeSet},
    fs::write,
    ops::Range,
    path::Path,
};

use anyhow::{Context, Result};
use syn::File;

use super::{
    Change,
    collect::{Collector, Occurrence},
    defs::{collect_prelude, collect_unqualified_names},
    diff::diff,
    resolve::resolve,
};

pub(super) struct Edit {
    range: Range<usize>,
    text: String,
}

pub(super) fn build_edits(c: &Collector, ast: &File, src: &str) -> Vec<Edit> {
    let prelude = collect_prelude(ast);
    let unqualified = collect_unqualified_names(ast);
    let by_scope: BTreeMap<&str, Vec<&Occurrence>> =
        c.occs.iter().fold(BTreeMap::new(), |mut acc, o| {
            acc.entry(&o.scope).or_default().push(o);
            acc
        });

    let mut edits = Vec::new();
    by_scope.iter().for_each(|(scope, occs)| {
        let info = c.scopes.get(*scope).unwrap_or_else(|| c.scopes.get("").unwrap());
        let mut existing = info.imports.clone();
        existing.extend(prelude.iter().cloned());
        existing.extend(info.defs.iter().cloned());
        // Pessimistically include every local visible at any occurrence in this
        // scope: a single import line serves all occurrences, so the chosen
        // short name must avoid collision in any of them.
        existing.extend(occs.iter().flat_map(|o| o.locals.iter().cloned()));
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
        occs.iter()
            .filter_map(|o| strats.get(&o.path).map(|s| (o, s)))
            .for_each(|(o, s)| {
                let text = if o.suffix.is_empty() {
                    s.repl()
                } else {
                    format!("{}::{}", s.repl(), o.suffix)
                };
                // Skip no-op rewrites: when the replacement equals the original
                // source, the short name is already in scope at the call site
                // (e.g. via a function-local `use` that `resolve` cannot see),
                // so a module-level import would be dead.
                if src.get(o.span.0..o.span.1) == Some(text.as_str()) {
                    return;
                }
                if let Some(u) = s.use_stmt() {
                    by_cfg.entry(o.cfg.clone()).or_default().insert(u);
                }
                edits.push(Edit { range: o.span.0..o.span.1, text });
            });

        let ind = &info.indent;
        let blocks: Vec<String> = by_cfg
            .iter()
            .flat_map(|(cfg, stmts)| {
                let pre: String = cfg.iter().map(|c| format!("{ind}#[{c}]\n")).collect();
                stmts.iter().map(move |s| format!("{pre}{ind}{s}"))
            })
            .collect();
        if !blocks.is_empty() {
            edits.push(Edit {
                range: info.pos..info.pos,
                text: format!("\n{}\n", blocks.join("\n")),
            });
        }
    });
    edits
}

pub(super) fn apply_edits(
    path: &Path,
    src: &str,
    mut edits: Vec<Edit>,
    dry: bool,
) -> Result<Change> {
    // Apply edits from the end of the file backwards so positions in earlier
    // edits remain valid. When two edits share a start, the longer (Replace)
    // sorts before the empty-range insertion, so the insertion lands strictly
    // before the replaced range rather than inside it.
    edits.sort_by_key(|e| (Reverse(e.range.start), Reverse(e.range.len())));
    let mut out = src.to_string();
    edits.into_iter().for_each(|e| out.replace_range(e.range, &e.text));
    if out == src {
        return Ok(Change::None);
    }
    if dry {
        return Ok(Change::Pending(diff(path, src, &out)));
    }
    write(path, &out).with_context(|| format!("write {}", path.display()))?;
    Ok(Change::Written)
}
