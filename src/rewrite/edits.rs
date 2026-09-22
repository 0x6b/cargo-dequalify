use std::{
    cmp::Reverse,
    collections::{BTreeMap, BTreeSet},
    ops::Range,
};

use syn::File;

use super::{
    attrs::render_cfg_union,
    collect::{Collector, Occurrence},
    defs::{collect_prelude, collect_unqualified_names},
    resolve::resolve,
};

pub(super) struct Edit {
    range: Range<usize>,
    text: String,
}

pub(super) fn build_edits(c: &Collector, ast: &File, src: &str) -> Vec<Edit> {
    let prelude = collect_prelude(ast);
    let unqualified = collect_unqualified_names(ast);
    let by_scope: BTreeMap<usize, Vec<&Occurrence>> =
        c.occs.iter().fold(BTreeMap::new(), |mut acc, o| {
            acc.entry(o.scope).or_default().push(o);
            acc
        });

    let mut edits = Vec::new();
    by_scope.iter().for_each(|(scope, occs)| {
        let info = c.scopes.get(*scope).unwrap_or_else(|| c.scopes.first().unwrap());
        let eligible: Vec<_> = occs
            .iter()
            .copied()
            .filter(|o| o.binding.is_none_or(|id| !c.protected_bindings.contains(&id)))
            .collect();
        let mut existing = info.imports.clone();
        existing.extend(prelude.iter().cloned());
        existing.extend(info.defs.iter().cloned());
        existing.extend(info.opaque_names.iter().cloned());
        // Pessimistically include every local visible at any occurrence in this
        // scope: a single import line serves all occurrences, so the chosen
        // short name must avoid collision in any of them.
        existing.extend(occs.iter().flat_map(|o| o.locals.iter().cloned()));
        if info.has_glob {
            existing.extend(unqualified.iter().cloned());
        }

        let scope_paths: Vec<_> = eligible
            .iter()
            .map(|o| o.path.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let strats = resolve(&scope_paths, &existing, &info.mappings);

        let mut requirements: BTreeMap<String, BTreeSet<Vec<String>>> = BTreeMap::new();
        eligible
            .iter()
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
                    requirements.entry(u).or_default().insert(o.cfg.clone());
                }
                edits.push(Edit { range: o.span.0..o.span.1, text });
            });

        let ind = &info.indent;
        let blocks: Vec<String> = requirements
            .into_iter()
            .map(|(stmt, conditions)| {
                let attr = render_cfg_union(conditions)
                    .map(|condition| format!("{ind}#[cfg({condition})]\n"))
                    .unwrap_or_default();
                format!("{attr}{ind}{stmt}")
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

pub(super) fn apply_edits(src: &str, mut edits: Vec<Edit>) -> String {
    // Apply edits from the end of the file backwards so positions in earlier
    // edits remain valid. When two edits share a start, the longer (Replace)
    // sorts before the empty-range insertion, so the insertion lands strictly
    // before the replaced range rather than inside it.
    edits.sort_by_key(|e| (Reverse(e.range.start), Reverse(e.range.len())));
    let mut out = src.to_string();
    edits.into_iter().for_each(|e| out.replace_range(e.range, &e.text));
    out
}
