use std::collections::{BTreeMap, BTreeSet};

use syn::{Path as SynPath, UseTree};

pub(super) fn path_str(p: &SynPath) -> String {
    p.segments
        .iter()
        .map(|s| s.ident.to_string())
        .collect::<Vec<_>>()
        .join("::")
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

pub(super) fn collect_idents(tree: &UseTree, out: &mut BTreeSet<String>) {
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

pub(super) fn has_glob_import(tree: &UseTree) -> bool {
    match tree {
        UseTree::Glob(_) => true,
        UseTree::Path(p) => has_glob_import(&p.tree),
        UseTree::Group(g) => g.items.iter().any(has_glob_import),
        _ => false,
    }
}

pub(super) fn is_internal(tree: &UseTree) -> bool {
    match tree {
        UseTree::Path(p) => matches!(p.ident.to_string().as_str(), "crate" | "self" | "super"),
        UseTree::Group(g) => g.items.iter().all(is_internal),
        _ => false,
    }
}

pub(super) fn collect_mappings(tree: &UseTree, out: &mut BTreeMap<String, String>) {
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

pub(super) fn resolve_path(
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
