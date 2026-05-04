use std::{
    collections::BTreeSet,
    fs::read_to_string,
    path::{Path, PathBuf},
};

use anyhow::{Result, anyhow};
use dunce::canonicalize;
use glob::glob;
use serde::Deserialize;
use toml::from_str;

#[derive(Deserialize)]
struct CargoToml {
    workspace: Option<Workspace>,
    package: Option<Package>,
}

#[derive(Deserialize)]
struct Workspace {
    members: Option<Vec<String>>,
    exclude: Option<Vec<String>>,
}

#[derive(Deserialize)]
struct Package {}

pub(super) fn find_cargo_toml(start: &Path) -> Result<PathBuf> {
    start
        .ancestors()
        .map(|d| d.join("Cargo.toml"))
        .find(|c| c.is_file())
        .ok_or_else(|| anyhow!("Cargo.toml not found"))
}

pub(super) fn load_workspace(path: &Path) -> Result<(bool, Vec<String>, Vec<String>)> {
    let parsed: CargoToml = from_str(&read_to_string(path)?)?;
    let ws = parsed.workspace;
    let mut members = ws.as_ref().and_then(|w| w.members.clone()).unwrap_or_default();
    let mut exclude = ws.as_ref().and_then(|w| w.exclude.clone()).unwrap_or_default();
    members.sort();
    members.dedup();
    exclude.sort();
    exclude.dedup();
    Ok((parsed.package.is_none(), members, exclude))
}

pub(super) fn workspace_crate_roots(
    cargo_toml: &Path,
    virtual_root: bool,
    members: &[String],
    exclude: &[String],
) -> Vec<PathBuf> {
    let root = cargo_toml.parent().unwrap_or(Path::new("."));
    let expand = |patterns: &[String]| -> BTreeSet<PathBuf> {
        patterns
            .iter()
            .flat_map(|m| {
                let pattern = root.join(m);
                let pattern_str = pattern.to_string_lossy();
                if pattern_str.contains('*') || pattern_str.contains('?') {
                    glob(&pattern_str)
                        .into_iter()
                        .flatten()
                        .filter_map(Result::ok)
                        .filter(|p| p.is_dir())
                        .collect()
                } else {
                    vec![pattern]
                }
            })
            .filter_map(|p| canonicalize(&p).ok().or(Some(p)))
            .collect()
    };
    let excluded: BTreeSet<PathBuf> = expand(exclude);
    let mut roots: BTreeSet<PathBuf> = expand(members)
        .into_iter()
        .filter(|p| !excluded.contains(p))
        .collect();
    if !virtual_root || roots.is_empty() {
        let r = canonicalize(root).unwrap_or_else(|_| root.to_path_buf());
        if !excluded.contains(&r) {
            roots.insert(r);
        }
    }
    roots.into_iter().collect()
}
