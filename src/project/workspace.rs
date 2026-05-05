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
    #[serde(rename = "default-members")]
    default_members: Option<Vec<String>>,
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

pub(super) struct WorkspaceManifest {
    pub(super) virtual_root: bool,
    pub(super) members: Vec<String>,
    pub(super) exclude: Vec<String>,
}

pub(super) fn load_workspace(path: &Path) -> Result<WorkspaceManifest> {
    let parsed: CargoToml = from_str(&read_to_string(path)?)?;
    let ws = parsed.workspace;
    // Prefer `default-members` when present; cargo uses it as the active set
    // for commands without `--workspace`, and refactoring should match that
    // default scope rather than always touching every member.
    let mut members = ws
        .as_ref()
        .and_then(|w| w.default_members.clone().or_else(|| w.members.clone()))
        .unwrap_or_default();
    let mut exclude = ws.as_ref().and_then(|w| w.exclude.clone()).unwrap_or_default();
    members.sort();
    members.dedup();
    exclude.sort();
    exclude.dedup();
    Ok(WorkspaceManifest { virtual_root: parsed.package.is_none(), members, exclude })
}

pub(super) fn workspace_crate_roots(cargo_toml: &Path, manifest: &WorkspaceManifest) -> Vec<PathBuf> {
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
            .map(|p| canonicalize(&p).unwrap_or(p))
            .collect()
    };
    let excluded: BTreeSet<PathBuf> = expand(&manifest.exclude);
    let mut roots: BTreeSet<PathBuf> = expand(&manifest.members)
        .into_iter()
        .filter(|p| !excluded.contains(p))
        .collect();
    if !manifest.virtual_root || roots.is_empty() {
        // `cargo_toml` is reached from a canonical input via `find_cargo_toml`,
        // so its parent is also canonical and matches any canonical entries
        // in `excluded` without an extra canonicalize call.
        let r = root.to_path_buf();
        if !excluded.contains(&r) {
            roots.insert(r);
        }
    }
    roots.into_iter().collect()
}
