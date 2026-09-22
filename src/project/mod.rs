mod walk;
mod workspace;

use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use dunce::canonicalize;
use rayon::prelude::*;
use walk::rs_files_under;
use workspace::{find_cargo_toml, load_workspace, workspace_crate_roots};

use crate::rewrite::{Change, Options, apply_plan, plan_file};

pub struct ProcessOutcome {
    pub workspace_root: PathBuf,
    pub generated_rust_files: Vec<PathBuf>,
    pub results: Vec<(PathBuf, Result<Change>)>,
}

pub fn process_path(path: &Path, options: &Options) -> Result<ProcessOutcome> {
    // Canonicalize once here so downstream code can rely on canonical paths
    // when comparing roots, members, and excludes. Also gives library
    // consumers a useful error if the target doesn't exist.
    let root = canonicalize(path).with_context(|| format!("canonicalize {}", path.display()))?;
    let cargo_toml = find_cargo_toml(&root)?;
    let manifest = load_workspace(&cargo_toml)?;
    let workspace_root = cargo_toml.parent().unwrap_or(Path::new(".")).to_path_buf();
    let crate_roots = workspace_crate_roots(&cargo_toml, &manifest);
    let rs_files = rs_files_under(&crate_roots, &workspace_root)?;
    let plans: Vec<_> = rs_files
        .files
        .par_iter()
        .map(|p| (p.clone(), plan_file(p, options)))
        .collect();
    let planning_failed = plans.iter().any(|(_, result)| result.is_err());
    let dry_run = options.dry_run || planning_failed;
    let results = plans
        .into_iter()
        .map(|(path, plan)| {
            let result = plan.and_then(|plan| apply_plan(&path, plan, dry_run));
            (path, result)
        })
        .collect();
    Ok(ProcessOutcome {
        workspace_root,
        generated_rust_files: rs_files.generated,
        results,
    })
}
