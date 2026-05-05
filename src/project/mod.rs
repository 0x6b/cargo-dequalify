mod walk;
mod workspace;

use std::path::{Path, PathBuf};

use anyhow::Result;
use rayon::prelude::*;
use walk::rs_files_under;
use workspace::{find_cargo_toml, load_workspace, workspace_crate_roots};

use crate::rewrite::{Change, Options, process_file};

pub struct ProcessOutcome {
    pub workspace_root: PathBuf,
    pub results: Vec<(PathBuf, Result<Change>)>,
}

pub fn process_path(path: &Path, options: &Options) -> Result<ProcessOutcome> {
    let cargo_toml = find_cargo_toml(path)?;
    let (virtual_root, members, exclude) = load_workspace(&cargo_toml)?;
    let workspace_root = cargo_toml.parent().unwrap_or(Path::new(".")).to_path_buf();
    let crate_roots = workspace_crate_roots(&cargo_toml, virtual_root, &members, &exclude);
    let rs_files = rs_files_under(&crate_roots);
    let results = rs_files
        .par_iter()
        .map(|p| (p.clone(), process_file(p, options)))
        .collect();
    Ok(ProcessOutcome { workspace_root, results })
}
