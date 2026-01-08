mod rewrite;

use std::{
    env::args,
    ffi::OsStr,
    fs::read_to_string,
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::{Context, Result, bail};
use clap::Parser;
use dunce::canonicalize;
use gix::discover;
use ignore::WalkBuilder;
use rayon::prelude::*;
use rewrite::process_file;
use serde::Deserialize;
use toml::from_str;

#[derive(Debug, Parser)]
#[command(author, version, about, long_about = None)]
/// Rewrite fully-qualified function calls into imported short names.
struct Cli {
    /// Optional path to a package or workspace root. Defaults to current dir.
    #[arg(value_name = "PATH", default_value = ".")]
    target: PathBuf,

    /// Actually modify files (default: dry-run mode).
    #[arg(short, long)]
    write: bool,

    /// Allow running --write on a dirty git working directory.
    #[arg(long)]
    allow_dirty: bool,

    /// Comma-separated list of top-level roots to ignore (e.g. "std,core,alloc").
    #[arg(long, value_delimiter = ',')]
    ignore_roots: Vec<String>,

    /// Run cargo fmt after writing changes. Optionally specify a toolchain (e.g., --fmt=nightly).
    #[arg(short, long, value_name = "TOOLCHAIN")]
    fmt: Option<Option<String>>,
}

fn main() -> Result<()> {
    let mut raw_args: Vec<String> = args().collect();
    if raw_args.get(1).is_some_and(|s| s == "dequalify") {
        raw_args.remove(1);
    }
    let cli = Cli::parse_from(&raw_args);

    let root = canonicalize(&cli.target)
        .with_context(|| format!("failed to canonicalize path {}", cli.target.display()))?;

    let cargo_toml = find_cargo_toml(&root)
        .with_context(|| format!("failed to find Cargo.toml starting from {}", root.display()))?;

    let workspace = load_workspace(&cargo_toml)
        .with_context(|| format!("failed to load workspace from {}", cargo_toml.display()))?;

    if cli.write && !cli.allow_dirty && is_git_dirty(&root) {
        bail!(
            "working directory has uncommitted changes, \
             please commit or stash them before running with --write, \
             or use --allow-dirty to override"
        );
    }

    let crate_roots = workspace_crate_roots(&cargo_toml, &workspace);

    let rs_files: Vec<PathBuf> = crate_roots
        .iter()
        .flat_map(|root| {
            WalkBuilder::new(root)
                .standard_filters(true)
                .hidden(false)
                .follow_links(false)
                .build()
                .filter_map(Result::ok)
                .filter(|e| e.path().is_file() && e.path().extension() == Some(OsStr::new("rs")))
                .map(|e| e.into_path())
        })
        .collect();

    let results: Vec<_> = rs_files
        .par_iter()
        .map(|path| (path.clone(), process_file(path, &cli.ignore_roots, !cli.write)))
        .collect();

    let mut diffs: Vec<_> = results
        .iter()
        .filter_map(|(path, res)| match res {
            Ok(Some(diff)) if !diff.is_empty() => Some((path.clone(), diff.clone())),
            Err(e) => {
                eprintln!("error processing {}: {e}", path.display());
                None
            }
            _ => None,
        })
        .collect();
    diffs.sort_by(|a, b| a.0.cmp(&b.0));

    for (_, diff) in &diffs {
        print!("{diff}");
    }

    let any_changes = results.iter().any(|(_, r)| matches!(r, Ok(Some(_))));

    if any_changes && !cli.write {
        eprintln!("# Run with `-w` to apply changes, or `-w -f` to also format.");
    }

    if any_changes && cli.write {
        if let Some(toolchain) = &cli.fmt {
            run_cargo_fmt(toolchain.as_deref())?;
        }
    }

    Ok(())
}

fn run_cargo_fmt(toolchain: Option<&str>) -> Result<()> {
    let mut cmd = Command::new("cargo");
    if let Some(tc) = toolchain {
        cmd.arg(format!("+{tc}"));
    }
    cmd.arg("fmt");

    let status = cmd.status().context("failed to run cargo fmt")?;
    if !status.success() {
        bail!("cargo fmt failed with {status}");
    }
    Ok(())
}

fn is_git_dirty(path: &Path) -> bool {
    let Ok(repo) = discover(path) else { return false };
    let Ok(platform) = repo.status(gix::progress::Discard) else { return false };
    let Ok(iter) = platform.into_index_worktree_iter(None) else { return false };
    iter.take(1).count() > 0
}

#[derive(Debug, Deserialize)]
struct CargoWorkspaceToml {
    workspace: Option<WorkspaceSection>,
    package: Option<PackageSection>,
}

#[derive(Debug, Deserialize)]
struct WorkspaceSection {
    members: Option<Vec<String>>,
}

#[derive(Debug, Deserialize)]
struct PackageSection {}

#[derive(Debug)]
struct WorkspaceInfo {
    virtual_root: bool,
    members: Vec<String>,
}

fn find_cargo_toml(start: &Path) -> Result<PathBuf> {
    for dir in start.ancestors() {
        let candidate = dir.join("Cargo.toml");
        if candidate.is_file() {
            return Ok(candidate);
        }
    }
    bail!("Cargo.toml not found");
}

fn load_workspace(cargo_toml: &Path) -> Result<WorkspaceInfo> {
    let content = read_to_string(cargo_toml)
        .with_context(|| format!("failed to read {}", cargo_toml.display()))?;
    let parsed: CargoWorkspaceToml = from_str(&content)
        .with_context(|| format!("failed to parse TOML {}", cargo_toml.display()))?;

    let virtual_root = parsed.package.is_none();
    let mut members = parsed
        .workspace
        .and_then(|ws| ws.members)
        .unwrap_or_default();
    members.sort();
    members.dedup();

    Ok(WorkspaceInfo { virtual_root, members })
}

fn workspace_crate_roots(cargo_toml: &Path, ws: &WorkspaceInfo) -> Vec<PathBuf> {
    let root_dir = cargo_toml.parent().unwrap_or(Path::new("."));

    let mut roots: Vec<PathBuf> = ws.members.iter().map(|m| root_dir.join(m)).collect();
    if !ws.virtual_root {
        roots.push(root_dir.to_path_buf());
    }
    if roots.is_empty() {
        roots.push(root_dir.to_path_buf());
    }

    roots.sort();
    roots.dedup();
    roots
}
