mod rewrite;

use std::{
    env::args,
    ffi::OsStr,
    fs::read_to_string,
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::{Context, Result, anyhow, bail};
use clap::Parser;
use dunce::canonicalize;
use gix::discover;
use glob::glob;
use ignore::WalkBuilder;
use rayon::prelude::*;
use rewrite::process_file;
use serde::Deserialize;
use toml::from_str;

#[derive(Debug, Parser)]
#[command(author, version, about)]
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
        .with_context(|| format!("canonicalize {}", cli.target.display()))?;
    let cargo_toml = find_cargo_toml(&root)?;
    let (virtual_root, members, exclude) = load_workspace(&cargo_toml)?;

    if cli.write && !cli.allow_dirty {
        match git_dirty_state(&root) {
            Ok(true) => bail!("uncommitted changes; commit/stash or use --allow-dirty"),
            Ok(false) => {}
            Err(e) => bail!(
                "could not determine git working-tree status: {e}; pass --allow-dirty to override"
            ),
        }
    }

    let crate_roots = workspace_crate_roots(&cargo_toml, virtual_root, &members, &exclude);
    let rs_files: Vec<PathBuf> = crate_roots
        .iter()
        .flat_map(|r| {
            WalkBuilder::new(r)
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
        .map(|p| (p.clone(), process_file(p, &cli.ignore_roots, !cli.write)))
        .collect();

    let mut diffs: Vec<_> = results
        .iter()
        .filter_map(|(p, r)| match r {
            Ok(Some(d)) if !d.is_empty() => Some((p.clone(), d.clone())),
            Err(e) => {
                eprintln!("error {}: {e}", p.display());
                None
            }
            _ => None,
        })
        .collect();
    diffs.sort_by(|a, b| a.0.cmp(&b.0));
    for (_, d) in &diffs {
        print!("{d}");
    }

    let any_changes = results.iter().any(|(_, r)| matches!(r, Ok(Some(_))));
    if any_changes && !cli.write {
        eprintln!("# Run with `-w` to apply, or `-w -f` to also format.");
    }
    if any_changes
        && cli.write
        && let Some(tc) = &cli.fmt
    {
        let workspace_root = cargo_toml.parent().unwrap_or(Path::new("."));
        run_cargo_fmt(workspace_root, tc.as_deref())?;
    }
    Ok(())
}

fn run_cargo_fmt(workspace_root: &Path, tc: Option<&str>) -> Result<()> {
    let mut cmd = Command::new("cargo");
    cmd.current_dir(workspace_root);
    if let Some(t) = tc {
        cmd.arg(format!("+{t}"));
    }
    let status = cmd.arg("fmt").status().context("cargo fmt")?;
    if !status.success() {
        bail!("cargo fmt failed");
    }
    Ok(())
}

/// Returns `Ok(true)` if the worktree containing `path` has uncommitted
/// changes, `Ok(false)` if it is clean *or* if `path` is not inside a git
/// repository (no protection needed). Returns `Err` only when discovery
/// succeeded but the status query itself failed, so the caller can decide
/// whether to abort rather than silently overwriting files.
fn git_dirty_state(path: &Path) -> Result<bool> {
    let repo = match discover(path) {
        Ok(r) => r,
        Err(_) => return Ok(false),
    };
    let mut iter = repo
        .status(gix::progress::Discard)
        .context("query git status")?
        .into_index_worktree_iter(None)
        .context("iterate index/worktree status")?;
    Ok(iter.next().is_some())
}

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

fn find_cargo_toml(start: &Path) -> Result<PathBuf> {
    start
        .ancestors()
        .map(|d| d.join("Cargo.toml"))
        .find(|c| c.is_file())
        .ok_or_else(|| anyhow!("Cargo.toml not found"))
}

fn load_workspace(path: &Path) -> Result<(bool, Vec<String>, Vec<String>)> {
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

fn workspace_crate_roots(
    cargo_toml: &Path,
    virtual_root: bool,
    members: &[String],
    exclude: &[String],
) -> Vec<PathBuf> {
    use std::collections::BTreeSet;
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
