mod fmt;
mod git;
mod walk;
mod workspace;

use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use cargo_dequalify::{Options, process_file};
use clap::Parser;
use dunce::canonicalize;
use rayon::prelude::*;

use fmt::run_cargo_fmt;
use git::git_dirty_state;
use walk::rs_files_under;
use workspace::{find_cargo_toml, load_workspace, workspace_crate_roots};

#[derive(Debug, Parser)]
#[command(author, version, about)]
/// Rewrite fully-qualified function calls into imported short names.
pub struct Cli {
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

pub fn run(cli: Cli) -> Result<()> {
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
    let rs_files = rs_files_under(&crate_roots);

    let opts = Options {
        ignore_roots: cli.ignore_roots.clone(),
        dry_run: !cli.write,
    };
    let results: Vec<_> = rs_files
        .par_iter()
        .map(|p| (p.clone(), process_file(p, &opts)))
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
