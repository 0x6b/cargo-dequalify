mod fmt;
mod git;

use std::path::PathBuf;

use anyhow::{Context, Result, bail};
use cargo_dequalify::{Change, Options, process_path};
use clap::Parser;
use dunce::canonicalize;
use fmt::run_cargo_fmt;
use git::git_dirty_state;

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

    if cli.write && !cli.allow_dirty {
        match git_dirty_state(&root) {
            Ok(true) => bail!("uncommitted changes; commit/stash or use --allow-dirty"),
            Ok(false) => {}
            Err(e) => bail!(
                "could not determine git working-tree status: {e}; pass --allow-dirty to override"
            ),
        }
    }

    let opts = Options {
        ignore_roots: cli.ignore_roots.clone(),
        dry_run: !cli.write,
    };
    let outcome = process_path(&root, &opts)?;

    let mut diffs: Vec<_> = outcome
        .results
        .iter()
        .filter_map(|(p, r)| match r {
            Ok(Change::Pending(d)) => Some((p.clone(), d.clone())),
            Err(e) => {
                eprintln!("error {}: {e}", p.display());
                None
            }
            _ => None,
        })
        .collect();
    diffs.sort_by(|a, b| a.0.cmp(&b.0));
    diffs.iter().for_each(|(_, d)| print!("{d}"));

    let any_changes = outcome
        .results
        .iter()
        .any(|(_, r)| matches!(r, Ok(Change::Written | Change::Pending(_))));
    if any_changes && !cli.write {
        eprintln!("# Run with `-w` to apply, or `-w -f` to also format.");
    }
    if any_changes
        && cli.write
        && let Some(tc) = &cli.fmt
    {
        run_cargo_fmt(&outcome.workspace_root, tc.as_deref())?;
    }
    Ok(())
}
