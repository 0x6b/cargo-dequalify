use std::path::Path;

use anyhow::{Context, Result};
use gix::{discover, progress::Discard};

/// Returns `Ok(true)` if the worktree containing `path` has uncommitted
/// changes, `Ok(false)` if it is clean *or* if `path` is not inside a git
/// repository (no protection needed). Returns `Err` only when discovery
/// succeeded but the status query itself failed, so the caller can decide
/// whether to abort rather than silently overwriting files.
pub(super) fn git_dirty_state(path: &Path) -> Result<bool> {
    let Ok(repo) = discover(path) else {
        return Ok(false);
    };
    let mut iter = repo
        .status(Discard)
        .context("query git status")?
        .into_index_worktree_iter(None)
        .context("iterate index/worktree status")?;
    Ok(iter.next().is_some())
}
