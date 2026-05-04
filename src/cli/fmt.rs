use std::{path::Path, process::Command};

use anyhow::{Context, Result, bail};

pub(super) fn run_cargo_fmt(workspace_root: &Path, tc: Option<&str>) -> Result<()> {
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
