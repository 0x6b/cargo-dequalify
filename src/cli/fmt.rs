use std::{
    collections::HashSet,
    fs::read_to_string,
    io::Write,
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::{Context, Result, bail};
use tempfile::{Builder, NamedTempFile};
use toml::{Table, Value, to_string_pretty};

pub(super) fn run_cargo_fmt(
    workspace_root: &Path,
    tc: Option<&str>,
    generated_rust_files: &[PathBuf],
) -> Result<()> {
    let rustfmt_config = if generated_rust_files.is_empty() {
        None
    } else {
        Some(rustfmt_config(workspace_root, generated_rust_files)?)
    };

    let mut cmd = Command::new("cargo");
    cmd.current_dir(workspace_root);
    if let Some(t) = tc {
        cmd.arg(format!("+{t}"));
    }
    cmd.arg("fmt");
    if let Some(config) = &rustfmt_config {
        cmd.arg("--").arg("--config-path").arg(config.path());
    }

    let status = cmd.status().context("cargo fmt")?;
    if !status.success() {
        bail!("cargo fmt failed");
    }
    Ok(())
}

fn rustfmt_config(
    workspace_root: &Path,
    generated_rust_files: &[PathBuf],
) -> Result<NamedTempFile> {
    let mut config = load_local_rustfmt_config(workspace_root)?;
    append_ignored_files(&mut config, generated_rust_files)?;
    let config = to_string_pretty(&config).context("serialize temporary rustfmt config")?;

    let mut file = Builder::new()
        .prefix(".cargo-dequalify-")
        .suffix("-rustfmt.toml")
        .tempfile_in(workspace_root)
        .context("create temporary rustfmt config")?;
    file.write_all(config.as_bytes())
        .context("write temporary rustfmt config")?;
    file.flush().context("flush temporary rustfmt config")?;
    Ok(file)
}

fn load_local_rustfmt_config(workspace_root: &Path) -> Result<Table> {
    for name in ["rustfmt.toml", ".rustfmt.toml"] {
        let path = workspace_root.join(name);
        if path.exists() {
            let content =
                read_to_string(&path).with_context(|| format!("read {}", path.display()))?;
            return content.parse().with_context(|| format!("parse {}", path.display()));
        }
    }

    Ok(Table::new())
}

fn append_ignored_files(config: &mut Table, generated_rust_files: &[PathBuf]) -> Result<()> {
    let Some(ignore) = config.remove("ignore") else {
        config.insert("ignore".to_owned(), ignored_files_value(Vec::new(), generated_rust_files));
        return Ok(());
    };

    let Value::Array(existing) = ignore else {
        bail!("rustfmt ignore must be an array");
    };

    config.insert("ignore".to_owned(), ignored_files_value(existing, generated_rust_files));
    Ok(())
}

fn ignored_files_value(mut existing: Vec<Value>, generated_rust_files: &[PathBuf]) -> Value {
    let mut seen: HashSet<String> =
        existing.iter().filter_map(Value::as_str).map(str::to_owned).collect();

    for path in generated_rust_files {
        let path = path.display().to_string();
        if seen.insert(path.clone()) {
            existing.push(Value::String(path));
        }
    }

    Value::Array(existing)
}

#[cfg(test)]
mod tests {
    #[cfg(test)]
    use toml::Table;

    use super::*;

    #[test]
    fn generated_ignores_are_added_to_local_ignore() {
        let mut config = Table::new();
        config.insert(
            "ignore".to_owned(),
            Value::Array(vec![Value::String("src/local.rs".to_owned())]),
        );

        append_ignored_files(
            &mut config,
            &[PathBuf::from("src/generated.rs"), PathBuf::from("src/local.rs")],
        )
        .unwrap();

        let ignored: Vec<_> = config["ignore"]
            .as_array()
            .unwrap()
            .iter()
            .map(|value| value.as_str().unwrap())
            .collect();

        assert_eq!(ignored, ["src/local.rs", "src/generated.rs"]);
    }
}
