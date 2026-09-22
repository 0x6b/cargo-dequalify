use std::{
    ffi::OsStr,
    path::{Path, PathBuf},
};

use anyhow::{Context, Result};
use gix::{attrs::StateRef, discover, worktree::stack::state::attributes::Source};
use ignore::{DirEntry, WalkBuilder};

pub(super) struct RustFiles {
    pub(super) files: Vec<PathBuf>,
    pub(super) generated: Vec<PathBuf>,
}

pub(super) fn rs_files_under(roots: &[PathBuf], workspace_root: &Path) -> Result<RustFiles> {
    let candidates: Vec<_> = roots.iter().flat_map(|r| rs_files_in(r)).collect();
    let Ok(repo) = discover(workspace_root) else {
        return Ok(RustFiles { files: candidates, generated: Vec::new() });
    };
    let worktree_root = repo.workdir().context("git repository has no worktree")?;
    let index = repo.index_or_load_from_head_or_empty().context("load git index")?;
    let source = Source::WorktreeThenIdMapping.adjust_for_bare(repo.is_bare());
    let mut attributes = repo.attributes_only(&index, source).context("load git attributes")?;
    let mut outcome = attributes.selected_attribute_matches(["linguist-generated"]);
    let mut files = Vec::new();
    let mut generated = Vec::new();

    for file in candidates {
        let Some(repo_relative) = file.strip_prefix(worktree_root).ok() else {
            files.push(file);
            continue;
        };
        attributes
            .at_entry(repo_relative, None)
            .with_context(|| format!("query git attributes for {}", file.display()))?
            .matching_attributes(&mut outcome);
        let is_generated =
            outcome
                .iter_selected()
                .next()
                .is_some_and(|matched| match matched.assignment.state {
                    StateRef::Set => true,
                    StateRef::Value(value) => value.as_bstr() == b"true".as_slice(),
                    StateRef::Unset | StateRef::Unspecified => false,
                });
        if is_generated {
            if let Some(relative) = relative_workspace_path(&file, workspace_root) {
                generated.push(relative.into());
            } else {
                files.push(file);
            }
        } else {
            files.push(file);
        }
    }

    generated.sort();
    generated.dedup();

    Ok(RustFiles { files, generated })
}

fn rs_files_in(root: &Path) -> impl Iterator<Item = PathBuf> {
    WalkBuilder::new(root)
        .standard_filters(true)
        .hidden(false)
        .follow_links(false)
        .build()
        .filter_map(Result::ok)
        .filter(|e| e.path().is_file() && e.path().extension() == Some(OsStr::new("rs")))
        .map(DirEntry::into_path)
}

fn relative_workspace_path(path: &Path, workspace_root: &Path) -> Option<String> {
    path.strip_prefix(workspace_root)
        .ok()
        .map(|path| path.to_string_lossy().replace('\\', "/"))
}

#[cfg(test)]
mod tests {
    use std::fs::{create_dir_all, write};

    #[cfg(test)]
    use tempfile::tempdir;

    use super::*;

    #[test]
    fn skips_generated_rust_files() {
        let temp = tempdir().unwrap();
        let root = temp.path();
        gix::init(root).unwrap();
        let src = root.join("src");
        create_dir_all(&src).unwrap();
        write(src.join("lib.rs"), "").unwrap();
        write(src.join("generated.rs"), "").unwrap();
        write(src.join("manual.rs"), "").unwrap();
        write(
            root.join(".gitattributes"),
            "src/generated.rs linguist-generated=true\nsrc/manual.rs linguist-generated=false\n",
        )
        .unwrap();

        let mut files = rs_files_under(&[root.to_path_buf()], root).unwrap();
        files.files.sort();

        assert_eq!(files.files, [src.join("lib.rs"), src.join("manual.rs")]);
        assert_eq!(files.generated, [PathBuf::from("src/generated.rs")]);
    }

    #[test]
    fn nested_gitattributes_override_parent_rules() {
        let temp = tempdir().unwrap();
        let root = temp.path();
        gix::init(root).unwrap();
        let src = root.join("src");
        create_dir_all(&src).unwrap();
        write(src.join("generated.rs"), "").unwrap();
        write(src.join("manual.rs"), "").unwrap();
        write(root.join(".gitattributes"), "*.rs linguist-generated\n").unwrap();
        write(src.join(".gitattributes"), "manual.rs -linguist-generated\n").unwrap();

        let files = rs_files_under(&[root.to_path_buf()], root).unwrap();

        assert_eq!(files.files, [src.join("manual.rs")]);
        assert_eq!(files.generated, [PathBuf::from("src/generated.rs")]);
    }

    #[test]
    fn star_does_not_match_across_directories() {
        let temp = tempdir().unwrap();
        let root = temp.path();
        gix::init(root).unwrap();
        let src = root.join("src");
        let nested = src.join("nested");
        create_dir_all(&nested).unwrap();
        write(src.join("generated.rs"), "").unwrap();
        write(nested.join("manual.rs"), "").unwrap();
        write(root.join(".gitattributes"), "src/*.rs linguist-generated\n").unwrap();

        let files = rs_files_under(&[root.to_path_buf()], root).unwrap();

        assert_eq!(files.files, [nested.join("manual.rs")]);
        assert_eq!(files.generated, [PathBuf::from("src/generated.rs")]);
    }
}
