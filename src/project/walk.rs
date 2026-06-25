use std::{
    ffi::OsStr,
    fs::read_to_string,
    path::{Path, PathBuf},
};

use globset::{Glob, GlobSet, GlobSetBuilder};
use ignore::{DirEntry, WalkBuilder};

pub(super) struct RustFiles {
    pub(super) files: Vec<PathBuf>,
    pub(super) generated: Vec<PathBuf>,
}

pub(super) fn rs_files_under(roots: &[PathBuf], workspace_root: &Path) -> RustFiles {
    let matcher = load_gitattributes(workspace_root);
    let mut files = Vec::new();
    let mut generated = Vec::new();

    for file in roots.iter().flat_map(|r| rs_files_in(r)) {
        let Some(relative) = relative_workspace_path(&file, workspace_root) else {
            files.push(file);
            continue;
        };

        if matcher
            .as_ref()
            .is_some_and(|matcher| matcher.is_generated(&relative))
        {
            generated.push(relative.into());
        } else {
            files.push(file);
        }
    }

    generated.sort();
    generated.dedup();

    RustFiles { files, generated }
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

struct GitAttrRule {
    glob: Glob,
    generated: bool,
}

struct GitAttrMatcher {
    globset: GlobSet,
    generated: Vec<bool>,
}

impl GitAttrMatcher {
    fn is_generated(&self, path: &str) -> bool {
        self.globset
            .matches(path)
            .last()
            .is_some_and(|&idx| self.generated[idx])
    }
}

fn load_gitattributes(root: &Path) -> Option<GitAttrMatcher> {
    let content = read_to_string(root.join(".gitattributes")).ok()?;
    let mut rules = Vec::new();

    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }

        let mut parts = line.split_whitespace();
        let Some(pattern) = parts.next() else {
            continue;
        };

        let generated = parts.find_map(|attr| match attr {
            "linguist-generated" | "linguist-generated=true" => Some(true),
            "-linguist-generated" | "linguist-generated=false" | "!linguist-generated" => {
                Some(false)
            }
            _ => None,
        });

        let Some(generated) = generated else {
            continue;
        };

        if let Ok(glob) = Glob::new(pattern) {
            rules.push(GitAttrRule { glob, generated });
        }
    }

    if rules.is_empty() {
        return None;
    }

    let mut builder = GlobSetBuilder::new();
    let mut generated = Vec::with_capacity(rules.len());

    for rule in rules {
        builder.add(rule.glob);
        generated.push(rule.generated);
    }

    builder
        .build()
        .ok()
        .map(|globset| GitAttrMatcher { globset, generated })
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
        let src = root.join("src");
        create_dir_all(&src).unwrap();
        write(src.join("lib.rs"), "").unwrap();
        write(src.join("generated.rs"), "").unwrap();
        write(root.join(".gitattributes"), "src/generated.rs linguist-generated=true\n").unwrap();

        let files = rs_files_under(&[root.to_path_buf()], root);

        assert_eq!(files.files, [src.join("lib.rs")]);
        assert_eq!(files.generated, [PathBuf::from("src/generated.rs")]);
    }

    #[test]
    fn later_gitattributes_rule_overrides_earlier_rule() {
        let mut builder = GlobSetBuilder::new();
        builder.add(Glob::new("src/*.rs").unwrap());
        builder.add(Glob::new("src/manual.rs").unwrap());

        let matcher = GitAttrMatcher {
            globset: builder.build().unwrap(),
            generated: vec![true, false],
        };

        assert!(matcher.is_generated("src/generated.rs"));
        assert!(!matcher.is_generated("src/manual.rs"));
    }
}
