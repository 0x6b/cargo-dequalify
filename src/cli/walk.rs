use std::{
    ffi::OsStr,
    path::{Path, PathBuf},
};

use ignore::WalkBuilder;

pub(super) fn rs_files_under(roots: &[PathBuf]) -> Vec<PathBuf> {
    roots.iter().flat_map(|r| rs_files_in(r)).collect()
}

fn rs_files_in(root: &Path) -> impl Iterator<Item = PathBuf> {
    WalkBuilder::new(root)
        .standard_filters(true)
        .hidden(false)
        .follow_links(false)
        .build()
        .filter_map(Result::ok)
        .filter(|e| e.path().is_file() && e.path().extension() == Some(OsStr::new("rs")))
        .map(|e| e.into_path())
}
