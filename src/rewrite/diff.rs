use std::path::Path;

use similar::{ChangeTag, TextDiff};

pub(super) fn diff(path: &Path, old: &str, new: &str) -> String {
    use std::fmt::Write;
    let d = TextDiff::from_lines(old, new);
    let mut out = String::new();
    writeln!(out, "--- {}", path.display()).unwrap();
    writeln!(out, "+++ {}", path.display()).unwrap();
    for h in d.unified_diff().context_radius(3).iter_hunks() {
        writeln!(out, "{}", h.header()).unwrap();
        for c in h.iter_changes() {
            write!(
                out,
                "{}{c}",
                match c.tag() {
                    ChangeTag::Delete => "-",
                    ChangeTag::Insert => "+",
                    ChangeTag::Equal => " ",
                }
            )
            .unwrap();
            if c.missing_newline() {
                writeln!(out).unwrap();
            }
        }
    }
    out
}
