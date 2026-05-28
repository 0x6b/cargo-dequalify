use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone)]
pub(super) struct Strategy {
    pub(super) full: String,
    segs: Vec<String>,
    len: usize,
    exists: bool,
}

impl Strategy {
    fn new(p: &str) -> Self {
        let segs: Vec<_> = p.split("::").map(String::from).collect();
        Self {
            full: p.into(),
            len: segs.len(),
            segs,
            exists: false,
        }
    }

    fn ident(&self) -> &str {
        &self.segs[self.len - 1]
    }

    fn up(&mut self) -> bool {
        if self.len > 1 {
            self.len -= 1;
            true
        } else {
            false
        }
    }

    fn same(&self) -> bool {
        self.len == 1
    }

    pub(super) fn use_stmt(&self) -> Option<String> {
        (!self.exists).then(|| format!("use {};", self.segs[..self.len].join("::")))
    }

    pub(super) fn repl(&self) -> String {
        // segs[len-1..] is the last imported segment plus any unimported tail.
        self.segs[self.len - 1..].join("::")
    }

    fn prefix(&self) -> String {
        self.segs[..self.len].join("::")
    }

    /// True if `mappings[ident]` is exactly the prefix this strategy would
    /// import — i.e. the existing import already covers this strategy and no
    /// new `use` is needed.
    fn already_imported(&self, mappings: &BTreeMap<String, String>) -> bool {
        mappings.get(&self.segs[self.len - 1]) == Some(&self.prefix())
    }
}

pub(super) fn resolve(
    paths: &[String],
    existing: &BTreeSet<String>,
    mappings: &BTreeMap<String, String>,
) -> BTreeMap<String, Strategy> {
    let mut strats: Vec<Strategy> = paths.iter().map(|p| Strategy::new(p)).collect();
    strats
        .iter_mut()
        .filter(|s| s.already_imported(mappings))
        .for_each(|s| s.exists = true);
    loop {
        let groups: BTreeMap<String, Vec<usize>> = strats
            .iter()
            .enumerate()
            .filter(|(_, s)| !s.same() && !s.exists)
            .fold(BTreeMap::new(), |mut acc, (i, s)| {
                acc.entry(s.ident().into()).or_default().push(i);
                acc
            });
        let changed = groups
            .values()
            .filter(|v| v.len() > 1)
            .flat_map(|v| v.iter().copied())
            .fold(false, |acc, i| acc | strats[i].up());
        if !changed {
            break;
        }
    }
    loop {
        let changed = strats
            .iter_mut()
            .filter(|s| !s.same() && !s.exists && existing.contains(s.ident()))
            .fold(false, |acc, s| {
                // An existing-name collision is only a real conflict when the
                // existing alias points elsewhere. If `mappings[ident]` is the
                // very prefix we'd import, we're already at the optimal short
                // form — mark `exists` so no new `use` is emitted.
                if s.already_imported(mappings) {
                    s.exists = true;
                    acc
                } else {
                    acc | s.up()
                }
            });
        if !changed {
            break;
        }
    }
    // Two strategies sharing an `ident` are compatible iff they share the same
    // import prefix (one `use` covers both). When prefixes differ, only the
    // first wins; the others fall back to their original qualified form.
    let mut chosen: BTreeMap<String, String> = BTreeMap::new();
    strats
        .into_iter()
        .filter(|s| !s.same())
        .filter_map(|s| {
            let ident = s.ident().to_string();
            let prefix = s.prefix();
            match chosen.get(&ident) {
                Some(p) if *p == prefix => Some((s.full.clone(), s)),
                None => {
                    chosen.insert(ident, prefix);
                    Some((s.full.clone(), s))
                }
                _ => None,
            }
        })
        .collect()
}
