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
        if self.len == self.segs.len() {
            self.segs.last().unwrap().clone()
        } else {
            format!("{}::{}", self.segs[self.len - 1], self.segs[self.len..].join("::"))
        }
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
        .filter(|s| mappings.get(s.segs.last().unwrap()).is_some_and(|m| m == &s.full))
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
            .fold(false, |acc, s| acc | s.up());
        if !changed {
            break;
        }
    }
    let mut used = BTreeSet::new();
    strats
        .into_iter()
        .filter_map(|s| {
            (!s.same() && used.insert(s.ident().to_string())).then(|| (s.full.clone(), s))
        })
        .collect()
}
