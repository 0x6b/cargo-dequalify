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
    let mut strats: Vec<_> = paths.iter().map(|p| Strategy::new(p)).collect();
    for s in &mut strats {
        if mappings.get(s.segs.last().unwrap()).is_some_and(|m| m == &s.full) {
            s.exists = true;
        }
    }
    loop {
        let mut groups: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        for (i, s) in strats.iter().enumerate() {
            if !s.same() && !s.exists {
                groups.entry(s.ident().into()).or_default().push(i);
            }
        }
        let mut changed = false;
        for v in groups.values().filter(|v| v.len() > 1) {
            for &i in v {
                changed |= strats[i].up();
            }
        }
        if !changed {
            break;
        }
    }
    loop {
        let mut changed = false;
        for s in &mut strats {
            if !s.same() && !s.exists && existing.contains(s.ident()) {
                changed |= s.up();
            }
        }
        if !changed {
            break;
        }
    }
    let mut used = BTreeSet::new();
    let mut res = BTreeMap::new();
    for s in strats {
        if !s.same() && used.insert(s.ident().to_string()) {
            res.insert(s.full.clone(), s);
        }
    }
    res
}
