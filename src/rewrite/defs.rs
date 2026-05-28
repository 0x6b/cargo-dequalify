use std::collections::BTreeSet;

use syn::{
    File, ForeignItem, ImplItem, Item, ItemConst, ItemEnum, ItemImpl, ItemMod, ItemStatic,
    ItemStruct, ItemTrait, ItemType, ItemUnion, Path as SynPath, TypePath,
    visit::{Visit, visit_path, visit_type_path},
};

use super::consts::{PRELUDE, PRIMITIVES};

/// Names defined directly inside a sequence of items (e.g. the contents of
/// a file or a `mod { ... }`). Includes inherent-impl method names so they
/// can shadow potential short-name imports.
pub(super) fn collect_defs(items: &[Item]) -> BTreeSet<String> {
    items.iter().flat_map(item_def_idents).collect()
}

fn item_def_idents(item: &Item) -> Vec<String> {
    match item {
        Item::Fn(f) => vec![f.sig.ident.to_string()],
        Item::Struct(ItemStruct { ident, .. })
        | Item::Enum(ItemEnum { ident, .. })
        | Item::Union(ItemUnion { ident, .. })
        | Item::Trait(ItemTrait { ident, .. })
        | Item::Type(ItemType { ident, .. })
        | Item::Mod(ItemMod { ident, .. })
        | Item::Static(ItemStatic { ident, .. })
        | Item::Const(ItemConst { ident, .. }) => vec![ident.to_string()],
        Item::Impl(ItemImpl { items, .. }) => items
            .iter()
            .filter_map(|ii| match ii {
                ImplItem::Fn(f) => Some(f.sig.ident.to_string()),
                ImplItem::Const(c) => Some(c.ident.to_string()),
                ImplItem::Type(t) => Some(t.ident.to_string()),
                _ => None,
            })
            .collect(),
        Item::ForeignMod(fm) => fm
            .items
            .iter()
            .filter_map(|fi| match fi {
                ForeignItem::Fn(f) => Some(f.sig.ident.to_string()),
                ForeignItem::Static(s) => Some(s.ident.to_string()),
                ForeignItem::Type(t) => Some(t.ident.to_string()),
                _ => None,
            })
            .collect(),
        _ => vec![],
    }
}

pub(super) fn collect_unqualified_names(ast: &File) -> BTreeSet<String> {
    struct V(BTreeSet<String>);
    impl<'a> Visit<'a> for V {
        fn visit_type_path(&mut self, n: &'a TypePath) {
            if n.qself.is_none() && n.path.segments.len() == 1 {
                let id = n.path.segments[0].ident.to_string();
                if id != "Self"
                    && !PRIMITIVES.contains(&id.as_str())
                    && !(id.len() == 1 && id.chars().next().unwrap().is_uppercase())
                {
                    self.0.insert(id);
                }
            }
            visit_type_path(self, n);
        }
    }
    let mut v = V(BTreeSet::new());
    v.visit_file(ast);
    v.0
}

pub(super) fn collect_prelude(ast: &File) -> BTreeSet<String> {
    struct V(BTreeSet<String>);
    impl<'a> Visit<'a> for V {
        // Use `visit_path` so we catch prelude names in every position they
        // can appear: type paths, expression paths, trait bounds, etc.
        fn visit_path(&mut self, n: &'a SynPath) {
            if n.segments.len() == 1 {
                let id = n.segments[0].ident.to_string();
                if PRELUDE.contains(&id.as_str()) {
                    self.0.insert(id);
                }
            }
            visit_path(self, n);
        }
    }
    let mut v = V(BTreeSet::new());
    v.visit_file(ast);
    v.0
}
