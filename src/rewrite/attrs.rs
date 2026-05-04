use syn::{Attribute, Meta, spanned::Spanned};

use super::use_tree::path_str;

pub(super) fn extract_cfg(attrs: &[Attribute]) -> Vec<String> {
    attrs
        .iter()
        .filter_map(|a| {
            if a.path().is_ident("cfg") {
                a.meta.require_list().ok().map(|l| format!("cfg({})", l.tokens))
            } else if a.path().is_ident("cfg_attr") {
                cfg_attr_predicate(a)
            } else {
                None
            }
        })
        .collect()
}

/// Lower a `#[cfg_attr(p, attr1, attr2, ...)]` attribute into the equivalent
/// `cfg(any(not(p), <inner>))` predicate. The item exists when `not(p) || q`
/// (or `not(p) || all(q1, q2, ...)`). Returns `None` if no inner `cfg(...)`
/// attribute is present.
fn cfg_attr_predicate(attr: &Attribute) -> Option<String> {
    use syn::{Token, parse::Parser, punctuated::Punctuated};
    let l = attr.meta.require_list().ok()?;
    let metas = Punctuated::<Meta, Token![,]>::parse_terminated
        .parse2(l.tokens.clone())
        .ok()?;
    let mut iter = metas.iter();
    let pred_str = meta_to_string(iter.next()?);
    let inner_cfgs: Vec<String> = iter
        .filter_map(|m| match m {
            Meta::List(ml) if ml.path.is_ident("cfg") => Some(ml.tokens.to_string()),
            _ => None,
        })
        .collect();
    let inner = match inner_cfgs.len() {
        0 => return None,
        1 => inner_cfgs.into_iter().next().unwrap(),
        _ => format!("all({})", inner_cfgs.join(", ")),
    };
    Some(format!("cfg(any(not({pred_str}), {inner}))"))
}

fn meta_to_string(m: &Meta) -> String {
    // Prefer the original source text when available; fall back to a
    // best-effort reconstruction.
    if let Some(s) = m.span().source_text() {
        return s;
    }
    match m {
        Meta::Path(p) => path_str(p),
        Meta::List(l) => format!("{}({})", path_str(&l.path), l.tokens),
        Meta::NameValue(nv) => format!("{} = ?", path_str(&nv.path)),
    }
}
