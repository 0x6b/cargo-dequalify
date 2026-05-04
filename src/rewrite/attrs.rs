use syn::{Attribute, Meta, spanned::Spanned};

use super::use_tree::path_str;

pub(super) fn extract_cfg(attrs: &[Attribute]) -> Vec<String> {
    use syn::{Token, parse::Parser, punctuated::Punctuated};
    let mut out = Vec::new();
    for a in attrs {
        if a.path().is_ident("cfg") {
            if let Ok(l) = a.meta.require_list() {
                out.push(format!("cfg({})", l.tokens));
            }
        } else if a.path().is_ident("cfg_attr") {
            // `#[cfg_attr(p, attr1, attr2, ...)]` applies the attrs only when
            // `p` holds. If an inner attribute is itself `cfg(q)`, the item
            // exists when `not(p) || q` (or `not(p) || all(q1, q2, ...)`).
            let Ok(l) = a.meta.require_list() else { continue };
            let Ok(metas) =
                Punctuated::<Meta, Token![,]>::parse_terminated.parse2(l.tokens.clone())
            else {
                continue;
            };
            let mut iter = metas.iter();
            let Some(pred) = iter.next() else { continue };
            let pred_str = meta_to_string(pred);
            let inner_cfgs: Vec<String> = iter
                .filter_map(|m| match m {
                    Meta::List(ml) if ml.path.is_ident("cfg") => Some(ml.tokens.to_string()),
                    _ => None,
                })
                .collect();
            if inner_cfgs.is_empty() {
                continue;
            }
            let inner = if inner_cfgs.len() == 1 {
                inner_cfgs.into_iter().next().unwrap()
            } else {
                format!("all({})", inner_cfgs.join(", "))
            };
            out.push(format!("cfg(any(not({pred_str}), {inner}))"));
        }
    }
    out
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
