use quote::ToTokens;
use syn::{Attribute, Meta, spanned::Spanned};

use super::use_tree::path_str;

pub(super) fn extract_cfg(attrs: &[Attribute]) -> Vec<String> {
    attrs
        .iter()
        .filter_map(|a| {
            if a.path().is_ident("cfg") {
                a.meta.require_list().ok().map(|l| l.tokens.to_string())
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
    Some(format!("any(not({pred_str}), {inner})"))
}

/// Render the union of conjunctions under which one generated import is
/// required. An empty conjunction means the import is unconditional.
pub(super) fn render_cfg_union<I>(requirements: I) -> Option<String>
where
    I: IntoIterator<Item = Vec<String>>,
{
    let mut clauses: Vec<Vec<String>> = requirements
        .into_iter()
        .map(|mut clause| {
            clause.sort();
            clause.dedup();
            clause
        })
        .collect();
    clauses.sort();
    clauses.dedup();
    if clauses.iter().any(Vec::is_empty) {
        return None;
    }

    // A weaker conjunction covers a stronger one: `a` already includes
    // `all(a, b)`, so the latter contributes nothing to the union.
    let snapshot = clauses.clone();
    clauses.retain(|clause| {
        !snapshot.iter().any(|other| {
            other.len() < clause.len() && other.iter().all(|predicate| clause.contains(predicate))
        })
    });

    let mut rendered = clauses.into_iter().map(render_conjunction);
    let first = rendered.next()?;
    let rest: Vec<_> = rendered.collect();
    if rest.is_empty() { Some(first) } else { Some(format!("any({first}, {})", rest.join(", "))) }
}

fn render_conjunction(clause: Vec<String>) -> String {
    if clause.len() == 1 {
        clause.into_iter().next().unwrap()
    } else {
        format!("all({})", clause.join(", "))
    }
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
        Meta::NameValue(nv) => format!("{} = {}", path_str(&nv.path), nv.value.to_token_stream()),
    }
}
