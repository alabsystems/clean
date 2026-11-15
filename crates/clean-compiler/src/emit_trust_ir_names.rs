//! Exact compiler identity versus the historical String wire label.
//!
//! Preserve ordinary round-tripping names. Reserve the ENTIRE escape namespace,
//! including otherwise ordinary user names inside it. Typed payloads use `a`
//! for the root, then `s<UTF-8 hex>z` / `n<canonical u64 hex>z` per component.
//! The disjoint namespace and explicit constructor tags make this reversible.

use clean_kernel::name::NameInner;
use clean_kernel::{Expr, ExprKind, Level, Name};

pub(crate) const PREFIX: &str = "__clean_typed_v1_";

pub(crate) fn is_legacy_name(name: &Name) -> bool {
    let label = name.to_string();
    !label.starts_with(PREFIX) && Name::from_string(&label) == *name
}

pub(crate) fn wire_name(name: &Name) -> String {
    if is_legacy_name(name) {
        return name.to_string();
    }
    let mut components = Vec::new();
    let mut current = name;
    while !current.is_anon() {
        components.push(current);
        current = match current.inner() {
            NameInner::Str(parent, _) | NameInner::Num(parent, _) => parent,
            NameInner::Anon => break,
        };
    }
    let mut output = format!("{PREFIX}a");
    for component in components.into_iter().rev() {
        match component.inner() {
            NameInner::Str(_, value) => {
                output.push('s');
                for byte in value.as_bytes() {
                    use std::fmt::Write;
                    // Writing into String is infallible.
                    let _ = write!(output, "{byte:02x}");
                }
            }
            NameInner::Num(_, value) => {
                use std::fmt::Write;
                let _ = write!(output, "n{value:x}");
            }
            NameInner::Anon => {}
        }
        output.push('z');
    }
    output
}

pub(crate) fn decode_wire_name(label: &str) -> Option<Name> {
    let Some(encoded) = label.strip_prefix(PREFIX) else {
        let name = Name::from_string(label);
        return (is_legacy_name(&name) && name.to_string() == label).then_some(name);
    };
    let mut rest = encoded.strip_prefix('a')?;
    let mut name = Name::anon();
    while !rest.is_empty() {
        let kind = rest.as_bytes()[0];
        let end = rest.find('z')?;
        let payload = rest.get(1..end)?;
        if !payload
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            return None;
        }
        name = match kind {
            b's' => {
                if payload.len() % 2 != 0 {
                    return None;
                }
                let bytes: Option<Vec<u8>> = payload
                    .as_bytes()
                    .as_chunks::<2>()
                    .0
                    .iter()
                    .map(|pair| {
                        let text = std::str::from_utf8(pair).ok()?;
                        u8::from_str_radix(text, 16).ok()
                    })
                    .collect();
                name.str(String::from_utf8(bytes?).ok()?)
            }
            b'n' => {
                let n = u64::from_str_radix(payload, 16).ok()?;
                if format!("{n:x}") != payload {
                    return None;
                }
                name.num(n)
            }
            _ => return None,
        };
        rest = rest.get(end + 1..)?;
    }
    (wire_name(&name) == label).then_some(name)
}

/// The legacy TV vocabulary projects all source constant/level/owner names to
/// strings. Decline before invoking it whenever that projection is not exact;
/// this also protects ordinary callers of escaped callees and erased type rows.
pub(crate) fn legacy_source_identity_supported(root: &Expr) -> bool {
    let mut expressions = vec![root];
    let mut levels: Vec<&Level> = Vec::new();
    let mut seen_exprs = std::collections::HashSet::new();
    let mut seen_levels = std::collections::HashSet::new();
    while let Some(expr) = expressions.pop() {
        if !seen_exprs.insert(expr.kind() as *const ExprKind) {
            continue;
        }
        if seen_exprs.len() > 100_000 {
            return false;
        }
        match expr.kind() {
            ExprKind::Const(name, args) => {
                if !is_legacy_name(name) {
                    return false;
                }
                levels.extend(args.iter());
            }
            ExprKind::Sort(level) => levels.push(level),
            ExprKind::App(f, a) | ExprKind::Lam(_, f, a) | ExprKind::Pi(_, f, a) => {
                expressions.extend([f.as_ref(), a.as_ref()]);
            }
            ExprKind::Let(_, ty, value, body, _) => {
                expressions.extend([ty.as_ref(), value.as_ref(), body.as_ref()]);
            }
            ExprKind::Proj(name, _, value) => {
                if !is_legacy_name(name) {
                    return false;
                }
                expressions.push(value);
            }
            ExprKind::MData(_, value) => expressions.push(value),
            ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Lit(_) | ExprKind::SProp => {}
            // Non-core extension forms are not part of this identity walk or
            // the legacy TV contract; never guess about hidden references.
            _ => return false,
        }
    }
    while let Some(level) = levels.pop() {
        if !seen_levels.insert(level as *const Level) {
            continue;
        }
        if seen_levels.len() > 100_000 {
            return false;
        }
        match level {
            Level::Param(name) if !is_legacy_name(name) => return false,
            Level::Succ(inner) => levels.push(inner),
            Level::Max(a, b) | Level::IMax(a, b) => levels.extend([a.as_ref(), b.as_ref()]),
            _ => {}
        }
    }
    true
}
