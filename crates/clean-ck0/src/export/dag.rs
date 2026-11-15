//! Reader resource accounting after elaboration. Sharing changes cost, never
//! the checks of names, levels, references, typing or reduction rules.
use super::{syntax, Refusal};
use crate::{RawExpr, RawLevel, RawLit};
use std::collections::HashMap;

pub(super) fn bound(raw: &RawExpr) -> Result<(), Refusal> {
    let mut stack = vec![(raw, 1u64)];
    let mut seen = HashMap::<*const RawExpr, u64>::new();
    let mut weight = 0u64;
    while let Some((raw, depth)) = stack.pop() {
        if depth > syntax::MAX_WIRE_DEPTH {
            return Err(Refusal::Limit);
        }
        let raw = raw.unshared();
        let key = std::ptr::from_ref(raw);
        let previous = seen.get(&key).copied();
        if previous.is_some_and(|prior| prior >= depth) {
            continue;
        }
        seen.insert(key, depth);
        if previous.is_none() {
            let payload = match raw {
                RawExpr::Sort(l) => level_weight(l),
                RawExpr::Const(_, levels) => {
                    levels.iter().map(level_weight).fold(0, u64::saturating_add)
                }
                RawExpr::Elim(_, motive, levels) => levels
                    .iter()
                    .map(level_weight)
                    .fold(level_weight(motive), u64::saturating_add),
                RawExpr::Lit(RawLit::Str(s)) => {
                    u64::try_from(s.len()).map_err(|_| Refusal::Limit)?
                }
                RawExpr::Lit(RawLit::Nat(n)) => {
                    u64::try_from(n.to_string().len()).map_err(|_| Refusal::Limit)?
                }
                _ => 0,
            };
            weight = weight.saturating_add(1).saturating_add(payload);
            if weight > syntax::MAX_WIRE_DAG {
                return Err(Refusal::Limit);
            }
        }
        let next = depth.saturating_add(1);
        match raw {
            RawExpr::App(a, b) | RawExpr::Lam(_, a, b) | RawExpr::Pi(_, a, b) => {
                stack.extend([(a.as_ref(), next), (b.as_ref(), next)])
            }
            RawExpr::Let(a, b, c) => {
                stack.extend([(a.as_ref(), next), (b.as_ref(), next), (c.as_ref(), next)])
            }
            RawExpr::Proj(_, _, e) => stack.push((e, next)),
            RawExpr::Shared(e) => stack.push((e, depth)),
            _ => {}
        }
    }
    Ok(())
}

fn level_weight(root: &RawLevel) -> u64 {
    let mut stack = vec![root];
    let mut nodes = 0u64;
    while let Some(level) = stack.pop() {
        nodes = nodes.saturating_add(1);
        match level {
            RawLevel::Succ(a) => stack.push(a),
            RawLevel::Max(a, b) | RawLevel::IMax(a, b) => stack.extend([a.as_ref(), b.as_ref()]),
            _ => {}
        }
    }
    nodes
}
