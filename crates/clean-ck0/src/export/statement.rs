//! Stable statement identity, before reader elaboration. Hashing grants no
//! checking authority: target mode also requires an admitted theorem/closure.
use super::*;
use crate::{RawExpr, RawLevel, RawLit};
use sha2::{Digest, Sha256};

// Resource envelope for the unchanged v1 expanded encoding. Measured types:
// CIC_L 57,567 bytes; pinned Ax0 Init 814,899 bytes. Next power of two.
const MAX_V1_STATEMENT_BYTES: u64 = 1_048_576;
const DOMAIN: &[u8] = b"clean-ck0-statement-v1\0";

pub(super) fn hash(raw: &RawExpr, arity: u32) -> Result<String, Refusal> {
    let size = encoding_size(raw, &mut std::collections::HashMap::new())?;
    let prefix = u64::try_from(DOMAIN.len())
        .map_err(|_| Refusal::Limit)?
        .saturating_add(4);
    if size.saturating_add(prefix) > MAX_V1_STATEMENT_BYTES {
        return Err(Refusal::Limit);
    }
    let mut h = Sha256::new();
    h.update(DOMAIN);
    h.update(arity.to_be_bytes());
    expr(&mut h, raw)?;
    Ok(h.finalize().iter().map(|b| format!("{b:02x}")).collect())
}
fn bytes(h: &mut Sha256, value: &[u8]) -> Result<(), Refusal> {
    h.update(
        u32::try_from(value.len())
            .map_err(|_| Refusal::Limit)?
            .to_be_bytes(),
    );
    h.update(value);
    Ok(())
}
fn name(h: &mut Sha256, value: &Name) -> Result<(), Refusal> {
    let mut parts = Vec::new();
    let mut n = value.clone();
    while let Some(parent) = n.parent() {
        parts.push(n);
        n = parent;
    }
    h.update(
        u32::try_from(parts.len())
            .map_err(|_| Refusal::Limit)?
            .to_be_bytes(),
    );
    for p in parts.iter().rev() {
        if let Some(s) = p.last_str() {
            h.update([0]);
            bytes(h, s.as_bytes())?;
        } else if let Some(n) = p.last_num() {
            h.update([1]);
            h.update(n.to_be_bytes());
        } else {
            return Err(malformed("statement name component"));
        }
    }
    Ok(())
}
fn level(h: &mut Sha256, l: &RawLevel) {
    match l {
        RawLevel::Zero => h.update([0]),
        RawLevel::Succ(a) => {
            h.update([1]);
            level(h, a);
        }
        RawLevel::Max(a, b) => {
            h.update([2]);
            level(h, a);
            level(h, b);
        }
        RawLevel::IMax(a, b) => {
            h.update([3]);
            level(h, a);
            level(h, b);
        }
        RawLevel::Param(p) => {
            h.update([4]);
            h.update(p.to_be_bytes());
        }
    }
}
fn expr(h: &mut Sha256, e: &RawExpr) -> Result<(), Refusal> {
    match e {
        RawExpr::Shared(node) => expr(h, node.unshared())?,
        RawExpr::BVar(i) => {
            h.update([0]);
            h.update(i.to_be_bytes());
        }
        RawExpr::Sort(l) => {
            h.update([1]);
            level(h, l);
        }
        RawExpr::Const(n, ls) => {
            h.update([2]);
            name(h, n)?;
            h.update(
                u32::try_from(ls.len())
                    .map_err(|_| Refusal::Limit)?
                    .to_be_bytes(),
            );
            for l in ls {
                level(h, l);
            }
        }
        RawExpr::App(a, b) => {
            h.update([3]);
            expr(h, a)?;
            expr(h, b)?;
        }
        RawExpr::Lam(_, a, b) => {
            h.update([4]);
            expr(h, a)?;
            expr(h, b)?;
        }
        RawExpr::Pi(_, a, b) => {
            h.update([5]);
            expr(h, a)?;
            expr(h, b)?;
        }
        RawExpr::Let(a, b, c) => {
            h.update([6]);
            expr(h, a)?;
            expr(h, b)?;
            expr(h, c)?;
        }
        RawExpr::Lit(RawLit::Nat(n)) => {
            h.update([7]);
            bytes(h, n.to_string().as_bytes())?;
        }
        RawExpr::Lit(RawLit::Str(s)) => {
            h.update([8]);
            bytes(h, s.as_bytes())?;
        }
        RawExpr::Proj(n, i, e) => {
            h.update([9]);
            name(h, n)?;
            h.update(i.to_be_bytes());
            expr(h, e)?;
        }
        RawExpr::Elim(..) => return Err(malformed("internal eliminator in wire statement")),
    }
    Ok(())
}

/// Compute expanded v1 work by shared identity, before streaming any repeated
/// path. The bytes and all existing pins stay v1; an oversized hash is a
/// resource refusal, independent of whole-export checking.
fn encoding_size(
    raw: &RawExpr,
    memo: &mut std::collections::HashMap<*const RawExpr, u64>,
) -> Result<u64, Refusal> {
    let raw = raw.unshared();
    let key = std::ptr::from_ref(raw);
    if let Some(size) = memo.get(&key) {
        return Ok(*size);
    }
    let size = match raw {
        RawExpr::Shared(node) => encoding_size(node, memo)?,
        RawExpr::BVar(_) => 5,
        RawExpr::Sort(level) => 1u64.saturating_add(level_size(level)),
        RawExpr::Const(n, levels) => levels
            .iter()
            .map(level_size)
            .fold(5u64.saturating_add(name_size(n)?), u64::saturating_add),
        RawExpr::App(a, b) | RawExpr::Lam(_, a, b) | RawExpr::Pi(_, a, b) => 1u64
            .saturating_add(encoding_size(a, memo)?)
            .saturating_add(encoding_size(b, memo)?),
        RawExpr::Let(a, b, c) => 1u64
            .saturating_add(encoding_size(a, memo)?)
            .saturating_add(encoding_size(b, memo)?)
            .saturating_add(encoding_size(c, memo)?),
        RawExpr::Proj(n, _, value) => 5u64
            .saturating_add(name_size(n)?)
            .saturating_add(encoding_size(value, memo)?),
        RawExpr::Lit(RawLit::Nat(n)) => {
            5u64.saturating_add(u64::try_from(n.to_string().len()).map_err(|_| Refusal::Limit)?)
        }
        RawExpr::Lit(RawLit::Str(s)) => {
            5u64.saturating_add(u64::try_from(s.len()).map_err(|_| Refusal::Limit)?)
        }
        RawExpr::Elim(..) => return Err(malformed("internal eliminator in wire statement")),
    };
    if size > MAX_V1_STATEMENT_BYTES {
        return Err(Refusal::Limit);
    }
    memo.insert(key, size);
    Ok(size)
}
fn name_size(name: &Name) -> Result<u64, Refusal> {
    let mut cursor = name.clone();
    let mut bytes = 4u64;
    while let Some(parent) = cursor.parent() {
        bytes = bytes.saturating_add(if let Some(value) = cursor.last_str() {
            5u64.saturating_add(u64::try_from(value.len()).map_err(|_| Refusal::Limit)?)
        } else if cursor.last_num().is_some() {
            9
        } else {
            return Err(malformed("statement name component"));
        });
        cursor = parent;
    }
    Ok(bytes)
}
fn level_size(root: &RawLevel) -> u64 {
    let mut stack = vec![root];
    let mut bytes = 0u64;
    while let Some(level) = stack.pop() {
        bytes = bytes.saturating_add(1);
        match level {
            RawLevel::Succ(a) => stack.push(a),
            RawLevel::Max(a, b) | RawLevel::IMax(a, b) => stack.extend([a.as_ref(), b.as_ref()]),
            RawLevel::Param(_) => bytes = bytes.saturating_add(4),
            RawLevel::Zero => {}
        }
    }
    bytes
}
