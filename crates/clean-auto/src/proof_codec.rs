// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Canonical, resource-bounded wire codec for kernel proof terms.
//!
//! `CertifiedPayload` and the solver cache intentionally share the raw
//! bincode-2 `standard()` representation.  The raw representation is already a
//! cross-repository CleanCic contract: adding an in-band prefix here would
//! invalidate authenticated payload bytes and consumers that decode an `Expr`
//! directly.  Domain/version separation therefore belongs to the enclosing
//! carrier (`ProofEvidence` plus lineage for CleanCic, and
//! `solver-cache-entry-v1` for the local cache).  This module supplies the
//! strongest compatible inner contract: one encoder, whole-slice canonical
//! decoding, byte/allocation limits, and structural node/depth limits.

use clean_kernel::expr::ZFCSetExpr;
use clean_kernel::name::{Name, NameInner};
use clean_kernel::{BigNat, Expr, ExprKind, Level, Literal, MDataValue};
use serde::de::DeserializeOwned;
use serde::Serialize;

/// Maximum encoded size of a proof term (64 MiB).
///
/// This is deliberately much larger than current solver/cache HTTP envelopes
/// (1 MiB), while still placing a hard ceiling below the kernel certificate
/// stream's separate 256 MiB artifact limit.
pub(crate) const TERM_MAX_BYTES: usize = 64 * 1024 * 1024;

/// Maximum encoded size of a reduced local context (16 MiB).
///
/// Contexts contain declarations only and are normally far smaller than their
/// proof term; 16 MiB leaves substantial headroom without allowing an
/// unauthenticated context to claim unbounded allocations.
pub(crate) const CONTEXT_MAX_BYTES: usize = 16 * 1024 * 1024;

/// Structural limits applied to one proof term.
pub(crate) const TERM_STRUCTURE_LIMITS: StructuralLimits = StructuralLimits {
    max_nodes: 2_000_000,
    max_depth: 4_096,
};

/// Aggregate structural limits applied across one reduced context.
pub(crate) const CONTEXT_STRUCTURE_LIMITS: StructuralLimits = StructuralLimits {
    max_nodes: 500_000,
    max_depth: 4_096,
};

#[derive(Clone, Copy, Debug)]
pub(crate) struct StructuralLimits {
    pub(crate) max_nodes: usize,
    pub(crate) max_depth: usize,
}

/// Aggregate budget shared by every expression/name/level in one carrier.
///
/// Counting the entire decoded tree (not just top-level Expr nodes) closes
/// cheap amplification paths through huge universe-level trees, hierarchical
/// names, metadata maps, and large natural literals.
pub(crate) struct StructuralBudget {
    limits: StructuralLimits,
    nodes: usize,
}

impl StructuralBudget {
    pub(crate) fn new(limits: StructuralLimits) -> Self {
        Self { limits, nodes: 0 }
    }

    pub(crate) fn enter(&mut self, depth: usize, count: usize, kind: &str) -> Result<(), String> {
        if depth > self.limits.max_depth {
            return Err(format!(
                "{kind} structural depth {depth} exceeds limit {}",
                self.limits.max_depth
            ));
        }
        self.nodes = self
            .nodes
            .checked_add(count)
            .ok_or_else(|| format!("{kind} structural node count overflow"))?;
        if self.nodes > self.limits.max_nodes {
            return Err(format!(
                "{kind} structural node count {} exceeds limit {}",
                self.nodes, self.limits.max_nodes
            ));
        }
        Ok(())
    }

    pub(crate) fn validate_name(&mut self, name: &Name, base_depth: usize) -> Result<(), String> {
        let mut current = name;
        let mut depth = base_depth;
        loop {
            self.enter(depth, 1, "name")?;
            match current.inner() {
                NameInner::Anon => return Ok(()),
                NameInner::Str(parent, _) | NameInner::Num(parent, _) => {
                    current = parent;
                    depth = depth.saturating_add(1);
                }
            }
        }
    }

    pub(crate) fn validate_expr(&mut self, root: &Expr) -> Result<(), String> {
        let mut pending = vec![(root, 1usize)];
        while let Some((expr, depth)) = pending.pop() {
            self.enter(depth, 1, "expression")?;
            let child_depth = depth.saturating_add(1);
            match expr.kind() {
                ExprKind::BVar(_)
                | ExprKind::FVar(_)
                | ExprKind::SProp
                | ExprKind::CubicalInterval
                | ExprKind::CubicalI0
                | ExprKind::CubicalI1 => {}
                ExprKind::Sort(level) => self.validate_level(level, child_depth)?,
                ExprKind::Const(name, levels) => {
                    self.validate_name(name, child_depth)?;
                    for level in levels {
                        self.validate_level(level, child_depth)?;
                    }
                }
                ExprKind::App(f, a) => {
                    pending.push((f, child_depth));
                    pending.push((a, child_depth));
                }
                ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                    pending.push((ty, child_depth));
                    pending.push((body, child_depth));
                }
                ExprKind::Let(name, ty, value, body, _) => {
                    self.validate_name(name, child_depth)?;
                    pending.push((ty, child_depth));
                    pending.push((value, child_depth));
                    pending.push((body, child_depth));
                }
                ExprKind::Lit(literal) => self.validate_literal(literal, child_depth)?,
                ExprKind::Proj(name, _, inner) => {
                    self.validate_name(name, child_depth)?;
                    pending.push((inner, child_depth));
                }
                ExprKind::MData(metadata, inner) => {
                    for (name, value) in metadata {
                        self.enter(child_depth, 1, "metadata entry")?;
                        self.validate_name(name, child_depth.saturating_add(1))?;
                        if let MDataValue::Name(name) = value {
                            self.validate_name(name, child_depth.saturating_add(1))?;
                        }
                    }
                    pending.push((inner, child_depth));
                }
                ExprKind::Squash(inner) => pending.push((inner, child_depth)),
                ExprKind::CubicalPath { ty, left, right } => {
                    pending.push((ty, child_depth));
                    pending.push((left, child_depth));
                    pending.push((right, child_depth));
                }
                ExprKind::CubicalPathLam { body } => pending.push((body, child_depth)),
                ExprKind::CubicalPathApp { path, arg } => {
                    pending.push((path, child_depth));
                    pending.push((arg, child_depth));
                }
                ExprKind::CubicalHComp { ty, phi, u, base } => {
                    pending.push((ty, child_depth));
                    pending.push((phi, child_depth));
                    pending.push((u, child_depth));
                    pending.push((base, child_depth));
                }
                ExprKind::CubicalTransp { ty, phi, base } => {
                    pending.push((ty, child_depth));
                    pending.push((phi, child_depth));
                    pending.push((base, child_depth));
                }
                ExprKind::CubicalCoe { ty, r, s, base } => {
                    pending.push((ty, child_depth));
                    pending.push((r, child_depth));
                    pending.push((s, child_depth));
                    pending.push((base, child_depth));
                }
                ExprKind::ZFCSet(set) => {
                    push_zfc_children(&mut pending, set, child_depth);
                }
                ExprKind::ZFCMem { element, set } => {
                    pending.push((element, child_depth));
                    pending.push((set, child_depth));
                }
                ExprKind::ZFCComprehension { domain, pred } => {
                    pending.push((domain, child_depth));
                    pending.push((pred, child_depth));
                }
            }
        }
        Ok(())
    }

    fn validate_level(&mut self, root: &Level, base_depth: usize) -> Result<(), String> {
        let mut pending = vec![(root, base_depth)];
        while let Some((level, depth)) = pending.pop() {
            self.enter(depth, 1, "universe level")?;
            let child_depth = depth.saturating_add(1);
            match level {
                Level::Zero => {}
                Level::Succ(inner) => pending.push((inner, child_depth)),
                Level::Max(left, right) | Level::IMax(left, right) => {
                    pending.push((left, child_depth));
                    pending.push((right, child_depth));
                }
                Level::Param(name) => self.validate_name(name, child_depth)?,
            }
        }
        Ok(())
    }

    fn validate_literal(&mut self, literal: &Literal, depth: usize) -> Result<(), String> {
        self.enter(depth, 1, "literal")?;
        if let Literal::Nat(BigNat::Big(limbs)) = literal {
            // Constructors normalize BigNat::Big to at least two limbs with a
            // non-zero most-significant limb.  Reject alternate structural
            // spellings before they enter the kernel.
            if limbs.len() < 2 || limbs.last() == Some(&0) {
                return Err("non-canonical BigNat limb representation".to_string());
            }
            self.enter(depth.saturating_add(1), limbs.len(), "BigNat limbs")?;
        }
        Ok(())
    }
}

fn push_zfc_children<'a>(pending: &mut Vec<(&'a Expr, usize)>, set: &'a ZFCSetExpr, depth: usize) {
    match set {
        ZFCSetExpr::Empty | ZFCSetExpr::Infinity => {}
        ZFCSetExpr::Singleton(expr)
        | ZFCSetExpr::Union(expr)
        | ZFCSetExpr::PowerSet(expr)
        | ZFCSetExpr::Choice(expr) => pending.push((expr, depth)),
        ZFCSetExpr::Pair(left, right) => {
            pending.push((left, depth));
            pending.push((right, depth));
        }
        ZFCSetExpr::Separation { set, pred } => {
            pending.push((set, depth));
            pending.push((pred, depth));
        }
        ZFCSetExpr::Replacement { set, func } => {
            pending.push((set, depth));
            pending.push((func, depth));
        }
    }
}

pub(crate) fn encode_term(term: &Expr) -> Result<Vec<u8>, String> {
    encode_canonical::<_, TERM_MAX_BYTES>(term, "proof term", |term| {
        let mut budget = StructuralBudget::new(TERM_STRUCTURE_LIMITS);
        budget.validate_expr(term)
    })
}

pub(crate) fn decode_term(bytes: &[u8]) -> Result<Expr, String> {
    decode_canonical::<Expr, _, TERM_MAX_BYTES>(
        bytes,
        "proof term",
        TERM_STRUCTURE_LIMITS,
        |term| {
            let mut budget = StructuralBudget::new(TERM_STRUCTURE_LIMITS);
            budget.validate_expr(term)
        },
    )
}

pub(crate) fn encode_context<T, F>(context: &T, validate: F) -> Result<Vec<u8>, String>
where
    T: Serialize,
    F: FnOnce(&T) -> Result<(), String>,
{
    encode_canonical::<_, CONTEXT_MAX_BYTES>(context, "reduced-context", validate)
}

pub(crate) fn decode_context<T, F>(bytes: &[u8], validate: F) -> Result<T, String>
where
    T: DeserializeOwned + Serialize,
    F: FnOnce(&T) -> Result<(), String>,
{
    decode_canonical::<T, _, CONTEXT_MAX_BYTES>(
        bytes,
        "reduced-context",
        CONTEXT_STRUCTURE_LIMITS,
        validate,
    )
}

fn encode_canonical<T, const LIMIT: usize>(
    value: &T,
    carrier: &str,
    validate: impl FnOnce(&T) -> Result<(), String>,
) -> Result<Vec<u8>, String>
where
    T: Serialize,
{
    validate(value).map_err(|message| format!("invalid {carrier}: {message}"))?;
    let encoded =
        bincode::serde::encode_to_vec(value, bincode::config::standard().with_limit::<LIMIT>())
            .map_err(|error| format!("encode {carrier}: {error}"))?;
    ensure_carrier_size(encoded.len(), LIMIT, carrier)?;
    Ok(encoded)
}

fn decode_canonical<T, F, const LIMIT: usize>(
    bytes: &[u8],
    carrier: &str,
    structural_limits: StructuralLimits,
    validate: F,
) -> Result<T, String>
where
    T: DeserializeOwned + Serialize,
    F: FnOnce(&T) -> Result<(), String>,
{
    ensure_carrier_size(bytes.len(), LIMIT, carrier)?;
    let config = bincode::config::standard().with_limit::<LIMIT>();
    let decoded = clean_kernel::with_decode_resource_limits(
        clean_kernel::DecodeResourceLimits {
            max_nodes: structural_limits.max_nodes,
            max_depth: structural_limits.max_depth,
        },
        || bincode::serde::decode_from_slice(bytes, config),
    );
    let (value, consumed) = decoded.map_err(|error| format!("decode {carrier}: {error}"))?;
    if consumed != bytes.len() {
        return Err(format!(
            "non-canonical {carrier} encoding: decoded {consumed} of {} bytes",
            bytes.len()
        ));
    }

    validate(&value).map_err(|message| format!("invalid {carrier}: {message}"))?;

    // Exact consumption is insufficient: bincode accepts non-minimal varints.
    // Re-encoding proves this byte string is the unique standard spelling of
    // the decoded structural value.
    let canonical = bincode::serde::encode_to_vec(&value, config)
        .map_err(|error| format!("re-encode {carrier}: {error}"))?;
    if canonical != bytes {
        return Err(format!(
            "non-canonical {carrier} encoding: canonical re-encoding is {} bytes, supplied carrier is {} bytes",
            canonical.len(),
            bytes.len()
        ));
    }
    Ok(value)
}

fn ensure_carrier_size(len: usize, limit: usize, carrier: &str) -> Result<(), String> {
    if len > limit {
        return Err(format!(
            "{carrier} carrier is {len} bytes, exceeds limit {limit}"
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn carrier_size_boundary_is_exact() {
        assert!(ensure_carrier_size(TERM_MAX_BYTES, TERM_MAX_BYTES, "proof term").is_ok());
        let error = ensure_carrier_size(TERM_MAX_BYTES + 1, TERM_MAX_BYTES, "proof term")
            .expect_err("one byte over the limit must fail before decoding");
        assert!(error.contains("exceeds limit"), "{error}");
    }

    #[test]
    fn bincode_limit_rejects_decode_over_budget() {
        // The length prefix fits the outer slice check, but decoding the first
        // claimed u64 element would cross the configured bincode accounting
        // budget.  This exercises `with_limit` independently of the outer
        // carrier-size guard.
        let bytes = [64u8];
        let error = decode_canonical::<Vec<u64>, _, 8>(
            &bytes,
            "test vector",
            StructuralLimits {
                max_nodes: 100,
                max_depth: 100,
            },
            |_| Ok(()),
        )
        .expect_err("with_limit must reject decoding past its byte budget");
        assert!(error.contains("LimitExceeded"), "{error}");
    }

    #[test]
    fn structural_budget_rejects_depth_and_nodes() {
        let expr = Expr::app(Expr::const_str("f"), Expr::nat_lit(0));

        let mut depth_budget = StructuralBudget::new(StructuralLimits {
            max_nodes: 100,
            max_depth: 1,
        });
        let error = depth_budget
            .validate_expr(&expr)
            .expect_err("child depth exceeds the test limit");
        assert!(error.contains("structural depth"), "{error}");

        let mut node_budget = StructuralBudget::new(StructuralLimits {
            max_nodes: 2,
            max_depth: 100,
        });
        let error = node_budget
            .validate_expr(&expr)
            .expect_err("whole-tree node count exceeds the test limit");
        assert!(error.contains("structural node count"), "{error}");
    }
}
