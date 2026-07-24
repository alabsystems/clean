// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Operations on the trusted [`Term`]: de Bruijn `lift`/`instantiate` (no index
//! escape — design §5/§8), structural equality (hash fast-reject then shape
//! compare), structural hashing, and loose-bvar metadata. Split out of
//! `term.rs` to keep both files under the 500-line convention; it operates on
//! `Term`/`TermKind`'s `pub(crate)` fields, which remain private to anything
//! outside the crate.

use crate::level::Level;
use crate::term::{Term, TermKind};
use std::sync::Arc;

impl Term {
    // --- de Bruijn operations (no index escape; design §5/§8) ---

    /// Lift loose bvars `>= cutoff` by `amount`. Bound vars are untouched.
    /// Saturates rather than wraps so an index can never silently collide with
    /// another variable.
    #[must_use]
    pub fn lift(&self, amount: u32) -> Term {
        self.lift_at(0, amount)
    }

    fn lift_at(&self, cutoff: u32, amount: u32) -> Term {
        if amount == 0 || !self.has_loose {
            return self.clone();
        }
        match &*self.kind {
            TermKind::BVar(i) => {
                if *i >= cutoff {
                    // Loose var lifts; saturating is safe — an index at u32::MAX
                    // is already past any real context, and the chokepoint bounds
                    // indices to the actual context depth.
                    Term::bvar(i.saturating_add(amount))
                } else {
                    self.clone()
                }
            }
            TermKind::Sort(_) | TermKind::Const(_) | TermKind::Elim(_) | TermKind::Lit(_) => {
                self.clone()
            }
            TermKind::App(f, a) => Term::app(f.lift_at(cutoff, amount), a.lift_at(cutoff, amount)),
            TermKind::Lam(bi, ty, body) => Term::lam(
                *bi,
                ty.lift_at(cutoff, amount),
                body.lift_at(cutoff.saturating_add(1), amount),
            ),
            TermKind::Pi(bi, ty, body) => Term::pi(
                *bi,
                ty.lift_at(cutoff, amount),
                body.lift_at(cutoff.saturating_add(1), amount),
            ),
            TermKind::Let(ty, val, body) => Term::let_(
                ty.lift_at(cutoff, amount),
                val.lift_at(cutoff, amount),
                body.lift_at(cutoff.saturating_add(1), amount),
            ),
            TermKind::Proj(name, idx, e) => {
                Term::proj(name.clone(), *idx, e.lift_at(cutoff, amount))
            }
        }
    }

    /// Substitute `BVar(0)` with `val`, decrementing loose bvars above 0 (β/let).
    #[must_use]
    pub fn instantiate(&self, val: &Term) -> Term {
        self.instantiate_at(val, 0)
    }

    fn instantiate_at(&self, val: &Term, depth: u32) -> Term {
        if !self.has_loose {
            return self.clone();
        }
        match &*self.kind {
            TermKind::BVar(i) => match i.cmp(&depth) {
                std::cmp::Ordering::Equal => val.lift(depth),
                std::cmp::Ordering::Greater => {
                    // i > depth: this loose var loses one binder; decrement.
                    Term::bvar(i.saturating_sub(1))
                }
                std::cmp::Ordering::Less => self.clone(),
            },
            TermKind::Sort(_) | TermKind::Const(_) | TermKind::Elim(_) | TermKind::Lit(_) => {
                self.clone()
            }
            TermKind::App(f, a) => {
                Term::app(f.instantiate_at(val, depth), a.instantiate_at(val, depth))
            }
            TermKind::Lam(bi, ty, body) => Term::lam(
                *bi,
                ty.instantiate_at(val, depth),
                body.instantiate_at(val, depth.saturating_add(1)),
            ),
            TermKind::Pi(bi, ty, body) => Term::pi(
                *bi,
                ty.instantiate_at(val, depth),
                body.instantiate_at(val, depth.saturating_add(1)),
            ),
            TermKind::Let(ty, val2, body) => Term::let_(
                ty.instantiate_at(val, depth),
                val2.instantiate_at(val, depth),
                body.instantiate_at(val, depth.saturating_add(1)),
            ),
            TermKind::Proj(name, idx, e) => {
                Term::proj(name.clone(), *idx, e.instantiate_at(val, depth))
            }
        }
    }

    /// Substitute universe params `Param(i)` by `subst[i]` throughout the term
    /// (in `Sort`, `Const`, and `Elim` levels). de Bruijn structure is
    /// unchanged. Used when δ-unfolding a constant (the body is over its level
    /// params; the `ConstRef`'s actual level args are the `subst`) and when
    /// instantiating a constant's declared type.
    #[must_use]
    pub fn instantiate_levels(&self, subst: &[Level]) -> Term {
        if subst.is_empty() {
            return self.clone();
        }
        match &*self.kind {
            TermKind::BVar(_) | TermKind::Lit(_) => self.clone(),
            TermKind::Sort(l) => Term::sort(l.instantiate_params(subst)),
            TermKind::Const(c) => Term::const_ref(c.instantiate_levels(subst)),
            TermKind::Elim(e) => Term::elim(e.instantiate_levels(subst)),
            TermKind::App(f, a) => {
                Term::app(f.instantiate_levels(subst), a.instantiate_levels(subst))
            }
            TermKind::Lam(bi, ty, body) => Term::lam(
                *bi,
                ty.instantiate_levels(subst),
                body.instantiate_levels(subst),
            ),
            TermKind::Pi(bi, ty, body) => Term::pi(
                *bi,
                ty.instantiate_levels(subst),
                body.instantiate_levels(subst),
            ),
            TermKind::Let(ty, val, body) => Term::let_(
                ty.instantiate_levels(subst),
                val.instantiate_levels(subst),
                body.instantiate_levels(subst),
            ),
            TermKind::Proj(name, idx, e) => {
                Term::proj(name.clone(), *idx, e.instantiate_levels(subst))
            }
        }
    }
}

/// Structural equality fast-rejects on the cached hash, then compares shapes.
impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        if Arc::ptr_eq(&self.kind, &other.kind) {
            return true;
        }
        if self.hash != other.hash {
            return false;
        }
        kind_eq(&self.kind, &other.kind)
    }
}
impl Eq for Term {}

impl std::hash::Hash for Term {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash);
    }
}

fn kind_eq(a: &TermKind, b: &TermKind) -> bool {
    match (a, b) {
        (TermKind::BVar(x), TermKind::BVar(y)) => x == y,
        (TermKind::Sort(x), TermKind::Sort(y)) => x == y,
        (TermKind::Const(x), TermKind::Const(y)) => x == y,
        (TermKind::Elim(x), TermKind::Elim(y)) => x == y,
        (TermKind::App(f1, a1), TermKind::App(f2, a2)) => f1 == f2 && a1 == a2,
        (TermKind::Lam(b1, t1, x1), TermKind::Lam(b2, t2, x2))
        | (TermKind::Pi(b1, t1, x1), TermKind::Pi(b2, t2, x2)) => b1 == b2 && t1 == t2 && x1 == x2,
        (TermKind::Let(t1, v1, x1), TermKind::Let(t2, v2, x2)) => t1 == t2 && v1 == v2 && x1 == x2,
        (TermKind::Lit(x), TermKind::Lit(y)) => x == y,
        (TermKind::Proj(n1, i1, e1), TermKind::Proj(n2, i2, e2)) => {
            n1 == n2 && i1 == i2 && e1 == e2
        }
        _ => false,
    }
}

/// True iff `kind` (built from already-validated children) has any loose bvar.
pub(crate) fn compute_has_loose(kind: &TermKind) -> bool {
    has_loose_at(kind, 0)
}

/// True iff `kind` has a bvar `>= bound` (i.e. loose relative to `bound` binders).
fn has_loose_at(kind: &TermKind, bound: u32) -> bool {
    match kind {
        TermKind::BVar(i) => *i >= bound,
        TermKind::Sort(_) | TermKind::Const(_) | TermKind::Elim(_) | TermKind::Lit(_) => false,
        TermKind::App(f, a) => has_loose_at(&f.kind, bound) || has_loose_at(&a.kind, bound),
        TermKind::Lam(_, ty, body) | TermKind::Pi(_, ty, body) => {
            has_loose_at(&ty.kind, bound) || has_loose_at(&body.kind, bound.saturating_add(1))
        }
        TermKind::Let(ty, val, body) => {
            has_loose_at(&ty.kind, bound)
                || has_loose_at(&val.kind, bound)
                || has_loose_at(&body.kind, bound.saturating_add(1))
        }
        TermKind::Proj(_, _, e) => has_loose_at(&e.kind, bound),
    }
}

/// Structural hash of a node, combining children's cached hashes.
pub(crate) fn structural_hash(kind: &TermKind) -> u64 {
    use std::hash::Hasher;
    let mut h = std::collections::hash_map::DefaultHasher::new();
    hash_kind(kind, &mut h);
    h.finish()
}

fn hash_kind<H: std::hash::Hasher>(kind: &TermKind, h: &mut H) {
    use std::hash::Hash;
    std::mem::discriminant(kind).hash(h);
    match kind {
        TermKind::BVar(i) => i.hash(h),
        TermKind::Sort(l) => l.hash(h),
        TermKind::Const(c) => c.hash(h),
        TermKind::Elim(e) => e.hash(h),
        TermKind::App(f, a) => {
            h.write_u64(f.hash);
            h.write_u64(a.hash);
        }
        TermKind::Lam(bi, ty, body) | TermKind::Pi(bi, ty, body) => {
            bi.hash(h);
            h.write_u64(ty.hash);
            h.write_u64(body.hash);
        }
        TermKind::Let(ty, val, body) => {
            h.write_u64(ty.hash);
            h.write_u64(val.hash);
            h.write_u64(body.hash);
        }
        TermKind::Lit(l) => l.hash(h),
        TermKind::Proj(name, idx, e) => {
            name.hash(h);
            idx.hash(h);
            h.write_u64(e.hash);
        }
    }
}
