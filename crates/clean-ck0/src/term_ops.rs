// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Operations on the trusted [`Term`]: de Bruijn `lift`/`instantiate` (no index
//! escape — design §5/§8), structural equality (hash fast-reject then shape
//! compare), structural hashing, and loose-bvar metadata. Split out of
//! `term.rs` to keep both files under the 500-line convention; it operates on
//! `Term`/`TermKind`'s `pub(crate)` fields, which remain private to anything
//! outside the crate.

use crate::level::{Level, LevelTooDeep};
use crate::term::{Term, TermKind};
use crate::term_dag::NodeKey;
use std::collections::HashMap;
use std::sync::Arc;
type WalkMemo = HashMap<(NodeKey, u32), Term>;

impl Term {
    // --- de Bruijn operations (no index escape; design §5/§8) ---

    /// Lift loose bvars `>= cutoff` by `amount`. Bound vars are untouched.
    /// Saturates rather than wraps so an index can never silently collide with
    /// another variable.
    #[must_use]
    pub fn lift(&self, amount: u32) -> Term {
        self.lift_at(0, amount)
    }

    pub(crate) fn lift_at(&self, cutoff: u32, amount: u32) -> Term {
        self.lift_at_memo(cutoff, amount, &mut HashMap::new())
    }

    fn lift_at_memo(&self, cutoff: u32, amount: u32, memo: &mut WalkMemo) -> Term {
        let key = (NodeKey(self.clone()), cutoff);
        if let Some(out) = memo.get(&key) {
            return out.clone();
        }

        if amount == 0 || self.loose <= cutoff {
            return self.clone();
        }
        let out = match &*self.kind {
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
            TermKind::App(f, a) => Term::app(
                f.lift_at_memo(cutoff, amount, memo),
                a.lift_at_memo(cutoff, amount, memo),
            ),
            TermKind::Lam(bi, ty, body) => Term::lam(
                *bi,
                ty.lift_at_memo(cutoff, amount, memo),
                body.lift_at_memo(cutoff.saturating_add(1), amount, memo),
            ),
            TermKind::Pi(bi, ty, body) => Term::pi(
                *bi,
                ty.lift_at_memo(cutoff, amount, memo),
                body.lift_at_memo(cutoff.saturating_add(1), amount, memo),
            ),
            TermKind::Let(ty, val, body) => Term::let_(
                ty.lift_at_memo(cutoff, amount, memo),
                val.lift_at_memo(cutoff, amount, memo),
                body.lift_at_memo(cutoff.saturating_add(1), amount, memo),
            ),
            TermKind::Proj(name, idx, e) => {
                Term::proj(name.clone(), *idx, e.lift_at_memo(cutoff, amount, memo))
            }
        };
        memo.insert(key, out.clone());
        out
    }

    /// True iff `BVar(idx)` occurs loose in the term (Lean's `has_loose_bvar`):
    /// under `k` binders the same variable is `BVar(idx + k)`.
    #[must_use]
    pub(crate) fn has_loose_bvar(&self, idx: u32) -> bool {
        self.has_loose_bvar_memo(idx, &mut HashMap::new())
    }
    fn has_loose_bvar_memo(&self, idx: u32, memo: &mut HashMap<(NodeKey, u32), bool>) -> bool {
        let key = (NodeKey(self.clone()), idx);
        if let Some(out) = memo.get(&key) {
            return *out;
        }
        // `loose` is one past the largest loose index, so none is `idx` or above.
        if self.loose <= idx {
            return false;
        }
        let out = match &*self.kind {
            TermKind::BVar(i) => *i == idx,
            TermKind::Sort(_) | TermKind::Const(_) | TermKind::Elim(_) | TermKind::Lit(_) => false,
            TermKind::App(f, a) => {
                f.has_loose_bvar_memo(idx, memo) || a.has_loose_bvar_memo(idx, memo)
            }
            TermKind::Lam(_, ty, body) | TermKind::Pi(_, ty, body) => {
                ty.has_loose_bvar_memo(idx, memo)
                    || body.has_loose_bvar_memo(idx.saturating_add(1), memo)
            }
            TermKind::Let(ty, val, body) => {
                ty.has_loose_bvar_memo(idx, memo)
                    || val.has_loose_bvar_memo(idx, memo)
                    || body.has_loose_bvar_memo(idx.saturating_add(1), memo)
            }
            TermKind::Proj(_, _, e) => e.has_loose_bvar_memo(idx, memo),
        };
        memo.insert(key, out);
        out
    }

    /// Substitute `BVar(0)` with `val`, decrementing loose bvars above 0 (β/let).
    #[must_use]
    pub fn instantiate(&self, val: &Term) -> Term {
        self.instantiate_at(val, 0)
    }

    fn instantiate_at(&self, val: &Term, depth: u32) -> Term {
        self.instantiate_at_memo(val, depth, &mut HashMap::new())
    }

    fn instantiate_at_memo(&self, val: &Term, depth: u32, memo: &mut WalkMemo) -> Term {
        let key = (NodeKey(self.clone()), depth);
        if let Some(out) = memo.get(&key) {
            return out.clone();
        }

        if self.loose <= depth {
            return self.clone();
        }
        let out = match &*self.kind {
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
            TermKind::App(f, a) => Term::app(
                f.instantiate_at_memo(val, depth, memo),
                a.instantiate_at_memo(val, depth, memo),
            ),
            TermKind::Lam(bi, ty, body) => Term::lam(
                *bi,
                ty.instantiate_at_memo(val, depth, memo),
                body.instantiate_at_memo(val, depth.saturating_add(1), memo),
            ),
            TermKind::Pi(bi, ty, body) => Term::pi(
                *bi,
                ty.instantiate_at_memo(val, depth, memo),
                body.instantiate_at_memo(val, depth.saturating_add(1), memo),
            ),
            TermKind::Let(ty, val2, body) => Term::let_(
                ty.instantiate_at_memo(val, depth, memo),
                val2.instantiate_at_memo(val, depth, memo),
                body.instantiate_at_memo(val, depth.saturating_add(1), memo),
            ),
            TermKind::Proj(name, idx, e) => {
                Term::proj(name.clone(), *idx, e.instantiate_at_memo(val, depth, memo))
            }
        };
        memo.insert(key, out.clone());
        out
    }

    /// Substitute the values of `vals.len()` binders at once, `self` sitting
    /// under them with `vals[0]` the outermost: under `d` binders of `self`,
    /// `BVar(d + m)` for `m < k` is `vals[k - 1 - m]` lifted by `d`, and a
    /// loose variable past the `k` loses them (Lean's `instantiate_rev`). It is
    /// `k` calls of [`Term::instantiate`] in one pass: each node is rebuilt at
    /// most once, where the calls rebuild again the copies each earlier one
    /// made (R176).
    #[must_use]
    pub(crate) fn instantiate_many(&self, vals: &[Term]) -> Term {
        let k = u32::try_from(vals.len()).unwrap_or(u32::MAX);
        self.instantiate_many_at(vals, k, 0)
    }

    fn instantiate_many_at(&self, vals: &[Term], k: u32, depth: u32) -> Term {
        self.instantiate_many_at_memo(vals, k, depth, &mut HashMap::new())
    }

    fn instantiate_many_at_memo(
        &self,
        vals: &[Term],
        k: u32,
        depth: u32,
        memo: &mut WalkMemo,
    ) -> Term {
        let key = (NodeKey(self.clone()), depth);
        if let Some(out) = memo.get(&key) {
            return out.clone();
        }

        if k == 0 || self.loose <= depth {
            return self.clone();
        }
        let out = match &*self.kind {
            // AUDIT: checked; an index, never a value.
            TermKind::BVar(i) => match i.checked_sub(depth) {
                // Bound inside `self`.
                None => self.clone(),
                // The `m`-th binder out from `self`: `vals` counted from its
                // end, or past them all.
                Some(m) => match usize::try_from(m)
                    .ok()
                    .and_then(|m| vals.iter().rev().nth(m))
                {
                    Some(v) => v.lift(depth),
                    None => Term::bvar(i.saturating_sub(k)),
                },
            },
            TermKind::Sort(_) | TermKind::Const(_) | TermKind::Elim(_) | TermKind::Lit(_) => {
                self.clone()
            }
            TermKind::App(f, a) => Term::app(
                f.instantiate_many_at_memo(vals, k, depth, memo),
                a.instantiate_many_at_memo(vals, k, depth, memo),
            ),
            TermKind::Lam(bi, ty, body) => Term::lam(
                *bi,
                ty.instantiate_many_at_memo(vals, k, depth, memo),
                body.instantiate_many_at_memo(vals, k, depth.saturating_add(1), memo),
            ),
            TermKind::Pi(bi, ty, body) => Term::pi(
                *bi,
                ty.instantiate_many_at_memo(vals, k, depth, memo),
                body.instantiate_many_at_memo(vals, k, depth.saturating_add(1), memo),
            ),
            TermKind::Let(ty, val, body) => Term::let_(
                ty.instantiate_many_at_memo(vals, k, depth, memo),
                val.instantiate_many_at_memo(vals, k, depth, memo),
                body.instantiate_many_at_memo(vals, k, depth.saturating_add(1), memo),
            ),
            TermKind::Proj(name, idx, e) => Term::proj(
                name.clone(),
                *idx,
                e.instantiate_many_at_memo(vals, k, depth, memo),
            ),
        };
        memo.insert(key, out.clone());
        out
    }

    /// Substitute universe params `Param(i)` by `subst[i]` throughout the term
    /// (in `Sort`, `Const`, and `Elim` levels). de Bruijn structure is
    /// unchanged. Used when δ-unfolding a constant (the body is over its level
    /// params; the `ConstRef`'s actual level args are the `subst`) and when
    /// instantiating a constant's declared type.
    ///
    /// # Errors
    /// [`LevelTooDeep`] when an instantiated level would be deeper than the
    /// depth bound: canonicalising can grow a level far past its inputs
    /// (R166), and the level is refused before anything walks it.
    pub(crate) fn instantiate_levels(&self, subst: &[Level]) -> Result<Term, LevelTooDeep> {
        if subst.is_empty() {
            return Ok(self.clone());
        }
        let t = self.instantiate_levels_rec(subst)?;
        // A level grown in place grows every term above it: the result is held
        // to the bound its inputs were, so nothing downstream walks a deeper one.
        if t.depth > crate::MAX_VALIDATE_DEPTH {
            return Err(LevelTooDeep);
        }
        Ok(t)
    }

    fn instantiate_levels_rec(&self, subst: &[Level]) -> Result<Term, LevelTooDeep> {
        self.instantiate_levels_rec_memo(subst, &mut HashMap::new())
    }

    fn instantiate_levels_rec_memo(
        &self,
        subst: &[Level],
        memo: &mut HashMap<NodeKey, Term>,
    ) -> Result<Term, LevelTooDeep> {
        let key = NodeKey(self.clone());
        if let Some(out) = memo.get(&key) {
            return Ok(out.clone());
        }

        let out = match &*self.kind {
            TermKind::BVar(_) | TermKind::Lit(_) => self.clone(),
            TermKind::Sort(l) => Term::sort(l.try_instantiate_params(subst)?),
            TermKind::Const(c) => Term::const_ref(c.instantiate_levels(subst)?),
            TermKind::Elim(e) => Term::elim(e.instantiate_levels(subst)?),
            TermKind::App(f, a) => Term::app(
                f.instantiate_levels_rec_memo(subst, memo)?,
                a.instantiate_levels_rec_memo(subst, memo)?,
            ),
            TermKind::Lam(bi, ty, body) => Term::lam(
                *bi,
                ty.instantiate_levels_rec_memo(subst, memo)?,
                body.instantiate_levels_rec_memo(subst, memo)?,
            ),
            TermKind::Pi(bi, ty, body) => Term::pi(
                *bi,
                ty.instantiate_levels_rec_memo(subst, memo)?,
                body.instantiate_levels_rec_memo(subst, memo)?,
            ),
            TermKind::Let(ty, val, body) => Term::let_(
                ty.instantiate_levels_rec_memo(subst, memo)?,
                val.instantiate_levels_rec_memo(subst, memo)?,
                body.instantiate_levels_rec_memo(subst, memo)?,
            ),
            TermKind::Proj(name, idx, e) => Term::proj(
                name.clone(),
                *idx,
                e.instantiate_levels_rec_memo(subst, memo)?,
            ),
        };
        memo.insert(key, out.clone());
        Ok(out)
    }
}

/// Structural equality fast-rejects on the cached hash, then compares shapes.
impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        if Arc::ptr_eq(&self.kind, &other.kind) || self.hash != other.hash {
            #[cfg(test)]
            crate::term::walk_step();
            return Arc::ptr_eq(&self.kind, &other.kind);
        }
        let mut stack = vec![(self, other)];
        let mut seen = std::collections::HashSet::new();
        while let Some((a, b)) = stack.pop() {
            #[cfg(test)]
            crate::term::walk_step();
            if Arc::ptr_eq(&a.kind, &b.kind) {
                continue;
            }
            if a.hash != b.hash {
                return false;
            }
            if !seen.insert((Arc::as_ptr(&a.kind), Arc::as_ptr(&b.kind))) {
                continue;
            }
            match (a.kind(), b.kind()) {
                (TermKind::BVar(x), TermKind::BVar(y)) if x == y => {}
                (TermKind::Sort(x), TermKind::Sort(y)) if x == y => {}
                (TermKind::Const(x), TermKind::Const(y)) if x == y => {}
                (TermKind::Elim(x), TermKind::Elim(y)) if x == y => {}
                (TermKind::Lit(x), TermKind::Lit(y)) if x == y => {}
                (TermKind::App(a, b), TermKind::App(c, d)) => stack.extend([(b, d), (a, c)]),
                (TermKind::Lam(i, a, b), TermKind::Lam(j, c, d))
                | (TermKind::Pi(i, a, b), TermKind::Pi(j, c, d))
                    if i == j =>
                {
                    stack.extend([(b, d), (a, c)])
                }
                (TermKind::Let(a, b, c), TermKind::Let(d, e, f)) => {
                    stack.extend([(c, f), (b, e), (a, d)])
                }
                (TermKind::Proj(n, i, a), TermKind::Proj(m, j, b)) if n == m && i == j => {
                    stack.push((a, b))
                }
                _ => return false,
            }
        }
        true
    }
}
impl Eq for Term {}

impl std::hash::Hash for Term {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash);
    }
}

pub(crate) fn kind_eq(a: &TermKind, b: &TermKind) -> bool {
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

/// One past the largest loose bvar of a node built from `kind`, from its
/// children's cached ranges (a binder's body loses one).
pub(crate) fn compute_loose_range(kind: &TermKind) -> u32 {
    let under = |t: &Term| t.loose.saturating_sub(1);
    match kind {
        TermKind::BVar(i) => i.saturating_add(1),
        TermKind::Sort(_) | TermKind::Const(_) | TermKind::Elim(_) | TermKind::Lit(_) => 0,
        TermKind::App(f, a) => f.loose.max(a.loose),
        TermKind::Lam(_, ty, body) | TermKind::Pi(_, ty, body) => ty.loose.max(under(body)),
        TermKind::Let(ty, val, body) => ty.loose.max(val.loose).max(under(body)),
        TermKind::Proj(_, _, e) => e.loose,
    }
}

/// Height of a node built from `kind` (a leaf is 1), from its children's and
/// its levels' cached depths in O(1) per child (R166). A level counts toward the
/// height of the term it sits in, as `validate`'s input bound counts it: level
/// operations recurse natively over it from wherever the term walk reached.
pub(crate) fn compute_depth(kind: &TermKind) -> u32 {
    let deepest = |levels: &[Level]| levels.iter().map(Level::depth).max();
    let below = match kind {
        TermKind::BVar(_) | TermKind::Lit(_) => 0,
        TermKind::Sort(l) => l.depth(),
        TermKind::Const(c) => deepest(c.levels()).unwrap_or(0),
        TermKind::Elim(e) => deepest(e.levels()).unwrap_or(0),
        TermKind::App(f, a) => f.depth.max(a.depth),
        TermKind::Lam(_, ty, body) | TermKind::Pi(_, ty, body) => ty.depth.max(body.depth),
        TermKind::Let(ty, val, body) => ty.depth.max(val.depth).max(body.depth),
        TermKind::Proj(_, _, e) => e.depth,
    };
    below.saturating_add(1)
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
