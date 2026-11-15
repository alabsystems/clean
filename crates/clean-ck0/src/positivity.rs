// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Strict-**positivity** checking (design §5.2 #2) — iterative (explicit work
//! stacks, stack-safe past 20k nesting depth and along any chain of
//! containers), fail-closed. Extracted from `inductive.rs` to keep both files
//! under the 500-line convention.
//!
//! A constructor type is checked in one post-order pass (`strict`): each
//! subterm in a strictly-positive position answers whether it mentions a block
//! type, and its parent applies the polarity rule to those answers, so each
//! node is read a bounded number of times (R176). The rules before R176 asked
//! each argument of a foreign application whether it mentions a block type by
//! a walk of its own and then walked it again, about `depth × |D|` for
//! `C (C (… (C D)))`. A foreign container's slot that must be strictly
//! positive is an obligation (`variance`), checked once per block whatever the
//! number of sites that need it; the oracle before R176 enumerated every simple
//! path through the containers (`2^k` scans for `k` containers that each use
//! the next one twice) and recursed natively once per container on the path.

use crate::name::Name;
use crate::term::{Term, TermKind};
use crate::validate::Env;

mod strict;
mod variance;

use strict::{scan_telescope, Target};
use variance::Obligations;

/// True iff `t` mentions `Const(n)` for ANY `n` in `names` (iterative).
pub(crate) fn term_mentions_any(t: &Term, names: &[Name]) -> bool {
    let mut stack = vec![t.clone()];
    while let Some(cur) = stack.pop() {
        match cur.kind() {
            TermKind::Const(c) => {
                if names.iter().any(|n| n == c.name()) {
                    return true;
                }
            }
            TermKind::App(f, a) => {
                stack.push(f.clone());
                stack.push(a.clone());
            }
            TermKind::Lam(_, ty, b) | TermKind::Pi(_, ty, b) => {
                stack.push(ty.clone());
                stack.push(b.clone());
            }
            TermKind::Let(ty, v, b) => {
                stack.push(ty.clone());
                stack.push(v.clone());
                stack.push(b.clone());
            }
            TermKind::Proj(_, _, e) => stack.push(e.clone()),
            TermKind::BVar(_) | TermKind::Sort(_) | TermKind::Elim(_) | TermKind::Lit(_) => {}
        }
    }
    false
}

/// True iff `t` mentions `Const(name)` anywhere (iterative).
pub(crate) fn term_mentions(t: &Term, name: &Name) -> bool {
    let mut stack = vec![t.clone()];
    while let Some(cur) = stack.pop() {
        match cur.kind() {
            TermKind::Const(c) => {
                if c.name() == name {
                    return true;
                }
            }
            TermKind::App(f, a) => {
                stack.push(f.clone());
                stack.push(a.clone());
            }
            TermKind::Lam(_, ty, b) | TermKind::Pi(_, ty, b) => {
                stack.push(ty.clone());
                stack.push(b.clone());
            }
            TermKind::Let(ty, v, b) => {
                stack.push(ty.clone());
                stack.push(v.clone());
                stack.push(b.clone());
            }
            TermKind::Proj(_, _, e) => stack.push(e.clone()),
            TermKind::BVar(_) | TermKind::Sort(_) | TermKind::Elim(_) | TermKind::Lit(_) => {}
        }
    }
    false
}

// ---------------------------------------------------------------------------
// Strict positivity (iterative, stack-safe, fail-closed, linear).
// ---------------------------------------------------------------------------

/// The strict-positivity check of one block's constructors: every type in
/// `block_names` must occur strictly-positively in each constructor type. For
/// a single-element block this is the M2 check.
///
/// The rules, applied to each Π domain of the constructor's telescope (its
/// final codomain, the return type, permits any occurrence):
///
/// * `A → B`: no block type may appear in `A`; `B` continues strictly
///   positive.
/// * `I a…` with `I` a block type: no `a` may mention a block type (nesting is
///   handled by the auxiliary construction BEFORE this check runs).
/// * `C a…` with `C` any other constant (a foreign container): each `a`
///   continues strictly positive, and an `a` that mentions a block type must
///   sit in a **strictly-positive parameter slot** of `C`. We do NOT assume
///   every container is covariant: a contravariant slot (the `X` of
///   `Hom (X Y) where mk : (X -> Y) -> Hom X Y`) puts the parent in a negative
///   position, which is what catches a contravariant container nested inside a
///   covariant one (`List (Hom (Tree A) (Tree A))`), where the inner container
///   stays folded. The slot is checked against `env`'s constructors of `C`;
///   an unknown container, an index slot or any doubt refuses (fail-closed).
/// * `h a…` with `h` not a constant: no `a` may mention a block type (its
///   covariance cannot be established), and `h` and each `a` continue
///   strictly positive.
/// * `λ`, `let`, projections: each part continues strictly positive.
///
/// What it establishes about a container's slots is kept for the block's next
/// constructor (R176). After a refusal every later check refuses: the slots a
/// refused check required are recorded as seen without having been shown
/// strictly positive, so they must never be read as established.
pub(crate) struct Positivity<'e> {
    block_names: &'e [Name],
    obligations: Obligations<'e>,
    refused: bool,
}

impl<'e> Positivity<'e> {
    /// A check of the block `block_names`, reading containers from `env`.
    pub(crate) fn new(env: &'e dyn Env, block_names: &'e [Name]) -> Self {
        Positivity {
            block_names,
            obligations: Obligations::new(env),
            refused: false,
        }
    }

    /// Check one constructor type. `Err(())` on the first non-strictly-
    /// positive / negative occurrence, and on every call after one.
    pub(crate) fn check_ctor(&mut self, ctor_ty: &Term) -> Result<(), ()> {
        if self.refused {
            return Err(());
        }
        let verdict = scan_telescope(
            ctor_ty,
            Target::Block(self.block_names),
            &mut self.obligations,
        )
        .and_then(|()| self.obligations.discharge());
        if verdict.is_err() {
            self.refused = true;
        }
        verdict
    }
}

/// True iff the de Bruijn variable that refers to the ctor's `param_idx`-th
/// leading-Pi parameter occurs anywhere in `t`, where `t` sits under `level`
/// binders from the ctor top. The target index *at this level* is
/// `level - 1 - param_idx`; it shifts as we descend further binders inside `t`.
fn bvar_mentions(t: &Term, param_idx: usize, level: usize) -> bool {
    // target index at the enclosing level, if representable.
    let base = match level.checked_sub(param_idx).and_then(|x| x.checked_sub(1)) {
        Some(b) => b,
        None => return false, // parameter not yet in scope here
    };
    // Walk with an explicit extra-binder counter so the target index shifts by
    // the number of binders descended INSIDE `t`.
    let mut stack: Vec<(Term, usize)> = vec![(t.clone(), 0)];
    while let Some((cur, extra)) = stack.pop() {
        let target = base.saturating_add(extra);
        match cur.kind() {
            TermKind::BVar(i) => {
                if usize::try_from(*i).map(|iv| iv == target).unwrap_or(false) {
                    return true;
                }
            }
            TermKind::App(f, a) => {
                stack.push((f.clone(), extra));
                stack.push((a.clone(), extra));
            }
            TermKind::Lam(_, ty, b) | TermKind::Pi(_, ty, b) => {
                stack.push((ty.clone(), extra));
                stack.push((b.clone(), extra.saturating_add(1)));
            }
            TermKind::Let(ty, v, b) => {
                stack.push((ty.clone(), extra));
                stack.push((v.clone(), extra));
                stack.push((b.clone(), extra.saturating_add(1)));
            }
            TermKind::Proj(_, _, e) => stack.push((e.clone(), extra)),
            TermKind::Const(_) | TermKind::Sort(_) | TermKind::Elim(_) | TermKind::Lit(_) => {}
        }
    }
    false
}

#[cfg(test)]
mod tests;
