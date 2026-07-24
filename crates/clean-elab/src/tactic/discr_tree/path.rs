// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::sync::LazyLock;

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Literal};

use super::key::{DiscrKey, IndexMode};
use crate::tactic::{Goal, ProofState};

static EQ_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Eq"));
static NAT_ZERO_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.zero"));

/// Maps a raw Nat-zero literal leaf to its constructor-spelling discrimination key.
///
/// The kernel treats `Lit(Nat 0)` and `Const(Nat.zero)` as definitionally equal
/// (`is_def_eq_offset`/`reduce_nat`), and the simp unifier bridges them via
/// `is_nat_zero`. But the discrimination tree keys them distinctly
/// (`DiscrKey::Lit` vs `DiscrKey::Const`), so a goal operand spelled as the raw
/// literal `0` would never select a lemma indexed under `Nat.zero` (e.g.
/// `Nat.zero_add`). To keep indexing and querying symmetric, we canonicalize a
/// genuine Nat-zero literal leaf to the `Const(Nat.zero, 0)` key.
///
/// SOUNDNESS: this only changes which candidate lemmas are *offered*. The actual
/// rewrite still runs through the simp unifier (`is_nat_zero`), the
/// `lhs_inst ≡ expr` def-eq guard, `proof_matches_rewrite`, and finally the
/// kernel `add_decl` re-typecheck. A spurious candidate that does not truly match
/// fails at unification; a wrong rewrite fails the kernel re-check. Since
/// `Lit(Nat 0)` is genuinely def-eq to `Nat.zero`, keying them together mirrors an
/// equivalence the kernel already enforces.
///
/// Checked on the RAW (pre-WHNF) expression so it fires only for literals already
/// present in the goal/pattern, NOT for arithmetic expressions like
/// `Nat.add Nat.zero Nat.zero` that WHNF would collapse to a literal — those keep
/// their existing collapsed-`Lit` keying, preserving the simproc/forall_congr path.
fn nat_literal_canonical_keys(expr: &Expr) -> Option<DiscrKey> {
    match expr.kind() {
        ExprKind::Lit(Literal::Nat(n)) if n.is_zero() => {
            Some(DiscrKey::Const(NAT_ZERO_NAME.clone(), 0))
        }
        _ => None,
    }
}

pub(crate) fn mk_path(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    mode: IndexMode,
) -> Vec<DiscrKey> {
    let mut keys = Vec::new();
    push_expr(state, goal, expr, mode, &mut keys);
    keys
}

pub(crate) fn query_path_is_too_generic(path: &[DiscrKey]) -> bool {
    if path.is_empty() || is_trivially_generic_path(path) {
        return true;
    }

    if matches!(path.first(), Some(DiscrKey::Star | DiscrKey::Other)) {
        return true;
    }

    let generic_keys = path.iter().filter(|key| is_generic_key(key)).count();
    generic_keys * 2 >= path.len()
}

pub(crate) fn is_trivially_generic_path(path: &[DiscrKey]) -> bool {
    matches!(path, [DiscrKey::Star]) || is_eq_star_path(path)
}

fn is_eq_star_path(path: &[DiscrKey]) -> bool {
    matches!(
        path,
        [
            DiscrKey::Const(name, 3),
            DiscrKey::Star,
            DiscrKey::Star,
            DiscrKey::Star,
        ] if name == &*EQ_NAME
    )
}

fn is_generic_key(key: &DiscrKey) -> bool {
    matches!(key, DiscrKey::Star | DiscrKey::Other)
}

fn push_expr(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    mode: IndexMode,
    keys: &mut Vec<DiscrKey>,
) {
    // Canonicalize a genuine Nat-zero literal leaf to its constructor key BEFORE
    // WHNF, so it fires only for literals already spelled in the goal/pattern.
    // See `nat_literal_canonical_keys` for the soundness argument.
    if let Some(key) = nat_literal_canonical_keys(expr) {
        keys.push(key);
        return;
    }

    let reduced = state.whnf(goal, expr);
    let head = reduced.get_app_fn();
    let args = reduced.get_app_args();

    match head.kind() {
        ExprKind::App(_, _) => keys.push(DiscrKey::Other),
        ExprKind::Const(name, _) => {
            keys.push(DiscrKey::Const(name.clone(), args.len()));
            push_args(state, goal, &args, mode, keys);
        }
        ExprKind::FVar(fvar) => {
            keys.push(DiscrKey::FVar(*fvar, args.len()));
            push_args(state, goal, &args, mode, keys);
        }
        ExprKind::Lit(lit) => {
            keys.push(DiscrKey::Lit(lit.clone()));
            push_args(state, goal, &args, mode, keys);
        }
        ExprKind::Proj(name, idx, inner) => {
            keys.push(DiscrKey::Proj(name.clone(), *idx, args.len()));
            push_expr(state, goal, inner, IndexMode::Normal, keys);
            push_args(state, goal, &args, mode, keys);
        }
        ExprKind::Pi(_, domain, _) => {
            keys.push(DiscrKey::Arrow);
            push_expr(state, goal, domain, IndexMode::Normal, keys);
        }
        ExprKind::BVar(_) => keys.push(DiscrKey::Star),
        ExprKind::MData(_, inner) => push_expr(state, goal, inner, mode, keys),
        ExprKind::Sort(_)
        | ExprKind::Lam(..)
        | ExprKind::Let(..)
        | ExprKind::SProp
        | ExprKind::Squash(_)
        | ExprKind::CubicalInterval
        | ExprKind::CubicalI0
        | ExprKind::CubicalI1
        | ExprKind::CubicalPath { .. }
        | ExprKind::CubicalPathLam { .. }
        | ExprKind::CubicalPathApp { .. }
        | ExprKind::CubicalHComp { .. }
        | ExprKind::CubicalTransp { .. }
        | ExprKind::CubicalCoe { .. }
        | ExprKind::ZFCSet(_)
        | ExprKind::ZFCMem { .. }
        | ExprKind::ZFCComprehension { .. } => keys.push(DiscrKey::Other),
    }
}

fn push_args(
    state: &ProofState,
    goal: &Goal,
    args: &[&Expr],
    mode: IndexMode,
    keys: &mut Vec<DiscrKey>,
) {
    match mode {
        IndexMode::NoIndexAtArgs => {
            keys.extend((0..args.len()).map(|_| DiscrKey::Star));
        }
        IndexMode::Normal => {
            for arg in args {
                push_expr(state, goal, arg, IndexMode::Normal, keys);
            }
        }
    }
}
