// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The last reading omega's hypothesis splitter gives a leaf: Lean's own.
//!
//! Lean 4.8's `omega` never sees a strict comparison or an equality as such:
//! `addFact` turns `a < b` into `a + 1 ≤ b` (`Int.add_one_le_of_lt`) and an
//! equality into a linear equation it solves (`Lean/Elab/Tactic/Omega/
//! Frontend.lean`). Clean's linear pipeline keeps both shapes and its
//! certificate replay refuses some of their refutations — `0 < a, a < 1 ⊢
//! False` and `c = 5, c < 3 ⊢ False` find the contradiction and then build no
//! kernel term — which is exactly the shape a case-split branch takes. So when
//! a leaf of the split tree still fails, its `Nat`/`Int` strict comparisons
//! are restated as `a + 1 ≤ b` (a definitional retyping: `Nat.lt a b` IS
//! `Nat.le (a + 1) b`, `Int.lt a b` IS `Int.le (a + 1) b`) and its `Nat`/`Int` equalities as two `≤` facts (a cast
//! through `Eq.ndrec`), and the pipeline runs once more. Nothing here proves
//! anything itself; every step is re-checked as the rest of the layer's are.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};

use super::super::proof_manipulation::cases_fvar;
use super::super::tc_app::{mk_tc_rel, nat_le_tc, rel_inst_for_type};
use super::super::{match_eq, match_gt, match_lt_any};
use super::{Goal, ProofState};

/// Restate every strict `Nat` comparison and every `Nat`/`Int` equality among
/// the current goal's locals as `≤` facts. Returns how many locals changed.
/// A step the checks refuse is skipped; one refused partway leaves an
/// equivalent fact (the caller rolls the whole leaf back unless it closes).
pub(super) fn tighten_leaf(state: &mut ProofState) -> usize {
    let Some(goal) = state.current_goal().cloned() else {
        return 0;
    };
    let mut changed = 0;
    for decl in &goal.local_ctx {
        if decl.value.is_some() {
            continue;
        }
        let ty = state.metas.instantiate(&decl.ty);
        if let Some(new_ty) = strict_as_le(&ty) {
            if state
                .replace_local_decl_type_validated(decl.fvar, new_ty)
                .is_ok()
            {
                changed += 1;
            }
            continue;
        }
        if equality_as_les(state, decl.fvar, &ty) {
            changed += 1;
        }
    }
    changed
}

/// `a < b` / `b > a` over `Nat` or `Int`, as `a + 1 ≤ b` (both carriers
/// define `<` that way: `Nat.lt n m := n + 1 ≤ m`, `Int.lt a b := a + 1 ≤ b`).
fn strict_as_le(ty: &Expr) -> Option<Expr> {
    let (carrier, lo, hi) = match_lt_any(ty).or_else(|| {
        // `x > y` is `y < x`.
        match_gt(ty).map(|(carrier, x, y)| (carrier, y, x))
    })?;
    if is_const(&carrier, "Nat") {
        let succ = Expr::apps(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            [lo, Expr::nat_lit(1)],
        );
        return Some(nat_le_tc(succ, hi));
    }
    if !is_const(&carrier, "Int") {
        return None;
    }
    let one = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(1),
    );
    let succ = Expr::apps(
        Expr::const_(Name::from_string("Int.add"), vec![]),
        [lo, one],
    );
    Some(mk_tc_rel(
        Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
        carrier.clone(),
        rel_inst_for_type(&carrier, "LE.le"),
        succ,
        hi,
    ))
}

/// Replace `h : a = b` (over `Nat` or `Int`) by `a ≤ b ∧ b ≤ a` and
/// destructure it. `true` when both steps were taken.
fn equality_as_les(state: &mut ProofState, fvar: FVarId, ty: &Expr) -> bool {
    let Some((carrier, a, b)) = match_eq(ty) else {
        return false;
    };
    let carrier_name = if is_const(&carrier, "Nat") {
        "Nat"
    } else if is_const(&carrier, "Int") {
        "Int"
    } else {
        return false;
    };
    let eq_level = match ty.get_app_fn().kind() {
        ExprKind::Const(_, levels) if levels.len() == 1 => levels[0].clone(),
        _ => return false,
    };
    let le = |l: Expr, r: Expr| {
        mk_tc_rel(
            Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            carrier.clone(),
            rel_inst_for_type(&carrier, "LE.le"),
            l,
            r,
        )
    };
    let refl = Expr::app(
        Expr::const_(
            Name::from_string(&format!("{carrier_name}.le_refl")),
            vec![],
        ),
        a.clone(),
    );
    // `@Eq.ndrec C a (λ x. motive x) (le_refl a) b h : motive b`
    let transport = |motive_body: Expr| {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.ndrec"),
                vec![Level::zero(), eq_level.clone()],
            ),
            [
                carrier.clone(),
                a.clone(),
                Expr::lam(BinderInfo::Default, carrier.clone(), motive_body),
                refl.clone(),
                b.clone(),
                Expr::fvar(fvar),
            ],
        )
    };
    // λ x. a ≤ x   and   λ x. x ≤ a   (x is BVar 0 under the motive binder)
    let a_le_b = transport(le(a.clone(), Expr::bvar(0)));
    let b_le_a = transport(le(Expr::bvar(0), a.clone()));
    let new_ty = Expr::apps(
        Expr::const_(Name::from_string("And"), vec![]),
        [le(a.clone(), b.clone()), le(b.clone(), a.clone())],
    );
    let cast = Expr::apps(
        Expr::const_(Name::from_string("And.intro"), vec![]),
        [le(a.clone(), b.clone()), le(b, a), a_le_b, b_le_a],
    );
    let Some(goal) = state.current_goal().cloned() else {
        return false;
    };
    if !cast_checks(state, &goal, &cast, &new_ty) {
        return false;
    }
    if state
        .replace_local_decl_with_cast(fvar, new_ty, cast)
        .is_err()
    {
        return false;
    }
    // The replaced local carries a fresh id; it is the one of type `new_ty`
    // now standing where `fvar` stood.
    let Some(replaced) = state.current_goal().and_then(|g| {
        g.local_ctx
            .iter()
            .find(|d| !goal.local_ctx.iter().any(|old| old.fvar == d.fvar))
            .map(|d| d.fvar)
    }) else {
        return false;
    };
    cases_fvar(state, replaced).is_ok() && state.goals.len() == 1
}

fn cast_checks(state: &ProofState, goal: &Goal, cast: &Expr, new_ty: &Expr) -> bool {
    state
        .infer_type_strict(goal, cast)
        .is_ok_and(|inferred| state.is_def_eq(goal, &inferred, new_ty))
}

fn is_const(e: &Expr, name: &str) -> bool {
    matches!(e.kind(), ExprKind::Const(n, _) if n.to_string() == name)
}
