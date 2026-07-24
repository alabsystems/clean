// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

use super::super::simp::mk_eq_trans_expr;
use super::super::{Goal, ProofState, TacticError};
use super::make_not;

#[derive(Debug, Clone)]
pub(crate) struct PropRewriteResult {
    pub(crate) expr: Expr,
    pub(crate) proof: Option<Expr>,
}

pub(super) fn require_const(state: &ProofState, constant: &str) -> Result<(), TacticError> {
    if state
        .env()
        .get_const(&Name::from_string(constant))
        .is_some()
    {
        Ok(())
    } else {
        Err(TacticError::EnvironmentMissing {
            constant: constant.to_string(),
        })
    }
}

pub(super) fn require_consts(state: &ProofState, constants: &[&str]) -> Result<(), TacticError> {
    for constant in constants {
        require_const(state, constant)?;
    }
    Ok(())
}

pub(super) fn mk_lambda<F>(state: &mut ProofState, binder_ty: &Expr, body_builder: F) -> Expr
where
    F: FnOnce(&mut ProofState, Expr) -> Expr,
{
    let fvar = state.fresh_fvar();
    let fvar_expr = Expr::fvar(fvar);
    let body = body_builder(state, fvar_expr.clone()).abstract_fvar(fvar);
    Expr::lam(BinderInfo::Default, binder_ty.clone(), body)
}

fn mk_eq_trans_or_err(
    state: &ProofState,
    goal: &Goal,
    lhs: &Expr,
    rhs: &Expr,
) -> Result<Expr, TacticError> {
    mk_eq_trans_expr(state, goal, lhs, rhs).ok_or_else(|| {
        TacticError::TypeCheckFailed(
            "push_neg: failed to compose recursive equality proofs with Eq.trans".into(),
        )
    })
}

pub(super) fn compose_rewrite_steps(
    state: &ProofState,
    goal: &Goal,
    first: PropRewriteResult,
    second: PropRewriteResult,
) -> Result<PropRewriteResult, TacticError> {
    let proof = match (first.proof, second.proof) {
        (None, proof) => proof,
        (proof, None) => proof,
        (Some(lhs), Some(rhs)) => Some(mk_eq_trans_or_err(state, goal, &lhs, &rhs)?),
    };
    Ok(PropRewriteResult {
        expr: second.expr,
        proof,
    })
}

pub(super) fn mk_prop_rewrite_result(expr: Expr, proof: Expr) -> PropRewriteResult {
    PropRewriteResult {
        expr,
        proof: Some(proof),
    }
}

pub(super) fn mk_false_elim(goal_ty: &Expr, false_proof: Expr) -> Expr {
    let mut proof = Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);
    proof = Expr::app(proof, goal_ty.clone());
    proof = Expr::app(proof, false_proof);
    proof
}

pub(super) fn mk_and_intro(lhs: &Expr, rhs: &Expr, lhs_proof: Expr, rhs_proof: Expr) -> Expr {
    let mut proof = Expr::const_(Name::from_string("And.intro"), vec![]);
    proof = Expr::app(proof, lhs.clone());
    proof = Expr::app(proof, rhs.clone());
    proof = Expr::app(proof, lhs_proof);
    proof = Expr::app(proof, rhs_proof);
    proof
}

pub(super) fn mk_and_left(lhs: &Expr, rhs: &Expr, and_proof: Expr) -> Expr {
    let mut proof = Expr::const_(Name::from_string("And.left"), vec![]);
    proof = Expr::app(proof, lhs.clone());
    proof = Expr::app(proof, rhs.clone());
    proof = Expr::app(proof, and_proof);
    proof
}

pub(super) fn mk_and_right(lhs: &Expr, rhs: &Expr, and_proof: Expr) -> Expr {
    let mut proof = Expr::const_(Name::from_string("And.right"), vec![]);
    proof = Expr::app(proof, lhs.clone());
    proof = Expr::app(proof, rhs.clone());
    proof = Expr::app(proof, and_proof);
    proof
}

pub(super) fn mk_or_inl(lhs: &Expr, rhs: &Expr, lhs_proof: Expr) -> Expr {
    let mut proof = Expr::const_(Name::from_string("Or.inl"), vec![]);
    proof = Expr::app(proof, lhs.clone());
    proof = Expr::app(proof, rhs.clone());
    proof = Expr::app(proof, lhs_proof);
    proof
}

pub(super) fn mk_or_inr(lhs: &Expr, rhs: &Expr, rhs_proof: Expr) -> Expr {
    let mut proof = Expr::const_(Name::from_string("Or.inr"), vec![]);
    proof = Expr::app(proof, lhs.clone());
    proof = Expr::app(proof, rhs.clone());
    proof = Expr::app(proof, rhs_proof);
    proof
}

pub(super) fn mk_or_rec(
    lhs: &Expr,
    rhs: &Expr,
    target: &Expr,
    branch_lhs: Expr,
    branch_rhs: Expr,
    disj: Expr,
) -> Expr {
    let or_type = super::make_or(lhs, rhs);
    let motive = Expr::lam(BinderInfo::Default, or_type, target.lift(1));
    let mut proof = Expr::const_(Name::from_string("Or.rec"), vec![]);
    proof = Expr::app(proof, lhs.clone());
    proof = Expr::app(proof, rhs.clone());
    proof = Expr::app(proof, motive);
    proof = Expr::app(proof, branch_lhs);
    proof = Expr::app(proof, branch_rhs);
    proof = Expr::app(proof, disj);
    proof
}

pub(super) fn mk_iff_intro(lhs: &Expr, rhs: &Expr, forward: Expr, backward: Expr) -> Expr {
    let mut proof = Expr::const_(Name::from_string("Iff.intro"), vec![]);
    proof = Expr::app(proof, lhs.clone());
    proof = Expr::app(proof, rhs.clone());
    proof = Expr::app(proof, forward);
    proof = Expr::app(proof, backward);
    proof
}

pub(super) fn mk_prop_eq_from_iff(lhs: &Expr, rhs: &Expr, iff_proof: Expr) -> Expr {
    // `propext : {a b : Prop} → (a ↔ b) → a = b` takes the `Iff` proof directly.
    // Apply it to the two (implicit) Prop arguments and then the `iff_proof`.
    //
    // Previously this extracted `Iff.mp`/`Iff.mpr` and applied `propext` to four
    // arguments as if its signature were `(a → b) → (b → a) → a = b`. Clean's
    // `propext` is the faithful `Iff`-shaped axiom (see
    // `clean-kernel/src/env/logic.rs::init_propext`), so the fourth application
    // hit an already-`Eq`-typed term and the kernel rejected it (`NotAFunction`).
    let mut proof = Expr::const_(Name::from_string("propext"), vec![]);
    proof = Expr::app(proof, lhs.clone());
    proof = Expr::app(proof, rhs.clone());
    proof = Expr::app(proof, iff_proof);
    proof
}

fn mk_eq_mp(lhs: &Expr, rhs: &Expr, eq_proof: Expr, value: Expr) -> Expr {
    let mut proof = Expr::const_(Name::from_string("Eq.mp"), vec![Level::zero()]);
    proof = Expr::app(proof, lhs.clone());
    proof = Expr::app(proof, rhs.clone());
    proof = Expr::app(proof, eq_proof);
    proof = Expr::app(proof, value);
    proof
}

fn mk_eq_mpr(lhs: &Expr, rhs: &Expr, eq_proof: Expr, value: Expr) -> Expr {
    let mut proof = Expr::const_(Name::from_string("Eq.mpr"), vec![Level::zero()]);
    proof = Expr::app(proof, lhs.clone());
    proof = Expr::app(proof, rhs.clone());
    proof = Expr::app(proof, eq_proof);
    proof = Expr::app(proof, value);
    proof
}

pub(super) fn mk_by_contradiction<F>(state: &mut ProofState, prop: &Expr, body_builder: F) -> Expr
where
    F: FnOnce(&mut ProofState, Expr) -> Expr,
{
    let body = mk_lambda(state, &make_not(prop), body_builder);
    let mut proof = Expr::const_(Name::from_string("Classical.byContradiction"), vec![]);
    proof = Expr::app(proof, prop.clone());
    proof = Expr::app(proof, body);
    proof
}

fn get_sort_level(
    state: &ProofState,
    goal: &Goal,
    ty: &Expr,
    context: &str,
) -> Result<Level, TacticError> {
    let sort = state.infer_type(goal, ty).map_err(|_| {
        TacticError::TypeCheckFailed(format!(
            "push_neg: failed to infer universe level for {context}"
        ))
    })?;
    match sort.kind() {
        ExprKind::Sort(level) => Ok(level.clone()),
        _ => Err(TacticError::TypeCheckFailed(format!(
            "push_neg: expected {context} to have a sort type"
        ))),
    }
}

pub(super) fn mk_exists_intro(
    state: &ProofState,
    goal: &Goal,
    ty: &Expr,
    pred: &Expr,
    witness: Expr,
    witness_proof: Expr,
) -> Result<Expr, TacticError> {
    let level = get_sort_level(state, goal, ty, "Exists witness type")?;
    let mut proof = Expr::const_(Name::from_string("Exists.intro"), vec![level]);
    proof = Expr::app(proof, ty.clone());
    proof = Expr::app(proof, pred.clone());
    proof = Expr::app(proof, witness);
    proof = Expr::app(proof, witness_proof);
    Ok(proof)
}

pub(super) fn mk_exists_elim(
    state: &ProofState,
    goal: &Goal,
    ty: &Expr,
    pred: &Expr,
    target: &Expr,
    exists_proof: Expr,
    continuation: Expr,
) -> Result<Expr, TacticError> {
    let level = get_sort_level(state, goal, ty, "Exists elimination domain")?;
    let mut proof = Expr::const_(Name::from_string("Exists.elim"), vec![level]);
    proof = Expr::app(proof, ty.clone());
    proof = Expr::app(proof, pred.clone());
    proof = Expr::app(proof, target.clone());
    proof = Expr::app(proof, exists_proof);
    proof = Expr::app(proof, continuation);
    Ok(proof)
}

pub(super) fn mk_push_neg_forall_congr(
    state: &mut ProofState,
    ty: &Expr,
    body_old: &Expr,
    body_new: &Expr,
    body_eq: &Expr,
) -> Result<Expr, TacticError> {
    require_consts(state, &["propext", "Eq.mp", "Eq.mpr"])?;

    let pi_old = Expr::pi(BinderInfo::Default, ty.clone(), body_old.clone());
    let pi_new = Expr::pi(BinderInfo::Default, ty.clone(), body_new.clone());

    let forward = mk_lambda(state, &pi_old, |state, hforall| {
        mk_lambda(state, ty, |_, x| {
            let body_eq_x = body_eq.clone().instantiate(&x);
            let body_old_x = body_old.clone().instantiate(&x);
            let body_new_x = body_new.clone().instantiate(&x);
            mk_eq_mp(
                &body_old_x,
                &body_new_x,
                body_eq_x,
                Expr::app(hforall.clone(), x),
            )
        })
    });

    let backward = mk_lambda(state, &pi_new, |state, hforall| {
        mk_lambda(state, ty, |_, x| {
            let body_eq_x = body_eq.clone().instantiate(&x);
            let body_old_x = body_old.clone().instantiate(&x);
            let body_new_x = body_new.clone().instantiate(&x);
            mk_eq_mpr(
                &body_old_x,
                &body_new_x,
                body_eq_x,
                Expr::app(hforall.clone(), x),
            )
        })
    });

    let iff_proof = mk_iff_intro(&pi_old, &pi_new, forward, backward);
    Ok(mk_prop_eq_from_iff(&pi_old, &pi_new, iff_proof))
}

pub(super) fn is_nat_type(ty: &Expr) -> bool {
    matches!(ty.kind(), ExprKind::Const(name, _) if name.to_string() == "Nat")
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::name::Name;
    use clean_kernel::{BinderInfo, Expr};

    fn mk_prop(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), vec![])
    }

    #[test]
    fn test_mk_or_rec_lifts_target_bvars_under_motive() {
        let lhs = mk_prop("P");
        let rhs = mk_prop("Q");
        // Target contains bvar(0) — simulates a goal built under an outer binder.
        let target = Expr::app(mk_prop("Goal"), Expr::bvar(0));

        let branch_lhs = mk_prop("branch_l");
        let branch_rhs = mk_prop("branch_r");
        let disj = mk_prop("h_or");

        let result = mk_or_rec(&lhs, &rhs, &target, branch_lhs, branch_rhs, disj);

        // The motive lambda is the 3rd argument (index 2) of Or.rec.
        // It should be: fun (_ : Or P Q) => target.lift(1)
        // i.e. bvar(0) in target becomes bvar(1) under the new binder.
        let or_type = Expr::app(Expr::app(mk_prop("Or"), lhs.clone()), rhs.clone());
        let expected_motive = Expr::lam(BinderInfo::Default, or_type, target.lift(1));

        // Walk the application spine to extract the motive (3rd arg after Or.rec).
        // Or.rec P Q motive branch_l branch_r disj
        //   ^0   ^1 ^2   ^3       ^4      ^5
        let mut spine = Vec::new();
        let mut cur = &result;
        while let ExprKind::App(f, a) = cur.kind() {
            spine.push(a.clone());
            cur = f;
        }
        spine.reverse();
        assert!(
            spine.len() >= 3,
            "Or.rec application spine too short: {spine:?}"
        );
        assert_eq!(*spine[2], expected_motive, "motive should lift target by 1");
    }
}
