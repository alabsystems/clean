// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr};

use super::super::{Goal, ProofState, TacticError};
use super::proof_utils::{
    mk_and_intro, mk_and_left, mk_and_right, mk_by_contradiction, mk_exists_elim, mk_exists_intro,
    mk_false_elim, mk_iff_intro, mk_lambda, mk_or_inl, mk_or_inr, mk_or_rec, mk_prop_eq_from_iff,
    require_consts,
};
use super::{make_and, make_exists_push_neg, make_forall_push_neg, make_not, make_or};

pub(super) fn mk_not_not_eq(state: &mut ProofState, p: &Expr) -> Result<Expr, TacticError> {
    require_consts(
        state,
        &[
            "Classical.byContradiction",
            "Iff.intro",
            "Iff.mp",
            "Iff.mpr",
            "propext",
        ],
    )?;

    let lhs = make_not(&make_not(p));
    let forward = mk_lambda(state, &lhs, |state, h| {
        mk_by_contradiction(state, p, |_, not_p| Expr::app(h.clone(), not_p))
    });
    let backward = mk_lambda(state, p, |state, hp| {
        mk_lambda(state, &make_not(p), |_, not_p| Expr::app(not_p, hp.clone()))
    });
    Ok(mk_prop_eq_from_iff(
        &lhs,
        p,
        mk_iff_intro(&lhs, p, forward, backward),
    ))
}

pub(super) fn mk_not_and_eq(
    state: &mut ProofState,
    p: &Expr,
    q: &Expr,
) -> Result<Expr, TacticError> {
    require_consts(
        state,
        &[
            "And.intro",
            "And.left",
            "And.right",
            "Classical.em",
            "Iff.intro",
            "Iff.mp",
            "Iff.mpr",
            "Or.inl",
            "Or.inr",
            "Or.rec",
            "propext",
        ],
    )?;

    let and_pq = make_and(p, q);
    let lhs = make_not(&and_pq);
    let not_p = make_not(p);
    let not_q = make_not(q);
    let rhs = make_or(&not_p, &not_q);

    let forward = mk_lambda(state, &lhs, |state, h| {
        let em_p = Expr::app(
            Expr::const_(Name::from_string("Classical.em"), vec![]),
            p.clone(),
        );
        let branch_p = mk_lambda(state, p, |state, hp| {
            let not_q_proof = mk_lambda(state, q, |_, hq| {
                let and_proof = mk_and_intro(p, q, hp.clone(), hq);
                Expr::app(h.clone(), and_proof)
            });
            mk_or_inr(&not_p, &not_q, not_q_proof)
        });
        let branch_not_p = mk_lambda(state, &not_p, |_, hnot_p| mk_or_inl(&not_p, &not_q, hnot_p));
        mk_or_rec(p, &not_p, &rhs, branch_p, branch_not_p, em_p)
    });

    let backward = mk_lambda(state, &rhs, |state, hor| {
        mk_lambda(state, &and_pq, |state, hpq| {
            let left_branch = mk_lambda(state, &not_p, |_, hnot_p| {
                Expr::app(hnot_p, mk_and_left(p, q, hpq.clone()))
            });
            let right_branch = mk_lambda(state, &not_q, |_, hnot_q| {
                Expr::app(hnot_q, mk_and_right(p, q, hpq.clone()))
            });
            mk_or_rec(
                &not_p,
                &not_q,
                &Expr::const_(Name::from_string("False"), vec![]),
                left_branch,
                right_branch,
                hor.clone(),
            )
        })
    });

    Ok(mk_prop_eq_from_iff(
        &lhs,
        &rhs,
        mk_iff_intro(&lhs, &rhs, forward, backward),
    ))
}

pub(super) fn mk_not_or_eq(
    state: &mut ProofState,
    p: &Expr,
    q: &Expr,
) -> Result<Expr, TacticError> {
    require_consts(
        state,
        &[
            "And.intro",
            "And.left",
            "And.right",
            "Iff.intro",
            "Iff.mp",
            "Iff.mpr",
            "Or.inl",
            "Or.inr",
            "Or.rec",
            "propext",
        ],
    )?;

    let or_pq = make_or(p, q);
    let lhs = make_not(&or_pq);
    let not_p = make_not(p);
    let not_q = make_not(q);
    let rhs = make_and(&not_p, &not_q);

    let forward = mk_lambda(state, &lhs, |state, h| {
        let not_p_proof = mk_lambda(state, p, |_, hp| Expr::app(h.clone(), mk_or_inl(p, q, hp)));
        let not_q_proof = mk_lambda(state, q, |_, hq| Expr::app(h.clone(), mk_or_inr(p, q, hq)));
        mk_and_intro(&not_p, &not_q, not_p_proof, not_q_proof)
    });

    let backward = mk_lambda(state, &rhs, |state, hand| {
        let not_p_proof = mk_and_left(&not_p, &not_q, hand.clone());
        let not_q_proof = mk_and_right(&not_p, &not_q, hand);
        mk_lambda(state, &or_pq, |state, hor| {
            let branch_p = mk_lambda(state, p, |_, hp| Expr::app(not_p_proof.clone(), hp));
            let branch_q = mk_lambda(state, q, |_, hq| Expr::app(not_q_proof.clone(), hq));
            mk_or_rec(
                p,
                q,
                &Expr::const_(Name::from_string("False"), vec![]),
                branch_p,
                branch_q,
                hor,
            )
        })
    });

    Ok(mk_prop_eq_from_iff(
        &lhs,
        &rhs,
        mk_iff_intro(&lhs, &rhs, forward, backward),
    ))
}

pub(super) fn mk_not_imp_eq(
    state: &mut ProofState,
    p: &Expr,
    q: &Expr,
) -> Result<Expr, TacticError> {
    require_consts(
        state,
        &[
            "And.intro",
            "And.left",
            "And.right",
            "Classical.byContradiction",
            "False.elim",
            "Iff.intro",
            "Iff.mp",
            "Iff.mpr",
            "propext",
        ],
    )?;

    let implication = Expr::arrow(p.clone(), q.clone());
    let lhs = make_not(&implication);
    let not_q = make_not(q);
    let rhs = make_and(p, &not_q);

    let forward = mk_lambda(state, &lhs, |state, h| {
        let p_proof = mk_by_contradiction(state, p, |state, not_p| {
            let imp_proof = mk_lambda(state, p, |_, hp| {
                mk_false_elim(q, Expr::app(not_p.clone(), hp))
            });
            Expr::app(h.clone(), imp_proof)
        });
        let not_q_proof = mk_lambda(state, q, |state, hq| {
            let imp_proof = mk_lambda(state, p, |_, _| hq.clone());
            Expr::app(h.clone(), imp_proof)
        });
        mk_and_intro(p, &not_q, p_proof, not_q_proof)
    });

    let backward = mk_lambda(state, &rhs, |state, hand| {
        let p_proof = mk_and_left(p, &not_q, hand.clone());
        let not_q_proof = mk_and_right(p, &not_q, hand);
        mk_lambda(state, &implication, |_, hpq| {
            Expr::app(not_q_proof.clone(), Expr::app(hpq, p_proof.clone()))
        })
    });

    Ok(mk_prop_eq_from_iff(
        &lhs,
        &rhs,
        mk_iff_intro(&lhs, &rhs, forward, backward),
    ))
}

pub(super) fn mk_not_forall_eq(
    state: &mut ProofState,
    goal: &Goal,
    ty: &Expr,
    body: &Expr,
) -> Result<Expr, TacticError> {
    require_consts(
        state,
        &[
            "Classical.byContradiction",
            "Exists.intro",
            "Exists.elim",
            "Iff.intro",
            "Iff.mp",
            "Iff.mpr",
            "propext",
        ],
    )?;

    let lhs = make_not(&make_forall_push_neg(ty, body));
    let not_body = make_not(body);
    let rhs = make_exists_push_neg(ty, &not_body, state);
    let pred_not = Expr::lam(BinderInfo::Default, ty.clone(), not_body.clone());

    let forward = mk_lambda(state, &lhs, |state, h| {
        mk_by_contradiction(state, &rhs, |state, hnot_rhs| {
            let forall_proof = mk_lambda(state, ty, |state, x| {
                let body_x = body.clone().instantiate(&x);
                let hnot_body_id = state.fresh_fvar();
                let hnot_body = Expr::fvar(hnot_body_id);
                let exists_intro =
                    mk_exists_intro(state, goal, ty, &pred_not, x.clone(), hnot_body.clone())
                        .expect("push_neg: Exists.intro should build under validated environment");
                let contradiction =
                    Expr::app(hnot_rhs.clone(), exists_intro).abstract_fvar(hnot_body_id);
                let not_body_lambda =
                    Expr::lam(BinderInfo::Default, make_not(&body_x), contradiction);
                let mut proof =
                    Expr::const_(Name::from_string("Classical.byContradiction"), vec![]);
                proof = Expr::app(proof, body_x);
                Expr::app(proof, not_body_lambda)
            });
            Expr::app(h.clone(), forall_proof)
        })
    });

    let backward = mk_lambda(state, &rhs, |state, hex| {
        mk_lambda(state, &make_forall_push_neg(ty, body), |state, hforall| {
            let continuation = mk_lambda(state, ty, |state, x| {
                let not_body_x = not_body.clone().instantiate(&x);
                mk_lambda(state, &not_body_x, |_, hnot_body| {
                    Expr::app(hnot_body, Expr::app(hforall.clone(), x.clone()))
                })
            });
            mk_exists_elim(
                state,
                goal,
                ty,
                &pred_not,
                &Expr::const_(Name::from_string("False"), vec![]),
                hex.clone(),
                continuation,
            )
            .expect("push_neg: Exists.elim should build under validated environment")
        })
    });

    Ok(mk_prop_eq_from_iff(
        &lhs,
        &rhs,
        mk_iff_intro(&lhs, &rhs, forward, backward),
    ))
}

pub(super) fn mk_not_exists_eq(
    state: &mut ProofState,
    goal: &Goal,
    ty: &Expr,
    body: &Expr,
) -> Result<Expr, TacticError> {
    require_consts(
        state,
        &[
            "Exists.intro",
            "Exists.elim",
            "Iff.intro",
            "Iff.mp",
            "Iff.mpr",
            "propext",
        ],
    )?;

    let pred = Expr::lam(BinderInfo::Default, ty.clone(), body.clone());
    let exists_body = make_exists_push_neg(ty, body, state);
    let lhs = make_not(&exists_body);
    let not_body = make_not(body);
    let rhs = make_forall_push_neg(ty, &not_body);

    let forward = mk_lambda(state, &lhs, |state, h| {
        mk_lambda(state, ty, |state, x| {
            let body_x = body.clone().instantiate(&x);
            let hx_id = state.fresh_fvar();
            let hx = Expr::fvar(hx_id);
            let exists_intro = mk_exists_intro(state, goal, ty, &pred, x.clone(), hx)
                .expect("push_neg: Exists.intro should build under validated environment");
            let body = Expr::app(h.clone(), exists_intro).abstract_fvar(hx_id);
            Expr::lam(BinderInfo::Default, body_x, body)
        })
    });

    let backward = mk_lambda(state, &rhs, |state, hforall| {
        mk_lambda(state, &exists_body, |state, hex| {
            let continuation = mk_lambda(state, ty, |state, x| {
                let body_x = body.clone().instantiate(&x);
                mk_lambda(state, &body_x, |_, hx| {
                    Expr::app(Expr::app(hforall.clone(), x.clone()), hx)
                })
            });
            mk_exists_elim(
                state,
                goal,
                ty,
                &pred,
                &Expr::const_(Name::from_string("False"), vec![]),
                hex,
                continuation,
            )
            .expect("push_neg: Exists.elim should build under validated environment")
        })
    });

    Ok(mk_prop_eq_from_iff(
        &lhs,
        &rhs,
        mk_iff_intro(&lhs, &rhs, forward, backward),
    ))
}

pub(super) fn mk_nat_not_le_eq(
    state: &mut ProofState,
    lhs: &Expr,
    rhs: &Expr,
) -> Result<Expr, TacticError> {
    require_consts(state, &["Nat.not_le", "Iff.mp", "Iff.mpr", "propext"])?;
    let old = make_not(&super::super::tc_app::nat_le_tc(lhs.clone(), rhs.clone()));
    let new = super::super::tc_app::nat_lt_tc(rhs.clone(), lhs.clone());
    let iff = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.not_le"), vec![]),
            lhs.clone(),
        ),
        rhs.clone(),
    );
    Ok(mk_prop_eq_from_iff(&old, &new, iff))
}

pub(super) fn mk_nat_not_lt_eq(
    state: &mut ProofState,
    lhs: &Expr,
    rhs: &Expr,
) -> Result<Expr, TacticError> {
    require_consts(state, &["Nat.not_lt", "Iff.mp", "Iff.mpr", "propext"])?;
    let old = make_not(&super::super::tc_app::nat_lt_tc(lhs.clone(), rhs.clone()));
    let new = super::super::tc_app::nat_le_tc(rhs.clone(), lhs.clone());
    let iff = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.not_lt"), vec![]),
            lhs.clone(),
        ),
        rhs.clone(),
    );
    Ok(mk_prop_eq_from_iff(&old, &new, iff))
}

/// Prove `¬(a ≥ b) = (a < b)` for Nat.
///
/// `a ≥ b` (`GE.ge a b`) is definitionally `b ≤ a` (`LE.le b a`), so this reuses
/// `Nat.not_le b a : ¬(b ≤ a) ↔ a < b`. The `old` proposition is built with the
/// *surface* `GE.ge` head so the resulting `Eq` LHS matches the actual hypothesis
/// / goal type syntactically; the kernel accepts the `propext` application up to
/// the `GE.ge ⟶ LE.le` delta reduction.
pub(super) fn mk_nat_not_ge_eq(
    state: &mut ProofState,
    lhs: &Expr,
    rhs: &Expr,
) -> Result<Expr, TacticError> {
    require_consts(state, &["Nat.not_le", "Iff.mp", "Iff.mpr", "propext"])?;
    let old = make_not(&super::super::tc_app::nat_ge_tc(lhs.clone(), rhs.clone()));
    let new = super::super::tc_app::nat_lt_tc(lhs.clone(), rhs.clone());
    // Nat.not_le (b) (a) : ¬(b ≤ a) ↔ a < b, with b = rhs, a = lhs.
    let iff = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.not_le"), vec![]),
            rhs.clone(),
        ),
        lhs.clone(),
    );
    Ok(mk_prop_eq_from_iff(&old, &new, iff))
}

/// Prove `¬(a > b) = (a ≤ b)` for Nat.
///
/// `a > b` (`GT.gt a b`) is definitionally `b < a` (`LT.lt b a`), so this reuses
/// `Nat.not_lt b a : ¬(b < a) ↔ a ≤ b`. As in [`mk_nat_not_ge_eq`], the `old`
/// side keeps the surface `GT.gt` head and the kernel discharges the delta gap.
pub(super) fn mk_nat_not_gt_eq(
    state: &mut ProofState,
    lhs: &Expr,
    rhs: &Expr,
) -> Result<Expr, TacticError> {
    require_consts(state, &["Nat.not_lt", "Iff.mp", "Iff.mpr", "propext"])?;
    let old = make_not(&super::super::tc_app::nat_gt_tc(lhs.clone(), rhs.clone()));
    let new = super::super::tc_app::nat_le_tc(lhs.clone(), rhs.clone());
    // Nat.not_lt (b) (a) : ¬(b < a) ↔ a ≤ b, with b = rhs, a = lhs.
    let iff = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.not_lt"), vec![]),
            rhs.clone(),
        ),
        lhs.clone(),
    );
    Ok(mk_prop_eq_from_iff(&old, &new, iff))
}
