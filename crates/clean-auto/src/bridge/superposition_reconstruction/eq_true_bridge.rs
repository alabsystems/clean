// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bridge helpers between raw propositions and the clausifier's `P = True` encoding.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};

use crate::bridge::disjunction::{
    mk_and_intro, mk_and_left, mk_and_right, mk_propext, mk_true_intro,
};
use crate::bridge::eq_proof_builders::mk_eq_mpr;

use super::proof_helpers::mk_negation;
use super::{ReconstructionError, ReconstructionResult, SuperpositionReconstructor};

impl SuperpositionReconstructor<'_> {
    fn mk_binary_prop(name: &str, left: &Expr, right: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string(name), vec![]), left.clone()),
            right.clone(),
        )
    }

    fn mk_eq_true_prop(prop: &Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    Expr::prop(),
                ),
                prop.clone(),
            ),
            Expr::const_(Name::from_string("True"), vec![]),
        )
    }

    fn mk_or_prop(left: &Expr, right: &Expr) -> Expr {
        Self::mk_binary_prop("Or", left, right)
    }

    fn match_binary_prop(expr: &Expr, expected_name: &str) -> Option<(Expr, Expr)> {
        let args = expr.get_app_args();
        if args.len() != 2 {
            return None;
        }
        let head = expr.get_app_fn();
        match head.kind() {
            ExprKind::Const(name, levels)
                if *name == Name::from_string(expected_name) && levels.is_empty() =>
            {
                Some((args[0].clone(), args[1].clone()))
            }
            _ => None,
        }
    }

    fn match_or(expr: &Expr) -> Option<(Expr, Expr)> {
        Self::match_binary_prop(expr, "Or")
    }

    fn match_and(expr: &Expr) -> Option<(Expr, Expr)> {
        Self::match_binary_prop(expr, "And")
    }

    fn match_not(expr: &Expr) -> Option<Expr> {
        let args = expr.get_app_args();
        if args.len() != 1 {
            return None;
        }
        let head = expr.get_app_fn();
        match head.kind() {
            ExprKind::Const(name, _) if *name == Name::from_string("Not") => Some(args[0].clone()),
            _ => None,
        }
    }

    fn match_negated_prop(expr: &Expr) -> Option<Expr> {
        if let Some(inner) = Self::match_not(expr) {
            return Some(inner);
        }

        match expr.kind() {
            ExprKind::Pi(_, domain, body)
                if matches!(
                    body.kind(),
                    ExprKind::Const(name, _) if *name == Name::from_string("False")
                ) =>
            {
                Some(domain.as_ref().clone())
            }
            _ => None,
        }
    }

    fn match_eq_true_prop(expr: &Expr) -> Option<Expr> {
        let args = expr.get_app_args();
        if args.len() != 3 {
            return None;
        }
        let head = expr.get_app_fn();
        match head.kind() {
            ExprKind::Const(name, _) if *name == Name::from_string("Eq") => {}
            _ => return None,
        }

        if *args[0] != Expr::prop() {
            return None;
        }
        if *args[2] != Expr::const_(Name::from_string("True"), vec![]) {
            return None;
        }

        Some(args[1].clone())
    }

    fn mk_by_contradiction(prop: &Expr, neg_prop_proof: &Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Classical.byContradiction"), vec![]),
                prop.clone(),
            ),
            neg_prop_proof.clone(),
        )
    }

    fn mk_not_eq_true_from_not(prop: &Expr, h_not_p: &Expr) -> Expr {
        let h_eq_true_id = FVarId::new(u64::MAX - 32);
        let h_eq_true = Expr::fvar(h_eq_true_id);
        let body = Expr::app(h_not_p.clone(), Self::of_eq_true(prop, &h_eq_true));
        Expr::lam(
            BinderInfo::Default,
            Self::mk_eq_true_prop(prop),
            body.abstract_fvar(h_eq_true_id),
        )
    }

    fn of_not_not(prop: &Expr, h_not_not_p: &Expr) -> Expr {
        let h_not_p_id = FVarId::new(u64::MAX - 33);
        let body = Expr::app(h_not_not_p.clone(), Expr::fvar(h_not_p_id));
        let witness = Expr::lam(
            BinderInfo::Default,
            mk_negation(prop),
            body.abstract_fvar(h_not_p_id),
        );
        Self::mk_by_contradiction(prop, &witness)
    }

    fn mk_not_of_not_or(left: &Expr, right: &Expr, h_not_or: &Expr, use_left: bool) -> Expr {
        let h_branch_id = FVarId::new(if use_left {
            u64::MAX - 34
        } else {
            u64::MAX - 35
        });
        let branch = if use_left {
            Self::mk_or_inl(left, right, &Expr::fvar(h_branch_id))
        } else {
            Self::mk_or_inr(left, right, &Expr::fvar(h_branch_id))
        };
        let body = Expr::app(h_not_or.clone(), branch);
        Expr::lam(
            BinderInfo::Default,
            if use_left {
                left.clone()
            } else {
                right.clone()
            },
            body.abstract_fvar(h_branch_id),
        )
    }

    fn mk_or_from_not_and(left: &Expr, right: &Expr, h_not_and: &Expr) -> Expr {
        let not_left = mk_negation(left);
        let not_right = mk_negation(right);
        let target = Self::mk_or_prop(&not_left, &not_right);
        let h_not_or_id = FVarId::new(u64::MAX - 36);
        let h_not_or = Expr::fvar(h_not_or_id);

        let left_proof = Self::of_not_not(
            left,
            &Self::mk_not_of_not_or(&not_left, &not_right, &h_not_or, true),
        );
        let right_proof = Self::of_not_not(
            right,
            &Self::mk_not_of_not_or(&not_left, &not_right, &h_not_or, false),
        );
        let body = Expr::app(
            h_not_and.clone(),
            mk_and_intro(left, right, &left_proof, &right_proof),
        );
        let witness = Expr::lam(
            BinderInfo::Default,
            mk_negation(&target),
            body.abstract_fvar(h_not_or_id),
        );
        Self::mk_by_contradiction(&target, &witness)
    }

    fn bridge_or(
        raw_left: &Expr,
        raw_right: &Expr,
        raw_proof: &Expr,
        clause_left: &Expr,
        clause_right: &Expr,
    ) -> Option<Expr> {
        let result_prop = Self::mk_or_prop(clause_left, clause_right);
        let left_branch =
            Self::bridge_raw_prop_proof_to_clause_prop(raw_left, &Expr::bvar(0), clause_left)?;
        let right_branch =
            Self::bridge_raw_prop_proof_to_clause_prop(raw_right, &Expr::bvar(0), clause_right)?;
        let f_inl = Expr::lam(
            BinderInfo::Default,
            raw_left.clone(),
            Self::mk_or_inl(clause_left, clause_right, &left_branch),
        );
        let f_inr = Expr::lam(
            BinderInfo::Default,
            raw_right.clone(),
            Self::mk_or_inr(clause_left, clause_right, &right_branch),
        );
        let motive = Self::mk_constant_or_motive(raw_left, raw_right, &result_prop);
        Some(Self::mk_or_rec(
            raw_left, raw_right, &motive, &f_inl, &f_inr, raw_proof,
        ))
    }

    fn bridge_and(
        raw_left: &Expr,
        raw_right: &Expr,
        raw_proof: &Expr,
        clause_prop: &Expr,
    ) -> Option<Expr> {
        let left_proof = mk_and_left(raw_proof);
        if let Some(bridged) =
            Self::bridge_raw_prop_proof_to_clause_prop(raw_left, &left_proof, clause_prop)
        {
            return Some(bridged);
        }

        let right_proof = mk_and_right(raw_proof);
        Self::bridge_raw_prop_proof_to_clause_prop(raw_right, &right_proof, clause_prop)
    }

    pub(super) fn eq_true_intro(prop: &Expr, hp: &Expr) -> Expr {
        let true_expr = Expr::const_(Name::from_string("True"), vec![]);
        let mp = Expr::lam(BinderInfo::Default, prop.clone(), mk_true_intro());
        let mpr = Expr::lam(BinderInfo::Default, true_expr.clone(), hp.clone());
        mk_propext(prop, &true_expr, &mp, &mpr)
    }

    pub(super) fn of_eq_true(prop: &Expr, h_eq_true: &Expr) -> Expr {
        let true_expr = Expr::const_(Name::from_string("True"), vec![]);
        mk_eq_mpr(
            &Level::zero(),
            prop,
            &true_expr,
            h_eq_true,
            &mk_true_intro(),
        )
    }

    pub(super) fn bridge_raw_prop_proof_to_clause_prop(
        raw_prop: &Expr,
        raw_proof: &Expr,
        clause_prop: &Expr,
    ) -> Option<Expr> {
        if raw_prop == clause_prop {
            return Some(raw_proof.clone());
        }

        if let Some(prop) = Self::match_eq_true_prop(clause_prop) {
            if raw_prop == &prop {
                return Some(Self::eq_true_intro(&prop, raw_proof));
            }
        }

        if let (Some((raw_left, raw_right)), Some((clause_left, clause_right))) =
            (Self::match_or(raw_prop), Self::match_or(clause_prop))
        {
            return Self::bridge_or(
                &raw_left,
                &raw_right,
                raw_proof,
                &clause_left,
                &clause_right,
            );
        }

        if let Some((raw_left, raw_right)) = Self::match_and(raw_prop) {
            if let Some(bridged) = Self::bridge_and(&raw_left, &raw_right, raw_proof, clause_prop) {
                return Some(bridged);
            }
        }

        // Bridge Pi(_, P, False) to Not(P) — definitionally equal in Lean 4
        // but structurally different. Covers equational goals where mk_negation
        // produces Pi form but clause_to_prop produces Not form.
        if let (Some(raw_inner), Some(clause_inner)) = (
            Self::match_negated_prop(raw_prop),
            Self::match_not(clause_prop),
        ) {
            if raw_inner == clause_inner {
                return Some(raw_proof.clone());
            }
            if let Some(eq_true_inner) = Self::match_eq_true_prop(&clause_inner) {
                if raw_inner == eq_true_inner {
                    return Some(Self::mk_not_eq_true_from_not(&eq_true_inner, raw_proof));
                }
            }
        }

        if let Some(raw_inner) = Self::match_negated_prop(raw_prop) {
            if let Some(inner) = Self::match_negated_prop(&raw_inner) {
                let inner_proof = Self::of_not_not(&inner, raw_proof);
                if let Some(bridged) =
                    Self::bridge_raw_prop_proof_to_clause_prop(&inner, &inner_proof, clause_prop)
                {
                    return Some(bridged);
                }
            }

            if let Some((left, right)) = Self::match_and(&raw_inner) {
                let raw_or_prop = Self::mk_or_prop(&mk_negation(&left), &mk_negation(&right));
                let raw_or_proof = Self::mk_or_from_not_and(&left, &right, raw_proof);
                if let Some(bridged) = Self::bridge_raw_prop_proof_to_clause_prop(
                    &raw_or_prop,
                    &raw_or_proof,
                    clause_prop,
                ) {
                    return Some(bridged);
                }
            }

            if let Some((left, right)) = Self::match_or(&raw_inner) {
                let not_left = mk_negation(&left);
                let not_left_proof = Self::mk_not_of_not_or(&left, &right, raw_proof, true);
                if let Some(bridged) = Self::bridge_raw_prop_proof_to_clause_prop(
                    &not_left,
                    &not_left_proof,
                    clause_prop,
                ) {
                    return Some(bridged);
                }

                let not_right = mk_negation(&right);
                let not_right_proof = Self::mk_not_of_not_or(&left, &right, raw_proof, false);
                if let Some(bridged) = Self::bridge_raw_prop_proof_to_clause_prop(
                    &not_right,
                    &not_right_proof,
                    clause_prop,
                ) {
                    return Some(bridged);
                }
            }
        }

        None
    }

    pub(super) fn bridge_raw_prop_proof_to_clause_id(
        &self,
        raw_prop: &Expr,
        raw_proof: &Expr,
        clause_id: u64,
        context: &str,
    ) -> ReconstructionResult<Expr> {
        let clause = self
            .clause_map
            .get(&clause_id)
            .ok_or(ReconstructionError::MissingClause(clause_id))?;
        let clause_prop = self.clause_to_prop(clause)?;
        Self::bridge_raw_prop_proof_to_clause_prop(raw_prop, raw_proof, &clause_prop).ok_or_else(
            || {
                ReconstructionError::UnsupportedInference(format!(
                    "{context}: cannot bridge raw proposition {raw_prop:?} to clause proposition \
                     {clause_prop:?} for clause {clause_id}"
                ))
            },
        )
    }

    pub(super) fn build_single_clause_body(
        &self,
        mut false_proof: Expr,
        goal: &Expr,
        fvar_base: u64,
    ) -> ReconstructionResult<Expr> {
        let h_fvar_id = FVarId::new(u64::MAX - 8);
        let raw_neg_goal = mk_negation(goal);
        let clause_proof = self.bridge_raw_prop_proof_to_clause_id(
            &raw_neg_goal,
            &Expr::fvar(h_fvar_id),
            0,
            "single-clause goal wrapper",
        )?;
        false_proof = false_proof.subst_fvar(FVarId::new(fvar_base), &clause_proof);
        Ok(false_proof.abstract_fvar(h_fvar_id))
    }
}

#[cfg(test)]
mod tests {
    use super::SuperpositionReconstructor;
    use clean_kernel::name::Name;
    use clean_kernel::{Expr, ExprKind, FVarId};

    fn prop(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), vec![])
    }

    fn mk_not(expr: &Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Not"), vec![]), expr.clone())
    }

    fn mk_or(left: &Expr, right: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Or"), vec![]), left.clone()),
            right.clone(),
        )
    }

    #[test]
    fn test_bridge_raw_prop_positive_to_eq_true_uses_propext() {
        let p = prop("P");
        let hp = Expr::fvar(FVarId::new(10));
        let clause_prop = SuperpositionReconstructor::mk_eq_true_prop(&p);

        let proof =
            SuperpositionReconstructor::bridge_raw_prop_proof_to_clause_prop(&p, &hp, &clause_prop)
                .expect("positive atomic bridge should succeed");

        let head = proof.get_app_fn();
        assert!(
            matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("propext")),
            "positive atomic bridge should build a propext proof, got {:?}",
            proof
        );
    }

    #[test]
    fn test_bridge_raw_prop_negative_to_not_eq_true_returns_lambda() {
        let p = prop("P");
        let hnp = Expr::fvar(FVarId::new(11));
        let clause_prop = mk_not(&SuperpositionReconstructor::mk_eq_true_prop(&p));

        let proof = SuperpositionReconstructor::bridge_raw_prop_proof_to_clause_prop(
            &mk_not(&p),
            &hnp,
            &clause_prop,
        )
        .expect("negative atomic bridge should succeed");

        assert!(
            matches!(proof.kind(), ExprKind::Lam(_, _, _)),
            "negative atomic bridge should build a lambda proof, got {:?}",
            proof
        );
    }

    #[test]
    fn test_bridge_raw_prop_or_to_or_eq_true_uses_or_rec() {
        let p = prop("P");
        let q = prop("Q");
        let hpq = Expr::fvar(FVarId::new(12));
        let clause_prop = mk_or(
            &SuperpositionReconstructor::mk_eq_true_prop(&p),
            &SuperpositionReconstructor::mk_eq_true_prop(&q),
        );

        let proof = SuperpositionReconstructor::bridge_raw_prop_proof_to_clause_prop(
            &mk_or(&p, &q),
            &hpq,
            &clause_prop,
        )
        .expect("Or bridge should succeed");

        let head = proof.get_app_fn();
        assert!(
            matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Or.rec")),
            "Or bridge should case split with Or.rec, got {:?}",
            proof
        );
    }
}
