// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Equivalence Tseitin clausification rule handlers for ay proof reconstruction.
//!
//! Reconstructs kernel proof terms for the 4 equiv Tseitin rules:
//! - `equiv_pos1`: `{¬(a = b), a, ¬b}`
//! - `equiv_pos2`: `{¬(a = b), ¬a, b}`
//! - `equiv_neg1`: `{(a = b), ¬a, ¬b}`
//! - `equiv_neg2`: `{(a = b), a, b}`
//!
//! Each produces a 3-literal tautology clause proven via nested `Classical.em`
//! case splits on the two propositional atoms `a` and `b`, then either:
//! - `Eq.mp` / `Eq.mpr` transport to derive a contradiction (EquivPos rules)
//! - `propext` + `Iff.intro` to construct the propositional equality (EquivNeg rules)
//!
//! Split from `tseitin.rs` for file size compliance (#302).

use ay_core::{ProofId, TermId};
use clean_kernel::{BinderInfo, Expr, Level};

use super::expr_builders;
use super::trace::RuleView;
use super::{ReconstructResult, ReconstructionContext, ReconstructionError};
use crate::bridge::disjunction;

impl<'a> ReconstructionContext<'a> {
    /// Reconstruct an equivalence Tseitin tautology clause.
    ///
    /// Dispatches to per-rule proof builders that use nested `Classical.em`
    /// case splits on the two propositional atoms to construct a kernel proof.
    pub(super) fn reconstruct_equiv_tautology(
        &mut self,
        rule: RuleView,
        clause: &[TermId],
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        if clause.len() != 3 {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: format!(
                    "equiv tautology clause must have 3 literals, got {}",
                    clause.len()
                ),
            });
        }
        let trace = self
            .trace
            .as_ref()
            .ok_or(ReconstructionError::ProofNotAvailable)?;

        // Extract the two atoms from the equality.
        // EquivPos: clause[0] = not(= a b), EquivNeg: clause[0] = (= a b)
        let (a_term, b_term) = match rule {
            RuleView::EquivPos1 | RuleView::EquivPos2 => {
                let inner = trace.as_not(clause[0]).ok_or_else(|| {
                    ReconstructionError::UnsupportedStep {
                        step_index: step_id.0,
                        description: "equiv_pos: first literal is not a negation".to_string(),
                    }
                })?;
                trace
                    .as_equality(inner)
                    .ok_or_else(|| ReconstructionError::UnsupportedStep {
                        step_index: step_id.0,
                        description: "equiv_pos: negated literal is not an equality".to_string(),
                    })?
            }
            RuleView::EquivNeg1 | RuleView::EquivNeg2 => {
                trace.as_equality(clause[0]).ok_or_else(|| {
                    ReconstructionError::UnsupportedStep {
                        step_index: step_id.0,
                        description: "equiv_neg: first literal is not an equality".to_string(),
                    }
                })?
            }
            _ => unreachable!("non-equiv rule in equiv reconstruction"),
        };

        // Translate clause props and atom props.
        let clause_props = self.translate_clause_props(clause)?;
        let a_prop = self.translate_term(a_term)?;
        let b_prop = self.translate_term(b_term)?;
        let clause_type = disjunction::or_chain_type(&clause_props);

        // Build the equality type: @Eq.{1} Prop a b
        let prop = Expr::sort(Level::zero());
        let eq_type = expr_builders::mk_eq(&prop, &a_prop, &b_prop);

        let proof = match rule {
            RuleView::EquivPos1 => {
                Self::build_equiv_pos1(&a_prop, &b_prop, &eq_type, &clause_props, &clause_type)
            }
            RuleView::EquivPos2 => {
                Self::build_equiv_pos2(&a_prop, &b_prop, &eq_type, &clause_props, &clause_type)
            }
            RuleView::EquivNeg1 => {
                Self::build_equiv_neg1(&a_prop, &b_prop, &clause_props, &clause_type)
            }
            RuleView::EquivNeg2 => {
                Self::build_equiv_neg2(&a_prop, &b_prop, &clause_props, &clause_type)
            }
            _ => unreachable!("non-equiv rule in equiv proof builder"),
        };

        Ok(proof)
    }

    /// EquivPos1: `{¬(a = b), a, ¬b}`
    ///
    /// Level 0 em on `a`:
    /// - inl (h_a): inject `a` at position 1 (shortcut)
    /// - inr (h_na): em on `b`:
    ///   - inl (h_b): build `¬(a=b)` via `Eq.mpr` contradiction, inject at 0
    ///   - inr (h_nb): inject `¬b` at position 2
    fn build_equiv_pos1(
        a: &Expr,
        b: &Expr,
        eq_type: &Expr,
        clause_props: &[Expr],
        clause_type: &Expr,
    ) -> Expr {
        let false_expr = Expr::const_(clean_kernel::name::Name::from_string("False"), vec![]);
        let not_a = Expr::pi(BinderInfo::Default, a.clone(), false_expr.clone());
        let not_b = Expr::pi(BinderInfo::Default, b.clone(), false_expr);

        let em_a = disjunction::mk_classical_em(a);
        let motive_a = disjunction::mk_constant_or_motive(a, &not_a, clause_type);

        // inl: h_a → inject a at position 1
        let f_inl_a = Expr::lam(
            BinderInfo::Default,
            a.clone(),
            disjunction::inject_into_or_chain(clause_props, 1, Expr::bvar(0)),
        );

        // inr: h_na → nested em on b
        let em_b = disjunction::mk_classical_em(b);
        let motive_b = disjunction::mk_constant_or_motive(b, &not_b, clause_type);

        // h_b case: build ¬(a=b) = lam (h_eq : Eq Prop a b) => h_na (Eq.mpr h_eq h_b)
        // de Bruijn: bvar(0) = h_eq, bvar(1) = h_b, bvar(2) = h_na
        let eq_mpr = expr_builders::mk_eq_mpr(&Level::zero(), a, b, &Expr::bvar(0), &Expr::bvar(1));
        let not_eq_proof = Expr::lam(
            BinderInfo::Default,
            eq_type.clone(),
            Expr::app(Expr::bvar(2), eq_mpr),
        );
        let f_inl_b = Expr::lam(
            BinderInfo::Default,
            b.clone(),
            disjunction::inject_into_or_chain(clause_props, 0, not_eq_proof),
        );

        // h_nb case: inject ¬b at position 2
        let f_inr_b = Expr::lam(
            BinderInfo::Default,
            not_b.clone(),
            disjunction::inject_into_or_chain(clause_props, 2, Expr::bvar(0)),
        );

        let inner = disjunction::mk_or_rec(b, &not_b, &motive_b, &f_inl_b, &f_inr_b, &em_b);
        let f_inr_a = Expr::lam(BinderInfo::Default, not_a.clone(), inner);

        disjunction::mk_or_rec(a, &not_a, &motive_a, &f_inl_a, &f_inr_a, &em_a)
    }

    /// EquivPos2: `{¬(a = b), ¬a, b}`
    ///
    /// Level 0 em on `a`:
    /// - inl (h_a): em on `b`:
    ///   - inl (h_b): inject `b` at position 2 (shortcut)
    ///   - inr (h_nb): build `¬(a=b)` via `Eq.mpr(Eq.symm(...))` contradiction, inject at 0
    /// - inr (h_na): inject `¬a` at position 1 (shortcut)
    fn build_equiv_pos2(
        a: &Expr,
        b: &Expr,
        eq_type: &Expr,
        clause_props: &[Expr],
        clause_type: &Expr,
    ) -> Expr {
        let false_expr = Expr::const_(clean_kernel::name::Name::from_string("False"), vec![]);
        let not_a = Expr::pi(BinderInfo::Default, a.clone(), false_expr.clone());
        let not_b = Expr::pi(BinderInfo::Default, b.clone(), false_expr);

        let em_a = disjunction::mk_classical_em(a);
        let motive_a = disjunction::mk_constant_or_motive(a, &not_a, clause_type);

        // inl: h_a → nested em on b
        let em_b = disjunction::mk_classical_em(b);
        let motive_b = disjunction::mk_constant_or_motive(b, &not_b, clause_type);

        // h_b case: inject b at position 2
        let f_inl_b = Expr::lam(
            BinderInfo::Default,
            b.clone(),
            disjunction::inject_into_or_chain(clause_props, 2, Expr::bvar(0)),
        );

        // h_nb case: build ¬(a=b) = lam (h_eq : Eq Prop a b) =>
        //   h_nb (Eq.mpr (Eq.symm h_eq) h_a) : False
        // Forward transport via Eq.symm + Eq.mpr: h : a=b → symm: b=a → mpr: a→b
        // de Bruijn: bvar(0) = h_eq, bvar(1) = h_nb, bvar(2) = h_a
        let prop = Expr::sort(Level::zero());
        let symm = expr_builders::mk_eq_symm(&prop, a, b, &Expr::bvar(0));
        let forward_transport =
            expr_builders::mk_eq_mpr(&Level::zero(), b, a, &symm, &Expr::bvar(2));
        let not_eq_proof = Expr::lam(
            BinderInfo::Default,
            eq_type.clone(),
            Expr::app(Expr::bvar(1), forward_transport),
        );
        let f_inr_b = Expr::lam(
            BinderInfo::Default,
            not_b.clone(),
            disjunction::inject_into_or_chain(clause_props, 0, not_eq_proof),
        );

        let inner = disjunction::mk_or_rec(b, &not_b, &motive_b, &f_inl_b, &f_inr_b, &em_b);
        let f_inl_a = Expr::lam(BinderInfo::Default, a.clone(), inner);

        // inr: h_na → inject ¬a at position 1
        let f_inr_a = Expr::lam(
            BinderInfo::Default,
            not_a.clone(),
            disjunction::inject_into_or_chain(clause_props, 1, Expr::bvar(0)),
        );

        disjunction::mk_or_rec(a, &not_a, &motive_a, &f_inl_a, &f_inr_a, &em_a)
    }

    /// EquivNeg1: `{(a = b), ¬a, ¬b}`
    ///
    /// Level 0 em on `a`:
    /// - inl (h_a): em on `b`:
    ///   - inl (h_b): build `a = b` via `propext(Iff.intro (fun _ => h_b) (fun _ => h_a))`
    ///   - inr (h_nb): inject `¬b` at position 2
    /// - inr (h_na): inject `¬a` at position 1 (shortcut)
    fn build_equiv_neg1(a: &Expr, b: &Expr, clause_props: &[Expr], clause_type: &Expr) -> Expr {
        let false_expr = Expr::const_(clean_kernel::name::Name::from_string("False"), vec![]);
        let not_a = Expr::pi(BinderInfo::Default, a.clone(), false_expr.clone());
        let not_b = Expr::pi(BinderInfo::Default, b.clone(), false_expr);

        let em_a = disjunction::mk_classical_em(a);
        let motive_a = disjunction::mk_constant_or_motive(a, &not_a, clause_type);

        // inl: h_a → nested em on b
        let em_b = disjunction::mk_classical_em(b);
        let motive_b = disjunction::mk_constant_or_motive(b, &not_b, clause_type);

        // h_b case: build a = b via propext
        // de Bruijn: bvar(0) = h_b, bvar(1) = h_a
        // mp = fun (_ : a) => h_b: inside lambda, h_b = bvar(1)
        let mp = Expr::lam(BinderInfo::Default, a.clone(), Expr::bvar(1));
        // mpr = fun (_ : b) => h_a: inside lambda, h_a = bvar(2)
        let mpr = Expr::lam(BinderInfo::Default, b.clone(), Expr::bvar(2));
        let eq_proof = disjunction::mk_propext(a, b, &mp, &mpr);
        let f_inl_b = Expr::lam(
            BinderInfo::Default,
            b.clone(),
            disjunction::inject_into_or_chain(clause_props, 0, eq_proof),
        );

        // h_nb case: inject ¬b at position 2
        let f_inr_b = Expr::lam(
            BinderInfo::Default,
            not_b.clone(),
            disjunction::inject_into_or_chain(clause_props, 2, Expr::bvar(0)),
        );

        let inner = disjunction::mk_or_rec(b, &not_b, &motive_b, &f_inl_b, &f_inr_b, &em_b);
        let f_inl_a = Expr::lam(BinderInfo::Default, a.clone(), inner);

        // inr: h_na → inject ¬a at position 1
        let f_inr_a = Expr::lam(
            BinderInfo::Default,
            not_a.clone(),
            disjunction::inject_into_or_chain(clause_props, 1, Expr::bvar(0)),
        );

        disjunction::mk_or_rec(a, &not_a, &motive_a, &f_inl_a, &f_inr_a, &em_a)
    }

    /// EquivNeg2: `{(a = b), a, b}`
    ///
    /// Level 0 em on `a`:
    /// - inl (h_a): inject `a` at position 1 (shortcut)
    /// - inr (h_na): em on `b`:
    ///   - inl (h_b): inject `b` at position 2 (shortcut)
    ///   - inr (h_nb): build `a = b` via `propext(Iff.intro (absurd ...) (absurd ...))`
    fn build_equiv_neg2(a: &Expr, b: &Expr, clause_props: &[Expr], clause_type: &Expr) -> Expr {
        let false_expr = Expr::const_(clean_kernel::name::Name::from_string("False"), vec![]);
        let not_a = Expr::pi(BinderInfo::Default, a.clone(), false_expr.clone());
        let not_b = Expr::pi(BinderInfo::Default, b.clone(), false_expr);

        let em_a = disjunction::mk_classical_em(a);
        let motive_a = disjunction::mk_constant_or_motive(a, &not_a, clause_type);

        // inl: h_a → inject a at position 1
        let f_inl_a = Expr::lam(
            BinderInfo::Default,
            a.clone(),
            disjunction::inject_into_or_chain(clause_props, 1, Expr::bvar(0)),
        );

        // inr: h_na → nested em on b
        let em_b = disjunction::mk_classical_em(b);
        let motive_b = disjunction::mk_constant_or_motive(b, &not_b, clause_type);

        // h_b case: inject b at position 2
        let f_inl_b = Expr::lam(
            BinderInfo::Default,
            b.clone(),
            disjunction::inject_into_or_chain(clause_props, 2, Expr::bvar(0)),
        );

        // h_nb case: build a = b via propext with absurd
        // de Bruijn: bvar(0) = h_nb, bvar(1) = h_na
        // mp = fun (h_a : a) => absurd h_a h_na : b
        //   inside lambda: bvar(0) = h_a, bvar(1) = h_nb, bvar(2) = h_na
        let mp = Expr::lam(
            BinderInfo::Default,
            a.clone(),
            disjunction::mk_absurd(a, b, &Expr::bvar(0), &Expr::bvar(2)),
        );
        // mpr = fun (h_b : b) => absurd h_b h_nb : a
        //   inside lambda: bvar(0) = h_b, bvar(1) = h_nb, bvar(2) = h_na
        let mpr = Expr::lam(
            BinderInfo::Default,
            b.clone(),
            disjunction::mk_absurd(b, a, &Expr::bvar(0), &Expr::bvar(1)),
        );
        let eq_proof = disjunction::mk_propext(a, b, &mp, &mpr);
        let f_inr_b = Expr::lam(
            BinderInfo::Default,
            not_b.clone(),
            disjunction::inject_into_or_chain(clause_props, 0, eq_proof),
        );

        let inner = disjunction::mk_or_rec(b, &not_b, &motive_b, &f_inl_b, &f_inr_b, &em_b);
        let f_inr_a = Expr::lam(BinderInfo::Default, not_a.clone(), inner);

        disjunction::mk_or_rec(a, &not_a, &motive_a, &f_inl_a, &f_inr_a, &em_a)
    }
}
