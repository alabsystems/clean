// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Disjunction proof term construction helpers.
//!
//! Delegates to shared `bridge::disjunction` free functions.
//! Methods on `SuperpositionReconstructor` are thin wrappers for backward
//! compatibility with existing callers in the superposition reconstruction
//! submodules.

use clean_kernel::Expr;

use super::SuperpositionReconstructor;
use crate::bridge::disjunction;

impl<'a> SuperpositionReconstructor<'a> {
    /// Build the type of a right-associative Or chain from a slice of propositions.
    pub(super) fn or_chain_type(props: &[Expr]) -> Expr {
        disjunction::or_chain_type(props)
    }

    /// Inject a proof into a specific position of a right-associative Or chain.
    pub(super) fn inject_into_or_chain(
        result_props: &[Expr],
        position: usize,
        proof: Expr,
    ) -> Expr {
        disjunction::inject_into_or_chain(result_props, position, proof)
    }

    /// Build `@Or.inl a b ha : Or a b`.
    pub(super) fn mk_or_inl(a: &Expr, b: &Expr, ha: &Expr) -> Expr {
        disjunction::mk_or_inl(a, b, ha)
    }

    /// Build `@Or.inr a b hb : Or a b`.
    pub(super) fn mk_or_inr(a: &Expr, b: &Expr, hb: &Expr) -> Expr {
        disjunction::mk_or_inr(a, b, hb)
    }

    /// Build `@Or.rec a b motive f_inl f_inr h`.
    pub(super) fn mk_or_rec(
        a: &Expr,
        b: &Expr,
        motive: &Expr,
        f_inl: &Expr,
        f_inr: &Expr,
        h: &Expr,
    ) -> Expr {
        disjunction::mk_or_rec(a, b, motive, f_inl, f_inr, h)
    }

    /// Build `@Classical.em p : Or p (Not p)`.
    pub(super) fn mk_classical_em(p: &Expr) -> Expr {
        use clean_kernel::name::Name;
        Expr::app(
            Expr::const_(Name::from_string("Classical.em"), vec![]),
            p.clone(),
        )
    }

    /// Build a constant motive for Or.rec: `fun (_ : Or a b) => target`.
    pub(super) fn mk_constant_or_motive(a: &Expr, b: &Expr, target: &Expr) -> Expr {
        disjunction::mk_constant_or_motive(a, b, target)
    }

    /// Weaken a sub-disjunction proof into a larger Or chain.
    pub(super) fn weaken_or_chain(
        sub_props: &[Expr],
        sub_proof: Expr,
        result_lit_props: &[Expr],
        result_prop: &Expr,
        positions: &[usize],
    ) -> Expr {
        assert_eq!(sub_props.len(), positions.len());
        assert!(!sub_props.is_empty());

        if sub_props.len() == 1 {
            return disjunction::inject_into_or_chain(result_lit_props, positions[0], sub_proof);
        }

        let head = &sub_props[0];
        let tail = disjunction::or_chain_type(&sub_props[1..]);
        let or_motive = disjunction::mk_constant_or_motive(head, &tail, result_prop);

        let inl_body =
            disjunction::inject_into_or_chain(result_lit_props, positions[0], Expr::bvar(0));
        let case_inl = Expr::lam(clean_kernel::BinderInfo::Default, head.clone(), inl_body);

        let inr_body = Self::weaken_or_chain(
            &sub_props[1..],
            Expr::bvar(0),
            result_lit_props,
            result_prop,
            &positions[1..],
        );
        let case_inr = Expr::lam(clean_kernel::BinderInfo::Default, tail.clone(), inr_body);

        disjunction::mk_or_rec(head, &tail, &or_motive, &case_inl, &case_inr, &sub_proof)
    }
}
