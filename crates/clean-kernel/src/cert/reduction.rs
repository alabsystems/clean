// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WHNF reduction for `CertVerifier`.
//!
//! Implements weak head normal form computation: beta, zeta, delta,
//! projection (iota-proj), iota (recursor), quotient, and MData reductions.
//! Definitional equality is in the sibling `def_eq` module.

use crate::env::TransparencyMode;
use crate::expr::stack_safe;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use std::sync::Arc;

use super::verifier::CertVerifier;

impl<'env> CertVerifier<'env> {
    /// Compute WHNF (weak head normal form)
    ///
    /// Public API for stack-safe WHNF. Used by tests; internal code uses whnf_impl.
    #[cfg(test)] // Only used by tests; internal code uses whnf_impl directly
    pub(super) fn whnf(&self, e: &Expr) -> Expr {
        self.whnf_impl(e)
    }

    /// Internal WHNF implementation.
    ///
    /// Handles beta, zeta, delta, projection (iota-proj), iota (recursor),
    /// quotient, and MData reductions.
    ///
    /// Reference: tc/whnf.rs `whnf_core_inner`
    pub(super) fn whnf_impl(&self, e: &Expr) -> Expr {
        stack_safe(|| self.whnf_inner(e))
    }

    /// Inner WHNF implementation.
    fn whnf_inner(&self, e: &Expr) -> Expr {
        match &e.kind {
            ExprKind::App(f, a) => {
                // Native Nat literal reduction (Lean 4 `reduce_nat` parity,
                // mirrors `tc/whnf.rs:383`): fire on the FULL application before
                // delta-unfolding the head, so closed `Nat.succ`/`Nat.add`/…/
                // `Nat.ble` compute in O(1) to a literal instead of unfolding to
                // `Nat.rec` and iota-reducing O(value) steps. Closes the
                // cert-replay Nat-defeq gap (see `cert/nat_reduce.rs`).
                if let ExprKind::Const(_, _) = e.get_app_fn().kind {
                    if let Some(reduced) = super::nat_reduce::reduce_nat(e, &|x| self.whnf_impl(x))
                    {
                        return self.whnf_impl(&reduced);
                    }
                }
                let f_whnf = self.whnf_impl(f);
                match &f_whnf.kind {
                    // Beta reduction: (λ x. body) arg → body[arg/x]
                    ExprKind::Lam(_, _, body) => {
                        let reduced = body.instantiate(a);
                        self.whnf_impl(&reduced)
                    }
                    _ => {
                        let app = Expr::from_kind(ExprKind::App(Arc::new(f_whnf), a.clone()));
                        // Try iota reduction (recursor application)
                        if let Some(reduced) = self.try_iota_reduction(&app) {
                            return self.whnf_impl(&reduced);
                        }
                        // Try quotient reduction (Quot.lift)
                        if let Some(reduced) = self.try_quot_reduction(&app) {
                            return self.whnf_impl(&reduced);
                        }
                        app
                    }
                }
            }
            // Zeta reduction: let x := val in body → body[val/x]
            ExprKind::Let(_, _, val, body, _) => {
                let reduced = body.instantiate(val);
                self.whnf_impl(&reduced)
            }
            // Delta reduction: unfold constants at Default transparency
            ExprKind::Const(name, levels) => self
                .env
                .unfold_with_transparency(name, levels, TransparencyMode::Default)
                .map_or_else(|| e.clone(), |val| self.whnf_impl(&val)),
            // Projection reduction: S.mk(params..., fields...).i → fields[i]
            ExprKind::Proj(struct_name, idx, expr) => self.reduce_proj(struct_name, *idx, expr),
            // MData transparency: strip metadata wrappers
            ExprKind::MData(_, inner) => self.whnf_impl(inner),
            _ => e.clone(),
        }
    }

    /// Reduce a projection expression.
    ///
    /// WHNF the struct expression, then check if it's a constructor application.
    /// If so, extract the field at the given index.
    ///
    /// Reference: tc/reduction.rs `reduce_proj_impl`
    fn reduce_proj(&self, struct_name: &Name, idx: u32, expr: &Expr) -> Expr {
        let expr_whnf = self.whnf_impl(expr);
        let head = expr_whnf.get_app_fn();
        if let ExprKind::Const(ctor_name, _) = &head.kind {
            if let Some(ctor_val) = self.env.get_constructor(ctor_name) {
                // Lean 4 parity: reduce_proj_core does NOT check that the
                // constructor's inductive matches the Proj struct name.
                // This is critical for type aliases (Part of #3209).
                let args = expr_whnf.get_app_args();
                let field_idx = ctor_val.num_params as usize + idx as usize;
                if field_idx < args.len() {
                    return self.whnf_impl(args[field_idx]);
                }
            }
        }
        // Can't reduce — return Proj with WHNF'd inner expression
        Expr::from_kind(ExprKind::Proj(
            struct_name.clone(),
            idx,
            Arc::new(expr_whnf),
        ))
    }

    /// Try iota reduction (recursor computation rule).
    ///
    /// For `I.rec params motive minors indices major`, if the major premise
    /// reduces to a constructor application, apply the corresponding recursor rule.
    ///
    /// Reference: tc/reduction.rs `try_iota_reduction`
    fn try_iota_reduction(&self, e: &Expr) -> Option<Expr> {
        let head = e.get_app_fn();
        let ExprKind::Const(rec_name, rec_levels) = &head.kind else {
            return None;
        };
        let rec_val = self.env.get_recursor(rec_name)?;
        let args = e.get_app_args();

        // Calculate position of major premise
        let args_before_major = match rec_val.arg_order {
            crate::inductive::RecursorArgOrder::MajorAfterMinors => {
                rec_val.num_params as usize
                    + rec_val.num_motives as usize
                    + rec_val.num_minors as usize
                    + rec_val.num_indices as usize
            }
            crate::inductive::RecursorArgOrder::MajorAfterMotive => {
                rec_val.num_params as usize
                    + rec_val.num_motives as usize
                    + rec_val.num_indices as usize
            }
        };

        // Check we have enough arguments
        let required_args = match rec_val.arg_order {
            crate::inductive::RecursorArgOrder::MajorAfterMinors => args_before_major + 1,
            crate::inductive::RecursorArgOrder::MajorAfterMotive => {
                args_before_major + 1 + rec_val.num_minors as usize
            }
        };
        if args.len() < required_args {
            return None;
        }

        // WHNF the major premise to find constructor head
        let major_whnf = self.whnf_impl(args[args_before_major]);

        // Expand a Nat literal major premise to constructor form so a recursor
        // (`Nat.rec`/`Nat.ble`/`Nat.pred`/`Nat.add` on a literal) can iota-reduce
        // — Lean 4 parity with `tc/reduction/mod.rs:166-180`
        // (`nat_lit_to_constructor`). The main `clean check` path does this; the
        // cert verifier omitted it, leaving e.g. `Nat.ble (succ j) 0` and
        // `addB true p ≡ Nat.succ p` stuck and breaking `export-cert` replay of
        // genuine Nat-counting proofs. Closes that gap (see `cert/nat_reduce.rs`).
        let major_whnf: Expr = match &major_whnf.kind {
            ExprKind::Lit(crate::expr::Literal::Nat(n)) => {
                super::nat_reduce::nat_lit_to_constructor(n)
            }
            _ => major_whnf,
        };

        // Check if major is a constructor application
        let major_head = major_whnf.get_app_fn();
        let ExprKind::Const(ctor_name, _) = &major_head.kind else {
            return None;
        };
        let ctor_val = self.env.get_constructor(ctor_name)?;

        // Rule selection. Fast path: same-inductive ctor → O(1) index lookup
        // (rules are built in constructor order). Fallback ([R10], design
        // 2026-07-02-parameterized-nested-inductives.md §4.4): restored
        // nested-family recursors `T.rec_N` carry rules keyed to a REAL
        // container's constructors (`List.cons` under `Tree.rec_1`), whose
        // `inductive_name` differs from the recursor's — select by NAME, as
        // `tc/reduction/mod.rs` does. Without this the cert/export-replay
        // lane left every nested family permanently stuck.
        let rule = if ctor_val.inductive_name == rec_val.inductive_name {
            let rule = rec_val.rules.get(ctor_val.constructor_idx as usize)?;
            debug_assert_eq!(
                &rule.constructor_name, ctor_name,
                "constructor_idx {} doesn't match rule constructor name",
                ctor_val.constructor_idx
            );
            rule
        } else {
            rec_val
                .rules
                .iter()
                .find(|r| &r.constructor_name == ctor_name)?
        };

        // Extract constructor fields
        let major_args = major_whnf.get_app_args();
        if (rule.num_fields as usize) > major_args.len() {
            return None;
        }
        let nparams = major_args.len() - rule.num_fields as usize;
        let fields: Vec<Expr> = major_args
            .iter()
            .skip(nparams)
            .take(rule.num_fields as usize)
            .map(|e| (*e).clone())
            .collect();

        // Verify level param count
        if rec_levels.len() != rec_val.level_params.len() {
            return None;
        }

        // Determine minor premise location
        let minors_start = match rec_val.arg_order {
            crate::inductive::RecursorArgOrder::MajorAfterMinors => {
                rec_val.num_params as usize + rec_val.num_motives as usize
            }
            crate::inductive::RecursorArgOrder::MajorAfterMotive => args_before_major + 1,
        };

        // RHS-based reduction (Lean 4 format)
        let result = if rule.rhs.is_lam() {
            let mut result = rule
                .rhs
                .instantiate_level_params_direct(&rec_val.level_params, rec_levels);

            let n_pm = rec_val.num_params as usize + rec_val.num_motives as usize;
            let n_pmm = n_pm + rec_val.num_minors as usize;

            match rec_val.arg_order {
                crate::inductive::RecursorArgOrder::MajorAfterMinors => {
                    for i in 0..n_pmm {
                        result = Expr::app(result, (*args.get(i)?).clone());
                    }
                }
                crate::inductive::RecursorArgOrder::MajorAfterMotive => {
                    for i in 0..n_pm {
                        result = Expr::app(result, (*args.get(i)?).clone());
                    }
                    for j in 0..rec_val.num_minors as usize {
                        let idx = minors_start + j;
                        result = Expr::app(result, (*args.get(idx)?).clone());
                    }
                }
            }

            for field in &fields {
                result = Expr::app(result, field.clone());
            }
            result
        } else {
            // Legacy fallback for non-lambda RHS
            let minor_idx = minors_start + ctor_val.constructor_idx as usize;
            if minor_idx >= args.len() {
                return None;
            }
            let mut result = args[minor_idx].clone();
            for field in &fields {
                result = Expr::app(result, field.clone());
            }
            result
        };

        // Apply extra arguments after major premise
        let extras_start = match rec_val.arg_order {
            crate::inductive::RecursorArgOrder::MajorAfterMinors => args_before_major + 1,
            crate::inductive::RecursorArgOrder::MajorAfterMotive => {
                args_before_major + 1 + rec_val.num_minors as usize
            }
        };
        let mut result = result;
        for extra in &args[extras_start..] {
            result = Expr::app(result, (*extra).clone());
        }

        Some(result)
    }

    /// Try quotient reduction (Quot.lift).
    ///
    /// Delegates to the shared `try_quot_lift_reduction` with our WHNF.
    fn try_quot_reduction(&self, e: &Expr) -> Option<Expr> {
        let head = e.get_app_fn();
        if !matches!(&head.kind, ExprKind::Const(name, _) if *name == *crate::quot::names::QUOT_LIFT)
        {
            return None;
        }
        let args = e.get_app_args();
        crate::quot::try_quot_lift_reduction(head, &args, |expr| self.whnf_impl(expr))
    }
}
