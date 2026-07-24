// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 5: Mathlib metaprogramming — synthInstanceQ + mkFreshExprMVarQ.

use super::MetaCtx;
use crate::unify::MetaState;
use clean_kernel::{Expr, ExprKind, ExprVisitor, FVarId};

/// Result of synthInstanceQ operation
#[derive(Debug, Clone)]
pub enum SynthInstanceQResult {
    /// Instance synthesis succeeded
    Success(Expr),
    /// Instance synthesis failed - no instance found
    NotFound,
    /// Instance synthesis is stuck on unresolved metavariables
    Stuck,
}

/// Result of mkFreshExprMVarQ operation
#[derive(Debug, Clone)]
pub struct FreshMVarQ {
    /// The metavariable expression (as Expr::FVar with metavar tag)
    pub mvar: Expr,
    /// The quoted type Q(τ) that was extracted
    pub quoted_type: Expr,
}

impl<'a> MetaCtx<'a> {
    /// Synthesize a type class instance, returning Q(Instance α)
    pub fn synth_instance_q(&mut self, class_goal: &Expr) -> SynthInstanceQResult {
        self.metas.push_scope();

        let result = self.try_synth_instance(class_goal);

        match result {
            Some(instance_expr) => {
                self.metas.commit();
                SynthInstanceQResult::Success(instance_expr)
            }
            None => {
                if self.goal_has_unresolved_metas(class_goal) {
                    self.metas.pop_scope();
                    SynthInstanceQResult::Stuck
                } else {
                    self.metas.pop_scope();
                    SynthInstanceQResult::NotFound
                }
            }
        }
    }

    /// Try to synthesize an instance for a type class goal
    fn try_synth_instance(&mut self, class_goal: &Expr) -> Option<Expr> {
        use crate::instances::extract_class_app;

        let instances = self.instances?;
        let goal = self.metas.instantiate(class_goal);
        let (class_name, goal_args) = extract_class_app(&goal)?;

        if !instances.is_class(&class_name) {
            return None;
        }

        let out_params: Vec<usize> = instances
            .get_class(&class_name)
            .map(|info| info.out_params.clone())
            .unwrap_or_default();

        for inst in instances.get_instances(&class_name) {
            if let Some(result) =
                self.try_match_instance(inst, &class_name, &goal_args, &out_params)
            {
                return Some(result);
            }
        }

        None
    }

    /// Try to match a single instance against the goal
    fn try_match_instance(
        &mut self,
        inst: &crate::instances::InstanceInfo,
        class_name: &clean_kernel::Name,
        goal_args: &[Expr],
        out_params: &[usize],
    ) -> Option<Expr> {
        use crate::instances::extract_class_app;
        use clean_kernel::BinderInfo;

        self.metas.push_scope();

        let mut inst_expr = inst.expr.clone();
        let mut inst_type = inst.type_.clone();

        // Apply implicit parameters
        while let ExprKind::Pi(bi, ref arg_ty, ref body_ty) = inst_type.kind() {
            let instantiated_arg_ty = self.metas.instantiate(arg_ty);

            let arg = match bi.info {
                BinderInfo::InstImplicit => {
                    self.metas.pop_scope();
                    return None;
                }
                _ => self.fresh_meta(instantiated_arg_ty),
            };

            inst_expr = if let ExprKind::Lam(_, _, body) = inst_expr.kind() {
                body.instantiate(&arg)
            } else {
                Expr::app(inst_expr, arg.clone())
            };
            inst_type = self.metas.instantiate(&body_ty.instantiate(&arg));
        }

        // Unify instance type with goal
        if let Some((inst_class, inst_args)) = extract_class_app(&inst_type) {
            if inst_class != *class_name || inst_args.len() != goal_args.len() {
                self.metas.pop_scope();
                return None;
            }

            if self.unify_params(&inst_args, goal_args, out_params, false)
                && self.unify_params(&inst_args, goal_args, out_params, true)
            {
                self.metas.commit();
                return Some(self.metas.instantiate(&inst_expr));
            }
        }

        self.metas.pop_scope();
        None
    }

    /// Unify parameters between instance and goal
    ///
    /// When `out_only` is false, unifies non-out-parameters.
    /// When `out_only` is true, unifies out-parameters.
    fn unify_params(
        &mut self,
        inst_args: &[Expr],
        goal_args: &[Expr],
        out_params: &[usize],
        out_only: bool,
    ) -> bool {
        for (idx, (inst_arg, goal_arg)) in inst_args.iter().zip(goal_args.iter()).enumerate() {
            let is_out = out_params.contains(&idx);
            if is_out == out_only && !self.is_def_eq(inst_arg, goal_arg) {
                return false;
            }
        }
        true
    }

    /// Check if an expression contains unresolved metavariables.
    ///
    /// Uses ExprVisitor trait (#1981) — the trait handles structural recursion
    /// over all ExprKind variants (including Cubical/ZFC).
    pub(crate) fn goal_has_unresolved_metas(&self, expr: &Expr) -> bool {
        struct HasUnresolvedMetas<'a> {
            metas: &'a MetaState,
        }
        impl ExprVisitor for HasUnresolvedMetas<'_> {
            type Result = bool;
            fn combine(&self, a: bool, b: bool) -> bool {
                a || b
            }
            fn visit_fvar(&mut self, id: FVarId) -> bool {
                if let Some(meta_id) = MetaState::from_fvar(id) {
                    self.metas.get_assignment(meta_id).is_none()
                } else {
                    false
                }
            }
        }
        let mut visitor = HasUnresolvedMetas { metas: &self.metas };
        visitor.visit_expr(expr)
    }

    /// Create a fresh metavariable with a quoted type (mkFreshExprMVarQ)
    pub fn mk_fresh_expr_mvar_q(&mut self, quoted_type: Expr) -> FreshMVarQ {
        let mvar = self.fresh_meta(quoted_type.clone());
        FreshMVarQ { mvar, quoted_type }
    }

    /// Create a fresh metavariable with a quoted type, optionally named
    pub fn mk_fresh_expr_mvar_q_with_name(
        &mut self,
        quoted_type: Expr,
        _name_hint: Option<&str>,
    ) -> FreshMVarQ {
        self.mk_fresh_expr_mvar_q(quoted_type)
    }

    /// Assign a value to a metavariable created by mkFreshExprMVarQ
    pub fn assign_mvar_q(&mut self, mvar: &Expr, value: Expr) -> bool {
        if let ExprKind::FVar(fvar) = mvar.kind() {
            if let Some(meta_id) = MetaState::from_fvar(*fvar) {
                self.metas.assign(meta_id, value);
                return true;
            }
        }
        false
    }
}
