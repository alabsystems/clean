// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generalized field notation resolved the way Lean's `resolveLValLoop`
//! (`Lean/Elab/App.lean:1531-1545`) resolves it: consume the receiver's
//! leading implicits without unfolding anything (`consumeImplicits`,
//! App.lean:1512), resolve against the consumed type's own head
//! (`resolveLValAux`, App.lean:1381), and unfold one definition at a time
//! only on a miss. Called from `elab_proj.rs`'s dot-notation path.

use super::*;
use crate::tactic::op_projection::head_beta;

impl<'a> ElabCtx<'a> {
    /// Generalized field notation on a receiver whose type leads with
    /// implicit binders, the way Lean's `resolveLValLoop`
    /// (`Lean/Elab/App.lean:1531`) does it: `consumeImplicits` (App.lean:1512)
    /// fills the leading implicits WITHOUT unfolding anything, then
    /// `resolveLValAux` (App.lean:1381) reads the CONSUMED type — a `∀` names
    /// `Function.<field>` (App.lean:1433-1436), a constant head `C` names
    /// `C.<field>` — and only on a miss does `unfoldDefinition?` take one δ
    /// step before trying again (App.lean:1541-1545).
    ///
    /// Clean used to reduce the peeled type to weak-head normal form first,
    /// so `coe_injective.eq_iff` (`coe_injective : ∀ {α} {p}, Injective
    /// fun a ↦ ↑a`) lost its `Function.Injective` head, and `val.extend g j b`
    /// (`Subtype.val : {α} → {p} → Subtype p → α`) never reached `Function.`
    /// because only an EXPLICIT leading binder did: `Subtype.coe_inj`,
    /// `coe_ne_coe`, `Function.extend_val_apply` and `extend_val_apply'` in
    /// `Mathlib/Data/Subtype.lean`, measured 2026-09-12.
    ///
    /// Returns `Ok(None)` when no target resolves, so the caller's own
    /// attempts still run. SOUNDNESS: resolution only; the application built
    /// here is elaborated like any other and re-checked by the kernel.
    pub(super) fn resolve_field_through_consumed_implicits(
        &mut self,
        receiver: &Expr,
        receiver_ty: &Expr,
        field_name: &SurfaceName,
    ) -> Result<Option<Expr>, ElabError> {
        // A δ-chain in a well-formed environment is finite; the bound only
        // keeps a malformed one from looping.
        const MAX_UNFOLD_STEPS: usize = 64;
        let (mut recv, mut recv_ty) =
            self.consume_receiver_implicits(receiver.clone(), receiver_ty);
        for _ in 0..MAX_UNFOLD_STEPS {
            if matches!(recv_ty.kind(), ExprKind::Pi(..)) {
                // `.forallE` names `Function.<field>`; a `∀` does not unfold,
                // so a miss here ends the search (Lean rethrows).
                return Ok(self.apply_function_namespace_field(field_name, &recv, &recv_ty));
            }
            if let ExprKind::Const(head, _) = recv_ty.get_app_fn().kind() {
                let name =
                    self.with_private_step(crate::namespace::append_names(head, field_name.name()));
                if self.is_const_accessible(&name) {
                    if let Some(info) = self.env.get_const(&name) {
                        let const_level_params = info.level_params.clone();
                        let const_type = info.type_.clone();
                        let levels: Vec<Level> = const_level_params
                            .iter()
                            .map(|_| self.fresh_universe_param())
                            .collect();
                        let fn_type = if levels.is_empty() {
                            const_type
                        } else {
                            const_type.instantiate_level_params_direct(&const_level_params, &levels)
                        };
                        let type_name = head.clone();
                        let fn_expr = Expr::const_(name, levels);
                        return self
                            .apply_dot_receiver(fn_expr, &fn_type, &recv, &recv_ty, &type_name)
                            .map(Some);
                    }
                }
            }
            let Some(unfolded) = self.unfold_definition_step(&recv_ty) else {
                return Ok(None);
            };
            (recv, recv_ty) = self.consume_receiver_implicits(recv, &unfolded);
        }
        Ok(None)
    }

    /// Lean's `consumeImplicits` (`Lean/Elab/App.lean:1512`) for a field
    /// access: `whnfCore` — here instantiation plus head β, never δ — then
    /// every leading `{x}` gets a metavariable, every `[x]` instance
    /// resolution (a metavariable when nothing resolves yet, as the rest of
    /// this path does), an explicit `optParam` binder its default, and the
    /// run stops at anything else. A `⦃x⦄` binder also stops it: Lean fills
    /// one only when the access has arguments (`hasArgs`), which this path
    /// does not see, so it keeps the arg-less reading.
    fn consume_receiver_implicits(&mut self, receiver: Expr, receiver_ty: &Expr) -> (Expr, Expr) {
        let mut recv = receiver;
        let mut ty = head_beta(&self.metas.instantiate(receiver_ty));
        while let ExprKind::Pi(bi, dom, body) = ty.kind() {
            let (info, dom, body) = (bi.info, self.metas.instantiate(dom), body.as_ref().clone());
            let arg = match info {
                BinderInfo::Implicit => self.fresh_meta(dom),
                BinderInfo::InstImplicit => match self.resolve_instance(&dom) {
                    Some(inst) => inst,
                    None => self.fresh_meta(dom),
                },
                BinderInfo::Default => match Self::opt_param_default(&dom) {
                    Some(default) => default,
                    None => break,
                },
                _ => break,
            };
            recv = Expr::app(recv, arg.clone());
            ty = head_beta(&self.metas.instantiate(&body.instantiate(&arg)));
        }
        (recv, ty)
    }

    /// Lean's `unfoldDefinition?` on a type: one δ step of its head constant
    /// (a definition that is not `@[irreducible]`), head-β-reduced against
    /// the arguments. `None` when the head does not unfold.
    pub(super) fn unfold_definition_step(&self, ty: &Expr) -> Option<Expr> {
        let ExprKind::Const(name, levels) = ty.get_app_fn().kind() else {
            return None;
        };
        let info = self.env.get_const(name)?;
        if info.kind != clean_kernel::ConstantKind::Definition
            || info.reducibility == Reducibility::Irreducible
        {
            return None;
        }
        let value = info
            .value
            .as_ref()?
            .instantiate_level_params_direct(&info.level_params, levels);
        let args = ty.get_app_args().into_iter().cloned();
        Some(head_beta(&Expr::apps(value, args)))
    }

    /// Dot notation into the `Function` namespace (Lean's `.forallE` case of
    /// `resolveLValAux`, App.lean:1433-1436): apply `Function.<field>` to the
    /// function-typed receiver as its first explicit argument, inserting its
    /// own leading implicits and pinning their carriers from the receiver's
    /// type. `None` when `Function.<field>` does not exist.
    ///
    /// SOUNDNESS: elaboration-completeness only; the produced `Function.<field>
    /// … receiver` application is kernel-re-checked.
    pub(super) fn apply_function_namespace_field(
        &mut self,
        field_name: &SurfaceName,
        receiver: &Expr,
        receiver_ty: &Expr,
    ) -> Option<Expr> {
        let fn_ns_name = SurfaceName::generated_path("Function")
            .append(field_name)
            .into_name();
        if !self.is_const_accessible(&fn_ns_name) {
            return None;
        }
        let info = self.env.get_const(&fn_ns_name)?;
        let const_level_params = info.level_params.clone();
        let const_type = info.type_.clone();
        let levels: Vec<Level> = const_level_params
            .iter()
            .map(|_| self.fresh_universe_param())
            .collect();
        let fn_type = if levels.is_empty() {
            const_type
        } else {
            const_type.instantiate_level_params_direct(&const_level_params, &levels)
        };
        let fn_expr = Expr::const_(fn_ns_name, levels);
        // Lean's `addLValArg` (App.lean:1587-1626) scans the WHOLE parameter
        // telescope — implicits included — for the first parameter that
        // `typeMatchesBaseName` accepts, which for the `Function` namespace is
        // `(← whnf type).isForall` (App.lean:1564-1567), and binds the
        // receiver THERE. For
        // `Function.surjInv : {α} → {β} → {f : α → β} → Surjective f → β → α`
        // that is the IMPLICIT `{f}`, so `f.surjInv hf x` is
        // `@Function.surjInv α β f hf x` (ground-truthed with `pp.explicit` on
        // the pinned v4.30.0-rc2 binary). Applying the receiver as the first
        // EXPLICIT argument instead put the function itself in the
        // surjectivity slot and pushed `hf` and `x` one slot late —
        // `Mathlib/Logic/Function/Basic.lean` `Function.comp_surjInv`.
        if let Some(applied) =
            self.apply_receiver_at_first_function_binder(&fn_expr, &fn_type, receiver, receiver_ty)
        {
            return Some(applied);
        }
        // No parameter's type is a function under reducible-and-instances
        // transparency, or an EXPLICIT non-matching parameter precedes the
        // one that is (which Lean would fill with a named argument). Keep the
        // long-standing behaviour rather than refuse: the receiver is the
        // explicit argument that follows.
        let (fn_with_implicits, fn_rest_ty) =
            self.insert_implicit_args(fn_expr, &fn_type, ArgsFollow::Yes);
        // Pin `Function.<field>`'s domain metavars (the function's
        // source/target types) from the receiver's actual type before
        // applying it, so no metavariable is left unsolved.
        let fn_rest_ty = self.whnf(&fn_rest_ty);
        if let ExprKind::Pi(_, arg_ty, _) = fn_rest_ty.kind() {
            let arg_ty = self.metas.instantiate(arg_ty);
            self.try_unify(&arg_ty, receiver_ty);
        }
        let applied = Expr::app(fn_with_implicits, receiver.clone());
        let applied = self.metas.instantiate(&applied);
        Some(self.metas.instantiate_levels(&applied))
    }

    /// Lean's `addLValArg` scan (`Lean/Elab/App.lean:1587-1626`) for the
    /// `Function` namespace: walk the constant's parameter telescope and bind
    /// the receiver at the FIRST parameter whose type is a function type,
    /// whatever that parameter's binder info.
    ///
    /// The transparency is load-bearing and is Lean's own: `typeMatchesBaseName`
    /// runs under `withReducibleAndInstances`, so a parameter typed
    /// `Surjective f` — an ordinary `def` that unfolds to `∀ b, ∃ a, f a = b` —
    /// does NOT read as a function there and cannot be mistaken for the
    /// function slot. Clean's plain `whnf` is full-delta and would match it,
    /// reproducing the same defect one step later; `whnf_instances` is
    /// `TransparencyMode::Instances`, Lean's mode exactly.
    ///
    /// Returns `None` — leaving the caller's long-standing behaviour in place —
    /// when no parameter matches, or when an EXPLICIT parameter that does not
    /// match comes first: Lean binds the receiver as a NAMED argument in that
    /// case, which this positional path cannot express, and guessing a slot is
    /// how the original defect arose.
    ///
    /// SOUNDNESS: argument placement only; the application built here is
    /// elaborated like any other and re-checked by the kernel.
    fn apply_receiver_at_first_function_binder(
        &mut self,
        fn_expr: &Expr,
        fn_type: &Expr,
        receiver: &Expr,
        receiver_ty: &Expr,
    ) -> Option<Expr> {
        // A well-formed constant's telescope is finite; the bound only keeps a
        // malformed one from looping.
        const MAX_BINDERS: usize = 64;
        let mut acc = fn_expr.clone();
        let mut ty = head_beta(&self.metas.instantiate(fn_type));
        for _ in 0..MAX_BINDERS {
            let ExprKind::Pi(bi, dom, body) = ty.kind() else {
                return None;
            };
            let (info, dom, body) = (bi.info, self.metas.instantiate(dom), body.as_ref().clone());
            if matches!(self.whnf_instances(&dom).kind(), ExprKind::Pi(..)) {
                // Pin this parameter's type from the receiver's actual type
                // before supplying it, so the carriers of any metavariables
                // inserted above are solved rather than left dangling.
                self.try_unify(&dom, receiver_ty);
                let applied = Expr::app(acc, receiver.clone());
                let applied = self.metas.instantiate(&applied);
                return Some(self.metas.instantiate_levels(&applied));
            }
            let arg = match info {
                BinderInfo::Implicit | BinderInfo::StrictImplicit => self.fresh_meta(dom),
                BinderInfo::InstImplicit => match self.resolve_instance(&dom) {
                    Some(inst) => inst,
                    None => self.fresh_meta(dom),
                },
                // An explicit parameter that is not the function slot belongs
                // to the user's own arguments.
                BinderInfo::Default => return None,
            };
            acc = Expr::app(acc, arg.clone());
            ty = head_beta(&self.metas.instantiate(&body.instantiate(&arg)));
        }
        None
    }
}
