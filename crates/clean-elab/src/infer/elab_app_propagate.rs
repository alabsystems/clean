// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean's `ElabAppArgs.propagateExpectedType` (`Lean/Elab/App.lean:343-458`)
//! for `elab_app`'s explicit-argument loop: before an explicit argument is
//! elaborated, a result type that does not depend on the remaining arguments
//! is unified with the expected type, so the arguments meet slots the
//! expected type has already pinned.

use super::*;

impl<'a> ElabCtx<'a> {
    /// Is the expected type literally `Prop` (Lean's `expectedType.isProp`)?
    pub(super) fn expected_is_literal_prop(&self) -> bool {
        self.current_expected_type.as_ref().is_some_and(|expected| {
            matches!(
                self.metas.instantiate(expected).kind(),
                ExprKind::Sort(level) if level.is_zero()
            )
        })
    }

    /// Lean's `ElabAppArgs.propagateExpectedType` (`Lean/Elab/App.lean:414-458`),
    /// run before an explicit argument is elaborated: when the application's
    /// result type after the `remaining` explicit arguments does not depend on
    /// any of them, unify it with the expected type NOW, so the arguments are
    /// elaborated against slots the expected type has already pinned.
    ///
    /// Returns whether propagation stays ARMED for the next argument. Lean
    /// disarms after a successful unification and when the expected type is
    /// literally `Prop` (it is used as a "Bool", e.g. by `if`); an argument
    /// that is `_`, `?_`/`?x` or a `by` block (`shouldPropagateExpectedTypeFor`),
    /// a result that depends on a remaining argument or carries an
    /// `optParam`/`autoParam`, and a failed unification all leave it armed.
    ///
    /// Measured 2026-09-12 (`Mathlib/Logic/Function/Basic.lean`,
    /// `Mathlib/Data/Subtype.lean`, `Mathlib/Logic/Unique.lean`): without it,
    /// `Subtype.ext h` checked `h : ↑a = b` against `↑?a₂` before `?a₂` was
    /// known, `funext fun x ↦ … ▸ rfl` solved `?g := f` from the `▸` and
    /// returned `f = f`, and `hf.forall.trans (forall_congr' …)` faced the
    /// non-pattern `?p (f x)`.
    ///
    /// Three Clean guards, each recorded at its own site: an expected type
    /// that is an unassigned metavariable has nothing to push inward
    /// (`expected_is_unassigned_meta`); a universe expected type is not
    /// propagated (see the guard below); and a heterogeneous arithmetic head
    /// never reaches here — it is Clean's stand-in for Lean's `binop%`
    /// elaborator, which does not go through `propagateExpectedType`
    /// (the caller's `is_hetero_binop_head` check).
    ///
    /// SOUNDNESS: speculative — assignments are kept only when the whole
    /// unification succeeds, and the finished term is re-checked by the
    /// kernel.
    pub(super) fn propagate_expected_type(
        &mut self,
        fn_type: &Expr,
        remaining: &[SurfaceArg],
    ) -> bool {
        self.propagate_expected_type_with_positioned_args(fn_type, remaining, false)
    }

    /// Named-argument resolution supplies positional slots for implicit binders
    /// too. Count each supplied slot, then resume ordinary treatment of trailing
    /// implicit binders. The dependency and transactional-unification guards are
    /// identical to the ordinary application path.
    pub(super) fn propagate_expected_type_with_positioned_args(
        &mut self,
        fn_type: &Expr,
        remaining: &[SurfaceArg],
        positioned: bool,
    ) -> bool {
        let Some(arg) = remaining.first() else {
            return true;
        };
        if matches!(
            arg.expr,
            SurfaceExpr::Hole(_) | SurfaceExpr::NamedHole(..) | SurfaceExpr::ByTactic(..)
        ) {
            return true;
        }
        let Some(expected) = self.current_expected_type.clone() else {
            return true;
        };
        if self.expected_is_literal_prop() {
            return false;
        }
        if self.expected_is_unassigned_meta() {
            return true;
        }
        let expected = self.metas.instantiate(&expected);
        // Clean guard: a universe (`Sort ℓ`) expected type is not propagated.
        // Clean's expected type is dynamically scoped, and `elab_pi` elaborates
        // a binder's domain and the body under the Pi's OWN expected sort,
        // where Lean's `elabType` gives each a fresh `Sort ?u`. Propagating
        // that sort pins the result universe of whatever type former sits
        // there, and Clean's level solver then commits a componentwise
        // `max`/`max` split that Lean postpones (`postponeIsLevelDefEq`).
        // Measured 2026-09-13 on the codata seed
        // (`crates/clean-elab/data/MTypeIndexedPoly2.lean`): `isigmaStep`
        // (`Sigma (fun a => …) : Type (max u v)` split `max u v =?= max ?u' ?v'`
        // into `?v' := v`), and `it_congr` / `icastB_comp`, whose `Eq.rec`
        // motive `fun h e => ∀ b : B i h, …` had its codomain `Sort ?u₁`
        // pinned to `Type u` by the domain `B i h`. The propagated shapes this
        // port is for all have a proposition or a function type as the
        // expected type.
        if matches!(expected.kind(), ExprKind::Sort(_)) {
            return true;
        }
        let fn_type = self.metas.instantiate(fn_type);
        let Some(body) =
            Self::forall_body_after_args(&fn_type, remaining.len(), self.explicit_mode, positioned)
        else {
            return true;
        };
        if body.has_loose_bvars() || self.has_opt_auto_params(&body) {
            return true;
        }
        // Without the entry WHNF, like Lean's lazy-δ `isDefEq`: reducing both
        // sides first unfolds a monad abbreviation in the result (`Id ?α` is
        // `?α`), so the do-block's `?m ?β` met a bare metavariable and the
        // monad was never pinned (`do if (← Id.mk true) then … else …`,
        // `test_elab_do_nested_action_in_if_condition`).
        self.metas.push_scope();
        let unified = {
            let ctx = self.build_local_ctx();
            let mut unifier = Unifier::with_env(&mut self.metas, self.env, ctx);
            matches!(
                unifier.unify_no_initial_whnf(&expected, &body),
                UnifyResult::Success
            )
        };
        if unified {
            self.metas.commit();
            false
        } else {
            self.metas.pop_scope();
            true
        }
    }

    /// Lean's `getForallBody` (`Lean/Elab/App.lean:350-365`, no named
    /// arguments): the part of `ty` left after `remaining` explicit binders,
    /// walked WITHOUT instantiating them, so a result that depends on one of
    /// them keeps a loose bound variable. Non-explicit binders are skipped
    /// (all binders under `@`), as are `optParam`/`autoParam` binders once
    /// the count is exhausted. `None` when `ty` runs out of binders first.
    fn forall_body_after_args(
        ty: &Expr,
        mut remaining: usize,
        explicit: bool,
        positioned: bool,
    ) -> Option<Expr> {
        let mut cur = ty.clone();
        loop {
            let next = match cur.kind() {
                ExprKind::Pi(bi, dom, body) => {
                    if positioned && remaining > 0 {
                        remaining -= 1;
                        body.as_ref().clone()
                    } else if !explicit && bi.info != BinderInfo::Default {
                        body.as_ref().clone()
                    } else if remaining > 0 {
                        remaining -= 1;
                        body.as_ref().clone()
                    } else if Self::is_opt_or_auto_param(dom) {
                        body.as_ref().clone()
                    } else {
                        return Some(cur.clone());
                    }
                }
                _ => return (remaining == 0).then_some(cur),
            };
            cur = next;
        }
    }

    /// Is `ty` a default-valued (`optParam α v`) or tactic-valued
    /// (`autoParam α tac`) parameter type?
    fn is_opt_or_auto_param(ty: &Expr) -> bool {
        Self::opt_param_default(ty).is_some()
            || matches!(ty.get_app_fn().kind(), ExprKind::Const(name, _) if name.to_string() == "autoParam")
    }

    /// Lean's `hasOptAutoParams`: does the telescope of `ty` bind an
    /// `optParam`/`autoParam` parameter? The head is reduced once; the
    /// binders under it are read as written.
    fn has_opt_auto_params(&self, ty: &Expr) -> bool {
        let mut cur = self.whnf(ty);
        loop {
            let next = match cur.kind() {
                ExprKind::Pi(_, dom, body) => {
                    if Self::is_opt_or_auto_param(dom) {
                        return true;
                    }
                    body.as_ref().clone()
                }
                _ => return false,
            };
            cur = next;
        }
    }

    /// Lean's `isNextOutParamOfLocalInstanceAndResult`
    /// (`Lean/Elab/App.lean:558-604`), read off the head's whole telescope:
    /// is the application's result type exactly one of the head's own
    /// implicit parameters, and is that parameter an `outParam` argument of
    /// one of the head's instance-implicit binders? Lean then turns
    /// `propagateExpected` off when it adds that implicit argument
    /// (`addImplicitArg`, App.lean:622-631), because the result is determined
    /// by instance resolution, not by the context: `getElem xs i h : elem`
    /// under `[GetElem coll idx elem valid]`, `HAdd.hAdd a b : γ` under
    /// `[HAdd α β γ]`. Propagating there would pin `elem` to the expected type
    /// before the instance is found (`(xs[i] : Int)` with `xs : List Nat`
    /// would search `GetElem (List Nat) Nat Int _`).
    ///
    /// Lean also gates the rule on `Lean.Internal.coeM` being in the
    /// environment, a bootstrapping condition for Lean's own `Prelude`; Clean's
    /// built-in prelude stands in for `Init`, so the rule applies there too.
    /// An argument position counts as an `outParam` when the class's type
    /// wraps its binder in `outParam` (imported classes) or the class registry
    /// records it (the built-in prelude's classes are registered without the
    /// wrapper).
    pub(super) fn result_is_out_param_of_local_instance(&self, fn_type: &Expr) -> bool {
        let mut binders: Vec<(BinderInfo, Expr)> = Vec::new();
        let mut cur = fn_type.clone();
        while let ExprKind::Pi(bi, dom, body) = cur.kind() {
            binders.push((bi.info, dom.as_ref().clone()));
            let next = body.as_ref().clone();
            cur = next;
        }
        // `isResultType`: the codomain is a bound variable naming binder `k`.
        let ExprKind::BVar(idx) = cur.kind() else {
            return false;
        };
        let Some(k) = usize::try_from(*idx)
            .ok()
            .and_then(|idx| binders.len().checked_sub(idx + 1))
        else {
            return false;
        };
        if !matches!(
            binders[k].0,
            BinderInfo::Implicit | BinderInfo::StrictImplicit
        ) {
            return false;
        }
        // `isOutParamOfLocalInstance`: a LATER `[C … x …]` binder with `x` at
        // an `outParam` position of `C`. Inside binder `m`'s domain, binder
        // `k` is the bound variable `m - 1 - k`.
        binders
            .iter()
            .enumerate()
            .skip(k + 1)
            .any(|(m, (info, dom))| {
                *info == BinderInfo::InstImplicit
                    && u32::try_from(m - 1 - k)
                        .is_ok_and(|bvar| self.class_arg_is_out_param(dom, bvar))
            })
    }

    /// Lean's `isOutParamOf`: is the bound variable `bvar` an argument of the
    /// class application `class_app` at one of the class's `outParam`
    /// positions?
    fn class_arg_is_out_param(&self, class_app: &Expr, bvar: u32) -> bool {
        let ExprKind::Const(class, _) = class_app.get_app_fn().kind() else {
            return false;
        };
        let registered: &[usize] = self
            .env
            .get_class_info(class)
            .map_or(&[][..], |info| info.out_params.as_slice());
        let mut class_ty = self.env.get_const(class).map(|info| info.type_.clone());
        for (pos, arg) in class_app.get_app_args().iter().enumerate() {
            let wrapped = match class_ty.as_ref().map(|ty| ty.kind()) {
                Some(ExprKind::Pi(_, dom, _)) => crate::tc_outparam::is_out_param_type(dom),
                _ => false,
            };
            if matches!(arg.kind(), ExprKind::BVar(i) if *i == bvar)
                && (wrapped || registered.contains(&pos))
            {
                return true;
            }
            class_ty = match class_ty.as_ref().map(|ty| ty.kind()) {
                Some(ExprKind::Pi(_, _, body)) => Some(body.as_ref().clone()),
                _ => None,
            };
        }
        false
    }
}
