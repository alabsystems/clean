// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Do-notation bind/pure desugaring primitives (#1818).
//!
//! Contains the core monadic desugaring functions:
//! - `elab_do_bind`: `let x <- e; rest` → `Bind.bind e (fun x => rest)`
//! - `elab_do_let`: `let x := e; rest` → `let x := e in rest`
//! - `elab_pure`: `return e` → `Pure.pure e`
//! - `elab_do_bind_expr`: like bind but for already-elaborated expressions
//!
//! Split from elab_do.rs to stay under 500-line limit.
//!
//! Reference: ~/lean4-ref/src/Lean/Elab/Do/Basic.lean

use super::*;

impl<'a> ElabCtx<'a> {
    /// Desugar `let x <- action; rest` to `@Bind.bind.{u,v} m α β action (fun x => rest)`
    pub(super) fn elab_do_bind(
        &mut self,
        binder: &SurfaceBinder,
        action: &SurfaceExpr,
        rest: &[DoElem],
    ) -> Result<Expr, ElabError> {
        // Elaborate the monadic action, then resolve implicit args (#3419).
        //
        // Plain `elaborate` returns a bare constant for polymorphic actions like
        // `StateT.get` — no implicits filled in. Its type is a Pi, not App, so
        // `try_extract_bind_inner_type` fails and the bind variable gets a fresh
        // metavar that never resolves, causing downstream field access (`s.counter`)
        // to fail.
        //
        // After plain elaboration, we apply implicit args to match the expected
        // monadic type `m ?α`. This fills in implicits (e.g., σ = MyState) so the
        // action's type becomes `App(m, α)` which `try_extract_bind_inner_type`
        // can decompose. We use `apply_implicit_to_expected_type` directly rather
        // than `elaborate_with_expected_type` to avoid changing `current_expected_type`
        // which would interfere with downstream `expected_do_result_components` calls.
        //
        // The action's expected type is the action's *own* monadic type `m α`
        // (α = the binder's value type), NEVER the do-block's overall result type
        // `m β`. Leaving `current_expected_type` = `m β` in scope leaks `β` into a
        // `match`-action's branch-type inference: each arm body is elaborated
        // against `m β`, so the casesOn motive is built as `fun _ => m β` even
        // though every arm actually produces `m α`. The kernel then rejects the
        // alternatives (`m α` vs the `m β` motive — the `Nat` vs `ValueId` /
        // `Nat` vs `PUnit` Type-mismatch cluster: `let addr ← match ptrVal with …`
        // in semAtomicLoad/RMW/Store/CmpXchg and the Memory/ARC/Borrow/Aggregate
        // siblings, Track trk-b-domonad).
        //
        // The expected type we *do* want is `m ?α`: the do-block's monad applied
        // to a FRESH element metavar. Pinning the monad head `m` (rather than
        // clearing the expected type to `None`) keeps a polymorphic `pure …` /
        // `throw …` / `Sem.throwUB …` action resolving its own `?m := Sem` — a bare
        // `None` leaves both `?m` and `?α` unconstrained and the metavars leak into
        // the kernel term ("contains free variables"). Leaving `?α` *fresh* lets a
        // `match` action solve it from the arm bodies (`a : Nat` ⇒ `?α := Nat`)
        // instead of being forced to the do-block's `β`. When the binder is
        // explicitly typed we pin `?α := annotation` directly. Mirrors
        // `elab_do_if`'s condition handling (Track KL).
        let action_expected_ty = self
            .do_monad_info
            .as_ref()
            .map(|info| info.m.clone())
            .map(|m| {
                let alpha = match binder.ty.as_ref() {
                    Some(ty_surface) => self
                        .elaborate(ty_surface)
                        .unwrap_or_else(|_| self.fresh_meta(Expr::type_())),
                    None => self.fresh_meta(Expr::type_()),
                };
                Expr::app(m, alpha)
            });
        let saved_expected = self.current_expected_type.take();
        self.current_expected_type = action_expected_ty;
        let action_result = self.elaborate(action);
        self.current_expected_type = saved_expected;
        let mut action_expr = action_result?;
        if let Some(info) = &self.do_monad_info {
            let u = info.u.clone();
            let m = info.m.clone();
            let alpha = self.fresh_meta(Expr::sort(Level::succ(u)));
            let expected_action_ty = Expr::app(m, alpha);
            if let Ok(resolved) =
                self.apply_implicit_to_expected_type(&action_expr, &expected_action_ty)
            {
                action_expr = resolved;
            }
        }

        // Determine the binder type for the continuation variable.
        // If annotated, use the annotation. Otherwise, try to extract the
        // inner type from the action's monadic type (action : m α → use α).
        // This avoids leaving an unresolved metavar that causes downstream
        // match elaboration to fail on opaque FVars (#1902).
        let bind_var_ty = if let Some(ty_surface) = &binder.ty {
            self.elaborate(ty_surface)?
        } else {
            self.try_extract_bind_inner_type(&action_expr)
                .unwrap_or_else(|| self.fresh_meta(Expr::type_()))
        };

        // Build continuation: fun x => rest_desugared
        // Push x as a local, elaborate rest, pop, abstract to de Bruijn.
        let fvar = self.push_local(binder.name.clone(), bind_var_ty.clone());
        let rest_expr = self.elab_do_elems(rest)?;
        self.pop_local();
        // Fix #3409: Instantiate metas BEFORE abstracting FVars.
        // Same pattern as #443 fix in elab_def_body.rs: if a metavariable in
        // rest_expr was resolved to an expression containing the FVar (e.g.,
        // `?m := App(f, FVar(x))`), we must substitute the meta first so the
        // FVar is visible for abstraction. Otherwise, abstract_fvar won't find
        // the FVar (it's hidden inside the uninstantiated meta), and after later
        // instantiation the FVar leaks as a free variable in the kernel term.
        let rest_inst = self.metas.instantiate(&rest_expr);
        let continuation = Expr::lam(
            BinderInfo::Default,
            bind_var_ty,
            rest_inst.abstract_fvar(fvar),
        );

        // Build: @Bind.bind.{u,v} m α β action continuation
        Ok(self.mk_bind_app(action_expr, continuation))
    }

    /// Desugar `let x := v; rest` to `let x := v in rest_desugared`
    ///
    /// The local binding is pushed so that rest elements can reference `x`.
    pub(super) fn elab_do_let(
        &mut self,
        binder: &SurfaceBinder,
        val: &SurfaceExpr,
        rest: &[DoElem],
    ) -> Result<Expr, ElabError> {
        // The do-block's expected monad type `m β` (`current_expected_type`)
        // belongs to the CONTINUATION (`rest`), NOT to this plain let's bound
        // value. In `do … let x := v; rest`, `v` has its own (annotated or
        // inferred) type while `rest` is what produces `m β`. A plain
        // `self.elaborate(val)` would (a) leak `m β` as the value's expected
        // type and (b) mutate `current_expected_type` as a side effect (it is
        // threaded mutably through `elaborate`), so the subsequent
        // `elab_do_elems(rest)` would run with a stale/wrong expected type. That
        // strands the do-block's `β`/`α` reads in `mk_bind_app`/`mk_pure_app`,
        // producing a continuation whose result type unifies as `Const vs Pi`
        // against the unfolded `Sem β` transformer stack (`semAlloca` /
        // `semLoad` / `semAtomic*` and the Memory/Atomic siblings — Track
        // trk-m-semmonad). Mirror the term-level `elab_let` (elab_core.rs):
        // clear the expected type for the value, restore it for `rest`.
        // `elaborate_with_expected_type` save/restores `current_expected_type`
        // itself, so after each value call the do-block expected type is intact.
        let body_expected = self.current_expected_type.clone();

        // Elaborate type and value, avoiding double elaboration when inferred.
        let (ty, val_expr) = if let Some(ty_surface) = &binder.ty {
            let ty_expr = self.elaborate(ty_surface)?;
            let val_expr = self.elaborate_with_expected_type(val, Some(ty_expr.clone()))?;
            (ty_expr, val_expr)
        } else {
            let val_expr = self.elaborate_with_expected_type(val, None)?;
            let ty = self.infer_type(&val_expr)?;
            (ty, val_expr)
        };

        // Restore the do-block's expected monad type for the continuation.
        self.current_expected_type = body_expected;

        // Push local so rest elements can reference this binding
        let fvar = self.push_local(binder.name.clone(), ty.clone());
        let rest_expr = self.elab_do_elems(rest)?;
        self.pop_local();

        // Fix #3409: Instantiate metas BEFORE abstracting FVars (same as bind).
        let rest_inst = self.metas.instantiate(&rest_expr);
        let body_abs = rest_inst.abstract_fvar(fvar);

        Ok(Expr::let_named(
            Name::from_string(&binder.name),
            ty,
            val_expr,
            body_abs,
            false,
        ))
    }

    /// Desugar `return e` to `@Pure.pure.{u,v} m α e`
    pub(super) fn elab_pure(&mut self, expr: &SurfaceExpr) -> Result<Expr, ElabError> {
        // Elaborate the payload against the monad's *inner* result type `α`
        // (from `do`'s expected `m α`) when available. Without an expected type
        // a leading-dot constructor in the payload (`pure (.Continue …)` /
        // `return .Ret …` — Control/Borrow `StepResult`) cannot resolve its
        // inductive head, failing with `Unknown identifier: .Continue`. The
        // bare-value `elaborate` path drops the expected type that the surrounding
        // `pure (.ctor …)` application form already threads (elab_app dot-ctor
        // pre-unify); the do-notation desugaring must thread it too.
        let val = match self.expected_do_result_alpha() {
            Some(alpha) => self.elaborate_with_expected_type(expr, Some(alpha))?,
            None => self.elaborate(expr)?,
        };
        Ok(self.mk_pure_app(val))
    }

    /// Like `elab_do_bind`, but takes an already-elaborated expression instead of a SurfaceExpr.
    /// Used for sequencing compound do-elements (if, for, match) with the rest of the block.
    pub(super) fn elab_do_bind_expr(
        &mut self,
        binder: &SurfaceBinder,
        action_expr: Expr,
        rest: &[DoElem],
    ) -> Result<Expr, ElabError> {
        let bind_var_ty = if let Some(ty_surface) = &binder.ty {
            self.elaborate(ty_surface)?
        } else {
            self.try_extract_bind_inner_type(&action_expr)
                .unwrap_or_else(|| self.fresh_meta(Expr::type_()))
        };

        let fvar = self.push_local(binder.name.clone(), bind_var_ty.clone());
        let rest_expr = self.elab_do_elems(rest)?;
        self.pop_local();
        // Fix #3409: Instantiate metas BEFORE abstracting FVars (same as bind).
        let rest_inst = self.metas.instantiate(&rest_expr);
        let continuation = Expr::lam(
            BinderInfo::Default,
            bind_var_ty,
            rest_inst.abstract_fvar(fvar),
        );

        // Build: @Bind.bind.{u,v} m α β action continuation
        Ok(self.mk_bind_app(action_expr, continuation))
    }

    /// Try to extract the inner type `α` from a monadic action's type `m α`.
    ///
    /// When the action has type `App(m, α)`, returns `Some(α)`. This provides
    /// a concrete type for the bind continuation variable, avoiding unresolved
    /// metavars that block downstream match elaboration (#1902).
    ///
    /// Checks the unreduced type FIRST to preserve monadic abbreviations (#3419).
    /// For example, `incCounter : MySem Nat` has type `App(MySem, Nat)` before
    /// whnf. After whnf, `MySem Nat` unfolds to `MyState → Except MyError (Prod Nat MyState)`
    /// which is a Pi, not an App, and the inner type extraction would fail.
    pub(super) fn try_extract_bind_inner_type(&mut self, action: &Expr) -> Option<Expr> {
        let action_ty = self.infer_type(action).ok()?;

        // Try unreduced first to preserve monadic abbreviations: `m α` keeps the
        // head monad constant/variable so a later `try_extract` decomposition or
        // a downstream field access still sees `App(m, α)` (#3419).
        //
        // Exception: a *beta-redex* type `(fun x => body) v` is NOT `m α`. It is
        // the casesOn motive applied to the scrutinee — exactly the type
        // `elab_match` synthesizes for a `match` action (`let x ← match …`). For
        // such a redex the unreduced App *argument* is the scrutinee VALUE, not
        // the monadic inner type; returning it binds the continuation variable at
        // the scrutinee's type (e.g. `Value`) and threads a value where a type
        // belongs, producing the `Discriminant(Const) vs Discriminant(FVar)` /
        // `Sort vs Value` kernel rejection (Track QR:
        // semLoad/semStore/semGEP/semDealloc). When the application head is a
        // lambda we instead recover `α` by reducing/unifying below.
        let head_is_lam = matches!(action_ty.get_app_fn().kind(), ExprKind::Lam(..));
        if let ExprKind::App(_, arg) = action_ty.kind() {
            if !head_is_lam {
                return Some((**arg).clone());
            }
        }

        // Beta-redex (casesOn motive applied to the scrutinee) or a monadic
        // abbreviation that only exposes `m α` after head reduction. WHNF reduces
        // the redex to the action's true monadic result type (`branch_ty`). For a
        // monad like `Sem := StateT σ (Except ε)` that type is the *unfolded*
        // transformer stack (a `Pi`), not an `App(Sem, α)`, so the bare App-arg
        // read does not recover `α`. Recover `α` monad-generically by unifying the
        // reduced type against `m ?α` (the do-block monad applied to a fresh
        // value-type metavariable) and reading the solved metavariable.
        let ty = self.whnf(&action_ty);
        if head_is_lam {
            let monad = self
                .do_monad_info
                .as_ref()
                .map(|info| (info.m.clone(), info.u.clone()));
            if let Some((m, u)) = monad {
                let alpha = self.fresh_meta(Expr::sort(Level::succ(u)));
                let candidate = Expr::app(m, alpha.clone());
                // Use the metavar-assigning unifier (not the rigid kernel
                // `is_def_eq`, which never solves `?α`): unifying `m ?α` against
                // the reduced action type whnf-unfolds the monad transformer
                // stack and assigns `?α` to the genuine value type.
                if self.try_unify(&candidate, &ty) {
                    let solved = self.metas.instantiate(&alpha);
                    let still_unsolved = matches!(
                        solved.kind(),
                        ExprKind::FVar(id) if MetaState::from_fvar(*id).is_some()
                    );
                    if !still_unsolved {
                        return Some(solved);
                    }
                }
            }
        }
        match ty.kind() {
            ExprKind::App(_, arg) => Some((**arg).clone()),
            _ => None,
        }
    }
}
