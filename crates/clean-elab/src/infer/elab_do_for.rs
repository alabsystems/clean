// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ForIn loop elaboration for do-notation (#1818 Phase 4C).
//!
//! Handles `for x in xs do body` by building `ForIn.forIn` applications.
//! When the body contains break/continue, sets up a `DoLoopContext` so
//! that break -> ForInStep.done and continue -> ForInStep.yield directly,
//! matching Lean 4 BuiltinDo/For.lean.
//!
//! When the body reassigns mutable variables, the accumulator beta carries
//! the mutable variable state as a product type instead of PUnit.
//! At each iteration start, the accumulator is destructured into individual
//! let-bindings; at the end (yield/done), current values are packed back.
//!
//! When the body uses `return e` (early return), the accumulator includes
//! an `Option rho` prefix: beta = Prod (Option rho) MutVarProduct. After
//! the loop, the Option component is case-split to propagate or discard
//! the return value.
//!
//! Reuses cached `DoMonadInfo` (m, u, v, PUnit) from the enclosing do-block
//! (#1814), eliminating per-loop fresh metavariable allocation.
//!
//! Reference: ~/lean4-ref/src/Lean/Elab/Do/BuiltinDo/For.lean

use super::elab_do_control;
use super::elab_do_prod;
use super::*;

impl<'a> ElabCtx<'a> {
    /// Desugar `for x in xs do body` in a do block (terminal position).
    ///
    /// Finalizes the loop accumulator before returning.  Even in terminal
    /// position the raw `m beta` tunneling representation is internal: it must
    /// be bound and mapped to the terminal `Unit` result, with any early-return
    /// `Option` discharged by the same post-loop path as a compound loop.
    pub(super) fn elab_do_for(
        &mut self,
        binder: &SurfaceBinder,
        collection: &SurfaceExpr,
        body: &[DoElem],
    ) -> Result<Expr, ElabError> {
        let expected = self.current_expected_type.clone();
        let core = self.elab_do_for_core(binder, collection, body);
        self.current_expected_type = expected.clone();
        let result = core.and_then(|(beta, mut_var_info, return_type, for_in_expr)| {
            self.elab_do_for_post_loop(for_in_expr, &beta, &mut_var_info, &return_type, None)
        });
        self.current_expected_type = expected;
        result
    }

    /// Desugar `for x in xs do body; rest` in a do block (compound position).
    ///
    /// Builds the ForIn.forIn call, then appends a post-loop continuation
    /// that extracts mutable variable state from the accumulator and
    /// case-splits the Option component for early return tunneling.
    ///
    /// Reference: Lean 4 BuiltinDo/For.lean:172-190
    pub(super) fn elab_do_for_compound(
        &mut self,
        binder: &SurfaceBinder,
        collection: &SurfaceExpr,
        body: &[DoElem],
        rest: &[DoElem],
    ) -> Result<Expr, ElabError> {
        let expected = self.current_expected_type.clone();
        let core = self.elab_do_for_core(binder, collection, body);
        self.current_expected_type = expected.clone();
        let result = core.and_then(|(beta, mut_var_info, return_type, for_in_expr)| {
            self.elab_do_for_post_loop(for_in_expr, &beta, &mut_var_info, &return_type, Some(rest))
        });
        self.current_expected_type = expected;
        result
    }

    /// Core for-loop elaboration: builds the ForIn.forIn expression and
    /// returns metadata for post-loop processing.
    ///
    /// Returns (beta, mut_var_info, return_type, for_in_expr).
    #[allow(clippy::type_complexity)]
    fn elab_do_for_core(
        &mut self,
        binder: &SurfaceBinder,
        collection: &SurfaceExpr,
        body: &[DoElem],
    ) -> Result<(Expr, Vec<(String, FVarId, Expr)>, Option<Expr>, Expr), ElabError> {
        // Collection and instance elaboration are nested judgments and may
        // temporarily install their own expected type. Capture the enclosing
        // do-result type before entering either judgment.
        let enclosing_result_alpha = self.expected_do_result_alpha();
        // The collection is a plain value (`List α`, a range, …), not a
        // monadic action: elaborate it with the do-block's own `m β` expected
        // type CLEARED, mirroring the mut lane (B96). Leaving `Id ?β`
        // installed let a literal collection unify `?β := List _` through
        // `Id`'s unfolding, corrupting the block's result type into a List
        // shape (the T2 "expected List Nat" mismatch).
        let saved_expected = self.current_expected_type.take();
        let collection_result = self.elaborate(collection);
        self.current_expected_type = saved_expected;
        let collection_expr = collection_result?;

        // Analyze the body's control effects (#1818 Phase 3).
        let body_control_info = elab_do_control::infer_control_info_seq(body);
        let has_break_or_continue = body_control_info.breaks || body_control_info.continues;
        let has_reassigns = !body_control_info.reassigns.is_empty();

        // Reuse cached monad info: u1 = do_u, u2 = do_v, m = do_m
        let (do_u, do_v, m) = self.get_or_create_monad_info();

        // Collection type ρ and element type α both live at the monad-domain
        // level `do_u`. This matches the standard `ForIn m ρ α` instances
        // (`ForIn m (List α) α` requires ρ = List α : Type u and α : Type u
        // with m : Type u → Type v), and lets `instForInList` resolve the
        // `[ForIn …]` argument below: the instance ties ρ's and α's universes
        // to the monad domain, so independent fresh *params* (which can never
        // be unified) would block resolution. (Track EE.)
        let u_rho = do_u.clone();
        let u_alpha = do_u.clone();

        let for_in_const = Expr::const_(
            Name::from_string("ForIn.forIn"),
            vec![do_u.clone(), do_v.clone(), u_rho.clone(), u_alpha.clone()],
        );

        // ρ : Type u_rho and α : Type u_alpha, i.e. their *types* are
        // `Sort (succ u_rho)` / `Sort (succ u_alpha)`. (The pre-existing code
        // used `Sort u_rho`, which made `ρ`/`α` Prop-typed metavars that could
        // never unify with a real `List _ : Type 0` collection — masked only
        // because nothing previously pinned them. Track EE.)
        let rho = self.fresh_meta(Expr::sort(Level::succ(u_rho.clone())));
        let alpha = self.fresh_meta(Expr::sort(Level::succ(u_alpha.clone())));

        let for_in_class = Expr::const_(
            Name::from_string("ForIn"),
            vec![do_u.clone(), do_v.clone(), u_rho, u_alpha],
        );
        let inst_ty = Expr::app(
            Expr::app(Expr::app(for_in_class, m.clone()), rho.clone()),
            alpha.clone(),
        );
        // Resolve the `[ForIn m ρ α]` instance now (Track EE). The for-loop
        // term is assembled by hand (it never flows through `elab_app`), so the
        // normal deferred-instance machinery never sees this `inst` metavar.
        // Without an assignment it would leak as a free variable and the kernel
        // would reject the enclosing declaration with "contains free variables"
        // (trust-ir `Semantics/Memory.lean` `semGEP`).
        //
        // Pin `ρ` to the collection's type first so the goal is concrete enough
        // for `instForInList : {m} {α} → ForIn m (List α) α` to unify (ρ = List
        // α, α = element). Both gates are mandatory.  A hand-built
        // `ForIn.forIn` application bypasses ordinary deferred instance
        // synthesis, so accepting either failure here would publish an
        // unassigned instance metavariable into the kernel term.
        self.enforce_expr_type(&collection_expr, &rho)?;
        let goal_ty = self.metas.instantiate(&inst_ty);
        let inst =
            self.resolve_instance(&goal_ty)
                .ok_or_else(|| ElabError::FailedToSynthesize {
                    class_name: Name::from_string("ForIn"),
                    goal: format!("{goal_ty:?}"),
                })?;
        self.enforce_expr_type(&inst, &goal_ty)?;

        // Compute mutable variable accumulator (mut_beta, mut_init).
        let (mut_beta, mut_init, mut_var_info) = if has_reassigns {
            self.compute_mut_var_accumulator(&body_control_info)?
        } else {
            // The accumulator `β` must inhabit `Type do_u = Sort (do_u + 1)`, so
            // the placeholder `PUnit` lives one universe ABOVE the cached
            // `PUnit.{do_u}` (which is `Sort do_u`, used elsewhere as a
            // Prop-level placeholder). Using the cached PUnit here made `β` a
            // `Sort do_u` value where `ForIn.forIn` demands `Type do_u`, so the
            // kernel rejected the term with `expected Sort(Succ u), got Sort u`.
            // (Track EE.)
            let punit_level = Level::succ(do_u.clone());
            let punit = Expr::const_(Name::from_string("PUnit"), vec![punit_level.clone()]);
            let punit_unit = Expr::const_(Name::from_string("PUnit.unit"), vec![punit_level]);
            (punit, punit_unit, vec![])
        };

        // Determine return type for early return tunneling.
        // The return type lives in Sort(Succ(do_u)) because the monad m operates
        // on types in Sort(Succ(u)) → Sort(Succ(v)). Using Sort(do_u) causes a
        // universe contradiction when do_u is a fresh param: the same param would
        // need to equal both Zero (from concrete types like Nat) and Succ(Zero).
        let return_type = if body_control_info.returns_early {
            enclosing_result_alpha
                .or_else(|| Some(self.fresh_meta(Expr::sort(Level::succ(do_u.clone())))))
        } else {
            None
        };

        // Extend accumulator to include Option rho when returns_early.
        // beta structure:
        //   no return, no mut: PUnit
        //   no return, mut:    Prod(mutVarTy1, Prod(mutVarTy2, ...))
        //   return, no mut:    Option rho
        //   return, mut:       Prod(Option rho, Prod(mutVarTy1, ...))
        let (beta, init) = if let Some(ref ret_ty) = return_type {
            let ret_level = elab_do_prod::type_universe(self, ret_ty)?;
            let option_ty = Expr::app(
                Expr::const_(Name::from_string("Option"), vec![ret_level.clone()]),
                ret_ty.clone(),
            );
            let none_const = Expr::const_(Name::from_string("Option.none"), vec![ret_level]);
            let none_val = Expr::app(none_const, ret_ty.clone());

            if mut_var_info.is_empty() {
                (option_ty, none_val)
            } else {
                let extended_beta = elab_do_prod::build_prod_type(self, &option_ty, &mut_beta)?;
                let extended_init = elab_do_prod::build_prod_value(
                    self, &option_ty, &mut_beta, none_val, mut_init,
                )?;
                (extended_beta, extended_init)
            }
        } else {
            (mut_beta, mut_init)
        };

        let loop_var_ty = if let Some(ty_surface) = &binder.ty {
            let annotated = self.elaborate(ty_surface)?;
            if !self.try_unify(&annotated, &alpha) && !self.is_def_eq(&annotated, &alpha) {
                return Err(ElabError::TypeMismatch {
                    expected: format!("{:?}", self.metas.instantiate(&alpha)),
                    actual: format!("{annotated:?}"),
                });
            }
            annotated
        } else {
            self.metas.instantiate(&alpha)
        };

        // Push loop variable (x : alpha) and accumulator (acc : beta)
        let fvar_x = self.push_local(binder.name.clone(), loop_var_ty.clone());
        let fvar_acc = self.push_local("__do_acc".to_string(), beta.clone());

        // Destructure accumulator at iteration start.
        // When returns_early AND has_reassigns, the accumulator is
        // Prod(Option rho, MutVarProduct): extract MutVarProduct via Prod.snd.
        let shadow_vars = if has_reassigns {
            let base_expr = if let Some(return_ty) = &return_type {
                let ret_level = elab_do_prod::type_universe(self, return_ty)?;
                let option_ty = Expr::app(
                    Expr::const_(Name::from_string("Option"), vec![ret_level]),
                    return_ty.clone(),
                );
                let mut_sigma = elab_do_prod::build_sigma_type(
                    self,
                    &mut_var_info
                        .iter()
                        .map(|(n, _, ty)| (n.clone(), ty.clone()))
                        .collect::<Vec<_>>(),
                )?;
                elab_do_prod::project_prod(
                    self,
                    &option_ty,
                    &mut_sigma,
                    Expr::fvar(fvar_acc),
                    false,
                )?
            } else {
                Expr::fvar(fvar_acc)
            };
            self.destructure_acc_from_expr(base_expr, &mut_var_info)?
        } else {
            vec![]
        };

        // Set up DoLoopContext when body has break/continue, mutable vars,
        // or early return.
        let needs_loop_ctx =
            has_break_or_continue || has_reassigns || body_control_info.returns_early;
        let outer_loop_ctx = self.do_loop_ctx.take();
        if needs_loop_ctx {
            self.do_loop_ctx = Some(DoLoopContext {
                sigma: beta.clone(),
                acc_fvar: fvar_acc,
                u_level: do_u.clone(),
                mut_vars: shadow_vars
                    .iter()
                    .map(|(name, fvar, ty, _)| (name.clone(), *fvar, ty.clone()))
                    .collect(),
                return_type: return_type.clone(),
            });
        }

        // `elab_do_elems` is fallible after the nested context becomes active.
        // Restore the enclosing loop before propagating either result; otherwise
        // a malformed loop body changes how a later `break`, `continue`, or
        // terminal `return` is elaborated in the reusable context.
        let body_result = self.elab_do_elems(body);
        self.do_loop_ctx = outer_loop_ctx;
        let body_expr = body_result?;

        // When DoLoopContext was active (needs_loop_ctx), terminal elements in
        // the body already produce ForInStep via inline yield wrapping in
        // elab_do_elems. No separate yield sequencing is needed — this fixes
        // the bug where `bind body yield_cont` would overwrite break/continue
        // results (ForInStep.done/yield from break/continue was discarded by
        // the bind, producing ForInStep.yield unconditionally).
        //
        // When needs_loop_ctx is false (simple body without control flow),
        // the body returns a normal monadic action and needs explicit yield.
        let mut sequenced_body = if needs_loop_ctx {
            body_expr
        } else {
            // Simple body (no break/continue/return/reassign): sequence
            //   body_expr >>= fun _ => pure (ForInStep.yield acc)
            // The step's result type is `ForInStep β`, NOT the do-block's
            // overall result `α`. `mk_pure_app`/`mk_bind_app` read the
            // do-block's expected `α`/`β` (e.g. `Unit` for a `Sem Unit` loop),
            // which is wrong here — using them produced `pure : m Unit` wrapping
            // a `ForInStep β` payload and a bind whose result was `m Unit`, so
            // the kernel saw `ForInStep.yield β <loop-var>` (type `ForInStep β`)
            // where `α` was expected. Build both `Bind.bind`/`Pure.pure`
            // explicitly at `ForInStep β`. (Track EE.)
            let acc_value = self.build_yield_acc_value(fvar_acc, &shadow_vars)?;
            let yield_const =
                Expr::const_(Name::from_string("ForInStep.yield"), vec![do_u.clone()]);
            let yield_expr = Expr::app(Expr::app(yield_const, beta.clone()), acc_value);
            let for_in_step_beta = Expr::app(
                Expr::const_(Name::from_string("ForInStep"), vec![do_u.clone()]),
                beta.clone(),
            );

            // pure (ForInStep.yield acc) : m (ForInStep β)
            let pure_const = Expr::const_(
                Name::from_string("Pure.pure"),
                vec![do_u.clone(), do_v.clone()],
            );
            let yield_pure = Expr::apps(
                pure_const,
                [m.clone(), for_in_step_beta.clone(), yield_expr],
            );

            // The discarded result binder is typed at the bind's `α` (the inner
            // type of `body_expr`). This is evidence carried by the action's
            // authenticated `m α` type, not a convention: defaulting to `Unit`
            // can turn an ill-typed body into a hand-built `Bind.bind` whose
            // continuation has the wrong domain.
            let bind_alpha = self
                .try_extract_bind_inner_type(&body_expr)
                .ok_or_else(|| ElabError::TypeMismatch {
                    expected: "for-loop body action of type `m α`".into(),
                    actual: self
                        .infer_type(&body_expr)
                        .map(|ty| format!("{:?}", self.metas.instantiate(&ty)))
                        .unwrap_or_else(|err| format!("untypable body ({err})")),
                })?;
            let fvar_discard = self.push_local("_".to_string(), bind_alpha.clone());
            let yield_abs = yield_pure.abstract_fvar(fvar_discard);
            self.pop_local();
            let yield_cont = Expr::lam(BinderInfo::Default, bind_alpha.clone(), yield_abs);

            // body_expr >>= yield_cont : m (ForInStep β)
            let bind_const = Expr::const_(
                Name::from_string("Bind.bind"),
                vec![do_u.clone(), do_v.clone()],
            );
            Expr::apps(
                bind_const,
                [
                    m.clone(),
                    bind_alpha,
                    for_in_step_beta,
                    body_expr,
                    yield_cont,
                ],
            )
        };

        // Fix #3419: Instantiate metas before abstracting FVars.
        // The body_expr (and thus sequenced_body) was elaborated with fvar_x,
        // fvar_acc, and shadow_vars in scope. Metas resolved during elaboration
        // may hide these FVars; instantiate first so abstract_fvar can find them.
        sequenced_body = self.metas.instantiate(&sequenced_body);

        // Pop shadow locals (in reverse order) wrapping in let-bindings.
        for (shadow_name, shadow_fvar, shadow_ty, proj_expr) in shadow_vars.iter().rev() {
            let abs = sequenced_body.abstract_fvar(*shadow_fvar);
            sequenced_body = Expr::let_named(
                Name::from_string(shadow_name),
                shadow_ty.clone(),
                proj_expr.clone(),
                abs,
                false,
            );
            self.pop_local();
        }

        self.pop_local(); // pop accumulator
        self.pop_local(); // pop loop variable

        // Abstract both parameters to build the body lambda:
        //   fun (x : alpha) (acc : beta) => … body … pure (ForInStep.yield …)
        // matching `ForIn.forIn`'s step `(α → β → m (ForInStep β))`: the loop
        // variable `x` is the OUTER binder and the accumulator `acc` the INNER.
        // `abstract_fvar` shifts existing BVars up, so to land `x` at BVar(1)
        // (outer) and `acc` at BVar(0) (inner) we must abstract `x` FIRST, then
        // `acc`. (The previous order abstracted `acc` first, swapping the two
        // binders' types — `acc : alpha` / `x : beta` — which only surfaced once
        // the term actually reached the kernel via the new `ForIn.forIn`. The
        // matching `lam(loop_var_ty, lam(beta, …))` nesting is unchanged.)
        let body_abs = sequenced_body.abstract_fvar(fvar_x).abstract_fvar(fvar_acc);
        let inner_lam = Expr::lam(BinderInfo::Default, beta.clone(), body_abs);
        let outer_lam = Expr::lam(BinderInfo::Default, loop_var_ty, inner_lam);

        // Build: @ForIn.forIn.{u1,u2,u,v} m rho alpha inst beta xs init body
        let e = Expr::app(for_in_const, m);
        let e = Expr::app(e, rho);
        let e = Expr::app(e, alpha);
        let e = Expr::app(e, inst);
        let e = Expr::app(e, beta.clone());
        let e = Expr::app(e, collection_expr);
        let e = Expr::app(e, init);
        let for_in_expr = Expr::app(e, outer_lam);

        Ok((beta, mut_var_info, return_type, for_in_expr))
    }

    /// Compute the accumulator type (beta) and initial value (init) from
    /// mutable variable info. Returns (beta, init, mut_var_info) where
    /// mut_var_info is the ordered list of (name, fvar_id, type).
    ///
    /// Reference: Lean 4 BuiltinDo/For.lean -- `initMutVars` computes beta/init.
    #[allow(clippy::type_complexity)]
    fn compute_mut_var_accumulator(
        &mut self,
        control_info: &elab_do_control::ControlInfo,
    ) -> Result<(Expr, Expr, Vec<(String, FVarId, Expr)>), ElabError> {
        let mut mut_var_info: Vec<(String, FVarId, Expr)> = Vec::new();
        for name in &control_info.reassigns {
            let found = self
                .locals
                .iter()
                .rev()
                .find(|(n, _, _)| n == name)
                .map(|(n, fvar, ty)| (n.clone(), *fvar, ty.clone()))
                .ok_or_else(|| ElabError::Unsupported {
                    feature: format!(
                        "for-loop reassignment `{name}` cannot be threaded: the mutable local is not in the surrounding loop scope"
                    ),
                })?;
            mut_var_info.push(found);
        }

        mut_var_info.sort_by(|a, b| a.0.cmp(&b.0));

        if mut_var_info.is_empty() {
            return Err(ElabError::InternalInvariant(
                "mutable for-loop accumulator requested without reassignment evidence".into(),
            ));
        }

        let sigma_types: Vec<(String, Expr)> = mut_var_info
            .iter()
            .map(|(name, _, ty)| (name.clone(), ty.clone()))
            .collect();
        let beta = elab_do_prod::build_sigma_type(self, &sigma_types)?;

        let sigma_vals: Vec<(String, Expr, Expr)> = mut_var_info
            .iter()
            .map(|(name, fvar, ty)| (name.clone(), Expr::fvar(*fvar), ty.clone()))
            .collect();
        let init = elab_do_prod::build_sigma_value(self, &sigma_vals)?;

        Ok((beta, init, mut_var_info))
    }

    /// Destructure an accumulator expression into individual let-bound locals
    /// for each mutable variable.
    ///
    /// Takes an arbitrary expression as the base (needed when the full
    /// accumulator includes an Option rho prefix that must be skipped).
    /// Pushes new locals that shadow the original mutable variables.
    /// Caller must pop these in reverse order after building the body.
    pub(super) fn destructure_acc_from_expr(
        &mut self,
        acc_expr: Expr,
        mut_var_info: &[(String, FVarId, Expr)],
    ) -> Result<Vec<(String, FVarId, Expr, Expr)>, ElabError> {
        if mut_var_info.is_empty() {
            return Ok(vec![]);
        }

        let sigma_types: Vec<(String, Expr)> = mut_var_info
            .iter()
            .map(|(n, _, ty)| (n.clone(), ty.clone()))
            .collect();
        let projections = elab_do_prod::destructure_sigma(self, &sigma_types, acc_expr)?;

        let mut shadow_vars = Vec::with_capacity(projections.len());
        for (i, (name, proj_expr)) in projections.into_iter().enumerate() {
            let ty = mut_var_info[i].2.clone();
            let shadow_fvar = self.push_local(name.clone(), ty.clone());
            shadow_vars.push((name, shadow_fvar, ty, proj_expr));
        }

        Ok(shadow_vars)
    }

    /// Build the accumulator value for fall-through yield when no
    /// DoLoopContext is active (simple case).
    fn build_yield_acc_value(
        &self,
        fvar_acc: FVarId,
        shadow_vars: &[(String, FVarId, Expr, Expr)],
    ) -> Result<Expr, ElabError> {
        if shadow_vars.is_empty() {
            return Ok(Expr::fvar(fvar_acc));
        }

        let vars: Vec<(String, Expr, Expr)> = shadow_vars
            .iter()
            .map(|(name, fvar, ty, _)| (name.clone(), Expr::fvar(*fvar), ty.clone()))
            .collect();
        elab_do_prod::build_sigma_value(self, &vars)
    }
}
