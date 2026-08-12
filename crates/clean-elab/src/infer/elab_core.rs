// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core elaboration helpers for identifiers, universes, and binder forms.

use super::*;
use crate::agent_diagnostics::nearest_string_candidates;
use crate::stack_safe;
use clean_kernel::sorry::{create_sorry_term_with_kind_at_level, SorryKind};
use clean_kernel::ConstantKind;

impl<'a> ElabCtx<'a> {
    /// `inferInstance` synthesizes an instance of the contextual expected type.
    /// A missing expected type or instance is a hard elaboration error; no
    /// placeholder term is fabricated.
    pub(in crate::infer) fn elab_infer_instance(&mut self) -> Result<Expr, ElabError> {
        let expected =
            self.current_expected_type
                .clone()
                .ok_or_else(|| ElabError::Unsupported {
                    feature:
                        "`inferInstance` without a known expected type (use `inferInstanceAs T`)"
                            .to_string(),
                })?;
        let expected = self.metas.instantiate(&expected);
        self.resolve_instance(&expected)
            .ok_or_else(|| ElabError::FailedToSynthesizeInstance {
                goal: format!("{expected:?}"),
            })
    }

    /// Classify a conditional guard after elaboration.
    ///
    /// Lean conditionals accept either `Bool` (through the Bool-to-Prop lane) or
    /// a term whose type is exactly `Prop`. Treating every non-Bool expression
    /// as a proposition defers an ill-typed `ite` to a distant kernel failure
    /// and can even ask instance synthesis for nonsense such as
    /// `Decidable (Type)`. Reject that category error at the elaboration
    /// boundary. Returns `true` for Bool and `false` for Prop.
    pub(in crate::infer) fn condition_is_bool(&self, condition: &Expr) -> Result<bool, ElabError> {
        let condition_ty = self.infer_type(condition)?;
        let condition_ty = self.whnf(&condition_ty);
        match condition_ty.kind() {
            ExprKind::Const(name, _) if *name == Name::from_string("Bool") => Ok(true),
            ExprKind::Sort(level) if level.normalize() == Level::Zero => Ok(false),
            _ => Err(ElabError::TypeMismatch {
                expected: "conditional guard of type Bool or Prop".to_string(),
                actual: format!("{condition_ty:?}"),
            }),
        }
    }

    pub(in crate::infer) fn resolve_decidable(&mut self, prop: &Expr) -> Result<Expr, ElabError> {
        let decidable_ty = Expr::app(
            Expr::const_(Name::from_string("Decidable"), vec![]),
            prop.clone(),
        );
        self.resolve_instance(&decidable_ty)
            .ok_or_else(|| ElabError::FailedToSynthesize {
                class_name: Name::from_string("Decidable"),
                goal: format!("{decidable_ty:?}"),
            })
    }

    fn sorry_goal_type(&mut self) -> Expr {
        self.current_expected_type
            .as_ref()
            .map(|ty| {
                let ty = self.metas.instantiate(ty);
                self.metas.instantiate_levels(&ty)
            })
            .unwrap_or_else(|| self.fresh_meta(Expr::type_()))
    }

    fn elab_sorry_with_kind(&mut self, kind: SorryKind) -> Result<Expr, ElabError> {
        let goal_ty = self.sorry_goal_type();
        // The elaborator may know local context and unresolved level assignments.
        // A failed sort inference is an elaboration error; fabricating universe
        // zero would change the judgment carried by the explicit trust marker.
        let goal_level = self.infer_sort(&goal_ty)?;
        Ok(create_sorry_term_with_kind_at_level(
            self.env, &goal_ty, kind, goal_level,
        ))
    }

    pub(super) fn elab_explicit_sorry(&mut self) -> Result<Expr, ElabError> {
        self.elab_sorry_with_kind(SorryKind::Explicit)
    }
    pub(super) fn elab_synthetic_sorry(&mut self) -> Result<Expr, ElabError> {
        self.elab_sorry_with_kind(SorryKind::Synthetic)
    }

    fn resolve_expected_ctor_ident(&mut self, ctor_suffix: &str) -> Option<Expr> {
        let mut expected_ty = self.current_expected_type.clone()?;
        loop {
            let expected_ty_whnf = self.whnf(
                &self
                    .metas
                    .instantiate_levels(&self.metas.instantiate(&expected_ty)),
            );
            if let ExprKind::Pi(_, domain, _) = expected_ty_whnf.kind() {
                expected_ty = domain.as_ref().clone();
                continue;
            }
            let ctor_name = Name::append(
                &Name::from_string(&self.get_type_name(&expected_ty_whnf).ok()?),
                ctor_suffix,
            );
            let levels: Vec<_> = self
                .env
                .get_const(&ctor_name)?
                .level_params
                .iter()
                .map(|_| self.fresh_universe_param())
                .collect();
            return Some(Expr::const_(ctor_name, levels));
        }
    }

    pub(super) fn elab_let(
        &mut self,
        binder: &SurfaceBinder,
        val: &SurfaceExpr,
        body: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        // The surrounding expected type belongs to the *body* of the `let`, not
        // its bound value: in `let x := v; body : T`, it is `body` that has
        // type `T`, while `v` has the binder's own (annotated or inferred)
        // type. Carrying the body's expected type into the value elaboration
        // leaks the wrong target — e.g. `Except E α` from the enclosing match —
        // and elaborating the value mutates `current_expected_type` so that the
        // body (often the `match` itself) is then elaborated with a stale/wrong
        // expected type. That breaks anonymous-constructor (`.ok`/`.error`) dot
        // resolution inside the match arms ("cannot unify ... Const vs App").
        // Clear it for the value; restore it for the body. (Track KL)
        let body_expected = self.current_expected_type.clone();

        // Elaborate type and value, avoiding double elaboration when type is inferred
        let (ty, val_expr) = if let Some(ty) = &binder.ty {
            // Explicit type annotation provided: the value is elaborated against
            // its own annotated type, not the body's expected type.
            let ty_expr = self.elaborate(ty)?;
            let val_expr = self.elaborate_with_expected_type(val, Some(ty_expr.clone()))?;
            (ty_expr, val_expr)
        } else {
            // Infer type from value - elaborate once and reuse. No expected type
            // applies to an unannotated `let` value.
            let val_expr = self.elaborate_with_expected_type(val, None)?;
            let ty = self.infer_type(&val_expr)?;
            (ty, val_expr)
        };

        // Push local, elaborate body with the let's expected type restored, then
        // abstract.
        let fvar = self.push_local(binder.name.clone(), ty.clone());
        let body_expr = self.elaborate_with_expected_type(body, body_expected)?;
        self.pop_local();
        // SOUNDNESS: instantiate assigned metavars/levels in the body before
        // abstracting `fvar` so any assignment mentioning a local is substituted
        // rather than left as a loose fvar in the closed `let`. TCB-neutral —
        // no-op absent assignments, and the kernel re-checks the result.
        let body_expr = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&body_expr));
        let body_abs = body_expr.abstract_fvar(fvar);
        let name = Name::from_string(&binder.name);
        Ok(Expr::let_named(name, ty, val_expr, body_abs, false))
    }

    /// Elaborate `let rec f : T := v in e`.
    ///
    /// Three-way dispatch, mirroring Lean's `where`/`let rec` semantics
    /// (`where` desugars to a leading `let rec` group —
    /// `Lean/Elab/Binders.lean:472-476 expandWhereDecls`; the group is
    /// elaborated by `Lean/Elab/LetRec.lean:140 elabLetRec` and each decl is
    /// lifted to a top-level auxiliary definition,
    /// `Lean/Elab/LetRec.lean:110 registerLetRecsToLift`):
    ///
    /// 1. **Non-recursive** (`v` never mentions `f`, shadowing-aware): a plain
    ///    `let f : T := v in e`. Lean lifts a non-self-referential `let rec`
    ///    decl to a plain auxiliary definition — no fixpoint is involved — so
    ///    a plain `let` binding of the independently elaborated value is
    ///    exactly its semantics. This is the common `where` helper shape
    ///    (audit d04).
    ///
    /// 2. **Structurally recursive**: lift `f` to a real self-contained
    ///    recursive *value* `V : T` through the existing structural-recursion
    ///    machinery (the same path that lowers top-level recursive `def`s via
    ///    `<Inductive>.rec`), and bind it with an ordinary non-recursive
    ///    `let f : T := V in e`. The kernel re-checks `V`.
    ///
    ///    `V` may legitimately reference outer locals (e.g. a `let rec go`
    ///    inside `def Memory.readBytes (mem) := …` that reads `mem`, or a
    ///    `where` helper reading the parent's binders — Lean's `where` decls
    ///    likewise see the parent's binders because the generated `let rec`
    ///    sits inside them, `Lean/Elab/MutualDef.lean:332-397`): those locals
    ///    remain in scope while `V` is elaborated, so they stay bound by the
    ///    enclosing binder. No explicit capture-lifting is required because
    ///    `let f := V in e` keeps `V` in the same local context.
    ///
    /// 3. **Recursive but not structurally liftable** (no decreasing
    ///    parameter, zero-parameter self-reference, …): FAIL LOUD with
    ///    [`ElabError::WhereLetRecUnsupported`]. The pre-2026-07 fallback
    ///    bound `f` to a synthetic `sorry` and let the enclosing declaration
    ///    register axiom-tainted (audit d04's "registers-anyway" trap); that
    ///    fallback is eliminated.
    pub(super) fn elab_let_rec(
        &mut self,
        binder: &SurfaceBinder,
        val: &SurfaceExpr,
        body: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        // Non-recursive binding: exactly a plain `let`. Two complementary,
        // shadowing-aware detectors decide "does `v` mention `f`":
        //  - the structural-recursion call detector (finds APPLIED self-calls
        //    anywhere, including match arms and do-blocks), and
        //  - the free-ident collector (finds BARE, non-applied self-mentions
        //    such as `let rec c : Nat := c`).
        // The second is essential: a bare self-mention routed to the plain
        // `let` path would leave `f` unresolved in the value, where decl-mode
        // auto-implicit insertion silently captures it as an extra implicit
        // binder — registering a declaration whose signature differs from the
        // one written. Both detectors must clear the value before it is
        // treated as non-recursive.
        let mentions_self = structural::detect_recursion_with_params(&binder.name, val, &[])
            .is_recursive
            || crate::where_desugar_ext::collect_free_idents(val).contains(&binder.name);
        if !mentions_self {
            return self.elab_let(binder, val, body);
        }

        // Recursive binding: lift to a real recursive value, or fail loud.
        if let Some(result) = self.try_elab_let_rec_lifted(binder, val, body)? {
            return Ok(result);
        }
        Err(ElabError::WhereLetRecUnsupported {
            name: binder.name.clone(),
            shape: self.describe_unliftable_let_rec(binder, val),
        })
    }

    /// True iff every detected self-call passes the parameter at `pos`
    /// through unchanged — i.e. the "decreasing" argument never actually
    /// decreases. Shared by the lift gate and the loud-error description.
    fn all_calls_pass_param_unchanged(
        calls: &[structural::RecursiveCall],
        param_names: &[String],
        pos: usize,
    ) -> bool {
        param_names.get(pos).is_some_and(|param| {
            calls.iter().all(|call| {
                matches!(call.args.get(pos),
                         Some(structural::RecursiveArg::Var(name)) if name == param)
            })
        })
    }

    /// Describe why a *recursive* `let rec`/`where` binding could not be
    /// lifted through the structural-recursion machinery. Used only to build
    /// the loud [`ElabError::WhereLetRecUnsupported`] message.
    fn describe_unliftable_let_rec(&self, binder: &SurfaceBinder, val: &SurfaceExpr) -> String {
        let mut params: Vec<String> = Vec::new();
        let mut inner = val;
        while let SurfaceExpr::Lambda(_, bs, b) = inner {
            params.extend(bs.iter().map(|p| p.name.clone()));
            inner = b;
        }
        if params.is_empty() {
            return "self-recursive with no parameters (a value-level fixpoint has no \
                    terminating interpretation)"
                .to_string();
        }
        let info = structural::detect_recursion_with_params(&binder.name, inner, &params);
        // Mirrors the lift gate below (B97): a name-equality "unchanged"
        // verdict is discounted when a whole-body-match arm rebinds the
        // parameter, so shapes that ATTEMPTED the lift and failed for another
        // reason fall to the generic description instead.
        let no_descent = info.decreasing_arg.is_none()
            || info.decreasing_arg.is_some_and(|pos| {
                Self::all_calls_pass_param_unchanged(&info.calls, &params, pos)
                    && !structural::whole_body_match_rebinds_param(inner, &params, pos)
            });
        if info.is_recursive && no_descent {
            return "recursive, but no structurally decreasing parameter was found \
                    (well-founded recursion is not supported for `where`/`let rec` \
                    local definitions)"
                .to_string();
        }
        "recursive, but not liftable through the structural-recursion machinery".to_string()
    }

    /// Attempt the structural-recursion lift for `let rec f := v in e`.
    ///
    /// Returns `Ok(Some(term))` on success, `Ok(None)` when the binding is not
    /// a liftable structurally recursive function (the caller then FAILS LOUD
    /// with [`ElabError::WhereLetRecUnsupported`] — there is no `sorry`
    /// fallback), and `Err` for genuine type errors discovered while
    /// elaborating the lifted value or the body.
    fn try_elab_let_rec_lifted(
        &mut self,
        binder: &SurfaceBinder,
        val: &SurfaceExpr,
        body: &SurfaceExpr,
    ) -> Result<Option<Expr>, ElabError> {
        use clean_parser::TerminationHints;

        let func_name = binder.name.clone();

        // 1. Recover the helper's (parameters, ascribed return type, body). Two
        //    encodings reach here:
        //
        //    (a) EQUATION form (`where go : Nat → Nat | 0 => 0 | k+1 => go k`):
        //        `build_let_rec` emits `Ascription(PatternMatchLambda([_x],
        //        match _x with …), τ)` with the full `τ = params → ret` on the
        //        binder. The `_x` scrutinee parameter is hidden from the plain
        //        lambda peel below, so reuse the top-level equation-def
        //        normalization — unwrap the return-type ascription, then peel one
        //        domain off `τ` to lift `_x` into a real binder — routing the
        //        helper through the IDENTICAL structural-recursion lowering a
        //        top-level equation `def` uses.
        //
        //    (b) PLAIN lambda (`let rec f (p₁ …) : R := body`, encoded as
        //        `Lambda([p₁ …], (body : R))`): peel the leading lambda binders.
        let eq_val = match val {
            SurfaceExpr::Ascription(_, boxed, _) => boxed.as_ref(),
            other => other,
        };
        let (helper_binders, ret_ty, helper_body): (
            Vec<SurfaceBinder>,
            Option<SurfaceExpr>,
            SurfaceExpr,
        ) = if let Some((lifted, ret, body)) = elab_decl_value::normalize_equation_def(
            self.env,
            &binder.name,
            &[],
            binder.ty.as_deref(),
            eq_val,
        ) {
            (lifted, ret, body)
        } else {
            let mut binders: Vec<SurfaceBinder> = Vec::new();
            let mut inner = val;
            while let SurfaceExpr::Lambda(_, bs, b) = inner {
                binders.extend(bs.iter().cloned());
                inner = b;
            }
            // No parameters → not a function we can lift via structural recursion.
            if binders.is_empty() {
                return Ok(None);
            }
            match inner {
                SurfaceExpr::Ascription(_, b, r) => (binders, Some((**r).clone()), (**b).clone()),
                other => (binders, binder.ty.as_deref().cloned(), other.clone()),
            }
        };
        let helper_body = &helper_body;

        // 2. Detect structural recursion on `func_name` over the helper's
        //    parameters. Only lift when a decreasing argument is found; any
        //    other shape (well-founded, non-recursive, mutual) defers to the
        //    conservative fallback so we never fabricate an ill-formed term.
        let param_names: Vec<String> = helper_binders.iter().map(|b| b.name.clone()).collect();
        let recursion_info =
            structural::detect_recursion_with_params(&func_name, helper_body, &param_names);
        let Some(dec_pos) = recursion_info.decreasing_arg else {
            return Ok(None);
        };
        if !recursion_info.is_recursive {
            return Ok(None);
        }
        // `find_decreasing_arg` falls back to "last variable position" when no
        // position is provably smaller. For a local helper, reject the lift
        // when EVERY self-call passes the chosen parameter through UNCHANGED
        // (`g m` with param `m`): that is not structural descent, and running
        // the `.rec` lowering on it only produces a downstream unification
        // error. Bailing here routes the shape to the caller's typed loud
        // `WhereLetRecUnsupported` ("no structurally decreasing parameter").
        //
        // B97 exception (shadowed rebind): when the whole body is
        // `match <param> with …` and some arm REBINDS the parameter's name
        // (`let rec go (k : Nat) := match k with | 0 => 0 | k + 1 => go k`),
        // the name-equality check above is unreliable — the call's `k` is the
        // rebound, one-step-smaller pattern component, exactly the shape the
        // shared B89 whole-body-match-scrutinee preference selected `dec_pos`
        // for. Proceed with the lift: the `.rec` lowering substitutes IHs
        // solely for genuinely smaller components, so a call that really
        // passes the OUTER parameter unchanged still fails loud downstream
        // (and the kernel re-checks the lowered value regardless).
        if Self::all_calls_pass_param_unchanged(&recursion_info.calls, &param_names, dec_pos)
            && !structural::whole_body_match_rebinds_param(helper_body, &param_names, dec_pos)
        {
            return Ok(None);
        }

        // 3. Run the helper through the structural-recursion lowering exactly
        //    like a top-level recursive `def`.
        //
        //    The namespace prefix is INTENTIONALLY KEPT in scope (this code used
        //    to `std::mem::take` it). The helper's binder/return types and body
        //    may mention namespace-scoped constants — inside `namespace TrustIr`,
        //    a helper param `cur : Addr` refers to `TrustIr.Addr`. Clearing the
        //    prefix broke that resolution: the bare `Addr` then fell through to
        //    auto-implicit and was bound as a fresh free variable typed `Sort u`,
        //    leaking an `UnknownFVar` / `FVar vs Const` mismatch into the lowered
        //    recursor term (Track F — `Memory.readBytes` and every imported-type
        //    extra param). The prefix was originally cleared only so
        //    `setup_recursion` would record the *unqualified* self-call name; we
        //    now restore that unqualified name explicitly after setup (below)
        //    instead, decoupling it from type resolution.
        let saved_ctx = self.recursive_def_ctx.take();

        let lowered: Result<(Expr, Expr), ElabError> = (|| {
            let termination = TerminationHints::default();
            // `setup_recursion` returns `Some` only for the explicit
            // `termination_by <measure>` well-founded path, which a bare
            // `let rec` never has; for structural recursion it installs
            // `recursive_def_ctx` and returns `None`.
            if self
                .setup_recursion(
                    &func_name,
                    &helper_binders,
                    ret_ty.as_ref(),
                    helper_body,
                    &termination,
                )?
                .is_some()
            {
                // Unexpected WF early-return: bail to the fallback.
                return Err(ElabError::CannotInfer);
            }
            // `setup_recursion` qualifies the recorded `func_name` with the
            // active namespace prefix (`TrustIr.go`). But a `let rec` helper's
            // self-calls are written *unqualified* (`go …`), and
            // `RecursiveDefContext::matches_call_name` only matches a bare
            // candidate against the *exact* recorded name (its suffix rule
            // requires the qualified side to be the candidate). Force the
            // recorded name back to the bare helper name so call-site IH
            // substitution recognizes `go …` — while the namespace prefix stays
            // in scope so the helper's binder/return types still resolve their
            // namespace-scoped constants (`Addr` → `TrustIr.Addr`).
            if let Some(ref mut ctx) = self.recursive_def_ctx {
                ctx.func_name = func_name.clone();
            }
            self.elab_def_body(&helper_binders, ret_ty.as_ref(), helper_body)
        })();

        // Always restore the recursion context, even on error.
        self.recursive_def_ctx = saved_ctx;

        let (helper_ty, helper_val) = match lowered {
            Ok(pair) => pair,
            // A `CannotInfer` here is our own bail-out signal for the WF path;
            // treat it as "not liftable" rather than a hard error so the
            // fallback can run. Other errors are genuine and propagate.
            Err(ElabError::CannotInfer) => return Ok(None),
            Err(e) => return Err(e),
        };

        // Instantiate metavariables/levels so the bound value is closed.
        let helper_ty = self.metas.instantiate(&helper_ty);
        let helper_ty = self.metas.instantiate_levels(&helper_ty);
        let helper_val = self.metas.instantiate(&helper_val);
        let helper_val = self.metas.instantiate_levels(&helper_val);

        // 4. Bind the lifted value with a plain non-recursive `let`, with `f`
        //    in scope for the body. Self-references in the body resolve to `f`
        //    (the bound local), whose value is the closed recursive term.
        let fvar = self.push_local(func_name.clone(), helper_ty.clone());
        let body_expr = self.elaborate(body)?;
        self.pop_local();
        // SOUNDNESS: instantiate assigned metavars/levels in the body before
        // abstracting `fvar` so no loose fvar leaks into the closed `let rec`
        // body. TCB-neutral — the kernel re-checks the lifted value and body.
        let body_expr = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&body_expr));
        let body_abs = body_expr.abstract_fvar(fvar);

        let name = Name::from_string(&func_name);
        Ok(Some(Expr::let_named(
            name, helper_ty, helper_val, body_abs, false,
        )))
    }

    /// Returns `true` iff `ty` is a proposition (`ty : Prop`, i.e. `Sort 0`).
    ///
    /// Used by [`elab_ascription`] to decide whether to preserve the ascribed
    /// type as written (proof ascriptions) or fall back to the inner term's
    /// inferred type (data/coercion ascriptions). A failure to infer the sort
    /// (e.g. unresolved metavariables) conservatively returns `false`, leaving
    /// the legacy behavior intact.
    fn ascription_is_prop(&self, ty: &Expr) -> bool {
        match self.infer_type(ty) {
            Ok(sort) => matches!(self.whnf(&sort).kind(), ExprKind::Sort(l) if l.is_zero()),
            Err(_) => false,
        }
    }

    pub(super) fn elab_ascription(
        &mut self,
        expr: &SurfaceExpr,
        ty: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        let ty_expr = self.elaborate(ty)?;
        let expr_val = self.elaborate_with_expected_type(expr, Some(ty_expr.clone()))?;

        // Infer the actual type of the expression
        let actual_ty = self.infer_type(&expr_val)?;

        // Unify the actual type with the expected type
        let ctx = self.build_local_ctx();
        let ur = Unifier::with_env(&mut self.metas, self.env, ctx).unify(&actual_ty, &ty_expr);
        match ur {
            UnifyResult::Success => {
                // Apply level instantiation - unification may solve level constraints
                let result = self.metas.instantiate(&expr_val);
                let result = self.metas.instantiate_levels(&result);

                // Preserve the ascribed type AS WRITTEN for proof ascriptions.
                //
                // For `show A = B from rfl` (and any `show T from e` where `T` is
                // a Prop), the inner proof's *inferred* type can differ
                // syntactically from the written `T`: a `rfl : @Eq α a a` carries
                // a single side, and inferring the inner term re-derives both
                // sides from that one expression, losing the surface forms `A`
                // and `B` (e.g. `Nat.land m n` δ-unfolds to its `Nat.rec` body).
                //
                // `rw [show A = B from rfl]` then searches the goal for the
                // *unfolded* `from` side, which does not occur (the goal still
                // holds the folded `Nat.land m n`), and fails `RewriteNoMatch`.
                //
                // Wrap the proof in an applied identity lambda
                // `(fun (h : T) => h) e`. Its inferred type is exactly the
                // ascribed `T` (App inference instantiates the lambda's
                // codomain, which is `T` verbatim — see tc/infer.rs App arm), so
                // downstream `match_equality` recovers `A`/`B` as written. The
                // kernel re-checks the beta-redex: it still requires `e : T` by
                // definitional equality, so soundness is unchanged (the redex
                // β-reduces back to `e`).
                //
                // Restricted to Prop-valued ascriptions whose written type
                // differs *syntactically* from the inner proof's inferred type.
                // When the inner term already infers to exactly the ascribed type
                // (e.g. `exact (f hP : Q)` where `f hP : Q`), wrapping would only
                // bloat the term and break callers that pattern-match the bare
                // proof — so we leave it untouched in that case.
                let ty_inst = self.metas.instantiate(&ty_expr);
                let ty_inst = self.metas.instantiate_levels(&ty_inst);
                let actual_inst = self.metas.instantiate(&actual_ty);
                let actual_inst = self.metas.instantiate_levels(&actual_inst);
                if ty_inst != actual_inst && self.ascription_is_prop(&ty_inst) {
                    let id_lam = Expr::lam(BinderInfo::Default, ty_inst.clone(), Expr::bvar(0));
                    return Ok(Expr::app(id_lam, result));
                }
                Ok(result)
            }
            UnifyResult::Failure(_msg) => {
                // Before returning TypeMismatch, try type coercion (#796).
                // Lean 4 inserts Coe instances when ascription types don't directly unify.
                if let Some(coerced) = self.try_coerce(&expr_val, &actual_ty, &ty_expr) {
                    let result = self.metas.instantiate(&coerced);
                    return Ok(self.metas.instantiate_levels(&result));
                }
                Err(ElabError::TypeMismatch {
                    expected: format!("{ty_expr:?}"),
                    actual: format!("{actual_ty:?} ({_msg})"),
                })
            }
            UnifyResult::Stuck => {
                // Stuck means unification could not determine correctness
                // (e.g., unsolved metavariables). Treat as error for soundness.
                Err(ElabError::CannotInfer)
            }
        }
    }

    /// Desugar `if c then a else b` → `@ite α c inst a b`.
    /// Both branches elaborate against one shared result type (#2786).
    pub(super) fn elab_if(
        &mut self,
        cond: &SurfaceExpr,
        then_br: &SurfaceExpr,
        else_br: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        // Capture the expected type *before* elaborating the condition: the
        // expected type belongs to the branches (`then`/`else`), not to the
        // condition. Elaborating the condition (`b == 0`, …) can mutate
        // `current_expected_type` as a side effect, which would otherwise strand
        // the branches without their expected type — breaking anonymous
        // constructor (`.ok`/`.error`) resolution when the `if` sits inside a
        // match arm. Elaborate the condition with the expected type cleared.
        // (Track KL)
        let branch_expected = self.current_expected_type.clone();
        let cond_expr = self.elaborate_with_expected_type(cond, None)?;
        let (result_ty, then_expr, else_expr) = if let Some(expected) = branch_expected {
            let t = self.elaborate_with_expected_type(then_br, Some(expected.clone()))?;
            let e = self.elaborate_with_expected_type(else_br, Some(expected.clone()))?;
            (expected, t, e)
        } else {
            let t = self.elaborate(then_br)?;
            let raw = self.infer_type(&t)?;
            let raw = self.metas.instantiate_levels(&self.metas.instantiate(&raw));
            // Insert any LEADING IMPLICIT args on the then-branch so its inferred
            // type is concrete before it becomes the else-branch's expected type.
            // Without this, a bare polymorphic `none : {α} → Option α` leaves the
            // branch type a function type, and an `else some 0 : Option Int` then
            // mismatches it. `insert_implicit_args` only fills leading implicit /
            // instance binders (explicit function types like `A → B` are left
            // untouched), so this is a no-op for genuinely function-valued branches.
            let (t, raw) = self.insert_implicit_args(t, &raw);
            let ty = self.metas.instantiate_levels(&self.metas.instantiate(&raw));
            let e = self.elaborate_with_expected_type(else_br, Some(ty.clone()))?;
            (ty, t, e)
        };
        let result_ty = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&result_ty));
        let level = self.infer_sort(&result_ty)?;
        // A `Bool` condition takes the Lean-faithful Bool→Prop lane (see
        // `mk_bool_if`); a genuine `Prop` condition takes the `ite` path below.
        let cond_is_bool = self.condition_is_bool(&cond_expr)?;
        if cond_is_bool {
            return Ok(self.mk_bool_if(&level, &result_ty, cond_expr, then_expr, else_expr));
        }
        let ite = Expr::const_(Name::from_string("ite"), vec![level]);
        let decidable_inst = self.resolve_decidable(&cond_expr)?;
        Ok(Expr::apps(
            ite,
            [result_ty, cond_expr, decidable_inst, then_expr, else_expr],
        ))
    }

    /// Lower `if (c : Bool) then t else e` the way Lean 4 does: the condition
    /// is coerced to the Prop `c = true` and the whole expression becomes
    /// `@ite.{u} α (c = true) inst t e` with `inst : Decidable (c = true)`
    /// from instance synthesis (`instDecidableEqBool c true` in a Lean-core
    /// environment, via the decEq bridge). Producing the SAME term shape real
    /// Lean produces is what lets clean-elaborated statements unify
    /// definitionally against `.olean`-imported encodings of the same source —
    /// the trust-ir Lean↔Clean bridge's Bool-guarded division arms (blocker
    /// B2) hinge on it.
    ///
    /// When the environment carries no `Decidable (c = true)` instance at all
    /// (bare kernel environments without a decidable-equality-of-Bool leaf),
    /// fall back to the definitional `Bool.rec` elimination — honest and
    /// self-contained, but a shape real Lean never emits (Lean core always has
    /// the instance). No `sorry` is ever synthesized on this path.
    pub(in crate::infer) fn mk_bool_if(
        &mut self,
        level: &Level,
        result_ty: &Expr,
        cond_expr: Expr,
        then_expr: Expr,
        else_expr: Expr,
    ) -> Expr {
        let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
        let prop = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [
                bool_ty.clone(),
                cond_expr.clone(),
                Expr::const_(Name::from_string("Bool.true"), vec![]),
            ],
        );
        let decidable_goal = Expr::app(
            Expr::const_(Name::from_string("Decidable"), vec![]),
            prop.clone(),
        );
        if let Some(inst) = self.resolve_instance(&decidable_goal) {
            let ite = Expr::const_(Name::from_string("ite"), vec![level.clone()]);
            return Expr::apps(ite, [result_ty.clone(), prop, inst, then_expr, else_expr]);
        }
        // Fallback: `@Bool.rec.{u} (fun _ : Bool => α) e t c` — Bool.rec's
        // false-case is the else-branch and its true-case the then-branch.
        // Non-dependent motive; lift result_ty's loose bound variables past
        // the new binder.
        let motive = Expr::lam(BinderInfo::Default, bool_ty, result_ty.lift(1));
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![level.clone()]);
        Expr::apps(bool_rec, [motive, else_expr, then_expr, cond_expr])
    }

    pub(super) fn elab_syntax_quote(&mut self, content: &str) -> Result<Expr, ElabError> {
        let quoted = parse_quotation(&format!("`{content}"))
            .map_err(|e| ElabError::MacroError(e.to_string()))?;
        let surface = syntax_to_surface(&quoted.syntax).ok_or_else(|| {
            ElabError::MacroError("could not convert syntax quotation to surface expression".into())
        })?;
        self.elaborate(&surface)
    }

    pub(super) fn elab_explicit(&mut self, inner: &SurfaceExpr) -> Result<Expr, ElabError> {
        // Explicit application: @f (#1231)
        // This disables implicit argument insertion for the inner expression.
        // Set explicit_mode = true so insert_implicit_args returns early.
        let prev_explicit_mode = self.explicit_mode;
        self.explicit_mode = true;
        let result = self.elaborate(inner);
        self.explicit_mode = prev_explicit_mode;
        result
    }

    pub(super) fn elab_if_decidable(
        &mut self,
        witness_name: &str,
        prop: &SurfaceExpr,
        then_br: &SurfaceExpr,
        else_br: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        // The condition and both branches are fallible after taking the outer
        // expected type and after introducing branch witnesses. A temporary
        // transaction commits successful metavariable work used by the result,
        // while restoring the exact expected/local state on every exit.
        self.with_temporary_local_scope(|this| {
            this.elab_if_decidable_inner(witness_name, prop, then_br, else_br)
        })
    }

    fn elab_if_decidable_inner(
        &mut self,
        witness_name: &str,
        prop: &SurfaceExpr,
        then_br: &SurfaceExpr,
        else_br: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        // if h : p then t else e
        // Desugars to: dite p (fun h : p => t) (fun h : ¬p => e)
        //
        // dite (Decidable If-Then-Else) has type:
        // dite : {α : Sort u} → (p : Prop) → [Decidable p] →
        //        (p → α) → (¬p → α) → α
        //
        // `dite`'s result type `α` is FIXED (it does not depend on the decision),
        // so BOTH branch bodies must inhabit the same `α` — the surrounding
        // expected type when one is known (#B09). Take it as the branches'
        // expected type and CLEAR it while elaborating the condition: `p`'s type
        // is `Prop`, never the branch result type, and letting the outer result
        // type leak into `elaborate(prop)` mis-checks the condition (the
        // def-body expected-type lane otherwise fails `n = 0` against
        // `n = 0 ∨ ¬ n = 0`). This mirrors `elab_if`, which likewise elaborates
        // its condition with the expected type cleared and propagates it into the
        // branches. A polymorphic proof/value body such as `Or.inl h` (`h : p`)
        // or `.ok x` needs that expected type to resolve its metavariables, and
        // the hypothesis binder is in scope so `h` is usable in that body.
        // Without it `dite` is unusable whenever `h` is actually consumed
        // (Init/Prelude.lean `dite`).
        let outer_expected = self.current_expected_type.take();
        let branch_expected = outer_expected.as_ref().map(|expected| {
            self.metas
                .instantiate_levels(&self.metas.instantiate(expected))
        });
        let prop_expr = self.elaborate(prop)?;
        if self.condition_is_bool(&prop_expr)? {
            return Err(ElabError::TypeMismatch {
                expected: "dependent-if condition of type Prop".to_string(),
                actual: "Bool".to_string(),
            });
        }

        // Create the then branch: (fun h : p => t), body checked against α.
        let then_fvar = self.push_local(witness_name.to_string(), prop_expr.clone());
        let then_expr = self.elaborate_with_expected_type(then_br, branch_expected.clone())?;
        self.pop_local();

        // `α` is the shared result type of BOTH branches: the known expected
        // type, else the then-branch's inferred type. Using it as the else
        // branch's expected type (below) cross-resolves the branches'
        // metavariables — `Or.inl h`'s right disjunct is pinned by `Or.inr h`'s
        // type and vice versa — so a `dite` in an INFERENCE position (`def f :=
        // if h : c then Or.inl h else Or.inr h`) leaves no dangling metavariable
        // that would otherwise leak to the kernel as a free variable. Mirrors
        // `elab_if`, which feeds the then-branch type to the else branch.
        let alpha = match &branch_expected {
            Some(expected) => expected.clone(),
            None => {
                let alpha = self.infer_type(&then_expr)?;
                let alpha = self.metas.instantiate(&alpha);
                self.metas.instantiate_levels(&alpha)
            }
        };
        // SOUNDNESS: instantiate assigned metavars/levels in the branch body
        // before abstracting its hypothesis fvar. A branch such as `Or.inl h`
        // solves metavars that mention `then_fvar`; abstracting first would
        // leave a loose fvar in the closed `(fun h => …)`, rejected by the
        // kernel. Instantiating only substitutes decided values (no-op when
        // none) and is TCB-neutral — the kernel re-checks the declaration.
        let then_body = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&then_expr));
        let then_lambda = Expr::lam(
            BinderInfo::Default,
            prop_expr.clone(),
            then_body.abstract_fvar(then_fvar),
        );

        // Create the else branch: (fun h : ¬p => e), body checked against α.
        // ¬p = p → False = Pi(Default, p, False)
        let not_prop = Expr::pi(
            BinderInfo::Default,
            prop_expr.clone(),
            Expr::const_(Name::from_string("False"), vec![]),
        );
        let else_fvar = self.push_local(witness_name.to_string(), not_prop.clone());
        let else_expr = self.elaborate_with_expected_type(else_br, Some(alpha.clone()))?;
        self.pop_local();
        // SOUNDNESS: as with the then-branch, instantiate assigned
        // metavars/levels in the else body before abstracting its fvar so no
        // loose fvar leaks into the closed `(fun h : ¬p => …)`. TCB-neutral.
        let else_body = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&else_expr));
        let else_lambda = Expr::lam(
            BinderInfo::Default,
            not_prop,
            else_body.abstract_fvar(else_fvar),
        );

        // Build: dite p then_lambda else_lambda
        // Note: The Decidable instance is resolved implicitly by type class resolution
        // dite : {α : Sort u} → (p : Prop) → [Decidable p] → (p → α) → (¬p → α) → α
        //
        // Re-instantiate `α` (and hence the branch lambdas at emit time) so any
        // metavariable the else-branch elaboration just solved is reflected.
        let alpha = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&alpha));
        // `alpha` must itself inhabit a sort. Propagate a malformed inferred
        // branch type instead of silently manufacturing `Type 1`.
        let level = self.infer_sort(&alpha)?;
        let dite = Expr::const_(Name::from_string("dite"), vec![level]);
        let decidable_inst = self.resolve_decidable(&prop_expr)?;
        let result = Expr::apps(
            dite,
            [alpha, prop_expr, decidable_inst, then_lambda, else_lambda],
        );
        Ok(result)
    }

    /// Check if a constant is accessible from the current namespace context.
    ///
    /// - `private` declarations are only accessible within their declaring namespace
    ///   (the constant's namespace prefix must match or be a parent of
    ///   the current `namespace_prefix`).
    /// - `protected` and `public` declarations are always accessible.
    pub(super) fn is_const_accessible(&self, name: &Name) -> bool {
        if !self.env.is_private(name) {
            return true;
        }
        // Extract the namespace of the constant (everything before the last `.`).
        // E.g., `Foo.Bar.helper` has namespace `Foo.Bar`.
        let name_str = name.to_string();
        let const_ns = match name_str.rsplit_once('.') {
            Some((ns, _)) => ns,
            None => "", // root-level constant
        };
        // The constant is accessible if the current namespace matches or
        // is a child of the constant's namespace.
        if const_ns.is_empty() {
            // Root-level private constant: accessible from the root namespace only.
            self.namespace_prefix.is_empty()
        } else {
            self.namespace_prefix == const_ns
                || self.namespace_prefix.starts_with(&format!("{const_ns}."))
        }
    }

    pub(super) fn elab_ident(&mut self, name: &str) -> Result<Expr, ElabError> {
        // Metaprogram value channel: a name bound to an already-elaborated kernel
        // `Expr` (e.g. `let t := inferType e`) splices that stored term directly,
        // bypassing the surface round-trip. The value was kernel-checked when it
        // was produced and is checked again wherever this body is used, so this
        // adds no trust surface (see `meta_query`).
        if let Some(value) = self.meta_value_bindings.get(name) {
            return Ok(value.clone());
        }

        // Explicit root-namespace escape: `_root_.Bool` forces resolution at the
        // top level, bypassing the current namespace prefix and auto-implicit
        // binding. Strip the marker and resolve the remainder as a global
        // constant / inductive / constructor (TrustIr `Ty.isSigned : Ty →
        // _root_.Bool`, Track R). If the stripped name is not a known global we
        // fall through so the normal UnknownIdent diagnostics still fire.
        if let Some(root_name) = name.strip_prefix("_root_.") {
            let global = Name::from_string(root_name);
            if let Some(info) = self.env.get_const(&global) {
                if self.is_const_accessible(&global) {
                    let levels: Vec<Level> = info
                        .level_params
                        .iter()
                        .map(|_| self.fresh_universe_param())
                        .collect();
                    return Ok(Expr::const_(global, levels));
                }
            }
            if self.env.get_inductive(&global).is_some()
                || self.env.get_constructor(&global).is_some()
                || self.env.get_recursor(&global).is_some()
            {
                return Ok(self.mk_const(&global));
            }
            return Err(self.unknown_ident_error(name));
        }

        // First check locals (including any existing auto-implicits)
        if let Some((fvar, _ty)) = self.lookup_local(name) {
            return Ok(Expr::fvar(fvar));
        }

        if let Some(ctor_suffix) = name.strip_prefix('.') {
            if let Some(ctor_expr) = self.resolve_expected_ctor_ident(ctor_suffix) {
                return Ok(ctor_expr);
            }
        }

        // Global resolution order mirrors Lean's `resolveGlobalName`
        // (`Lean/ResolveName.lean`): candidates from the CURRENT NAMESPACE
        // OUTWARD win first (`resolveUsingNamespace` walks `Foo.Bar.name`,
        // then `Foo.name`), and only when that walk finds nothing are the
        // root-level exact name, aliases, and `open` decls consulted
        // (`resolveGlobalNameCore`'s anonymous-namespace stage). The previous
        // order checked the ROOT constant first, so inside `namespace Bar` a
        // bare `w` resolved to the root `w` instead of `Bar.w` — a silently
        // WRONG value the kernel then certified (gap sweep B03,
        // namespaces_scoping/p21).
        //
        // 1. Current-namespace-outward walk (#3410 + B03 reorder). Inside
        //    `namespace Foo.Bar`, try `Foo.Bar.name`, then `Foo.name`.
        if !self.namespace_prefix.is_empty() {
            let mut prefix = self.namespace_prefix.as_str();
            loop {
                let qualified_str = format!("{prefix}.{name}");
                let qualified_name = Name::from_string(&qualified_str);
                if self.is_const_accessible(&qualified_name) {
                    if let Some(info) = self.env.get_const(&qualified_name) {
                        let levels: Vec<Level> = info
                            .level_params
                            .iter()
                            .map(|_| self.fresh_universe_param())
                            .collect();
                        return Ok(Expr::const_(qualified_name, levels));
                    }
                    // Namespace-relative inductives/constructors/recursors may
                    // not carry a plain constant entry (mirrors the `_root_.`
                    // branch above).
                    if self.env.get_inductive(&qualified_name).is_some()
                        || self.env.get_constructor(&qualified_name).is_some()
                        || self.env.get_recursor(&qualified_name).is_some()
                    {
                        return Ok(self.mk_const(&qualified_name));
                    }
                }
                // Namespace-qualified ALIASES (B13): `export Foo (x)` inside
                // `namespace Bar` registers `Bar.x ↦ Foo.x` (Lean `elabExport`:
                // alias under the current namespace), so a bare `x` inside
                // `Bar` must find it during this same outward walk — aliases
                // participate in the per-prefix candidate set exactly like env
                // constants (`Lean/ResolveName.lean` `resolveGlobalNameCore`
                // consults `getAliases` at every prefix step).
                if let Some(target) = self.namespace_state.resolve(&qualified_str).cloned() {
                    if self.is_const_accessible(&target) {
                        return Ok(self.mk_const(&target));
                    }
                }
                // Walk up: "Foo.Bar" -> "Foo", then stop
                match prefix.rsplit_once('.') {
                    Some((parent, _)) => prefix = parent,
                    None => break,
                }
            }
        }

        // 2. `open`ed-namespace aliases (Lean folds these into the root-stage
        //    candidate set; clean keeps last-open-wins).
        if let Some(qualified) = self.namespace_state.resolve(name).cloned() {
            if self.is_const_accessible(&qualified) {
                return Ok(self.mk_const(&qualified));
            }
        }

        // 3. Root-level exact constant.
        let const_name = Name::from_string(name);
        if let Some(info) = self.env.get_const(&const_name) {
            // Enforce private visibility: private declarations are only
            // accessible within their declaring namespace.
            if !self.is_const_accessible(&const_name) {
                // Fall through to auto-implicit / UnknownIdent
            } else {
                // Use fresh universe parameters for polymorphic constants so
                // later applications can unify them with concrete levels.
                let levels: Vec<Level> = info
                    .level_params
                    .iter()
                    .map(|_| self.fresh_universe_param())
                    .collect();
                return Ok(Expr::const_(const_name, levels));
            }
        }

        // Monad typeclass alias fallback (#3435) and prelude-export fallback (#3527).
        //
        // Lean 4 supplies bare `pure`/`bind`/... through `open Pure`/`open Bind`
        // which the Monad typeclass does implicitly. It additionally exports
        // inductive-type constructors via `export Option (some none)`,
        // `export Sum (inl inr)`, etc. in `Init/Prelude.lean`, so users write
        // `some x` rather than `Option.some x`.
        //
        // Our elaborator has no open-prelude step, so a bare `pure`, `some`,
        // etc. otherwise falls through to auto-implicit and gets bound as a
        // fresh free variable whose type inherits the expected type. That
        // silently shadows the real constant and produces errors such as
        // `UnknownFVar(FVarId(N))` (the auto-implicit fvar references a binder
        // that is no longer in scope by the time the term is re-checked) or
        // type mismatches where an auto-implicit domain unifies with an
        // unrelated value type (see #3435).
        //
        // The fix is to treat these names as aliases for their underlying
        // constants when (a) the identifier is not found as any other
        // constant / local and (b) the target constant actually exists.
        // We only handle identifiers with clear typeclass / prelude ownership
        // to avoid accidentally shadowing user-defined names.
        const PRELUDE_ALIASES: &[(&str, &str)] = &[
            // Monad typeclass methods (#3435).
            ("pure", "Pure.pure"),
            ("bind", "Bind.bind"),
            ("map", "Functor.map"),
            ("seq", "Seq.seq"),
            ("seqLeft", "SeqLeft.seqLeft"),
            ("seqRight", "SeqRight.seqRight"),
            // MonadExcept methods, exported by `Init/Prelude.lean` via
            // `export MonadExcept (throw tryCatch)`. Without this, a bare
            // `throw e` falls through to auto-implicit and is bound as a fresh
            // free variable typed `Sort u` — the elaborator then applies the
            // error argument to a non-function `Sort(u_0)` ("Too many
            // arguments: function type Sort(...)"). Aliasing to the registered
            // `MonadExcept.throw` axiom resolves it to the real polymorphic op.
            ("throw", "MonadExcept.throw"),
            ("tryCatch", "MonadExcept.tryCatch"),
            // Indexing and collection-literal heads, exported by Lean via
            // `export GetElem (getElem)` / `export GetElem? (getElem? getElem!)`
            // (Init/GetElem.lean:79/112) and `export Insert (insert)` /
            // `export Singleton (singleton)` (Init/Core.lean:593/602). The
            // parser emits these bare names for `xs[i]`-family subscripts and
            // `{a, b, c}` collection literals (Brick P1); like the entries
            // above, the alias fires only when the target constant is
            // registered, so it is a no-op in environments without the classes.
            ("getElem", "GetElem.getElem"),
            ("getElem?", "GetElem?.getElem?"),
            ("getElem!", "GetElem?.getElem!"),
            ("insert", "Insert.insert"),
            ("singleton", "Singleton.singleton"),
            // Inductive-type constructors exported by `Init/Prelude.lean`
            // (#3527). Matching Lean 4's `export Option (some none)` etc.
            ("some", "Option.some"),
            ("none", "Option.none"),
            ("inl", "Sum.inl"),
            ("inr", "Sum.inr"),
            // `export Bool (false true)` (Init/Prelude.lean). Clean's native
            // prelude ships root-level reducible `true`/`false` defs, so this
            // alias only fires in environments without them — e.g. a real-Lean
            // `.olean` import, where a bare `false` otherwise fell through to
            // auto-implicit and silently GENERALIZED the statement over an
            // arbitrary Bool (`(r == 0) = false` became `∀ b, (r == 0) = b`,
            // fail-closed but wrong — trust-ir bridge division-guard
            // statements).
            ("true", "Bool.true"),
            ("false", "Bool.false"),
        ];
        for (alias, target) in PRELUDE_ALIASES {
            if name == *alias {
                let target_name = Name::from_string(target);
                if let Some(info) = self.env.get_const(&target_name) {
                    if self.is_const_accessible(&target_name) {
                        let levels: Vec<Level> = info
                            .level_params
                            .iter()
                            .map(|_| self.fresh_universe_param())
                            .collect();
                        return Ok(Expr::const_(target_name, levels));
                    }
                }
            }
        }

        // Core combinator `id`, absent from clean's prelude (elaborator Brick E1).
        //
        // Lean's `Init/Prelude.lean` defines `@[reducible] def id {α : Sort u}
        // (a : α) : α := a` and exports it at the root. Clean's prelude never
        // registers it, so a bare `id` reached here (no local, no constant, no
        // alias) otherwise falls through to auto-implicit and is bound as a fresh
        // free variable typed `Sort u`; applying an explicit argument to a
        // `Sort u`-typed head then fails `TooManyArguments { func_type:
        // "Sort(u)" }` — the standalone `id 5` gap, and every `id $ x` / `id <| x`
        // / `x |> id` reduction (all of which desugar to `App(id, [x])`).
        //
        // Resolve it here to the definitional identity lambda `fun {α : Sort u}
        // (a : α) => a`. Placing the check AFTER local / constant / namespace /
        // alias resolution means a user-defined `id` (the integration-test
        // `def id (A : Type) (x : A) := x`) or a binder named `id` still wins;
        // this only fires when `id` is otherwise unresolved. The application
        // elaborator then inserts the leading implicit `{α}` as a metavariable
        // through the ordinary `insert_implicit_args` path (identical to how the
        // registered `HAdd.hAdd`/`id zero` heads flow), applies the explicit
        // argument, and the kernel re-checks the resulting β-redex — so this adds
        // no trust and no new constant: `(fun a => a) x` reduces to `x`.
        if name == "id" {
            // fun {α : Sort u} (a : α) => a
            //   outer binder α : Sort u   (Implicit)
            //   inner binder a : α        (α is de Bruijn index 0 under the outer binder)
            //   body a                    (a is de Bruijn index 0 under the inner binder)
            let sort_u = Expr::sort(self.fresh_universe_param());
            let inner = Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0));
            return Ok(Expr::lam(BinderInfo::Implicit, sort_u, inner));
        }

        // Core combinator `cond`, absent from clean's prelude (like `id` above).
        //
        // Lean's `Init/Prelude.lean` defines `@[macro_inline] def cond {α : Sort u}
        // (c : Bool) (x y : α) : α := match c with | true => x | false => y`, exported
        // at the root. Clean never registers it, so a bare `cond` reaching here (no
        // local, no constant, no alias) otherwise falls through to auto-implicit and
        // is bound as a fresh free variable, then `cond true 1 0` fails
        // `TooManyArguments`/`UnknownIdent`.
        //
        // Resolve it to the definitional term
        //   fun {α : Sort u} (c : Bool) (x y : α) => @Bool.rec.{u} (fun _ => α) y x c
        // `Bool.rec`'s minors are in constructor order (false, then true), so the
        // false-case is `y` (`cond false x y = y`) and the true-case is `x`
        // (`cond true x y = x`); the recursor's ι-rules give exactly those two
        // computation rules, which the kernel re-checks (the `cond_true`/`cond_false`
        // `rfl` tests). Placed AFTER local / constant / alias resolution, so a
        // user-defined `cond` — or a future prelude registration — still wins; this
        // only fires when `cond` is otherwise unresolved, and `add_decl` re-checks
        // the resulting β/ι-redex, so it adds no trust and no new constant.
        if name == "cond" {
            // de Bruijn in the innermost body scope {α, c, x, y}: y=0, x=1, c=2, α=3.
            let u = self.fresh_universe_param();
            let sort_u = Expr::sort(u.clone());
            let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
            let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![u]);
            // motive `fun (_ : Bool) => α`; under its extra binder α is bvar 4.
            let motive = Expr::lam(BinderInfo::Default, bool_c.clone(), Expr::bvar(4));
            // @Bool.rec motive (false=y) (true=x) (major=c)
            let core = Expr::apps(
                bool_rec,
                [motive, Expr::bvar(0), Expr::bvar(1), Expr::bvar(2)],
            );
            let lam_y = Expr::lam(BinderInfo::Default, Expr::bvar(2), core); // (y : α)
            let lam_x = Expr::lam(BinderInfo::Default, Expr::bvar(1), lam_y); // (x : α)
            let lam_c = Expr::lam(BinderInfo::Default, bool_c, lam_x); // (c : Bool)
            return Ok(Expr::lam(BinderInfo::Implicit, sort_u, lam_c)); // {α : Sort u}
        }

        // Bare `default`, absent from clean's prelude as a root export. Lean's
        // `Init/Prelude.lean` defines `@[reducible] def default {α} [Inhabited α]
        // : α := Inhabited.default`, exported at the root — i.e. `default` IS
        // `@Inhabited.default`. Clean registers `Inhabited.default` but not the
        // bare alias, so a correctly-`deriving Inhabited` structure is unusable:
        // `(default : T)` reaches here unresolved and is auto-bound as a fresh
        // free variable (`UnknownIdent "default"` / a leaked fvar in `(default :
        // T).field`). Resolve it to the registered `Inhabited.default` by
        // delegating to the ordinary constant path — the leading `{α}` implicit
        // (from the expected type) and the `[Inhabited α]` instance are then
        // inserted/synthesized exactly as for an explicit `Inhabited.default`
        // (verified to reduce: `(Inhabited.default : S).field = <field default>`).
        // Placed AFTER local / constant / alias resolution, so a user-defined
        // `default` still wins; only fires when `default` is otherwise unresolved,
        // and adds no new constant or trust (it names the registered projection).
        if name == "default"
            && self
                .env
                .get_const(&Name::from_string("Inhabited.default"))
                .is_some()
        {
            return self.elab_ident("Inhabited.default");
        }

        // Bare `not`, a root export in Lean's `Init/Prelude.lean` (`def not :
        // Bool → Bool | true => false | false => true`) — `not` IS `Bool.not`.
        // Clean registers `Bool.not` but not the bare alias, so `not b` reached
        // here unresolved and was auto-bound as a fresh free variable
        // (`UnknownIdent "not"`, or `TooManyArguments` once applied). Resolve it
        // to the registered `Bool.not` — a plain `Bool → Bool` function whose
        // application reduces by rfl. Placed AFTER local / constant / alias
        // resolution, so a user-defined `not` still wins; only fires when `not`
        // is otherwise unresolved, and adds no new constant or trust (it names
        // the registered function). Same shape as the `default`/`cond` aliases.
        if name == "not" && self.env.get_const(&Name::from_string("Bool.not")).is_some() {
            return self.elab_ident("Bool.not");
        }

        // Bare `xor`, a root export in Lean's `Init/Prelude.lean` (`def xor :
        // Bool → Bool → Bool`) — `xor` IS `Bool.xor`. Same shape as `not`
        // above: clean registers `Bool.xor` but not the bare alias, so `xor a b`
        // reached here unresolved. Resolve it to `Bool.xor` (a plain
        // `Bool → Bool → Bool` whose application reduces by rfl). Placed after
        // local / constant / alias resolution, so a user-defined `xor` wins.
        if name == "xor" && self.env.get_const(&Name::from_string("Bool.xor")).is_some() {
            return self.elab_ident("Bool.xor");
        }

        // Bare `compare`, a root export in Lean's `Init/Data/Ord` (`export Ord
        // (compare)`) — `compare` IS `@Ord.compare : {α} → [Ord α] → α → α →
        // Ordering`. Clean registers the `Ord.compare` projection (reducible,
        // unfolds through the `Ord` instance) but not the bare alias, so
        // `compare a b` reached here unresolved and was auto-bound as a fresh
        // free variable, then over-applied (`TooManyArguments`). Resolve it to
        // `Ord.compare`; the elaborator then inserts + synthesizes the implicit
        // `{α}` and instance `[Ord α]` (e.g. `instOrdNat`) exactly as for an
        // explicit `Ord.compare a b` — verified to reduce: `compare (2:Nat) 7`
        // ≡ `Ordering.lt`. Placed AFTER local / constant / alias resolution, so
        // a user-defined `compare` still wins; adds no new constant or trust.
        // Same shape as the `default` / `not` / `xor` aliases (and mirrors the
        // registered `min`/`max` := `Min.min`/`Max.max` surface aliases).
        if name == "compare"
            && self
                .env
                .get_const(&Name::from_string("Ord.compare"))
                .is_some()
        {
            return self.elab_ident("Ord.compare");
        }

        // Bare `hash`, a root export in Lean's `Init/Prelude.lean` (`export
        // Hashable (hash)`) — `hash` IS `@Hashable.hash : {α} → [Hashable α]
        // → α → Nat` (Nat-valued in Clean's prelude; Lean's is UInt64 — a
        // pre-existing kernel divergence, see `data_typeclasses_hashable`).
        // Same shape as the `compare` alias above: resolve to `Hashable.hash`
        // and let the elaborator insert + synthesize the implicit `{α}` and
        // `[Hashable α]` instance (prelude `instHashableNat` / a derived
        // instance). Placed AFTER local / constant / alias resolution, so a
        // user-defined `hash` still wins; adds no new constant or trust.
        if name == "hash"
            && self
                .env
                .get_const(&Name::from_string("Hashable.hash"))
                .is_some()
        {
            return self.elab_ident("Hashable.hash");
        }

        // Auto-implicit handling (#164)
        // Respect `set_option autoImplicit false` at file or section scope.
        //
        // SIGNATURE-ONLY (gap sweep B03): Lean's auto-bound implicits apply
        // exclusively to declaration *headers* — binder types and the result
        // type (`Lean/Elab/MutualDef.lean` `elabHeaders` under
        // `withAutoBoundImplicit`; validity rules in `Lean/Elab/Binders.lean` /
        // `isValidAutoBoundImplicitName`). An unknown identifier in a VALUE
        // position (`in_term_body`) is a loud `unknown identifier` — a typo'd
        // ident in a def body must never be silently generalized into an
        // implicit binder (namespaces_scoping/p20, p23).
        let auto_implicit_enabled = match self.get_option("autoImplicit") {
            Some(Some(v)) => v != "false",
            _ => true, // default: enabled
        };
        let relaxed_auto_implicit = match self.get_option("relaxedAutoImplicit") {
            Some(Some(v)) => v != "false",
            _ => true, // default: enabled
        };
        if auto_implicit_enabled
            && self.in_decl_context
            && !self.in_term_body
            && Self::is_valid_auto_implicit_name(name, relaxed_auto_implicit)
        {
            if let Some(fvar) = self.has_auto_implicit(name) {
                return Ok(Expr::fvar(fvar));
            }

            // Reuse the expected type when available so constructor-local names
            // like `x`, `y`, `z`, `t`, or `c` become term binders. Fall back to
            // `Sort u` so header-level parameters like `α` still auto-bind.
            let ty = self
                .current_expected_type
                .as_ref()
                .map(|ty| {
                    let ty = self.metas.instantiate(ty);
                    self.metas.instantiate_levels(&ty)
                })
                .unwrap_or_else(|| Expr::sort(self.fresh_universe_param()));

            // Add the auto-implicit
            let fvar = self.add_auto_implicit(name.to_string(), ty);
            return Ok(Expr::fvar(fvar));
        }

        Err(self.unknown_ident_error(name))
    }

    pub(super) fn unknown_ident_error(&self, name: &str) -> ElabError {
        // Protected-name diagnostic (B13, namespaces_scoping/p16): a simple
        // `open Foo` deliberately does NOT alias `protected def Foo.x` (Lean
        // skips protected names in `OpenDecl.simple` resolution), so a bare
        // `x` afterwards is unknown — but the actionable fix is the qualified
        // name, not a fuzzy-match list. Point at it directly.
        for ns in self.namespace_state.open_namespaces() {
            let qualified_str = format!("{ns}.{name}");
            let qualified = Name::from_string(&qualified_str);
            if self.env.is_protected(&qualified) && self.env.get_const(&qualified).is_some() {
                return ElabError::ProtectedIdent {
                    name: name.to_string(),
                    qualified: qualified_str,
                    namespace_: ns.to_string(),
                };
            }
        }
        let suggestions = self.nearest_theorem_names(name, 5);
        if suggestions.is_empty() {
            ElabError::UnknownIdent(name.to_string())
        } else {
            ElabError::UnknownIdentWithSuggestions {
                name: name.to_string(),
                suggestions,
            }
        }
    }

    fn nearest_theorem_names(&self, name: &str, limit: usize) -> Vec<String> {
        let theorem_names: Vec<String> = self
            .env
            .constants()
            .filter(|info| info.kind == ConstantKind::Theorem)
            .filter(|info| self.is_const_accessible(&info.name))
            .map(|info| info.name.to_string())
            .collect();
        nearest_string_candidates(name, theorem_names.iter().map(String::as_str), limit)
    }

    pub(super) fn elab_universe(&mut self, univ: &UniverseExpr) -> Result<Expr, ElabError> {
        let level = match univ {
            UniverseExpr::Prop => Level::zero(),
            UniverseExpr::Type => Level::succ(Level::zero()),
            UniverseExpr::TypeLevel(level_expr) => {
                let l = self.elab_level(level_expr)?;
                Level::succ(l)
            }
            // Type* (Mathlib syntax): create a fresh universe parameter + 1.
            // Under the strict `--prelude lean4-core` lane, `Type*` is
            // Mathlib-only (Lean core rejects it at parse time), so mirror the
            // B07 strict-monad gate and reject it LOUDLY here rather than
            // silently accepting with fresh-universe semantics
            // (GAP_SWEEP_2026-07-09 universes/p09). `Type _` (a level hole) is
            // the core-compatible spelling and is unaffected — it parses to
            // `TypeLevel(Param("_"))`, not `TypeImplicit`.
            UniverseExpr::TypeImplicit if self.env.lean4_core_strict_monads() => {
                return Err(ElabError::Lean4CoreOnlySyntax {
                    syntax: "Type*",
                    hint: "use `Type _` (a universe hole) or an explicit `Type u`",
                });
            }
            UniverseExpr::TypeImplicit => Level::succ(self.fresh_universe_param()),
            UniverseExpr::Sort(level_expr) => self.elab_level(level_expr)?,
            // Sort without explicit level: create a fresh universe parameter
            UniverseExpr::SortImplicit => self.fresh_universe_param(),
            // `Sort*` (Mathlib): a fresh universe parameter, the `Sort`
            // analogue of `Type*`. Gated LOUDLY under `--prelude lean4-core`
            // exactly like `Type*` above (`Sort*` is Mathlib-only; core rejects
            // it at parse time). `Sort _` (a level hole) is the core-compatible
            // spelling and is unaffected.
            UniverseExpr::SortStar if self.env.lean4_core_strict_monads() => {
                return Err(ElabError::Lean4CoreOnlySyntax {
                    syntax: "Sort*",
                    hint: "use `Sort _` (a universe hole) or an explicit `Sort u`",
                });
            }
            UniverseExpr::SortStar => self.fresh_universe_param(),
        };
        Ok(Expr::sort(level))
    }

    pub(super) fn elab_level(&mut self, level: &LevelExpr) -> Result<Level, ElabError> {
        stack_safe(|| match level {
            LevelExpr::Lit(n) => {
                let mut l = Level::zero();
                for _ in 0..*n {
                    l = Level::succ(l);
                }
                Ok(l)
            }
            LevelExpr::Param(name) => {
                // A level HOLE `_` (from `Type _` / `Sort _`) is not a named
                // parameter — it is a universe metavariable to be solved during
                // elaboration (Lean's `levelMVarToParam`). Mint a fresh one so
                // each `_` is independent and stays assignable (NOT rigid).
                if name == "_" {
                    return Ok(self.fresh_universe_param());
                }
                // Check if it's a known universe parameter; if not, auto-add it.
                // This matches Lean 4's auto-bound implicit universe behavior:
                // `class Foo (X : Type u)` without explicit `universe u` declaration
                // will implicitly declare `u` as a universe parameter.
                if !self.universe_params.contains(name) {
                    self.universe_params.push(name.clone());
                }
                Ok(Level::param(Name::from_string(name)))
            }
            LevelExpr::Succ(inner) => {
                let l = self.elab_level(inner)?;
                Ok(Level::succ(l))
            }
            LevelExpr::Max(l1, l2) => {
                let l1 = self.elab_level(l1)?;
                let l2 = self.elab_level(l2)?;
                Ok(Level::max(l1, l2))
            }
            LevelExpr::IMax(l1, l2) => {
                let l1 = self.elab_level(l1)?;
                let l2 = self.elab_level(l2)?;
                Ok(Level::imax(l1, l2))
            }
            LevelExpr::Antiquot(name) => {
                // Level antiquotation: $u inside q(Type $u) or q(Sort $u)
                // Look up the level variable from the enclosing scope.
                // For now, treat it as a level parameter (will be resolved during
                // antiquotation processing in q-quotations).
                //
                // In a full implementation, we'd check if `name` is bound to a
                // Level value in scope. For Phase 4, we treat it as a level param
                // that will be substituted.
                Ok(Level::param(Name::from_string(name)))
            }
        })
    }

    pub(super) fn elab_lambda(
        &mut self,
        binders: &[SurfaceBinder],
        body: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        stack_safe(|| {
            if binders.is_empty() {
                // Base case: elaborate the lambda body against the codomain
                // expected type the enclosing binder set in
                // `current_expected_type` (line ~741). Routing through
                // `elaborate_with_expected_type` (rather than the bare
                // `elaborate`) runs `apply_implicit_to_expected_type` on the
                // body, so a polymorphic head like `none : {α} → Option α`
                // gets its implicit `{α}` inserted and unified against the
                // expected codomain (`Option Value`). Without this, the body
                // keeps its leading implicit Pi (`{α} → Option α`), the lambda
                // is typed `Nat → ({α} → Option α)`, and the kernel rejects it
                // with the leaked universe param ("Too many arguments: function
                // type Sort(...)"). Falls back to a plain `elaborate` when no
                // expected codomain is known, preserving prior behavior. The
                // kernel re-checks the inserted application, so this only fills
                // implicits the expected type already determines — it cannot
                // weaken the kernel check.
                let expected = self.current_expected_type.clone();
                return match expected {
                    Some(_) => self.elaborate_with_expected_type(body, expected),
                    None => self.elaborate(body),
                };
            }

            let binder = &binders[0];
            let prev_expected = self.current_expected_type.clone();
            let expected_pi = prev_expected.as_ref().and_then(|expected_ty| {
                let expected_ty = self.metas.instantiate(expected_ty);
                let expected_ty = self.metas.instantiate_levels(&expected_ty);
                let expected_ty = self.whnf(&expected_ty);
                match expected_ty.kind() {
                    ExprKind::Pi(bi, domain, codomain) => {
                        Some((*bi, domain.as_ref().clone(), codomain.as_ref().clone()))
                    }
                    _ => None,
                }
            });

            // Implicit-lambda insertion (Lean `Elab/Binders.lean` `elabFunBinders`
            // / `addAutoBoundImplicits`): when the EXPECTED type's leading binder
            // is implicit or instance-implicit but the surface lambda binder is
            // EXPLICIT, Lean binds that implicit here automatically WITHOUT
            // consuming the surface binder, then continues the same binder list
            // against the codomain. This types `fun x => x : {α} → α → α` as
            // `fun {α} x => x`, `fun f x => f x : {α β} → (α→β) → α → β` as
            // `fun {α}{β} f x => f x`, etc. The two opt-outs — naming the implicit
            // (`fun {α} x`) or `@` (`@fun α x`) — make the surface binder implicit
            // / all-explicit, so this branch is skipped and the normal path binds
            // it directly. Restricted to Implicit/InstImplicit (the binders Lean
            // auto-inserts at a lambda); strict-implicit falls through to the
            // normal path. Terminates: each insertion strips one Pi layer off the
            // finite expected type. The synthetic binder is named with the
            // inaccessible dagger, so no source identifier in `body` can resolve
            // to it (capture-free); it is abstracted to a bvar and `add_decl`
            // re-checks the closed lambda, so this only fills implicits the
            // expected type already fixes — it cannot weaken the kernel check.
            if let Some((exp_bd, domain, codomain)) = &expected_pi {
                if matches!(exp_bd.info, BinderInfo::Implicit | BinderInfo::InstImplicit)
                    && convert_binder_info(binder.info) == BinderInfo::Default
                    // `@fun α x => x` sets `explicit_mode` (the `@` disables
                    // implicit insertion): the surface binder `α` is meant to bind
                    // the implicit position directly, so DON'T insert here.
                    && !self.explicit_mode
                {
                    let exp_bd = *exp_bd;
                    let domain = domain.clone();
                    let codomain = codomain.clone();
                    let fvar = self.push_local("✝implicit".to_string(), domain.clone());
                    let is_inst = exp_bd.info == BinderInfo::InstImplicit;
                    if is_inst {
                        self.push_local_instance(fvar, domain.clone());
                    }
                    self.current_expected_type = Some({
                        let codomain = codomain.instantiate(&Expr::fvar(fvar));
                        let codomain = self.metas.instantiate(&codomain);
                        self.metas.instantiate_levels(&codomain)
                    });
                    let inner_result = self.elab_lambda(binders, body);
                    self.current_expected_type = prev_expected;
                    if is_inst {
                        self.pop_local_instance();
                    }
                    self.pop_local();
                    let inner = inner_result?;
                    let domain = self
                        .metas
                        .instantiate_levels(&self.metas.instantiate(&domain));
                    let inner = self
                        .metas
                        .instantiate_levels(&self.metas.instantiate(&inner));
                    let inner_abs = inner.abstract_fvar(fvar);
                    return Ok(Expr::lam(exp_bd, domain, inner_abs));
                }
            }

            let ty = if let Some(ty) = &binder.ty {
                self.elaborate(ty)?
            } else if let Some((_, domain, _)) = expected_pi.as_ref() {
                domain.clone()
            } else {
                // Create a fresh metavariable for the type
                self.fresh_meta(Expr::type_())
            };

            let bi = convert_binder_info(binder.info);
            let fvar = self.push_local(binder.name.clone(), ty.clone());

            // For instance-implicit binders, register as local instance for nested resolution
            let is_inst_implicit = bi == BinderInfo::InstImplicit;
            if is_inst_implicit {
                self.push_local_instance(fvar, ty.clone());
            }

            self.current_expected_type = expected_pi.map(|(_, _, codomain)| {
                let codomain = codomain.instantiate(&Expr::fvar(fvar));
                let codomain = self.metas.instantiate(&codomain);
                self.metas.instantiate_levels(&codomain)
            });
            let inner_result = self.elab_lambda(&binders[1..], body);
            self.current_expected_type = prev_expected;

            if is_inst_implicit {
                self.pop_local_instance();
            }
            self.pop_local();
            let inner = inner_result?;

            // SOUNDNESS: instantiate assigned metavars/levels in the domain and
            // body before abstracting the binder fvar. If a metavar in `ty` or
            // `inner` was assigned during elaboration — and the assignment
            // mentions `fvar` or another local — abstracting first would leave a
            // loose fvar / uninstantiated metavar in the closed lambda, which the
            // kernel rejects ("contains free variables" / a Pi domain that leaked
            // an FVar). Instantiating only substitutes already-decided values, so
            // it is a no-op when nothing was assigned and produces the correct
            // closed term otherwise. TCB-neutral: no kernel code is touched and
            // `add_decl` still re-checks the result.
            let ty = self.metas.instantiate_levels(&self.metas.instantiate(&ty));
            let inner = self
                .metas
                .instantiate_levels(&self.metas.instantiate(&inner));

            // Abstract the fvar to a bvar
            let inner_abs = inner.abstract_fvar(fvar);
            Ok(Expr::lam(bi, ty, inner_abs))
        })
    }

    pub(super) fn elab_pi(
        &mut self,
        binders: &[SurfaceBinder],
        body: &SurfaceExpr,
    ) -> Result<Expr, ElabError> {
        stack_safe(|| {
            if binders.is_empty() {
                return self.elaborate(body);
            }

            let binder = &binders[0];
            let ty = if let Some(ty) = &binder.ty {
                self.elaborate(ty)?
            } else {
                // Lean 4: unannotated Pi binders get fresh metavars (Sort ?u)
                let binder_sort = Expr::sort(self.fresh_universe_param());
                self.fresh_meta(binder_sort)
            };

            let bi = convert_binder_info(binder.info);
            let fvar = self.push_local(binder.name.clone(), ty.clone());

            // For instance-implicit binders, register as local instance for nested resolution
            let is_inst_implicit = bi == BinderInfo::InstImplicit;
            if is_inst_implicit {
                self.push_local_instance(fvar, ty.clone());
            }

            let inner = self.elab_pi(&binders[1..], body)?;

            if is_inst_implicit {
                self.pop_local_instance();
            }
            self.pop_local();

            // SOUNDNESS: instantiate assigned metavars/levels in the domain and
            // body before abstracting the binder fvar. An unannotated Pi binder
            // gets `ty = fresh_meta(...)`; if that domain (or a nested dependent
            // domain) is later assigned to a term mentioning `fvar`, abstracting
            // first leaks a loose fvar and the kernel sees `Pi(…, FVar(0), …)`
            // where it expected a `Sort`. Instantiating substitutes only
            // already-decided values, so it is a no-op absent assignments and
            // yields the correct closed term otherwise. TCB-neutral: the kernel
            // re-checks the declaration.
            let ty = self.metas.instantiate_levels(&self.metas.instantiate(&ty));
            let inner = self
                .metas
                .instantiate_levels(&self.metas.instantiate(&inner));

            // Abstract the fvar to a bvar
            let inner_abs = inner.abstract_fvar(fvar);
            Ok(Expr::pi(bi, ty, inner_abs))
        })
    }
}
