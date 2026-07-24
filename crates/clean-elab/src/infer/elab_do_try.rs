// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Try/catch/finally, refutable let, repeat, while, and dbg_trace elaboration
//! for do-notation.
//!
//! Extracted from elab_do.rs to maintain the 500-line file limit.
//!
//! - `elab_do_try_catch`: Desugars `try ... catch ... finally ...` to
//!   `MonadExcept.tryCatch` / `tryCatchThe` / `tryFinally` compositions.
//! - `elab_do_let_else`: Desugars `let pat <- action | fallback` to
//!   `Bind.bind action (fun __x => match __x with | pat => rest | _ => fallback)`.
//! - `elab_do_repeat`: Desugars `repeat body` to `for _ in Lean.Loop.mk do body`.
//! - `elab_do_while`: Desugars `while cond do body` to a ForIn loop with
//!   condition-guarded ForInStep.yield/done.
//! - `elab_do_dbg_trace`: Desugars `dbg_trace msg` to `dbgTrace msg (fun () => rest)`.
//!
//! Reference: ~/lean4-ref/src/Lean/Elab/BuiltinDo/TryCatch.lean
//! Reference: ~/lean4-ref/src/Lean/Elab/BuiltinDo/Let.lean

use super::*;
use clean_parser::SurfaceBinderInfo;

impl<'a> ElabCtx<'a> {
    /// Desugar `try body catch e => handler [finally fin]` in a do block.
    ///
    /// Catch clauses are folded left: each wraps the accumulated body in
    /// `MonadExcept.tryCatch` (untyped) or `tryCatchThe ExcType` (typed).
    /// An optional `finally` clause wraps the result in `tryFinally`.
    ///
    /// Reference: ~/lean4-ref/src/Lean/Elab/BuiltinDo/TryCatch.lean
    pub(super) fn elab_do_try_catch(
        &mut self,
        try_body: &[DoElem],
        catches: &[DoCatchClause],
        finally_body: Option<&[DoElem]>,
    ) -> Result<Expr, ElabError> {
        let mut body = self.elab_do_body_with_outer_continuation(try_body)?;

        for catch_clause in catches {
            body = self.elab_do_catch_clause(body, catch_clause)?;
        }

        if let Some(fin_elems) = finally_body {
            body = self.elab_do_finally(body, fin_elems)?;
        }

        Ok(body)
    }

    /// Elaborate a single catch clause, wrapping `body` in the appropriate
    /// `tryCatch`/`tryCatchThe` call.
    fn elab_do_catch_clause(
        &mut self,
        body: Expr,
        catch_clause: &DoCatchClause,
    ) -> Result<Expr, ElabError> {
        let handler_body = self.elab_do_body_with_outer_continuation(&catch_clause.body)?;

        let exc_ty = if let Some(exc_type_surface) = &catch_clause.exc_type {
            self.elaborate(exc_type_surface)?
        } else {
            // Untyped `catch e => …`: infer the exception type from the
            // do-block's monad (`Except ε` / `ExceptT ε m'`) BEFORE building the
            // handler, so the handler's binder type and the `tryCatch` `ε`
            // argument agree on a CONCRETE type. Falling back to a fresh
            // metavariable (for a non-`Except` monad) leaves untyped catch
            // genuinely ambiguous — it then fails to solve, loudly.
            self.infer_catch_exception_type()
                .unwrap_or_else(|| self.fresh_meta(Expr::type_()))
        };

        let fvar = self.push_local(catch_clause.binder.clone(), exc_ty.clone());
        let handler_abs = handler_body.abstract_fvar(fvar);
        self.pop_local();
        let handler_lambda = Expr::lam(BinderInfo::Default, exc_ty.clone(), handler_abs);

        if catch_clause.exc_type.is_some() {
            self.mk_try_catch_the(exc_ty, body, handler_lambda)
        } else {
            self.mk_monad_except_try_catch(exc_ty, body, handler_lambda)
        }
    }

    /// Infer the exception type for an untyped `catch e => …`: the do-block
    /// monad's error type, when the monad is `Except ε` (ε = its single
    /// argument) or `ExceptT ε m'` (ε = its first argument). Returns `None` for
    /// any other monad — untyped catch is then genuinely ambiguous.
    fn infer_catch_exception_type(&mut self) -> Option<Expr> {
        let (_, _, m, _) = self.expected_do_result_components()?;
        let m_whnf = self.whnf(&m);
        let ExprKind::Const(name, _) = m_whnf.get_app_fn().kind() else {
            return None;
        };
        // `get_app_args_iter` yields reverse spine order; reverse to source order.
        let mut args: Vec<Expr> = m_whnf.get_app_args_iter().cloned().collect();
        args.reverse();
        let is_except = *name == Name::from_string("Except");
        let is_except_t = *name == Name::from_string("ExceptT");
        if (is_except && args.len() == 1) || (is_except_t && !args.is_empty()) {
            Some(args[0].clone())
        } else {
            None
        }
    }

    /// Build `tryCatchThe ε body handler` for typed catch clauses.
    ///
    /// Reuses cached monad info (#1814): `v` = do-block's `u`, `w` = do-block's
    /// `v`, `m` = do-block's `m`. Only `u` (exception universe) is fresh.
    fn mk_try_catch_the(
        &mut self,
        epsilon: Expr,
        body: Expr,
        handler: Expr,
    ) -> Result<Expr, ElabError> {
        // ε's universe: the registered type declares `ε : type_u = Sort(succ u)`,
        // i.e. `ε : Sort(u_exc + 1)`, so `u_exc` is the PREDECESSOR of ε's sort
        // level (`infer_sort(String) = 1` ⇒ `u_exc = 0`). A fresh universe param
        // would be left unsolved → a kernel universe mismatch.
        let u_exc = match self.infer_sort(&epsilon)? {
            Level::Succ(inner) => inner.as_ref().clone(),
            other => other,
        };
        // Concrete `(u, m, α)` off the block's expected result type (like
        // `mk_bind_app`) so no monad/universe metavariable is left unsolved.
        let (base_u, base_v, base_m) = self.get_or_create_monad_info();
        let (do_u, _do_v, m, alpha) = self.expected_do_result_components().unwrap_or_else(|| {
            let type_u = Expr::sort(Level::succ(base_u.clone()));
            (base_u, base_v, base_m, self.fresh_meta(type_u))
        });

        // Registered `tryCatchThe.{u,v} : {ε}{m}{α} → m α → (ε → m α) → m α` — a
        // plain (instance-free) axiom with TWO level params. The previous build
        // passed THREE levels and inserted a nonexistent `MonadExceptOf ε m`
        // instance argument, over-applying the axiom (cryptic `NotAFunction`).
        // `@tryCatchThe.{u_exc,u} ε m α body handler`.
        let try_catch_the = Expr::const_(Name::from_string("tryCatchThe"), vec![u_exc, do_u]);
        Ok(Expr::apps(
            try_catch_the,
            [epsilon, m, alpha, body, handler],
        ))
    }

    /// Build `MonadExcept.tryCatch body handler` for untyped catch clauses.
    ///
    /// Reuses cached monad info (#1814): `v` = do-block's `u`, `w` = do-block's
    /// `v`, `m` = do-block's `m`. Only `u` (exception universe) is fresh.
    fn mk_monad_except_try_catch(
        &mut self,
        epsilon: Expr,
        body: Expr,
        handler: Expr,
    ) -> Result<Expr, ElabError> {
        // `ε` is already CONCRETE here: `elab_do_catch_clause` inferred it from
        // the monad (`Except ε`) before building the handler, so the handler's
        // binder type and this `ε` argument agree.
        //
        // ε's universe: `ε : Sort(u_exc + 1)` in the registered type, so `u_exc`
        // is the predecessor of ε's sort level.
        let u_exc = match self.infer_sort(&epsilon)? {
            Level::Succ(inner) => inner.as_ref().clone(),
            other => other,
        };
        // Concrete `(u, v, m, α)` off the block's expected result type (like
        // `mk_bind_app`) so no monad/universe metavariable is left unsolved.
        let (base_u, base_v, base_m) = self.get_or_create_monad_info();
        let (do_u, do_v, m, alpha) = self.expected_do_result_components().unwrap_or_else(|| {
            let type_u = Expr::sort(Level::succ(base_u.clone()));
            (base_u, base_v, base_m, self.fresh_meta(type_u))
        });

        // Registered `MonadExcept.tryCatch.{u,v,w} : {ε}{m}{α} → m α →
        // (ε → m α) → m α` is a plain (instance-free) axiom — mirror that arity.
        // The previous build inserted a nonexistent `MonadExcept ε m` instance
        // argument, over-applying the axiom (cryptic `NotAFunction`).
        // `@MonadExcept.tryCatch.{u_exc,u,v} ε m α body handler`.
        let try_catch = Expr::const_(
            Name::from_string("MonadExcept.tryCatch"),
            vec![u_exc, do_u, do_v],
        );
        Ok(Expr::apps(try_catch, [epsilon, m, alpha, body, handler]))
    }

    /// Build `tryFinally body fin` for finally clauses.
    ///
    /// Reuses cached monad info (#1814): `u` = do-block's `u`, `v` = do-block's
    /// `v`, `m` = do-block's `m`. Direct mapping — same universe structure.
    fn elab_do_finally(&mut self, body: Expr, fin_elems: &[DoElem]) -> Result<Expr, ElabError> {
        // Read the CONCRETE `(u, v, m, α)` off the do-block's expected result
        // type — exactly as `mk_bind_app`/`mk_pure_app` do — so the emitted term
        // carries no unsolved monad/universe metavariables (the failure mode of a
        // raw `Expr::app` build). `α` is the block result type = the body's value
        // type (`tryFinally … : m α` returns the body's result).
        let (base_u, base_v, base_m) = self.get_or_create_monad_info();
        let (u, v, m, alpha) = self.expected_do_result_components().unwrap_or_else(|| {
            let type_u = Expr::sort(Level::succ(base_u.clone()));
            (base_u, base_v, base_m, self.fresh_meta(type_u))
        });

        // The finalizer's value is DISCARDED (`tryFinally … : m α` returns the
        // BODY's result, not the finalizer's). Elaborate it at `m ?β` — the
        // block's monad with a FRESH value type — not the block's result type
        // (which would force `pure () : m α`, rejecting a Unit finalizer), and
        // not `None` (which would leave the finalizer's monad ambiguous).
        let beta = self.fresh_meta(Expr::sort(Level::succ(u.clone())));
        let fin_expected = Expr::app(m.clone(), beta.clone());
        let saved_expected = self.current_expected_type.take();
        self.current_expected_type = Some(fin_expected);
        let fin_result = self.elab_do_body_with_outer_continuation(fin_elems);
        self.current_expected_type = saved_expected;
        let fin_expr = fin_result?;

        // The kernel registers `tryFinally.{u,v} : {m}{α}{β} → m α → m β → m α`
        // as a plain (instance-free) axiom — mirror that arity exactly:
        // `@tryFinally.{u,v} m α β body fin : m α`. (The previous build inserted
        // nonexistent `MonadFinally`/`Functor` instance arguments — the
        // `MonadFinally` class is not registered — over-applying the axiom and
        // failing with a cryptic `NotAFunction`.)
        let try_finally = Expr::const_(Name::from_string("tryFinally"), vec![u, v]);
        Ok(Expr::apps(try_finally, [m, alpha, beta, body, fin_expr]))
    }

    /// Desugar `let pat <- action | fallback` in a do block.
    ///
    /// For variable and wildcard patterns, desugars directly to bind + let.
    /// For constructor patterns, desugars through the do-match infrastructure
    /// to get proper casesOn dispatch:
    ///   `let __x <- action; match __x with | pat => rest | _ => fallback`
    pub(super) fn elab_do_let_else(
        &mut self,
        pat: &SurfacePattern,
        action: &SurfaceExpr,
        fallback: &[DoElem],
        rest: &[DoElem],
    ) -> Result<Expr, ElabError> {
        // Constructor patterns use match-based desugaring for correct casesOn dispatch
        if !matches!(pat, SurfacePattern::Var(_) | SurfacePattern::Wildcard) {
            return self.elab_do_let_else_ctor(pat, action, fallback, rest);
        }

        let action_expr = self.elaborate(action)?;
        let result_ty = self.fresh_meta(Expr::type_());
        let fvar = self.push_local("__let_else_x".to_string(), result_ty.clone());

        let fallback_expr = self.elab_do_body_with_outer_continuation(fallback)?;

        let match_expr = match pat {
            SurfacePattern::Var(name) => {
                // Variable pattern always matches — degenerate case
                let inner_fvar = self.push_local(name.clone(), result_ty.clone());
                let body = if rest.is_empty() {
                    let unit = Expr::const_(Name::from_string("Unit.unit"), vec![]);
                    self.mk_pure_app(unit)
                } else {
                    self.elab_do_elems(rest)?
                };
                self.pop_local();
                let _ = fallback_expr;
                // Fix #3419: Instantiate metas before abstracting FVars.
                let body_inst = self.metas.instantiate(&body);
                Expr::let_named(
                    Name::from_string(name),
                    result_ty.clone(),
                    Expr::bvar(0),
                    body_inst.abstract_fvar(inner_fvar),
                    false,
                )
            }
            SurfacePattern::Wildcard => {
                let success_expr = if rest.is_empty() {
                    let unit = Expr::const_(Name::from_string("Unit.unit"), vec![]);
                    self.mk_pure_app(unit)
                } else {
                    self.elab_do_elems(rest)?
                };
                let _ = fallback_expr;
                success_expr
            }
            _ => unreachable!("constructor patterns handled by elab_do_let_else_ctor"),
        };

        self.pop_local();
        // Fix #3419: Instantiate metas before abstracting FVars.
        let match_inst = self.metas.instantiate(&match_expr);
        let cont_abs = match_inst.abstract_fvar(fvar);
        let continuation = Expr::lam(BinderInfo::Default, result_ty, cont_abs);

        Ok(self.mk_bind_app(action_expr, continuation))
    }

    /// Desugar constructor-pattern refutable let through do-match infrastructure.
    ///
    /// Constructs a synthetic do-element sequence:
    ///   `let __x <- action; match __x with | pat => rest | _ => fallback`
    /// and processes it through `elab_do_elems`, which dispatches the match
    /// through `elab_do_match` for proper casesOn construction.
    fn elab_do_let_else_ctor(
        &mut self,
        pat: &SurfacePattern,
        action: &SurfaceExpr,
        fallback: &[DoElem],
        rest: &[DoElem],
    ) -> Result<Expr, ElabError> {
        let span = action.span();
        let fresh = "__let_else_x".to_string();
        let binder = SurfaceBinder::new(&fresh, None, SurfaceBinderInfo::Explicit);
        let bind_elem = DoElem::Bind(span, binder, Box::new(action.clone()));

        // Success arm: the continuation after the pattern match
        let success_body = if rest.is_empty() {
            let unit_expr = SurfaceExpr::Ident(span, "Unit.unit".to_string());
            vec![DoElem::Return(span, Box::new(unit_expr))]
        } else {
            rest.to_vec()
        };
        let success_arm = DoMatchArm {
            span,
            patterns: vec![pat.clone()],
            body: success_body,
        };

        // Fallback arm: wildcard catches non-matching patterns
        let fallback_arm = DoMatchArm {
            span,
            patterns: vec![SurfacePattern::Wildcard],
            body: fallback.to_vec(),
        };

        let discr = SurfaceExpr::Ident(span, fresh);
        let match_elem = DoElem::Match(span, vec![discr], vec![success_arm, fallback_arm]);

        self.elab_do_elems(&[bind_elem, match_elem])
    }

    /// Desugar `repeat body` to `for _ in Lean.Loop.mk do body`.
    ///
    /// Constructs a synthetic `DoElem::For` and processes it through the
    /// existing for-loop elaboration infrastructure.
    ///
    /// Reference: Lean 4 desugars `doRepeat` to `for _ in Lean.Loop.mk do body`
    pub(super) fn elab_do_repeat(&mut self, body: &[DoElem]) -> Result<Expr, ElabError> {
        let span = body
            .first()
            .map_or(clean_parser::Span::new(0, 0), |e| e.span());
        let binder = SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit);
        let collection = SurfaceExpr::Ident(span, "Lean.Loop.mk".to_string());
        let for_elem = DoElem::For(span, binder, Box::new(collection), body.to_vec());
        self.elab_do_elems(&[for_elem])
    }

    /// Desugar `while cond do body` to a ForIn loop with condition check.
    ///
    /// Builds:
    /// ```text
    /// @ForIn.forIn m Lean.Loop Unit inst PUnit Lean.Loop.mk PUnit.unit
    ///   (fun (_ : Unit) (acc : PUnit) =>
    ///     if cond then do body; pure (ForInStep.yield acc)
    ///     else pure (ForInStep.done acc))
    /// ```
    ///
    /// The condition check is embedded in the loop body: when `cond` is false,
    /// `ForInStep.done` terminates the loop. When true, the body executes and
    /// `ForInStep.yield` continues the next iteration.
    ///
    /// When the body contains break/continue, a DoLoopContext is set up so
    /// that break → ForInStep.done and continue → ForInStep.yield directly.
    pub(super) fn elab_do_while(
        &mut self,
        cond: &SurfaceExpr,
        body: &[DoElem],
    ) -> Result<Expr, ElabError> {
        let cond_expr = self.elaborate(cond)?;

        // Analyze body control effects to determine if DoLoopContext is needed
        let body_control_info = elab_do_control::infer_control_info_seq(body);
        let has_break_or_continue = body_control_info.breaks || body_control_info.continues;

        let (do_u, do_v, m) = self.get_or_create_monad_info();
        let u_rho = self.fresh_universe_param();
        let u_alpha = self.fresh_universe_param();

        let for_in_const = Expr::const_(
            Name::from_string("ForIn.forIn"),
            vec![do_u.clone(), do_v.clone(), u_rho.clone(), u_alpha.clone()],
        );

        // Types: ρ = Lean.Loop, α = Unit
        let loop_ty = Expr::const_(Name::from_string("Lean.Loop"), vec![]);
        let unit_ty = Expr::const_(Name::from_string("Unit"), vec![]);
        let unit_ty_for_app = unit_ty.clone();

        // ForIn instance
        let for_in_class = Expr::const_(
            Name::from_string("ForIn"),
            vec![do_u.clone(), do_v, u_rho, u_alpha],
        );
        let inst_ty = Expr::app(
            Expr::app(Expr::app(for_in_class, m.clone()), loop_ty.clone()),
            unit_ty.clone(),
        );
        let inst = self.fresh_meta(inst_ty);

        // β = PUnit, init = PUnit.unit
        let (beta, init) = self.get_or_create_punit();

        // Build body lambda: fun (_ : Unit) (acc : PUnit) => if cond then ... else ...
        // Push loop variables BEFORE elaborating body so DoLoopContext can reference acc
        let fvar_elem = self.push_local("_".to_string(), unit_ty.clone());
        let fvar_acc = self.push_local("__do_acc".to_string(), beta.clone());

        // Set up DoLoopContext so break/continue inside body produce ForInStep directly
        let outer_loop_ctx = self.do_loop_ctx.take();
        if has_break_or_continue {
            self.do_loop_ctx = Some(DoLoopContext {
                sigma: beta.clone(),
                acc_fvar: fvar_acc,
                u_level: do_u.clone(),
                mut_vars: vec![],
                return_type: None,
            });
        }

        // Elaborate the body inside the lambda scope, but restore the enclosing
        // loop context before propagating failure. An error here used to strand
        // the inner accumulator and make later control-flow elaboration observe
        // the wrong loop.
        let body_result = self.elab_do_elems(body);
        self.do_loop_ctx = outer_loop_ctx;
        let body_expr = body_result?;

        // Continue branch: body; pure (ForInStep.yield acc)
        let yield_const = Expr::const_(Name::from_string("ForInStep.yield"), vec![do_u.clone()]);
        let acc_ref = Expr::fvar(fvar_acc);
        let yield_val = Expr::app(Expr::app(yield_const, beta.clone()), acc_ref);
        let yield_pure = self.mk_pure_app(yield_val);

        let discard_ty = self.fresh_meta(Expr::type_());
        let fvar_d = self.push_local("_".to_string(), discard_ty.clone());
        let yield_abs = yield_pure.abstract_fvar(fvar_d);
        self.pop_local();
        let yield_cont = Expr::lam(BinderInfo::Default, discard_ty, yield_abs);
        let continue_branch = self.mk_bind_app(body_expr, yield_cont);

        // Break branch (condition false): pure (ForInStep.done acc)
        let done_const = Expr::const_(Name::from_string("ForInStep.done"), vec![do_u.clone()]);
        let acc_ref2 = Expr::fvar(fvar_acc);
        let done_val = Expr::app(Expr::app(done_const, beta.clone()), acc_ref2);
        let break_branch = self.mk_pure_app(done_val);

        // Build: ite result_ty cond inst continue_branch break_branch
        let u_ite = self.fresh_universe_param();
        let ite_const = Expr::const_(Name::from_string("ite"), vec![u_ite.clone()]);
        let ite_result_ty = self.fresh_meta(Expr::sort(u_ite));
        let decidable = Expr::const_(Name::from_string("Decidable"), vec![]);
        let ite_inst_ty = Expr::app(decidable, cond_expr.clone());
        let ite_inst = self.fresh_meta(ite_inst_ty);

        let ite_app = Expr::app(ite_const, ite_result_ty);
        let ite_app = Expr::app(ite_app, cond_expr);
        let ite_app = Expr::app(ite_app, ite_inst);
        let ite_app = Expr::app(ite_app, continue_branch);
        let ite_app = Expr::app(ite_app, break_branch);

        self.pop_local(); // acc
        self.pop_local(); // elem

        let body_abs = ite_app.abstract_fvar(fvar_acc).abstract_fvar(fvar_elem);
        let inner_lam = Expr::lam(BinderInfo::Default, beta.clone(), body_abs);
        let outer_lam = Expr::lam(BinderInfo::Default, unit_ty, inner_lam);

        // Build: @ForIn.forIn m Lean.Loop Unit inst PUnit Lean.Loop.mk PUnit.unit body
        let loop_mk = Expr::const_(Name::from_string("Lean.Loop.mk"), vec![]);
        let e = Expr::app(for_in_const, m);
        let e = Expr::app(e, loop_ty);
        let e = Expr::app(e, unit_ty_for_app);
        let e = Expr::app(e, inst);
        let e = Expr::app(e, beta);
        let e = Expr::app(e, loop_mk);
        let e = Expr::app(e, init);
        Ok(Expr::app(e, outer_lam))
    }

    /// Desugar `dbg_trace msg; rest` to `dbgTrace msg (fun () => rest)`.
    ///
    /// In terminal position (no rest), produces `dbgTrace msg (fun () => pure ())`.
    ///
    /// Reference: Lean 4 `doDbgTrace` elaboration
    pub(super) fn elab_do_dbg_trace(
        &mut self,
        msg: &SurfaceExpr,
        rest: &[DoElem],
    ) -> Result<Expr, ElabError> {
        let msg_expr = self.elaborate(msg)?;

        let rest_expr = if rest.is_empty() {
            let unit = Expr::const_(Name::from_string("Unit.unit"), vec![]);
            self.mk_pure_app(unit)
        } else {
            self.elab_do_elems(rest)?
        };

        // Build continuation thunk: fun (_ : Unit) => rest
        let unit_ty = Expr::const_(Name::from_string("Unit"), vec![]);
        let fvar = self.push_local("_".to_string(), unit_ty.clone());
        let rest_abs = rest_expr.abstract_fvar(fvar);
        self.pop_local();
        let thunk = Expr::lam(BinderInfo::Default, unit_ty, rest_abs);

        // Build: dbgTrace msg thunk
        let dbg_trace = Expr::const_(Name::from_string("dbgTrace"), vec![]);
        let e = Expr::app(dbg_trace, msg_expr);
        Ok(Expr::app(e, thunk))
    }
}
