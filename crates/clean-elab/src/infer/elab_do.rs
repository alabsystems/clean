// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Do-notation elaboration: desugars `do { ... }` blocks to Bind.bind / Pure.pure chains.
//!
//! Lean 4 `do` notation is syntactic sugar for monadic programming. The desugaring is:
//! - `do { let x <- e; rest }` → `Bind.bind e (fun x => do { rest })`
//! - `do { let x := e; rest }` → `let x := e in do { rest }`
//! - `do { return e }` → `Pure.pure e`
//! - `do { e; rest }` → `Bind.bind e (fun _ => do { rest })`
//! - `do { e }` (final) → `e`
//!
//! Reference: ~/lean4-ref/src/Lean/Elab/Do/Basic.lean

use super::elab_do_control::{has_top_level_non_terminal_return, infer_control_info_seq};
use super::*;
use clean_parser::SurfaceBinderInfo;

/// Cached monad information for a single do-block (#1814).
///
/// Lean 4 (`Do/Basic.lean:26-38`) creates `MonadInfo { m, u, v, cachedPUnit,
/// cachedPUnitUnit }` once at the start of do-block elaboration and reuses it
/// for every `mkBindApp` / `mkPureApp` / `forIn` call. Without caching, each
/// operation creates fresh universe parameters and monad metavariables that
/// must all unify — unnecessary unification burden.
pub(crate) struct DoMonadInfo {
    /// The monad `m : Type u → Type v`, a single metavariable shared across the block.
    pub(crate) m: Expr,
    /// Universe level `u` in `m : Type u → Type v`.
    pub(crate) u: Level,
    /// Universe level `v` in `m : Type u → Type v`.
    pub(crate) v: Level,
    /// Cached `PUnit.{u}` — the unit type at the do-block's input universe.
    /// Used as the accumulator type `β` in for-loops with no `let mut`.
    pub(crate) cached_punit: Expr,
    /// Cached `PUnit.unit.{u}` — the unit value at the do-block's input universe.
    /// Used as the initial accumulator in for-loops with no `let mut`.
    pub(crate) cached_punit_unit: Expr,
}

impl<'a> ElabCtx<'a> {
    /// Create `DoMonadInfo` for the current do-block.
    ///
    /// Matches Lean 4's `extractMonadInfo` (`Do/Basic.lean:601-634`) dual-branch
    /// design:
    /// - When `current_expected_type` is set and has the form `m α` (e.g. `Id Nat`),
    ///   extracts concrete `(u, v, m)` from it. This avoids rigid `Level::Param`
    ///   that can't unify with concrete `Level::Zero` from prelude types.
    /// - Otherwise, falls back to fresh universe params + fresh monad metavar
    ///   (`mkUnknownMonadResult` branch).
    fn mk_do_monad_info(&mut self) -> DoMonadInfo {
        // Branch 1: extract concrete (u, v, m) from expected type
        if let Some((u, v, m, _alpha)) = self.expected_do_result_components() {
            let cached_punit = Expr::const_(Name::from_string("PUnit"), vec![u.clone()]);
            let cached_punit_unit = Expr::const_(Name::from_string("PUnit.unit"), vec![u.clone()]);
            return DoMonadInfo {
                m,
                u,
                v,
                cached_punit,
                cached_punit_unit,
            };
        }

        // Branch 2: no expected type — fresh params (mkUnknownMonadResult)
        let u = self.fresh_universe_param();
        let v = self.fresh_universe_param();
        let m_ty = Expr::arrow(
            Expr::sort(Level::succ(u.clone())),
            Expr::sort(Level::succ(v.clone())),
        );
        let m = self.fresh_meta(m_ty);
        let cached_punit = Expr::const_(Name::from_string("PUnit"), vec![u.clone()]);
        let cached_punit_unit = Expr::const_(Name::from_string("PUnit.unit"), vec![u.clone()]);
        DoMonadInfo {
            m,
            u,
            v,
            cached_punit,
            cached_punit_unit,
        }
    }

    /// Elaborate a do-notation block by desugaring to Bind.bind / Pure.pure chains.
    ///
    /// Before elaboration, runs the nested action lifting pre-pass: any
    /// `<- expr` (LiftMethod) inside term positions is extracted into
    /// `let __do_lift_N <- expr` bindings prepended before the containing element.
    ///
    /// Sets `do_monad_info` for the duration of the block so that all
    /// `mk_bind_app` / `mk_pure_app` calls share a single `(m, u, v)`.
    pub(super) fn elab_do(&mut self, elems: &[DoElem]) -> Result<Expr, ElabError> {
        if elems.is_empty() {
            return Err(ElabError::NotImplemented("empty do block".into()));
        }

        // A do block has no intentional local-scope output: all binders are
        // abstracted into the produced bind/loop continuations. Pair the do-state
        // guard below with the generic local/meta transaction so a failing
        // element cannot strand a loop variable, catch binder, expected type, or
        // partial metavariable assignment in a reusable context.
        self.with_temporary_local_scope(|this| this.elab_do_inner(elems))
    }

    fn elab_do_inner(&mut self, elems: &[DoElem]) -> Result<Expr, ElabError> {
        // Save any outer do-block's monad info (for nested do blocks)
        let outer_monad_info = self.do_monad_info.take();
        let outer_control_info = self.do_control_info.take();
        let outer_control_stack = self.do_control_stack.take();
        let outer_wrapped_monad = self.do_wrapped_monad.take();
        let outer_loop_ctx = self.do_loop_ctx.take();
        let outer_mut_vars = std::mem::take(&mut self.do_mut_vars);
        let outer_pure_state = self.do_pure_state;
        self.do_pure_state = false;

        // Every path below is fallible. Compute the nested block's result inside
        // one closure, then restore the complete outer do context before
        // propagating success or error. Manual restoration at the tail is not
        // sufficient: any intervening `?` would strand nested monad/control/loop
        // state in the reusable ElabCtx.
        let result = (|| -> Result<Expr, ElabError> {
            // Create fresh monad info for this do-block
            self.do_monad_info = Some(self.mk_do_monad_info());

            // Pre-pass: expand nested actions (`<- expr`) in all elements
            let expanded = self.expand_all_nested_actions(elems);

            // Pre-pass: infer control info (#1818 Phase 3)
            // Determines which control effects (break, continue, early return, mutable
            // reassignment) are present.
            let mut control_info = infer_control_info_seq(&expanded);

            // Terminal return optimization: The ControlInfo pre-pass marks ALL Return
            // elements as `returns_early: true` (matching Lean 4's InferControlInfo.lean).
            // However, in clean's sequential elaboration model, the EarlyReturn transformer
            // (ExceptT) is only needed when `elab_do_early_return` is called, which
            // happens via the `[DoElem::Return(_, expr), rest @ ..]` dispatch pattern.
            // Returns that are terminal in the top-level sequence (including returns
            // inside terminal if/match branches) are handled by `elab_pure` and don't
            // need ExceptT wrapping.
            if control_info.returns_early && !has_top_level_non_terminal_return(&expanded) {
                control_info.returns_early = false;
            }

            // Build control stack from control info (#1818 Phase 4B/4C)
            // The stack wraps the base monad in transformers for break/continue/return/mut.
            // Brick B08 (`docs/plans/GAP_SWEEP_2026-07-09.md`): route mutating /
            // early-return blocks through the pure functional state-threading lane
            // (`elab_do_mut`) instead of the transformer stack — the stack left
            // `StateT.run`/`ExceptT.run` initial states as unsolved metavars,
            // leaking "Declaration contains free variables". The pure lane emits
            // ordinary `let`/`ite`/`Pure.pure` terms that kernel-check AND compute.
            //
            // Brick B23 extends the pure lane to `for x in xs do <mut body>`:
            // `for` loops over mutable accumulators (with `break`/`continue`
            // guards) lower to an inlined `ForIn.forIn`/`List.forIn` recursion
            // whose accumulator carries the mut state (`elab_do_pure_for`);
            // several accumulators pack into one right-nested `Prod` (B93).
            // Only `List` collections and reassign/let/let-mut/if/break/
            // continue/nested-for bodies are in scope — everything else the
            // pure-`for` handler rejects LOUD.
            //
            // `try`/`catch` still needs the transformer stack, so it keeps the
            // legacy path. `while`/`repeat`, and a `break`/`continue` that is NOT
            // enclosed by a loop, remain descoped LOUD (a typed error, never an
            // unbound-fvar term).
            let needs_stack = control_info.needs_control_stack();
            let has_try = elab_do_mut::do_block_has_try_catch(&expanded);
            let has_while_repeat = elab_do_mut::do_block_has_while_repeat(&expanded);
            let has_toplevel_break_continue =
                elab_do_mut::do_block_has_toplevel_break_continue(&expanded);

            // The legacy try/catch transformer lane has no authenticated
            // initial-state value to supply to `StateT.run`.  Reject this
            // combination before constructing the stack; emitting a fresh
            // state hole here previously produced a term with free variables.
            if has_try && !control_info.reassigns.is_empty() {
                return Err(ElabError::Unsupported {
                    feature: "`try`/`catch` combined with mutable reassignment is not supported until the genuine initial state can be threaded through StateT"
                        .into(),
                });
            }

            if needs_stack && !has_try && (has_while_repeat || has_toplevel_break_continue) {
                return Err(ElabError::Unsupported {
                    feature: "do-notation control flow: `while`/`repeat`, or a \
                          `break`/`continue` outside a `for` loop, combined with \
                          mutable state or early `return`, is not yet supported \
                          (B23 lowers `for`-over-mut only)"
                        .into(),
                });
            }

            let pure_state = needs_stack && !has_try;
            if pure_state {
                elab_do_mut::collect_do_mut_var_names(&expanded, &mut self.do_mut_vars);
                self.do_pure_state = true;
            } else if needs_stack {
                // Legacy transformer-stack lane (try/catch only, post-B08).
                // Resolve return_type: fresh metavar that unification will constrain
                // when the do-block's expected type is known.
                let return_type = if control_info.returns_early {
                    Some(self.fresh_meta(Expr::type_()))
                } else {
                    None
                };

                // Resolve mut_var_types: fresh metavars for each reassigned variable.
                // During elaboration of `let mut x := e`, the metavar will be unified
                // with x's actual type via the local binding.
                let mut_var_types: Vec<(String, Expr)> = control_info
                    .reassigns
                    .iter()
                    .map(|name| (name.clone(), self.fresh_meta(Expr::type_())))
                    .collect();
                let state_sigma = if mut_var_types.is_empty() {
                    None
                } else {
                    Some(elab_do_prod::build_sigma_type(self, &mut_var_types)?)
                };

                let stack =
                    elab_do_stack::ControlStack::build(&control_info, return_type, state_sigma)?;

                // Compute the wrapped monad for bind/pure calls inside this block.
                // When transformers are active, bind/pure must target the outermost
                // transformer monad, not the base monad.
                if stack.has_transformers() {
                    if let Some(ref info) = self.do_monad_info {
                        self.do_wrapped_monad = Some(stack.compute_wrapped_monad(info));
                    }
                }

                self.do_control_stack = Some(stack);
            }

            self.do_control_info = Some(control_info);

            let mut result = self.elab_do_elems(&expanded)?;

            // Apply transformer unwrapping if ControlStack is active (#1818 Phase 4C).
            // Each transformer layer is peeled off from outermost to innermost.
            // Take ownership temporarily to avoid borrow conflict with &mut self
            // (apply_control_unwrap needs &mut self for fresh_meta calls).
            {
                let stack_taken = self.do_control_stack.take();
                let info_taken = self.do_monad_info.take();
                if let (Some(ref stack), Some(ref info)) = (&stack_taken, &info_taken) {
                    if stack.has_transformers() {
                        result = self.apply_control_unwrap(result, stack, info)?;
                    }
                }
                // stack_taken and info_taken are this block's values, dropped here.
                // Outer values are restored below.
            }

            Ok(result)
        })();

        // Restore outer do-block state before propagating the nested result.
        self.do_monad_info = outer_monad_info;
        self.do_control_info = outer_control_info;
        self.do_control_stack = outer_control_stack;
        self.do_wrapped_monad = outer_wrapped_monad;
        self.do_loop_ctx = outer_loop_ctx;
        self.do_mut_vars = outer_mut_vars;
        self.do_pure_state = outer_pure_state;

        result
    }

    /// Expand nested actions across all do-elements, flattening lifted bindings
    /// into the element sequence.
    fn expand_all_nested_actions(&self, elems: &[DoElem]) -> Vec<DoElem> {
        let mut counter = 0usize;
        let mut result = Vec::with_capacity(elems.len());
        for elem in elems {
            let (lifted, new_elem) = self.expand_do_elem_actions(elem, &mut counter);
            result.extend(lifted);
            result.push(new_elem);
        }
        result
    }

    /// Recursively desugar a sequence of do-elements.
    ///
    /// Processes left-to-right, threading the monadic context through each element.
    pub(super) fn elab_do_elems(&mut self, elems: &[DoElem]) -> Result<Expr, ElabError> {
        stack_safe(|| match elems {
            [] => Err(ElabError::NotImplemented(
                "empty do element sequence".into(),
            )),

            // === Terminal (single) elements ===
            // #3517: use expected type so fresh implicits unify.
            [DoElem::Expr(_, expr)] => {
                let exp = self.current_expected_type.clone();
                let r = self.elaborate_with_expected_type(expr, exp)?;
                self.maybe_yield_wrap(r)
            }

            [DoElem::Return(_, expr)] => {
                // Inside a for-loop body, even terminal return is early return
                // (it stops the loop and returns from the enclosing function).
                if self.do_loop_ctx.is_some() {
                    return self.elab_do_early_return(expr);
                }
                self.elab_pure(expr)
            }

            [DoElem::Let(_, _, _)] | [DoElem::LetMut(_, _, _)] | [DoElem::LetRec(_, _)] => {
                Err(ElabError::NotImplemented(
                    "do block cannot end with a let binding (no continuation)".into(),
                ))
            }

            [DoElem::Bind(_, _, _)] => Err(ElabError::NotImplemented(
                "do block cannot end with a bind (no continuation)".into(),
            )),

            // === Compound (multi-element) sequences ===
            [DoElem::Bind(_, binder, action), rest @ ..] => {
                // let x <- e; rest  →  Bind.bind e (fun x => rest_desugared)
                self.elab_do_bind(binder, action, rest)
            }

            [DoElem::Let(_, binder, val), rest @ ..] => {
                // let x := e; rest  →  let x := e in rest_desugared
                self.elab_do_let(binder, val, rest)
            }

            [DoElem::LetMut(_, binder, val), rest @ ..] => self.elab_do_let(binder, val, rest),
            [DoElem::LetRec(_, decls), rest @ ..] => self.elab_do_let_rec_elem(decls, rest),

            [DoElem::Return(_, expr), ..] => {
                // Inside a for-loop body, return generates ForInStep.done with
                // the return value tunneled through the accumulator.
                if self.do_loop_ctx.is_some() {
                    return self.elab_do_early_return(expr);
                }
                // Non-terminal return: if we have a ControlStack with EarlyReturn,
                // use ExceptT.throw to exit early. Otherwise, just Pure.pure.
                if let Some(stack) = &self.do_control_stack {
                    if stack.return_layer_idx.is_some() {
                        return self.elab_do_early_return(expr);
                    }
                }
                // Terminal return or no EarlyReturn layer: Pure.pure e
                self.elab_pure(expr)
            }

            [DoElem::Expr(_, expr), rest @ ..] => {
                // e; rest  →  Bind.bind e (fun _ => rest_desugared)
                let binder = SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit);
                self.elab_do_bind(&binder, expr, rest)
            }

            // === If as do-element (terminal or compound) ===
            [DoElem::If(_, cond, then_branch, else_branch)] => {
                // B08 pure lane: `if` over mut / early-return guards thread
                // state as ordinary `ite` terms (see `elab_do_pure_if`).
                if self.do_pure_state {
                    return self.elab_do_pure_if(cond, then_branch, else_branch.as_deref(), &[]);
                }
                self.elab_do_if(cond, then_branch, else_branch.as_deref())
            }
            [DoElem::If(_, cond, then_branch, else_branch), rest @ ..] => {
                if self.do_pure_state {
                    return self.elab_do_pure_if(cond, then_branch, else_branch.as_deref(), rest);
                }
                // if cond then branch1 else branch2; rest
                // → Bind.bind (if cond then branch1 else branch2) (fun _ => rest)
                //
                // In STATEMENT position the `if`'s value is discarded (bound to
                // `_`) before `rest`, so it is an `m Unit` action — NOT the
                // block's result type. Pin the expected type to `m Unit` while
                // elaborating the branches, so a Unit-valued branch is accepted:
                // an explicit `if … then pure () else pure ()`, or a `unless`/
                // `when` guard (which desugars to exactly this shape). The
                // no-else path in `elab_do_if` already does this; the with-else
                // path otherwise elaborates both branches at the block result
                // type and rejects `pure ()` (Nat vs Unit). Absent monad info,
                // fall back to the historical ambient-typed elaboration.
                let saved_expected = self.current_expected_type.take();
                if let Some(info) = self.do_monad_info.as_ref() {
                    let unit_ty = Expr::const_(Name::from_string("Unit"), vec![]);
                    self.current_expected_type = Some(Expr::app(info.m.clone(), unit_ty));
                }
                let if_result = self.elab_do_if(cond, then_branch, else_branch.as_deref());
                self.current_expected_type = saved_expected;
                let if_expr = if_result?;
                let binder = SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit);
                self.elab_do_bind_expr(&binder, if_expr, rest)
            }

            // === IfLet as do-element (terminal or compound) ===
            [DoElem::IfLet(_, pat, scrutinee, then_branch, else_branch)] => {
                self.elab_do_if_let(pat, scrutinee, then_branch, else_branch.as_deref())
            }
            [DoElem::IfLet(_, pat, scrutinee, then_branch, else_branch), rest @ ..] => {
                let expr =
                    self.elab_do_if_let(pat, scrutinee, then_branch, else_branch.as_deref())?;
                let binder = SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit);
                self.elab_do_bind_expr(&binder, expr, rest)
            }

            // === IfDecidable as do-element (terminal or compound) ===
            [DoElem::IfDecidable(_, witness, prop, then_branch, else_branch)] => {
                self.elab_do_if_decidable(witness, prop, then_branch, else_branch.as_deref())
            }
            [DoElem::IfDecidable(_, witness, prop, then_branch, else_branch), rest @ ..] => {
                let expr =
                    self.elab_do_if_decidable(witness, prop, then_branch, else_branch.as_deref())?;
                let binder = SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit);
                self.elab_do_bind_expr(&binder, expr, rest)
            }

            // === For as do-element (terminal or compound) ===
            // B23 pure lane: `for x in xs do <mut body>` threads the mutable
            // accumulator through an inlined `List.forIn` recursion that
            // kernel-checks AND computes (`elab_do_pure_for`). B96: a body
            // with an early `return` routes through the same lane even with
            // no `mut` state (0-var pack + Option-tunneling accumulator),
            // whenever the block's monad is concrete — the monadic ForIn lane
            // has no computing lowering for those bodies
            // (`pure_for_return_routes`).
            [DoElem::For(_, binder, collection, body)] => {
                if self.do_pure_state || self.pure_for_return_routes(body) {
                    return self.elab_do_pure_for(binder, collection, body, &[]);
                }
                let result = self.elab_do_for(binder, collection, body)?;
                self.maybe_yield_wrap(result)
            }
            [DoElem::For(_, binder, collection, body), rest @ ..] => {
                if self.do_pure_state || self.pure_for_return_routes(body) {
                    return self.elab_do_pure_for(binder, collection, body, rest);
                }
                self.elab_do_for_compound(binder, collection, body, rest)
            }

            // === Match as do-element (terminal or compound) ===
            // Branches call elab_do_elems recursively; terminals in branches
            // get yield wrapping via the do_loop_ctx check above.
            [DoElem::Match(_, discrs, arms)] => self.elab_do_match(discrs, arms),
            [DoElem::Match(_, discrs, arms), rest @ ..] => {
                let match_expr = self.elab_do_match(discrs, arms)?;
                let discard_binder = SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit);
                self.elab_do_bind_expr(&discard_binder, match_expr, rest)
            }

            // === TryCatch as do-element (terminal or compound) ===
            // Branches call elab_do_elems recursively; terminals handled.
            [DoElem::TryCatch(_, try_body, catches, finally_body)] => {
                self.elab_do_try_catch(try_body, catches, finally_body.as_deref())
            }
            [DoElem::TryCatch(_, try_body, catches, finally_body), rest @ ..] => {
                let try_expr =
                    self.elab_do_try_catch(try_body, catches, finally_body.as_deref())?;
                let discard_binder = SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit);
                self.elab_do_bind_expr(&discard_binder, try_expr, rest)
            }

            // === LetElse (refutable pattern bind) as compound element ===
            [DoElem::LetElse(_, pat, action, fallback)] => {
                // Terminal refutable let — elaborate action, match, then use
                // then-branch = pure () (no continuation), else = fallback
                self.elab_do_let_else(pat, action, fallback, &[])
            }
            [DoElem::LetElse(_, pat, action, fallback), rest @ ..] => {
                self.elab_do_let_else(pat, action, fallback, rest)
            }
            [DoElem::LetExpr(_, pat, discr, kind, fallback)] => {
                self.elab_do_let_expr_elem(pat, discr, *kind, fallback, &[])
            }
            [DoElem::LetExpr(_, pat, discr, kind, fallback), rest @ ..] => {
                self.elab_do_let_expr_elem(pat, discr, *kind, fallback, rest)
            }

            // === Repeat (infinite loop) as do-element ===
            [DoElem::Repeat(_, body)] | [DoElem::Repeat(_, body), ..] if self.do_pure_state => {
                let _ = body;
                Err(ElabError::Unsupported {
                    feature: "`repeat` loops over mutable state are not supported \
                              (B23 lowers `for`-over-mut only)"
                        .into(),
                })
            }
            [DoElem::Repeat(_, body)] => {
                let result = self.elab_do_repeat(body)?;
                self.maybe_yield_wrap(result)
            }
            [DoElem::Repeat(_, body), rest @ ..] => {
                let expr = self.elab_do_repeat(body)?;
                let binder = SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit);
                self.elab_do_bind_expr(&binder, expr, rest)
            }

            // === While (conditional loop) as do-element ===
            [DoElem::While(_, cond, body)] | [DoElem::While(_, cond, body), ..]
                if self.do_pure_state =>
            {
                let _ = (cond, body);
                Err(ElabError::Unsupported {
                    feature: "`while` loops over mutable state are not supported \
                              (B23 lowers `for`-over-mut only)"
                        .into(),
                })
            }
            [DoElem::While(_, cond, body)] => {
                let result = self.elab_do_while(cond, body)?;
                self.maybe_yield_wrap(result)
            }
            [DoElem::While(_, cond, body), rest @ ..] => {
                let expr = self.elab_do_while(cond, body)?;
                let binder = SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit);
                self.elab_do_bind_expr(&binder, expr, rest)
            }

            // === DbgTrace as do-element ===
            [DoElem::DbgTrace(_, msg)] => self.elab_do_dbg_trace(msg, &[]),
            [DoElem::DbgTrace(_, msg), rest @ ..] => self.elab_do_dbg_trace(msg, rest),

            // === Break (BreakT = OptionT failure at break layer) ===
            // Break already produces ForInStep.done when do_loop_ctx is active.
            // In the B23 pure lane a `break`/`continue` that reaches this level
            // is NOT enclosed by a `for` loop (the loop handler consumes its own
            // break/continue) — reject LOUD, never a free-var term.
            [DoElem::Break(_), ..] if self.do_pure_state => Err(ElabError::Unsupported {
                feature: "`break` outside a `for` loop is not valid in a mutating \
                          `do` block (B23)"
                    .into(),
            }),
            [DoElem::Break(_), ..] => self.elab_do_break(),

            // === Continue (ContinueT = OptionT failure at continue layer) ===
            // Continue already produces ForInStep.yield when do_loop_ctx is active.
            [DoElem::Continue(_), ..] if self.do_pure_state => Err(ElabError::Unsupported {
                feature: "`continue` outside a `for` loop is not valid in a mutating \
                          `do` block (B23)"
                    .into(),
            }),
            [DoElem::Continue(_), ..] => self.elab_do_continue(),

            // === Reassign: `x := new_val` ===
            // Inside a for-loop: let-shadowing + DoLoopContext update.
            // Outside: StateT.set via ControlStack.
            [DoElem::Reassign(_, name, val)] => {
                if self.do_loop_ctx.is_some() && self.is_loop_mut_var(name) {
                    self.elab_do_reassign_in_loop(name, val, &[])
                } else if self.do_pure_state {
                    // A do-block cannot end with a reassignment — it produces no
                    // value. Loud, not a free-variable term.
                    Err(ElabError::Unsupported {
                        feature: "a `do` block cannot end with a `:=` reassignment \
                                  (it produces no value)"
                            .into(),
                    })
                } else {
                    self.elab_do_reassign(name, val)
                }
            }
            [DoElem::Reassign(_, name, val), rest @ ..] => {
                if self.do_loop_ctx.is_some() && self.is_loop_mut_var(name) {
                    self.elab_do_reassign_in_loop(name, val, rest)
                } else if self.do_pure_state {
                    // B08 pure lane: `x := v` desugars to `let`-shadowing.
                    self.elab_do_reassign_pure(name, val, rest)
                } else {
                    self.elab_do_reassign_with_rest(name, val, rest)
                }
            }
            [DoElem::PatternReassign(span, pat, val), rest @ ..] => {
                self.elab_do_elems(&self.desugar_pattern_reassign(*span, pat, val, rest))
            }
        })
    }

    /// Build the full `@Bind.bind.{u,v} m α β action continuation` application.
    ///
    /// Kernel decl (data_monad.rs): `Bind.bind.{u,v} : {m : Type u → Type v} → {α β : Type u} → m α → (α → m β) → m β`
    /// 5 args total: m (implicit), α (implicit), β (implicit), action (explicit), continuation (explicit)
    ///
    /// Note: The kernel declaration omits the [Bind m] instance arg (simplified axiom).
    /// We match the kernel's 5-arg form: @Bind.bind.{u,v} m α β action continuation
    ///
    /// Uses cached `DoMonadInfo` when inside a do-block (#1814), matching Lean 4's
    /// pattern of reusing `info.m`, `info.u`, `info.v` from `(← read).monadInfo`.
    pub(super) fn mk_bind_app(&mut self, action: Expr, continuation: Expr) -> Expr {
        let (base_u, base_v, base_m) = self.get_or_create_monad_info();
        let (u, v, m, beta) = self.expected_do_result_components().unwrap_or_else(|| {
            let type_u = Expr::sort(Level::succ(base_u.clone()));
            (base_u, base_v, base_m, self.fresh_meta(type_u))
        });

        let bind_const = Expr::const_(Name::from_string("Bind.bind"), vec![u.clone(), v.clone()]);

        // α : Type u, β : Type u (Type u = Sort(u+1))
        let alpha = self
            .try_extract_bind_inner_type(&action)
            .unwrap_or_else(|| self.fresh_meta(Expr::sort(Level::succ(u.clone()))));

        // @Bind.bind.{u,v} m α β action continuation
        let e = Expr::app(bind_const, m);
        let e = Expr::app(e, alpha);
        let e = Expr::app(e, beta);
        let e = Expr::app(e, action);
        Expr::app(e, continuation)
    }

    /// Build the full `@Pure.pure.{u,v} m α val` application.
    ///
    /// Lean 4 signature: `Pure.pure.{u,v} : {m : Type u → Type v} → {α : Type u} → α → m α`
    /// Kernel decl (data_monad.rs): `Pure.pure` with level_params [u, v], 3 args (m implicit, α implicit, val explicit)
    ///
    /// Note: The kernel declaration omits the [Pure m] instance arg (simplified axiom).
    /// We match the kernel's 3-arg form: @Pure.pure.{u,v} m α val
    ///
    /// Uses cached `DoMonadInfo` when inside a do-block (#1814).
    pub(super) fn mk_pure_app(&mut self, val: Expr) -> Expr {
        let (base_u, base_v, base_m) = self.get_or_create_monad_info();
        let (u, v, m, alpha) = self.expected_do_result_components().unwrap_or_else(|| {
            let type_u = Expr::sort(Level::succ(base_u.clone()));
            (base_u, base_v, base_m, self.fresh_meta(type_u))
        });

        let pure_const = Expr::const_(Name::from_string("Pure.pure"), vec![u.clone(), v.clone()]);

        // @Pure.pure.{u,v} m α val
        let e = Expr::app(pure_const, m);
        let e = Expr::app(e, alpha);
        Expr::app(e, val)
    }

    /// Build `@Pure.pure.{u,v} m α val` with an **explicitly supplied** value
    /// type `α`, rather than reading the do-block's expected inner type.
    ///
    /// The do-block's `α` (from `expected_do_result_components`) is the type of
    /// the *whole block's* result, which is wrong for a `pure` whose value type
    /// is locally known and differs — notably the synthesized `pure ()` of a
    /// no-else statement-position `if`, whose value is `()` : `Unit` regardless
    /// of the block's result type. Mirrors `mk_pure_app` otherwise.
    pub(super) fn mk_pure_app_at(&mut self, alpha: Expr, val: Expr) -> Expr {
        let (base_u, base_v, base_m) = self.get_or_create_monad_info();
        let (u, v, m) = self
            .expected_do_result_components()
            .map(|(u, v, m, _alpha)| (u, v, m))
            .unwrap_or((base_u, base_v, base_m));

        let pure_const = Expr::const_(Name::from_string("Pure.pure"), vec![u, v]);
        let e = Expr::app(pure_const, m);
        let e = Expr::app(e, alpha);
        Expr::app(e, val)
    }

    /// The inner result type `α` of the `do`-block's expected monad type `m α`,
    /// if an expected type is in scope and decomposes as a monad application.
    ///
    /// Used to give a leading-dot-constructor payload of `pure`/`return` the
    /// concrete inductive type it needs to resolve against (see `elab_pure`).
    pub(super) fn expected_do_result_alpha(&self) -> Option<Expr> {
        self.expected_do_result_components()
            .map(|(_, _, _, alpha)| alpha)
    }

    pub(super) fn expected_do_result_components(&self) -> Option<(Level, Level, Expr, Expr)> {
        let expected_ty = self.current_expected_type.clone()?;
        let expected_ty = self.metas.instantiate(&expected_ty);
        let expected_ty = self.metas.instantiate_levels(&expected_ty);

        // Try the App(m, α) decomposition BEFORE whnf reduction (#3419).
        // Monad abbreviations like `MySem Nat` = `App(MySem, Nat)` should be
        // matched as `m = MySem, α = Nat` without unfolding the abbreviation.
        // Full whnf would unfold `StateT MyState (Except MyError) Nat` to a Pi
        // type `MyState → Except MyError (Prod Nat MyState)`, destroying the
        // monadic structure and causing `expected_do_result_components` to fail.
        // This causes fresh monad metas to be created that are never resolved,
        // leaking FVars into the kernel term.
        //
        // We try unreduced first, then fall through to whnf for cases where the
        // expected type needs head reduction to expose the App form (e.g., let
        // bindings or meta-variable solutions).
        if let Some(result) = self.try_decompose_monad_app(&expected_ty) {
            return Some(result);
        }

        // Fallback: whnf reduce and try again. This handles cases like
        // `let m := Id in m Nat` where the App form only appears after reduction.
        let expected_ty = self.whnf(&expected_ty);
        self.try_decompose_monad_app(&expected_ty)
    }

    /// Try to decompose an expression of the form `App(m, α)` into `(u, v, m, α)`
    /// where `m : Type u → Type v`.
    fn try_decompose_monad_app(&self, ty: &Expr) -> Option<(Level, Level, Expr, Expr)> {
        let v = Self::sort_level_input(&self.whnf(&self.infer_type(ty).ok()?))?;
        match ty.kind() {
            ExprKind::App(m, result_ty) => {
                let result_ty = result_ty.as_ref().clone();
                let result_ty_ty = self.whnf(&self.infer_type(&result_ty).ok()?);
                let u = Self::sort_level_input(&result_ty_ty)?;
                Some((u, v, m.as_ref().clone(), result_ty))
            }
            _ => None,
        }
    }

    fn sort_level_input(expr_ty: &Expr) -> Option<Level> {
        let ExprKind::Sort(level) = expr_ty.kind() else {
            return None;
        };
        match level {
            Level::Succ(inner) => Some(inner.as_ref().clone()),
            Level::Zero => Some(Level::zero()),
            _ => None,
        }
    }
}
