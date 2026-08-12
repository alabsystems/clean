// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pure functional state-threading lane for `do`-notation mutation and
//! control flow (Brick **B08** — `docs/plans/GAP_SWEEP_2026-07-09.md`).
//!
//! # What this lane does
//!
//! Lean's real `do` elaborator ([`src/Lean/Elab/Do.lean`]) tracks the set of
//! `mut` variables, threads them as a tuple through a `StateT`/`ExceptT`/
//! `ForInStep` join-point machine, and lowers `for`/`break`/`continue`/`return`
//! onto that machine. Clean's earlier attempt at that transformer stack left
//! the `StateT.run`/`ExceptT.run` initial-state arguments as unsolved
//! metavariables, so every mutating block failed kernel registration with
//! "Declaration contains free variables" (GAP_SWEEP do_notation rows
//! p08/p12/p13/p14/p15/p16).
//!
//! For the fragment of that language that carries **no genuine monad effect on
//! the state** — straight-line `mut` reassignment, `if`-without-`else` over
//! `mut`, and tail-position early-`return` guards — the state does not need a
//! transformer at all: it is exactly Lean's own observation that a `mut`
//! variable with no escaping control flow desugars to `let`-shadowing. This
//! lane implements that fragment directly, producing ordinary
//! `let`/`ite`/`Pure.pure`/`Bind.bind` terms that the kernel both accepts AND
//! reduces (so `rfl` value pins compute), which is the honest, computable
//! subset of B08.
//!
//! # Descope discipline
//!
//! Bricks B23/B93 extend the lane to `for..in` over `List` (with
//! `break`/`continue`, body-local `let mut`, nested `for`, and one-or-many
//! `Prod`-packed accumulators — see `elab_do_pure_for`); brick B96 adds
//! early `return` inside `for` bodies (both with and without `mut`
//! accumulators, including nested loops) via an `Option`-tunneling
//! accumulator slot. Everything still outside the fragment — `while`,
//! `repeat`, a `break`/`continue` outside a loop, multi-variable `if`
//! joins, non-tail early return outside a loop — is rejected LOUD
//! with a typed [`ElabError::Unsupported`], never with an unbound-fvar
//! term the kernel rejects with a confusing "free variables" message. The
//! gate that routes into / away from this lane lives in `elab_do`.
//!
//! Ground truth: Lean 4 `src/Lean/Elab/Do.lean` (`mkMutableCode`,
//! `ToTerm.run`, the `doIf`/`doReturn` codegen).

use super::elab_do_control::{infer_control_info_seq, ControlInfo};
use super::*;
use clean_parser::{DoElem, SurfaceBinder, SurfaceBinderInfo};

/// Ordered accumulator bundle threaded through the B23/B93/B96 `for`
/// lowering: the sorted accumulator names and types, the mut-only pack, the
/// FULL `ForIn` accumulator type `beta`, and the early-return tunnel (B96).
struct ForAccState {
    /// Sorted accumulator variable names. May be EMPTY for a B96 loop whose
    /// only accumulator content is the early-return `Option` slot.
    vars: Vec<String>,
    /// Types parallel to `vars`.
    tys: Vec<Expr>,
    /// The mut-only pack type: `tys[0]` itself when single (B23,
    /// byte-identical), right-nested `Prod` when several (B93); `None` when
    /// `vars` is empty.
    mut_beta: Option<Expr>,
    /// The full `ForIn` accumulator type: `mut_beta` alone (no `return`),
    /// `Option R` (return, no muts), or `Prod (Option R) mut_beta` (both).
    beta: Expr,
    /// `Some((R, level_of_R))` when the body tunnels an early `return e : R`
    /// through the accumulator (B96); `R` is the do-block's result type.
    tunnel: Option<(Expr, Level)>,
}

impl<'a> ElabCtx<'a> {
    /// Type of the most-recent local named `name`, if in scope.
    fn lookup_local_ty(&self, name: &str) -> Option<Expr> {
        self.locals
            .iter()
            .rev()
            .find(|(n, _, _)| n == name)
            .map(|(_, _, ty)| ty.clone())
    }

    /// FVarId of the most-recent local named `name`, if in scope.
    fn lookup_local_fvar(&self, name: &str) -> Option<FVarId> {
        self.locals
            .iter()
            .rev()
            .find(|(n, _, _)| n == name)
            .map(|(_, fvar, _)| *fvar)
    }

    fn immutable_reassign_err(name: &str) -> ElabError {
        ElabError::Unsupported {
            feature: format!(
                "reassignment of immutable variable `{name}` — only `let mut` \
                 variables can be reassigned with `:=`"
            ),
        }
    }

    /// Build `ite`/`Bool.rec` selecting `then_expr`/`else_expr` at result type
    /// `result_ty`, resolving the `Decidable` instance (Prop) or taking the
    /// Bool→Prop lane (`mk_bool_if`) exactly as `elab_do_if` / `elab_if` do.
    fn mk_do_ite(
        &mut self,
        cond_expr: Expr,
        then_expr: Expr,
        else_expr: Expr,
        result_ty: Expr,
    ) -> Result<Expr, ElabError> {
        let result_ty = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&result_ty));
        let level = self.infer_sort(&result_ty)?;
        let cond_is_bool = self.condition_is_bool(&cond_expr)?;
        if cond_is_bool {
            return Ok(self.mk_bool_if(&level, &result_ty, cond_expr, then_expr, else_expr));
        }
        let ite_const = Expr::const_(Name::from_string("ite"), vec![level]);
        let inst = self.resolve_decidable(&cond_expr)?;
        Ok(Expr::apps(
            ite_const,
            [result_ty, cond_expr, inst, then_expr, else_expr],
        ))
    }

    /// `x := v; rest` in the pure lane → `let x := v in rest` (shadowing).
    ///
    /// The reassigned name must be a `let mut` variable in scope; a plain
    /// (immutable) binding rejects LOUD, matching Lean's "cannot reassign
    /// immutable variable" (do_notation/p19).
    pub(super) fn elab_do_reassign_pure(
        &mut self,
        name: &str,
        val: &SurfaceExpr,
        rest: &[DoElem],
    ) -> Result<Expr, ElabError> {
        if !self.do_mut_vars.iter().any(|v| v == name) {
            return Err(Self::immutable_reassign_err(name));
        }
        let ty = self
            .lookup_local_ty(name)
            .ok_or_else(|| ElabError::Unsupported {
                feature: format!("mutable variable `{name}` is not in scope for reassignment"),
            })?;
        // Elaborate the value against the mutable local's tracked type — this
        // both clears the do-block's own `m β` expected type (so `x := x + n`
        // elaborates at `Nat`, not `Option Nat`) and rejects a mismatched
        // reassignment (`x := <wrong-type>`) rather than shipping an ill-typed
        // term to the kernel (Lean parity, do_notation/p19-adjacent).
        let val_expr = self.elaborate_with_expected_type(val, Some(ty.clone()))?;
        self.enforce_expr_type(&val_expr, &ty)?;
        let fvar = self.push_local(name.to_string(), ty.clone());
        let rest_expr = self.elab_do_elems(rest)?;
        self.pop_local();
        let rest_inst = self.metas.instantiate(&rest_expr);
        let body_abs = rest_inst.abstract_fvar(fvar);
        Ok(Expr::let_named(
            Name::from_string(name),
            ty,
            val_expr,
            body_abs,
            false,
        ))
    }

    /// Thread a straight-line `if`-branch as `let`-shadowing and return the
    /// final value of `yield_var`. The branch must contain only `Reassign` /
    /// plain `Let` (no monadic bind, no nested control) — anything else is a
    /// LOUD descope.
    fn elab_pure_state_branch_value(
        &mut self,
        branch: &[DoElem],
        yield_var: &str,
    ) -> Result<Expr, ElabError> {
        match branch {
            [] => {
                let fvar =
                    self.lookup_local_fvar(yield_var)
                        .ok_or_else(|| ElabError::Unsupported {
                            feature: format!("mutable variable `{yield_var}` is not in scope"),
                        })?;
                Ok(Expr::fvar(fvar))
            }
            [DoElem::Reassign(_, name, val), rest @ ..] => {
                if !self.do_mut_vars.iter().any(|v| v == name) {
                    return Err(Self::immutable_reassign_err(name));
                }
                let ty = self
                    .lookup_local_ty(name)
                    .ok_or_else(|| ElabError::Unsupported {
                        feature: format!("mutable variable `{name}` is not in scope"),
                    })?;
                let val_expr = self.elaborate_with_expected_type(val, Some(ty.clone()))?;
                self.enforce_expr_type(&val_expr, &ty)?;
                let fvar = self.push_local(name.clone(), ty.clone());
                let rest_val = self.elab_pure_state_branch_value(rest, yield_var);
                self.pop_local();
                let rest_val = rest_val?;
                let rest_inst = self.metas.instantiate(&rest_val);
                let body_abs = rest_inst.abstract_fvar(fvar);
                Ok(Expr::let_named(
                    Name::from_string(name),
                    ty,
                    val_expr,
                    body_abs,
                    false,
                ))
            }
            [DoElem::Let(_, binder, val), rest @ ..] => {
                let (ty, val_expr) = match &binder.ty {
                    Some(t) => {
                        let ty = self.elaborate(t)?;
                        let val_expr = self.elaborate_with_expected_type(val, Some(ty.clone()))?;
                        (ty, val_expr)
                    }
                    None => {
                        let val_expr = self.elaborate_with_expected_type(val, None)?;
                        let ty = self.infer_type(&val_expr)?;
                        (ty, val_expr)
                    }
                };
                let fvar = self.push_local(binder.name.clone(), ty.clone());
                let rest_val = self.elab_pure_state_branch_value(rest, yield_var);
                self.pop_local();
                let rest_val = rest_val?;
                let rest_inst = self.metas.instantiate(&rest_val);
                let body_abs = rest_inst.abstract_fvar(fvar);
                Ok(Expr::let_named(
                    Name::from_string(&binder.name),
                    ty,
                    val_expr,
                    body_abs,
                    false,
                ))
            }
            _ => Err(ElabError::Unsupported {
                feature: "do-notation `if` branch over mutable state must be a \
                          straight-line `let`/reassignment sequence (B08)"
                    .into(),
            }),
        }
    }

    /// Elaborate `if cond then T [else E]; rest` in the pure state lane.
    ///
    /// Three supported shapes (else → LOUD descope):
    /// - **plain monadic** `if` (branches touch no `mut`, no `return`):
    ///   delegates to the ordinary [`ElabCtx::elab_do_if`] path.
    /// - **early-return guard** — one branch always exits via `return`; the
    ///   other branch's fall-through is the continuation (`rest`). Lowers to
    ///   `ite result_ty cond inst (pure retVal) (⟦continuation⟧)`.
    ///   (do_notation/p16.)
    /// - **single-variable `mut` join** — both branches only reassign one
    ///   `mut` variable. Lowers to `let x := ite _ cond inst xThen xElse; rest`.
    ///   (do_notation/p08.)
    pub(super) fn elab_do_pure_if(
        &mut self,
        cond: &SurfaceExpr,
        then_branch: &[DoElem],
        else_branch: Option<&[DoElem]>,
        rest: &[DoElem],
    ) -> Result<Expr, ElabError> {
        let then_info = infer_control_info_seq(then_branch);
        let else_info = else_branch
            .map(infer_control_info_seq)
            .unwrap_or_else(ControlInfo::pure);

        // `break`/`continue` never reach the pure lane (gated in elab_do), but
        // guard defensively.
        if then_info.breaks || then_info.continues || else_info.breaks || else_info.continues {
            return Err(ElabError::Unsupported {
                feature: "`break`/`continue` inside a mutating `do` block is not \
                          yet supported (B08)"
                    .into(),
            });
        }

        let then_pure = then_info.reassigns.is_empty() && !then_info.returns_early;
        let else_pure = else_info.reassigns.is_empty() && !else_info.returns_early;
        let then_exits = then_info.num_regular_exits == 0;
        let else_exits = else_info.num_regular_exits == 0;

        // Plain monadic if: no state / early-return interaction. Delegate.
        if then_pure && else_pure && !then_exits && !else_exits {
            let if_expr = self.elab_do_if(cond, then_branch, else_branch)?;
            if rest.is_empty() {
                return Ok(if_expr);
            }
            let binder = SurfaceBinder::new("_", None, SurfaceBinderInfo::Explicit);
            return self.elab_do_bind_expr(&binder, if_expr, rest);
        }

        // Early-return guard: the then-branch always exits (and does not touch
        // mut). The continuation is (else ++ rest) — or just rest when the else
        // is empty.
        if then_exits && then_info.reassigns.is_empty() {
            let result_ty = self.current_expected_type.clone();
            let cond_expr = self.elaborate_with_expected_type(cond, None)?;
            let then_expr = self.elab_do_elems(then_branch)?;
            let mut cont: Vec<DoElem> = Vec::new();
            if let Some(e) = else_branch {
                cont.extend_from_slice(e);
            }
            cont.extend_from_slice(rest);
            let else_expr = self.elab_do_elems(&cont)?;
            let result_ty = match result_ty {
                Some(result_ty) => result_ty,
                None => self.infer_type(&then_expr)?,
            };
            return self.mk_do_ite(cond_expr, then_expr, else_expr, result_ty);
        }
        // Symmetric guard: the else-branch always exits; the then-branch's
        // fall-through continues into `rest`.
        if let Some(else_elems) = else_branch {
            if else_exits && else_info.reassigns.is_empty() && then_info.reassigns.is_empty() {
                let result_ty = self.current_expected_type.clone();
                let cond_expr = self.elaborate_with_expected_type(cond, None)?;
                let else_expr = self.elab_do_elems(else_elems)?;
                let mut cont: Vec<DoElem> = then_branch.to_vec();
                cont.extend_from_slice(rest);
                let then_expr = self.elab_do_elems(&cont)?;
                let result_ty = match result_ty {
                    Some(result_ty) => result_ty,
                    None => self.infer_type(&then_expr)?,
                };
                return self.mk_do_ite(cond_expr, then_expr, else_expr, result_ty);
            }
        }

        // Single-variable mut join: both branches only reassign one mut var.
        if then_info.returns_early || else_info.returns_early {
            return Err(ElabError::Unsupported {
                feature: "do-notation early `return` is only supported as a \
                          tail-position `if` guard (B08)"
                    .into(),
            });
        }
        let mut mutated: Vec<String> = then_info
            .reassigns
            .union(&else_info.reassigns)
            .cloned()
            .collect();
        mutated.sort();
        if mutated.len() == 1 && !then_exits && !else_exits {
            let var = mutated[0].clone();
            if !self.do_mut_vars.contains(&var) {
                return Err(Self::immutable_reassign_err(&var));
            }
            let (var_fvar, var_ty) =
                match (self.lookup_local_fvar(&var), self.lookup_local_ty(&var)) {
                    (Some(f), Some(t)) => (f, t),
                    _ => {
                        return Err(ElabError::Unsupported {
                            feature: format!("mutable variable `{var}` is not in scope"),
                        })
                    }
                };
            let cond_expr = self.elaborate_with_expected_type(cond, None)?;
            let then_val = self.elab_pure_state_branch_value(then_branch, &var)?;
            let else_val = match else_branch {
                Some(e) => self.elab_pure_state_branch_value(e, &var)?,
                None => Expr::fvar(var_fvar),
            };
            let joined = self.mk_do_ite(cond_expr, then_val, else_val, var_ty.clone())?;
            let fvar = self.push_local(var.clone(), var_ty.clone());
            let rest_expr = self.elab_do_elems(rest)?;
            self.pop_local();
            let rest_inst = self.metas.instantiate(&rest_expr);
            let body_abs = rest_inst.abstract_fvar(fvar);
            return Ok(Expr::let_named(
                Name::from_string(&var),
                var_ty,
                joined,
                body_abs,
                false,
            ));
        }

        Err(ElabError::Unsupported {
            feature: "do-notation `if` over mutable state: only single-variable \
                      joins and tail early-return guards are supported (B08)"
                .into(),
        })
    }

    // ════════════════════════════════════════════════════════════════════════
    // Bricks B23/B93 — `for x in xs do <mut body>` (ForIn accumulate +
    // break/continue; multi-accumulator Prod packing)
    // ════════════════════════════════════════════════════════════════════════

    /// Lower `for x in xs do <body>; rest` in the pure state lane.
    ///
    /// The loop's accumulators are the `let mut` variables bound **outside**
    /// the loop that the body reassigns. One accumulator (the most common
    /// shape, `s := s + f x`) threads directly as the `ForIn` accumulator `β`
    /// — the original B23 lowering, preserved term-for-term. Several (B93)
    /// pack into a single right-nested `Prod` accumulator in sorted-name
    /// order:
    ///
    /// ```text
    /// Bind.bind (List.forIn-fold xs ⟦pack s₁ … sₙ⟧ (fun x acc => ⟦bodyₛ⟧))
    ///           (fun acc => let s₁ := acc.1; …; let sₙ := acc.2.….2; ⟦rest⟧)
    /// ```
    ///
    /// Body statements are limited to reassignment / plain `let` / `let mut`
    /// / `if` / `break` / `continue` / nested `for`. A `let mut` declared
    /// inside the body is **not** an accumulator — it is fresh per iteration
    /// and threads by the same `let`-shadowing as the accumulators. A nested
    /// `for` lowers recursively through the same core, its own accumulators
    /// resolved in the scope at its position. The loop lowers to the inlined
    /// `List.forIn` recursion (`build_list_forin_fold`) — the exact
    /// kernel-registered body of `List.forIn` (`data_for_in.rs`).
    ///
    /// `break`/`continue` inside the body lower to `ForInStep.done`/`.yield`
    /// over the packed current values. The emitted term uses Clean's
    /// simplified `Bind.bind`/`Pure.pure` (which the B07 materialization pass
    /// rewrites to computing instance-projected form) and kernel
    /// `Expr::proj` for the unpacking (which reduces on `Prod.mk`), so `rfl`
    /// value pins over `Option`/`Id` compute.
    ///
    /// The registered `ForIn.forIn`/`List.forIn` carry a `[Monad m]` binder
    /// (Lean-fidelity, olean import — commit A4) that Clean's opaque `Monad`
    /// axiom carrier cannot satisfy with a real term, so this lane inlines
    /// `List.forIn`'s recursion directly rather than applying the projection.
    ///
    /// Early `return e` inside the body (B96) tunnels through an `Option R`
    /// slot prepended to the accumulator (`R` = the do-block result type):
    /// `return e` lowers to `ForInStep.done (some e ⊗ muts)`, fall-through /
    /// `continue` to `yield (none ⊗ muts)`, `break` to `done (none ⊗ muts)`;
    /// after the loop the `Option` component is case-split (`some r → pure r`,
    /// `none →` rebind muts and continue). A nested loop's `return` tunnels
    /// onward through the ENCLOSING loop's `Option` slot.
    ///
    /// Anything outside this fragment (non-`List` collections, monadic binds
    /// in the body, unknown monad, accumulator types outside `Type _`) is
    /// rejected LOUD with a typed [`ElabError::Unsupported`].
    ///
    /// Ground truth: Lean 4 `src/Lean/Elab/Do.lean` (`ForIn` lowering; the
    /// tuple-packed mutable state; `doForToTerm`'s return tunneling), and
    /// `clean-kernel` `data_for_in.rs` (`List.forIn` body being inlined).
    pub(super) fn elab_do_pure_for(
        &mut self,
        binder: &SurfaceBinder,
        collection: &SurfaceExpr,
        body: &[DoElem],
        rest: &[DoElem],
    ) -> Result<Expr, ElabError> {
        self.elab_pure_for_core(binder, collection, body, None, |this| {
            this.elab_do_elems(rest)
        })
    }

    /// B96 routing predicate: `true` when a `for` body containing an early
    /// `return` should route through this pure state-threading lane even
    /// though the block carries no `mut` state. Requires do-block statement
    /// level (no active monadic-lane loop context, no legacy transformer
    /// stack) and a concrete (metavariable-free) do-block monad.
    /// The monadic `ForIn` lane has no computing lowering for these
    /// bodies (its `[Monad m]`-projected `ForIn.forIn` does not reduce, and
    /// its return continuation leaked out-of-scope fvars — the T1 "contains
    /// free variables" kernel rejection); the pure core lowers them to
    /// kernel-checked terms that compute.
    pub(super) fn pure_for_return_routes(&self, body: &[DoElem]) -> bool {
        if self.do_pure_state
            || self.do_loop_ctx.is_some()
            || self.do_control_stack.is_some()
            || self.do_wrapped_monad.is_some()
        {
            return false;
        }
        if !infer_control_info_seq(body).returns_early {
            return false;
        }
        // The result type `alpha` may still be an unassigned metavariable
        // here (`Id ?β` before the block's terminal pins it); the tunnel's
        // `return e` elaborates against it and assigns it, so only the monad
        // itself must be concrete.
        match self.expected_do_result_components() {
            Some((_, _, m, _alpha)) => {
                let m = self.metas.instantiate(&m);
                !self.has_metavars(&m)
            }
            None => false,
        }
    }

    /// Shared core of the B23/B93/B96 `for` lowering.
    ///
    /// `outer` is `None` at do-block level (the final `Bind.bind`'s result
    /// type `α` is the block's own result type, and a tunneled `return`
    /// finishes with `pure r`), or `Some(enclosing accumulator state)` when
    /// this loop is nested inside another pure-lane loop's step body (then
    /// `α = ForInStep β_outer`, and a tunneled `return` propagates as the
    /// enclosing loop's `ForInStep.done` — B96 nested tunneling). `elab_rest`
    /// elaborates the continuation with the accumulators re-bound in scope at
    /// their final values.
    fn elab_pure_for_core(
        &mut self,
        binder: &SurfaceBinder,
        collection: &SurfaceExpr,
        body: &[DoElem],
        outer: Option<&ForAccState>,
        elab_rest: impl FnOnce(&mut Self) -> Result<Expr, ElabError>,
    ) -> Result<Expr, ElabError> {
        let body_info = infer_control_info_seq(body);
        let returns_early = body_info.returns_early;

        // The accumulators: reassigned `let mut` variables bound OUTSIDE the
        // loop, in deterministic sorted-name order. A reassigned variable
        // declared by `let mut` INSIDE the body is fresh per iteration — the
        // step walker threads it; it never accumulates across iterations.
        let mut reassigned: Vec<String> = body_info.reassigns.iter().cloned().collect();
        reassigned.sort();
        let mut body_local_muts: Vec<String> = Vec::new();
        collect_do_mut_var_names(body, &mut body_local_muts);
        let mut vars: Vec<String> = Vec::new();
        for name in reassigned {
            let declared_in_body = body_local_muts.contains(&name);
            let in_scope = self.lookup_local_fvar(&name).is_some();
            if declared_in_body && in_scope {
                return Err(ElabError::Unsupported {
                    feature: format!(
                        "`for` loop body declares `let mut {name}` while a variable \
                         named `{name}` is also bound outside the loop; this \
                         shadowing reassignment is not supported (B93)"
                    ),
                });
            }
            if declared_in_body {
                continue;
            }
            if !self.do_mut_vars.contains(&name) {
                return Err(Self::immutable_reassign_err(&name));
            }
            if !in_scope {
                return Err(ElabError::Unsupported {
                    feature: format!(
                        "mutable variable `{name}` is not in scope for the `for` loop"
                    ),
                });
            }
            vars.push(name);
        }
        // A loop with neither an accumulator variable nor an early `return`
        // has nothing for this lane to thread (B23/B93). With a `return`, the
        // Option slot alone is a legitimate accumulator (B96, 0-var pack).
        if vars.is_empty() && !returns_early {
            return Err(ElabError::Unsupported {
                feature: "`for` loops over mutable state need at least one \
                          accumulator variable bound outside the loop (B23/B93)"
                    .into(),
            });
        }

        let mut var_fvars: Vec<FVarId> = Vec::with_capacity(vars.len());
        let mut var_tys: Vec<Expr> = Vec::with_capacity(vars.len());
        for name in &vars {
            match (self.lookup_local_fvar(name), self.lookup_local_ty(name)) {
                (Some(f), Some(t)) => {
                    var_fvars.push(f);
                    var_tys.push(t);
                }
                _ => {
                    return Err(ElabError::Unsupported {
                        feature: format!(
                            "mutable variable `{name}` is not in scope for the `for` loop"
                        ),
                    })
                }
            }
        }

        // The mut-only pack type: one variable threads its own type
        // (byte-identical to B23); several pack right-nested `Prod`.
        let mut_beta = if var_tys.is_empty() {
            None
        } else {
            Some(self.pack_acc_ty(&var_tys)?)
        };

        // The do-block's monad `m : Type do_u → Type do_v` must be concrete for
        // the lowered term to kernel-check AND compute. When the expected type
        // is unknown (`m` a metavariable) we cannot honestly build a computing
        // ForIn, so descope LOUD.
        let (do_u, do_v, m, block_alpha) =
            self.expected_do_result_components()
                .ok_or_else(|| ElabError::Unsupported {
                    feature: "a `for` loop over mutable state needs a known monad type \
                          (an expected result type) to desugar (B23)"
                        .into(),
                })?;
        let bind_alpha = match outer {
            Some(o) => Expr::app(
                Expr::const_(Name::from_string("ForInStep"), vec![do_u.clone()]),
                o.beta.clone(),
            ),
            None => block_alpha.clone(),
        };

        // The early-return tunnel (B96): `return e` carries `e : R` where `R`
        // is the do-block's result type, at EVERY nesting depth.
        let tunnel = if returns_early {
            let ret_ty = self.metas.instantiate(&block_alpha);
            let ret_level = self.acc_type_level(&ret_ty)?;
            Some((ret_ty, ret_level))
        } else {
            None
        };

        // The full ForIn accumulator type.
        let beta = match (&tunnel, &mut_beta) {
            (None, Some(mb)) => mb.clone(),
            (Some((ret_ty, ret_level)), None) => Self::option_ty(ret_ty, ret_level),
            (Some((ret_ty, ret_level)), Some(mb)) => {
                let opt_ty = Self::option_ty(ret_ty, ret_level);
                let lf = self.acc_type_level(&opt_ty)?;
                let lt = self.acc_type_level(mb)?;
                Expr::apps(
                    Expr::const_(Name::from_string("Prod"), vec![lf, lt]),
                    [opt_ty, mb.clone()],
                )
            }
            (None, None) => {
                return Err(ElabError::InternalInvariant(
                    "for-loop accumulator with neither mut pack nor return tunnel (B96)".into(),
                ))
            }
        };

        // Elaborate the collection with the do-block's `m β` expected type
        // cleared (the collection is `List α`, not a monadic action). Only
        // `List` collections are supported (the only registered `ForIn`
        // instance shape).
        let saved_expected = self.current_expected_type.take();
        let coll_result = self.elaborate(collection);
        self.current_expected_type = saved_expected;
        let coll_expr = coll_result?;
        let coll_ty = self.infer_type(&coll_expr)?;
        let coll_ty = self.whnf(&self.metas.instantiate(&coll_ty));
        let (alpha, coll_expr) = match coll_ty.kind() {
            ExprKind::App(head, elem) if matches!(head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("List")) => {
                (elem.as_ref().clone(), coll_expr)
            }
            // B144: `for x in (arr : Array α)` iterates the backing list.
            // `Array` wraps `List` (`Array.mk (data : List α)`, projection
            // `Array.data α arr : List α`), and this pure lane lowers the loop
            // to an inlined `List.rec` fold over a `List α` *term* — never a
            // synthesized `ForIn` instance. So iterating an array is exactly
            // iterating its backing list: feed `Array.data α arr` to the same
            // fold. `Array.data` is a real reducing projection, so a literal
            // `#[..]` (= `Array.mk (cons-chain)`) still computes; a variable
            // array stays well-typed and symbolic. `do_u` is the element level
            // the fold reconstructs `List.{do_u} α` at, so `Array.data` uses it
            // too (keeping the projected list's `List` head level matched).
            ExprKind::App(head, elem) if matches!(head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("Array")) =>
            {
                let alpha = elem.as_ref().clone();
                let data_const = Expr::const_(Name::from_string("Array.data"), vec![do_u.clone()]);
                let as_list = Expr::apps(data_const, [alpha.clone(), coll_expr]);
                (alpha, as_list)
            }
            // R144: `for c in (s : String)` iterates the backing `List Char`.
            // `String` is a NON-polymorphic structure (`String.mk (data : List
            // Char)`, projection `String.data s : List Char` — no level params,
            // element `Char : Type 0`), so its collection type is a bare
            // `Const("String")`, not an `App`. Exactly as the `Array` case,
            // feed the backing list `String.data s` to the same inlined
            // `List.rec` fold; the fold reconstructs `List.{do_u} Char`, which
            // matches `String.data`'s `List.{0} Char` in the ordinary case
            // (`do_u = 0`, e.g. an `Id`/`Option`/`IO` do-block), and otherwise
            // the `infer_type(&fold)` backstop below rejects LOUD.
            ExprKind::Const(n, _) if *n == Name::from_string("String") => {
                let alpha = Expr::const_(Name::from_string("Char"), vec![]);
                let data_const = Expr::const_(Name::from_string("String.data"), vec![]);
                let as_list = Expr::app(data_const, coll_expr);
                (alpha, as_list)
            }
            _ => {
                return Err(ElabError::Unsupported {
                    feature: "`for` loops in a mutating `do` block are only supported \
                              over `List`, `Array`, and `String` collections (B23)"
                        .into(),
                })
            }
        };

        let loop_var_ty = match &binder.ty {
            Some(ty_surface) => self.elaborate(ty_surface)?,
            None => alpha.clone(),
        };

        // Build the step lambda `fun (x : α) (acc : β) => ⟦body⟧ : m (ForInStep β)`.
        // With one accumulator (no tunnel), `acc` shadows the mutable variable
        // itself; otherwise `acc` is the packed local and each variable is
        // re-bound to its projection at the body entry (the `Option` slot, when
        // present, occupies `.1` and the mut pack rides in `.2`).
        let accs = ForAccState {
            vars,
            tys: var_tys,
            mut_beta,
            beta,
            tunnel,
        };
        let fvar_x = self.push_local(binder.name.clone(), loop_var_ty.clone());
        let fvar_acc = self.push_local(Self::acc_local_name(&accs), accs.beta.clone());
        let step_value = self.elab_do_for_acc_body(body, &accs, fvar_acc, &m, &do_u, &do_v);
        self.pop_local();
        self.pop_local();
        let step_value = step_value?;
        let step_value = self.metas.instantiate(&step_value);
        // `x` is the OUTER binder (α), `acc` the INNER (β): abstract `x` first.
        let step_abs = step_value.abstract_fvar(fvar_x).abstract_fvar(fvar_acc);
        let step_lam = Expr::lam(
            BinderInfo::Default,
            loop_var_ty,
            Expr::lam(BinderInfo::Default, accs.beta.clone(), step_abs),
        );

        // The initial accumulator packs the mutable variables' current
        // bindings, prefixed by `Option.none R` when tunneling (B96).
        let var_vals: Vec<Expr> = var_fvars.iter().map(|f| Expr::fvar(*f)).collect();
        let init = self.pack_full_acc(&accs, &var_vals, None)?;
        let fold = self.build_list_forin_fold(
            &alpha, &accs.beta, &m, &do_u, &do_v, &coll_expr, &init, &step_lam,
        );

        // Defensive: the inlined fold must type-check to `m β`. If it does not
        // (a shape we did not anticipate), reject LOUD rather than ship a term
        // the kernel would reject with a confusing message.
        if self.infer_type(&fold).is_err() {
            return Err(ElabError::Unsupported {
                feature: "the `for` loop desugaring did not type-check; this shape \
                          is not yet supported (B23)"
                    .into(),
            });
        }

        // Continuation: `Bind.bind fold (fun (acc : β) => ⟦rest⟧)`, with each
        // accumulator re-bound to its projection before `rest` (a no-op for a
        // single accumulator, whose binder already carries the variable name).
        // When tunneling (B96), the continuation case-splits the `Option`
        // component first: `some r` finishes (or tunnels onward), `none`
        // rebinds the muts and continues with `rest`.
        let fvar_cont = self.push_local(Self::acc_local_name(&accs), accs.beta.clone());
        let rest_result = if accs.tunnel.is_some() {
            self.build_tunnel_case_split(
                &accs,
                fvar_cont,
                outer,
                &m,
                &do_u,
                &do_v,
                &bind_alpha,
                elab_rest,
            )
        } else {
            self.with_acc_unpacked(&accs, fvar_cont, elab_rest)
        };
        self.pop_local();
        let rest_expr = rest_result?;
        let rest_inst = self.metas.instantiate(&rest_expr);
        let cont = Expr::lam(
            BinderInfo::Default,
            accs.beta.clone(),
            rest_inst.abstract_fvar(fvar_cont),
        );

        // @Bind.bind.{do_u,do_v} m β bind_alpha fold cont
        let bind_const = Expr::const_(Name::from_string("Bind.bind"), vec![do_u, do_v]);
        Ok(Expr::apps(
            bind_const,
            [m, accs.beta.clone(), bind_alpha, fold, cont],
        ))
    }

    /// Name of the accumulator lambda local: the variable itself when single
    /// (B23 shadowing), a reserved packed name when several (B93) or when the
    /// accumulator carries the early-return `Option` layer (B96 — the local
    /// is then never a plain mut variable, even with a single accumulator).
    fn acc_local_name(accs: &ForAccState) -> String {
        if accs.tunnel.is_some() {
            return "__b96_acc".to_string();
        }
        match accs.vars.as_slice() {
            [only] => only.clone(),
            _ => "__b23_acc".to_string(),
        }
    }

    /// `Option R` at `R`'s universe.
    fn option_ty(ret_ty: &Expr, ret_level: &Level) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Option"), vec![ret_level.clone()]),
            ret_ty.clone(),
        )
    }

    /// `@Option.none R` — the fall-through tunnel component.
    fn option_none(ret_ty: &Expr, ret_level: &Level) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Option.none"), vec![ret_level.clone()]),
            ret_ty.clone(),
        )
    }

    /// `@Option.some R val` — the early-return tunnel component.
    fn option_some(ret_ty: &Expr, ret_level: &Level, val: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Option.some"), vec![ret_level.clone()]),
            [ret_ty.clone(), val],
        )
    }

    /// Pack explicit component values into the FULL accumulator value shape
    /// of `accs`: the mut pack alone (B23/B93), the `Option` component alone
    /// (B96 tunnel, no muts), or `Prod.mk option mutpack` (both). `ret_val`
    /// is `Some(e)` for a `return e` component and `None` for
    /// `Option.none` (fall-through / `break` / `continue` / init); it must
    /// be `None` when the loop does not tunnel.
    fn pack_full_acc(
        &self,
        accs: &ForAccState,
        mut_vals: &[Expr],
        ret_val: Option<Expr>,
    ) -> Result<Expr, ElabError> {
        let mut_pack = match &accs.mut_beta {
            Some(_) => Some(self.pack_acc_values(mut_vals, &accs.tys)?),
            None => None,
        };
        match (&accs.tunnel, mut_pack) {
            (None, Some(pack)) => {
                if ret_val.is_some() {
                    return Err(ElabError::InternalInvariant(
                        "early-return component requested for a non-tunneling `for` \
                         accumulator (B96)"
                            .into(),
                    ));
                }
                Ok(pack)
            }
            (Some((ret_ty, ret_level)), pack) => {
                let opt_val = match ret_val {
                    Some(e) => Self::option_some(ret_ty, ret_level, e),
                    None => Self::option_none(ret_ty, ret_level),
                };
                match (pack, &accs.mut_beta) {
                    (None, None) => Ok(opt_val),
                    (Some(pack), Some(mb)) => {
                        let opt_ty = Self::option_ty(ret_ty, ret_level);
                        let lf = self.acc_type_level(&opt_ty)?;
                        let lt = self.acc_type_level(mb)?;
                        Ok(Expr::apps(
                            Expr::const_(Name::from_string("Prod.mk"), vec![lf, lt]),
                            [opt_ty, mb.clone(), opt_val, pack],
                        ))
                    }
                    _ => Err(ElabError::InternalInvariant(
                        "for-loop accumulator mut pack/type mismatch (B96)".into(),
                    )),
                }
            }
            (None, None) => Err(ElabError::InternalInvariant(
                "empty accumulator pack in `for` lowering (B96)".into(),
            )),
        }
    }

    /// Build the post-loop `Option.rec` case-split for a tunneling loop
    /// (B96): `some r` finishes the block (`pure r`) — or, when this loop is
    /// nested inside another pure-lane loop, tunnels onward as the ENCLOSING
    /// loop's `ForInStep.done (some r ⊗ enclosing muts)` — and `none` rebinds
    /// the mut accumulators and continues with the loop's continuation.
    #[allow(clippy::too_many_arguments)]
    fn build_tunnel_case_split(
        &mut self,
        accs: &ForAccState,
        fvar_cont: FVarId,
        outer: Option<&ForAccState>,
        m: &Expr,
        do_u: &Level,
        do_v: &Level,
        bind_alpha: &Expr,
        elab_rest: impl FnOnce(&mut Self) -> Result<Expr, ElabError>,
    ) -> Result<Expr, ElabError> {
        let Some((ret_ty, ret_level)) = accs.tunnel.clone() else {
            return Err(ElabError::InternalInvariant(
                "tunnel case-split requested without an early-return tunnel (B96)".into(),
            ));
        };
        // The Option component: the whole accumulator (no muts) or its `.1`.
        let option_val = if accs.vars.is_empty() {
            Expr::fvar(fvar_cont)
        } else {
            Expr::proj(Name::from_string("Prod"), 0, Expr::fvar(fvar_cont))
        };

        // none → rebind the mut accumulators and continue with the rest. The
        // continuation's type is authenticated against `m bind_alpha` so a
        // shape bug fails HERE as a typed mismatch, not at the kernel.
        let m_result = Expr::app(m.clone(), bind_alpha.clone());
        let none_branch = self.with_acc_unpacked(accs, fvar_cont, elab_rest)?;
        self.enforce_expr_type(&none_branch, &m_result)?;

        // some r → `pure r` at do-block level; nested, tunnel onward through
        // the enclosing loop's Option slot.
        let fvar_r = self.push_local("__b96_ret".to_string(), ret_ty.clone());
        let some_val = match outer {
            None => {
                let pure_const = Expr::const_(
                    Name::from_string("Pure.pure"),
                    vec![do_u.clone(), do_v.clone()],
                );
                Ok(Expr::apps(
                    pure_const,
                    [m.clone(), ret_ty.clone(), Expr::fvar(fvar_r)],
                ))
            }
            Some(o) => self
                .pack_step_acc(o, Some(Expr::fvar(fvar_r)))
                .map(|acc_val| self.mk_pure_for_in_step(m, &o.beta, do_u, do_v, true, acc_val)),
        };
        self.pop_local();
        let some_val = some_val?;
        let some_inst = self.metas.instantiate(&some_val);
        let some_case = Expr::lam(
            BinderInfo::Default,
            ret_ty.clone(),
            some_inst.abstract_fvar(fvar_r),
        );

        // motive: `fun (_ : Option R) => m bind_alpha` (non-dependent).
        let motive = Expr::lam(
            BinderInfo::Default,
            Self::option_ty(&ret_ty, &ret_level),
            m_result.clone(),
        );

        // @Option.rec.{u1, u2} R motive none_case some_case option_val, with
        // u1 = sort of `m bind_alpha` and u2 = R's universe.
        let rec_u1 = self.infer_sort(&m_result)?;
        let option_rec = Expr::const_(Name::from_string("Option.rec"), vec![rec_u1, ret_level]);
        Ok(Expr::apps(
            option_rec,
            [ret_ty, motive, none_branch, some_case, option_val],
        ))
    }

    /// Build the step-lambda body: bind each accumulator name over the packed
    /// accumulator local, then walk the body statements. With one accumulator
    /// the local IS the variable (shadowing) and no unpacking is emitted —
    /// exactly the B23 term.
    fn elab_do_for_acc_body(
        &mut self,
        body: &[DoElem],
        accs: &ForAccState,
        fvar_acc: FVarId,
        m: &Expr,
        do_u: &Level,
        do_v: &Level,
    ) -> Result<Expr, ElabError> {
        self.with_acc_unpacked(accs, fvar_acc, |this| {
            this.elab_do_for_step_value(body, accs, m, do_u, do_v)
        })
    }

    /// Run `k` with each accumulator variable bound to its projection of the
    /// packed accumulator local, wrapping `k`'s result in the projection
    /// `let`s. Single accumulator without a tunnel: the local already carries
    /// the variable's name — run `k` directly (B23 byte-identity). With a
    /// tunnel (B96) the `Option` slot occupies `.1`, so the mut variables
    /// project from the `.2` component; no vars means nothing to unpack.
    fn with_acc_unpacked(
        &mut self,
        accs: &ForAccState,
        fvar_acc: FVarId,
        k: impl FnOnce(&mut Self) -> Result<Expr, ElabError>,
    ) -> Result<Expr, ElabError> {
        if accs.vars.is_empty() {
            return k(self);
        }
        if accs.tunnel.is_some() {
            let base = Expr::proj(Name::from_string("Prod"), 1, Expr::fvar(fvar_acc));
            return self.bind_acc_projection_lets(&accs.vars, &accs.tys, base, k);
        }
        if accs.vars.len() == 1 {
            return k(self);
        }
        self.bind_acc_projection_lets(&accs.vars, &accs.tys, Expr::fvar(fvar_acc), k)
    }

    /// `let v₁ := pack.1; let v₂ := pack.2.1; …; let vₙ := pack.2.….2; ⟦k⟧` —
    /// the right-nested `Prod` unpacking used at the step-body entry and in
    /// the loop continuation. Uses kernel `Expr::proj` on `Prod` (which
    /// reduces on `Prod.mk`), so `rfl` value pins compute.
    fn bind_acc_projection_lets(
        &mut self,
        vars: &[String],
        tys: &[Expr],
        pack: Expr,
        k: impl FnOnce(&mut Self) -> Result<Expr, ElabError>,
    ) -> Result<Expr, ElabError> {
        let ((var, ty), (vrest, trest)) = match (vars.split_first(), tys.split_first()) {
            (Some((v, vr)), Some((t, tr))) => ((v, t), (vr, tr)),
            _ => {
                return Err(ElabError::Unsupported {
                    feature: "empty accumulator pack in `for` lowering (B93)".into(),
                })
            }
        };
        let val = if vrest.is_empty() {
            pack.clone()
        } else {
            Expr::proj(Name::from_string("Prod"), 0, pack.clone())
        };
        let fvar = self.push_local(var.clone(), ty.clone());
        let inner = if vrest.is_empty() {
            k(self)
        } else {
            let tail = Expr::proj(Name::from_string("Prod"), 1, pack);
            self.bind_acc_projection_lets(vrest, trest, tail, k)
        };
        self.pop_local();
        let inner = inner?;
        let inner_inst = self.metas.instantiate(&inner);
        Ok(Expr::let_named(
            Name::from_string(var),
            ty.clone(),
            val,
            inner_inst.abstract_fvar(fvar),
            false,
        ))
    }

    /// The packed `ForIn` accumulator type: the type itself for one
    /// accumulator; right-nested `Prod` (`β₁ × (β₂ × …)`) for several, with
    /// universe levels read off the actual types' sorts.
    fn pack_acc_ty(&self, tys: &[Expr]) -> Result<Expr, ElabError> {
        match tys.split_first() {
            None => Err(ElabError::Unsupported {
                feature: "empty accumulator pack in `for` lowering (B93)".into(),
            }),
            Some((first, [])) => Ok(first.clone()),
            Some((first, rest)) => {
                let tail = self.pack_acc_ty(rest)?;
                let lf = self.acc_type_level(first)?;
                let lt = self.acc_type_level(&tail)?;
                Ok(Expr::apps(
                    Expr::const_(Name::from_string("Prod"), vec![lf, lt]),
                    [first.clone(), tail],
                ))
            }
        }
    }

    /// Pack per-accumulator values into the `Prod.mk` chain matching
    /// [`Self::pack_acc_ty`]; a single value passes through unchanged.
    fn pack_acc_values(&self, vals: &[Expr], tys: &[Expr]) -> Result<Expr, ElabError> {
        match (vals.split_first(), tys.split_first()) {
            (Some((v, [])), Some(_)) => Ok(v.clone()),
            (Some((v, vrest)), Some((t, trest))) => {
                let tail_val = self.pack_acc_values(vrest, trest)?;
                let tail_ty = self.pack_acc_ty(trest)?;
                let lf = self.acc_type_level(t)?;
                let lt = self.acc_type_level(&tail_ty)?;
                Ok(Expr::apps(
                    Expr::const_(Name::from_string("Prod.mk"), vec![lf, lt]),
                    [t.clone(), tail_ty, v.clone(), tail_val],
                ))
            }
            _ => Err(ElabError::Unsupported {
                feature: "empty accumulator pack in `for` lowering (B93)".into(),
            }),
        }
    }

    /// The `Type`-level `u` with `ty : Type u`, for `Prod`'s universe
    /// arguments. Accumulator types outside `Type _` (e.g. `Prop`) descope
    /// LOUD — `Prod` cannot pack them.
    fn acc_type_level(&self, ty: &Expr) -> Result<Level, ElabError> {
        let sort = self.infer_sort(ty)?;
        match &sort {
            Level::Succ(inner) => Ok(inner.as_ref().clone()),
            _ => Err(ElabError::Unsupported {
                feature: format!(
                    "multi-accumulator `for` loops pack accumulators in `Prod`, \
                     which needs every accumulator type in `Type _`; this type's \
                     sort is `Sort {sort:?}` (B93)"
                ),
            }),
        }
    }

    /// Build `m (ForInStep β)` for a for-loop body suffix in the pure lane.
    ///
    /// Every accumulator (and body-local `let mut`) is threaded by
    /// `let`-shadowing; the sequence terminates in a `ForInStep`-producing
    /// `pure` over the packed current values (with the `Option` tunnel
    /// component prepended when the loop tunnels an early `return` — B96):
    /// - fall-through / `continue` → `pure (ForInStep.yield ⟦none ⊗ pack vars⟧)`,
    /// - `break`                   → `pure (ForInStep.done ⟦none ⊗ pack vars⟧)`,
    /// - `return e`                → `pure (ForInStep.done ⟦some e ⊗ pack vars⟧)`.
    ///
    /// `if` guards join on `m (ForInStep β)` (each branch is elaborated with the
    /// continuation `rest` inlined unless the branch already exits). A nested
    /// `for` lowers recursively through [`Self::elab_pure_for_core`], its
    /// `Bind.bind` continuation walking the remaining statements at
    /// `m (ForInStep β)` — and its own tunneled `return`, if any, propagating
    /// through THIS loop's `Option` slot.
    fn elab_do_for_step_value(
        &mut self,
        elems: &[DoElem],
        accs: &ForAccState,
        m: &Expr,
        do_u: &Level,
        do_v: &Level,
    ) -> Result<Expr, ElabError> {
        stack_safe(|| match elems {
            // Fall-through: yield the current accumulator values.
            [] => {
                let acc = self.pack_step_acc(accs, None)?;
                Ok(self.mk_pure_for_in_step(m, &accs.beta, do_u, do_v, false, acc))
            }
            [DoElem::Break(_), ..] => {
                let acc = self.pack_step_acc(accs, None)?;
                Ok(self.mk_pure_for_in_step(m, &accs.beta, do_u, do_v, true, acc))
            }
            [DoElem::Continue(_), ..] => {
                let acc = self.pack_step_acc(accs, None)?;
                Ok(self.mk_pure_for_in_step(m, &accs.beta, do_u, do_v, false, acc))
            }
            // B96: `return e` stops the loop and tunnels `e` out through the
            // accumulator's `Option` slot. Anything after it is dead code
            // (ControlInfo `sequence` semantics).
            [DoElem::Return(_, expr), ..] => {
                let Some((ret_ty, _)) = accs.tunnel.clone() else {
                    return Err(ElabError::InternalInvariant(
                        "`return` reached a non-tunneling `for` body walker (B96)".into(),
                    ));
                };
                let val_expr = self.elaborate_with_expected_type(expr, Some(ret_ty.clone()))?;
                self.enforce_expr_type(&val_expr, &ret_ty)?;
                let acc = self.pack_step_acc(accs, Some(val_expr))?;
                Ok(self.mk_pure_for_in_step(m, &accs.beta, do_u, do_v, true, acc))
            }
            [DoElem::Reassign(_, name, val), rest @ ..] => {
                // A loop accumulator threads at its packed slot type; a
                // body-local `let mut` (bound by the LetMut arm below) threads
                // at its own binding type. Anything else is LOUD.
                let ty = if let Some(idx) = accs.vars.iter().position(|v| v == name) {
                    accs.tys[idx].clone()
                } else if !self.do_mut_vars.contains(name) {
                    return Err(Self::immutable_reassign_err(name));
                } else if let Some(ty) = self.lookup_local_ty(name) {
                    ty
                } else {
                    return Err(ElabError::Unsupported {
                        feature: format!(
                            "`for` loop body reassigns `{name}`, which is neither a \
                             loop accumulator nor a body-local `let mut` in scope \
                             (B23/B93)"
                        ),
                    });
                };
                let val_expr = self.elaborate_with_expected_type(val, Some(ty.clone()))?;
                self.enforce_expr_type(&val_expr, &ty)?;
                let fvar = self.push_local(name.clone(), ty.clone());
                let rest_val = self.elab_do_for_step_value(rest, accs, m, do_u, do_v);
                self.pop_local();
                let rest_val = rest_val?;
                let rest_inst = self.metas.instantiate(&rest_val);
                Ok(Expr::let_named(
                    Name::from_string(name),
                    ty,
                    val_expr,
                    rest_inst.abstract_fvar(fvar),
                    false,
                ))
            }
            [DoElem::Let(_, binder, val), rest @ ..] => {
                let (ty, val_expr) = match &binder.ty {
                    Some(t) => {
                        let ty = self.elaborate(t)?;
                        let val_expr = self.elaborate_with_expected_type(val, Some(ty.clone()))?;
                        (ty, val_expr)
                    }
                    None => {
                        let val_expr = self.elaborate_with_expected_type(val, None)?;
                        let ty = self.infer_type(&val_expr)?;
                        (ty, val_expr)
                    }
                };
                let fvar = self.push_local(binder.name.clone(), ty.clone());
                let rest_val = self.elab_do_for_step_value(rest, accs, m, do_u, do_v);
                self.pop_local();
                let rest_val = rest_val?;
                let rest_inst = self.metas.instantiate(&rest_val);
                Ok(Expr::let_named(
                    Name::from_string(&binder.name),
                    ty,
                    val_expr,
                    rest_inst.abstract_fvar(fvar),
                    false,
                ))
            }
            // A body-local `let mut` is fresh per iteration: bind it exactly
            // like a plain `let`; later reassignments shadow it through the
            // Reassign arm above (it is never packed into the accumulator).
            [DoElem::LetMut(_, binder, val), rest @ ..] => {
                let (ty, val_expr) = match &binder.ty {
                    Some(t) => {
                        let ty = self.elaborate(t)?;
                        let val_expr = self.elaborate_with_expected_type(val, Some(ty.clone()))?;
                        (ty, val_expr)
                    }
                    None => {
                        let val_expr = self.elaborate_with_expected_type(val, None)?;
                        let ty = self.infer_type(&val_expr)?;
                        (ty, val_expr)
                    }
                };
                let fvar = self.push_local(binder.name.clone(), ty.clone());
                let rest_val = self.elab_do_for_step_value(rest, accs, m, do_u, do_v);
                self.pop_local();
                let rest_val = rest_val?;
                let rest_inst = self.metas.instantiate(&rest_val);
                Ok(Expr::let_named(
                    Name::from_string(&binder.name),
                    ty,
                    val_expr,
                    rest_inst.abstract_fvar(fvar),
                    false,
                ))
            }
            [DoElem::If(_, cond, then_branch, else_branch), rest @ ..] => {
                let cond_expr = self.elaborate_with_expected_type(cond, None)?;

                let then_seq = Self::branch_with_continuation(then_branch, rest);
                let then_val = self.elab_do_for_step_value(&then_seq, accs, m, do_u, do_v)?;

                let else_seq = match else_branch {
                    Some(e) => Self::branch_with_continuation(e, rest),
                    None => rest.to_vec(),
                };
                let else_val = self.elab_do_for_step_value(&else_seq, accs, m, do_u, do_v)?;

                let for_in_step_beta = Expr::app(
                    Expr::const_(Name::from_string("ForInStep"), vec![do_u.clone()]),
                    accs.beta.clone(),
                );
                let result_ty = Expr::app(m.clone(), for_in_step_beta);
                self.mk_do_ite(cond_expr, then_val, else_val, result_ty)
            }
            // A nested `for` lowers recursively through the same core: its own
            // accumulators resolve in the scope at this position (body-local
            // `let mut`s of THIS body, or this loop's accumulators), and its
            // `Bind.bind` continuation walks the remaining statements at
            // `m (ForInStep β)`. Passing THIS loop's accumulator state as the
            // nested loop's `outer` both pins that bind result type and lets a
            // nested tunneled `return` propagate through this loop's `Option`
            // slot (B96).
            [DoElem::For(_, nbinder, ncollection, nbody), rest @ ..] => {
                self.elab_pure_for_core(nbinder, ncollection, nbody, Some(accs), |this| {
                    this.elab_do_for_step_value(rest, accs, m, do_u, do_v)
                })
            }
            _ => Err(ElabError::Unsupported {
                feature: "unsupported statement in a `for` loop body over mutable \
                          state (B23/B93 supports reassignment, `let`, `let mut`, \
                          `if`, `break`, `continue`, nested `for`)"
                    .into(),
            }),
        })
    }

    /// `branch ++ rest` when `branch` falls through; just `branch` when it
    /// always exits (`break`/`continue`/`return`) so `rest` is dead code.
    fn branch_with_continuation(branch: &[DoElem], rest: &[DoElem]) -> Vec<DoElem> {
        if infer_control_info_seq(branch).num_regular_exits == 0 {
            branch.to_vec()
        } else {
            let mut seq = branch.to_vec();
            seq.extend_from_slice(rest);
            seq
        }
    }

    /// The current value of the loop accumulator `var` (its innermost local).
    fn current_acc_value(&self, var: &str) -> Result<Expr, ElabError> {
        self.lookup_local_fvar(var)
            .map(Expr::fvar)
            .ok_or_else(|| ElabError::Unsupported {
                feature: format!("mutable accumulator `{var}` is not in scope"),
            })
    }

    /// The current values of all loop accumulators (their innermost locals),
    /// packed into the FULL accumulator value shape — with the `Option`
    /// tunnel component (`some ret_val` / `none`) prepended when the loop
    /// tunnels an early `return` (B96). Single accumulator without a tunnel:
    /// exactly [`Self::current_acc_value`] (B23 byte-identity).
    fn pack_step_acc(&self, accs: &ForAccState, ret_val: Option<Expr>) -> Result<Expr, ElabError> {
        let vals = accs
            .vars
            .iter()
            .map(|v| self.current_acc_value(v))
            .collect::<Result<Vec<_>, _>>()?;
        self.pack_full_acc(accs, &vals, ret_val)
    }

    /// `@Pure.pure.{do_u,do_v} m (ForInStep β) (@ForInStep.(done|yield).{do_u} β acc)`.
    fn mk_pure_for_in_step(
        &self,
        m: &Expr,
        beta: &Expr,
        do_u: &Level,
        do_v: &Level,
        done: bool,
        acc: Expr,
    ) -> Expr {
        let ctor = if done {
            "ForInStep.done"
        } else {
            "ForInStep.yield"
        };
        let step = Expr::apps(
            Expr::const_(Name::from_string(ctor), vec![do_u.clone()]),
            [beta.clone(), acc],
        );
        let for_in_step_beta = Expr::app(
            Expr::const_(Name::from_string("ForInStep"), vec![do_u.clone()]),
            beta.clone(),
        );
        let pure_const = Expr::const_(
            Name::from_string("Pure.pure"),
            vec![do_u.clone(), do_v.clone()],
        );
        Expr::apps(pure_const, [m.clone(), for_in_step_beta, step])
    }

    /// Build the inlined `List.forIn` fold applied to the initial accumulator:
    ///
    /// ```text
    /// (@List.rec.{succ (max u v), u} α (fun _ => β → m β)
    ///     (fun acc => Pure.pure m β acc)
    ///     (fun hd _ ih acc =>
    ///        Bind.bind m (ForInStep β) β (step hd acc)
    ///          (fun s => @ForInStep.rec.{succ v, u} β (fun _ => m β)
    ///                       (fun b => Pure.pure m β b) (fun b => ih b) s))
    ///     xs) init
    /// ```
    ///
    /// This is exactly `List.forIn`'s kernel-registered body (`data_for_in.rs`)
    /// specialised to the (concrete) do-block monad `m`, built with
    /// `push_local`/`abstract_fvar` so the de Bruijn indices are machine-checked.
    #[allow(clippy::too_many_arguments)]
    fn build_list_forin_fold(
        &mut self,
        alpha: &Expr,
        beta: &Expr,
        m: &Expr,
        do_u: &Level,
        do_v: &Level,
        xs: &Expr,
        init: &Expr,
        step_lam: &Expr,
    ) -> Expr {
        let list_alpha = Expr::app(
            Expr::const_(Name::from_string("List"), vec![do_u.clone()]),
            alpha.clone(),
        );
        let for_in_step_beta = Expr::app(
            Expr::const_(Name::from_string("ForInStep"), vec![do_u.clone()]),
            beta.clone(),
        );
        let m_beta = Expr::app(m.clone(), beta.clone());
        // ih : β → m β  (non-dependent, closed)
        let ih_ty = Expr::pi(BinderInfo::Default, beta.clone(), m_beta.clone());
        let pure_const = Expr::const_(
            Name::from_string("Pure.pure"),
            vec![do_u.clone(), do_v.clone()],
        );
        let bind_const = Expr::const_(
            Name::from_string("Bind.bind"),
            vec![do_u.clone(), do_v.clone()],
        );

        // motive := fun (_ : List α) => (β → m β)
        let motive = Expr::lam(BinderInfo::Default, list_alpha.clone(), ih_ty.clone());

        // nil := fun (acc : β) => @Pure.pure m β acc
        let nil_case = {
            let acc_fv = self.push_local("__forin_acc".to_string(), beta.clone());
            let pure_acc = Expr::apps(
                pure_const.clone(),
                [m.clone(), beta.clone(), Expr::fvar(acc_fv)],
            );
            self.pop_local();
            Expr::lam(
                BinderInfo::Default,
                beta.clone(),
                pure_acc.abstract_fvar(acc_fv),
            )
        };

        // cons := fun (hd : α) (tl : List α) (ih : β → m β) (acc : β) =>
        //           @Bind.bind m (ForInStep β) β (step_lam hd acc)
        //             (fun s => @ForInStep.rec β (fun _ => m β)
        //                          (fun b => @Pure.pure m β b) (fun b => ih b) s)
        let cons_case = {
            let hd_fv = self.push_local("__forin_hd".to_string(), alpha.clone());
            let tl_fv = self.push_local("__forin_tl".to_string(), list_alpha.clone());
            let ih_fv = self.push_local("__forin_ih".to_string(), ih_ty.clone());
            let acc_fv = self.push_local("__forin_acc".to_string(), beta.clone());

            let step_app = Expr::apps(step_lam.clone(), [Expr::fvar(hd_fv), Expr::fvar(acc_fv)]);

            // continuation: fun (s : ForInStep β) => ForInStep.rec β motive2 done yield s
            let s_fv = self.push_local("__forin_s".to_string(), for_in_step_beta.clone());
            let motive2 = Expr::lam(
                BinderInfo::Default,
                for_in_step_beta.clone(),
                m_beta.clone(),
            );
            let done_minor = {
                let b_fv = self.push_local("__forin_b".to_string(), beta.clone());
                let pure_b = Expr::apps(
                    pure_const.clone(),
                    [m.clone(), beta.clone(), Expr::fvar(b_fv)],
                );
                self.pop_local();
                Expr::lam(
                    BinderInfo::Default,
                    beta.clone(),
                    pure_b.abstract_fvar(b_fv),
                )
            };
            let yield_minor = {
                let b_fv = self.push_local("__forin_b".to_string(), beta.clone());
                let ih_b = Expr::app(Expr::fvar(ih_fv), Expr::fvar(b_fv));
                self.pop_local();
                Expr::lam(BinderInfo::Default, beta.clone(), ih_b.abstract_fvar(b_fv))
            };
            let for_in_step_rec = Expr::const_(
                Name::from_string("ForInStep.rec"),
                vec![Level::succ(do_v.clone()), do_u.clone()],
            );
            let rec_app = Expr::apps(
                for_in_step_rec,
                [
                    beta.clone(),
                    motive2,
                    done_minor,
                    yield_minor,
                    Expr::fvar(s_fv),
                ],
            );
            self.pop_local(); // s
            let cont = Expr::lam(
                BinderInfo::Default,
                for_in_step_beta.clone(),
                rec_app.abstract_fvar(s_fv),
            );

            let bind_app = Expr::apps(
                bind_const,
                [
                    m.clone(),
                    for_in_step_beta.clone(),
                    beta.clone(),
                    step_app,
                    cont,
                ],
            );

            self.pop_local(); // acc
            self.pop_local(); // ih
            self.pop_local(); // tl
            self.pop_local(); // hd

            // hd outermost … acc innermost: abstract hd → tl → ih → acc.
            let body_abs = bind_app
                .abstract_fvar(hd_fv)
                .abstract_fvar(tl_fv)
                .abstract_fvar(ih_fv)
                .abstract_fvar(acc_fv);
            Expr::lam(
                BinderInfo::Default,
                alpha.clone(),
                Expr::lam(
                    BinderInfo::Default,
                    list_alpha.clone(),
                    Expr::lam(
                        BinderInfo::Default,
                        ih_ty,
                        Expr::lam(BinderInfo::Default, beta.clone(), body_abs),
                    ),
                ),
            )
        };

        // @List.rec.{succ (max u v), u} α motive nil cons xs
        let list_rec = Expr::const_(
            Name::from_string("List.rec"),
            vec![
                Level::succ(Level::max(do_u.clone(), do_v.clone())),
                do_u.clone(),
            ],
        );
        let rec_app = Expr::apps(
            list_rec,
            [alpha.clone(), motive, nil_case, cons_case, xs.clone()],
        );
        // (… : β → m β) init : m β
        Expr::app(rec_app, init.clone())
    }
}

/// Collect the names declared with `let mut` anywhere in a do-block.
pub(super) fn collect_do_mut_var_names(elems: &[DoElem], out: &mut Vec<String>) {
    stack_safe(|| {
        for elem in elems {
            match elem {
                DoElem::LetMut(_, binder, _) if !out.contains(&binder.name) => {
                    out.push(binder.name.clone());
                }
                DoElem::If(_, _, t, e)
                | DoElem::IfLet(_, _, _, t, e)
                | DoElem::IfDecidable(_, _, _, t, e) => {
                    collect_do_mut_var_names(t, out);
                    if let Some(e) = e {
                        collect_do_mut_var_names(e, out);
                    }
                }
                DoElem::Match(_, _, arms) => {
                    for arm in arms {
                        collect_do_mut_var_names(&arm.body, out);
                    }
                }
                DoElem::For(_, _, _, body)
                | DoElem::Repeat(_, body)
                | DoElem::While(_, _, body) => {
                    collect_do_mut_var_names(body, out);
                }
                DoElem::TryCatch(_, try_body, catches, finally_body) => {
                    collect_do_mut_var_names(try_body, out);
                    for c in catches {
                        collect_do_mut_var_names(&c.body, out);
                    }
                    if let Some(f) = finally_body {
                        collect_do_mut_var_names(f, out);
                    }
                }
                DoElem::LetElse(_, _, _, fallback) | DoElem::LetExpr(_, _, _, _, fallback) => {
                    collect_do_mut_var_names(fallback, out);
                }
                _ => {}
            }
        }
    });
}

/// True if the block contains any `try`/`catch`/`finally` anywhere. Such
/// blocks keep the legacy transformer-stack lane (the pure lane models only
/// mutation and if/return control flow).
pub(super) fn do_block_has_try_catch(elems: &[DoElem]) -> bool {
    stack_safe(|| {
        elems.iter().any(|elem| match elem {
            DoElem::TryCatch(..) => true,
            DoElem::If(_, _, t, e)
            | DoElem::IfLet(_, _, _, t, e)
            | DoElem::IfDecidable(_, _, _, t, e) => {
                do_block_has_try_catch(t) || e.as_ref().is_some_and(|e| do_block_has_try_catch(e))
            }
            DoElem::Match(_, _, arms) => arms.iter().any(|arm| do_block_has_try_catch(&arm.body)),
            DoElem::For(_, _, _, body) | DoElem::Repeat(_, body) | DoElem::While(_, _, body) => {
                do_block_has_try_catch(body)
            }
            DoElem::LetElse(_, _, _, fallback) | DoElem::LetExpr(_, _, _, _, fallback) => {
                do_block_has_try_catch(fallback)
            }
            _ => false,
        })
    })
}

/// True if the block contains any `while`/`repeat` loop anywhere (recursively,
/// including inside `for` bodies). B23's pure lane models `for` loops only, so a
/// `while`/`repeat` combined with a control effect is descoped LOUD.
pub(super) fn do_block_has_while_repeat(elems: &[DoElem]) -> bool {
    stack_safe(|| {
        elems.iter().any(|elem| match elem {
            DoElem::While(..) | DoElem::Repeat(..) => true,
            DoElem::For(_, _, _, body) => do_block_has_while_repeat(body),
            DoElem::If(_, _, t, e)
            | DoElem::IfLet(_, _, _, t, e)
            | DoElem::IfDecidable(_, _, _, t, e) => {
                do_block_has_while_repeat(t)
                    || e.as_ref().is_some_and(|e| do_block_has_while_repeat(e))
            }
            DoElem::Match(_, _, arms) => {
                arms.iter().any(|arm| do_block_has_while_repeat(&arm.body))
            }
            DoElem::TryCatch(_, try_body, catches, finally_body) => {
                do_block_has_while_repeat(try_body)
                    || catches.iter().any(|c| do_block_has_while_repeat(&c.body))
                    || finally_body
                        .as_ref()
                        .is_some_and(|f| do_block_has_while_repeat(f))
            }
            DoElem::LetElse(_, _, _, fallback) | DoElem::LetExpr(_, _, _, _, fallback) => {
                do_block_has_while_repeat(fallback)
            }
            _ => false,
        })
    })
}

/// True if the block contains a `break`/`continue` that is NOT enclosed by a
/// loop (`for`/`while`/`repeat`). Loops consume their own break/continue
/// (`ControlInfo` strips them), so a top-level break/continue is a control form
/// the pure lane cannot lower — descoped LOUD (Lean also rejects it outside a
/// loop). Descends into `if`/`match`/fallback branches but NOT loop bodies.
pub(super) fn do_block_has_toplevel_break_continue(elems: &[DoElem]) -> bool {
    stack_safe(|| {
        elems.iter().any(|elem| match elem {
            DoElem::Break(_) | DoElem::Continue(_) => true,
            // A loop consumes its own break/continue: do not descend.
            DoElem::For(..) | DoElem::While(..) | DoElem::Repeat(..) => false,
            DoElem::If(_, _, t, e)
            | DoElem::IfLet(_, _, _, t, e)
            | DoElem::IfDecidable(_, _, _, t, e) => {
                do_block_has_toplevel_break_continue(t)
                    || e.as_ref()
                        .is_some_and(|e| do_block_has_toplevel_break_continue(e))
            }
            DoElem::Match(_, _, arms) => arms
                .iter()
                .any(|arm| do_block_has_toplevel_break_continue(&arm.body)),
            DoElem::TryCatch(_, try_body, catches, finally_body) => {
                do_block_has_toplevel_break_continue(try_body)
                    || catches
                        .iter()
                        .any(|c| do_block_has_toplevel_break_continue(&c.body))
                    || finally_body
                        .as_ref()
                        .is_some_and(|f| do_block_has_toplevel_break_continue(f))
            }
            DoElem::LetElse(_, _, _, fallback) | DoElem::LetExpr(_, _, _, _, fallback) => {
                do_block_has_toplevel_break_continue(fallback)
            }
            _ => false,
        })
    })
}

/// True if the block contains any `for`/`while`/`repeat`/`break`/`continue`
/// anywhere (recursively). These are the control-flow forms the pure lane does
/// NOT model; when combined with a control effect the block is descoped LOUD.
#[allow(dead_code)]
pub(super) fn do_block_has_hard_control(elems: &[DoElem]) -> bool {
    stack_safe(|| {
        elems.iter().any(|elem| match elem {
            DoElem::For(..) | DoElem::While(..) | DoElem::Repeat(..) => true,
            DoElem::Break(_) | DoElem::Continue(_) => true,
            DoElem::If(_, _, t, e)
            | DoElem::IfLet(_, _, _, t, e)
            | DoElem::IfDecidable(_, _, _, t, e) => {
                do_block_has_hard_control(t)
                    || e.as_ref().is_some_and(|e| do_block_has_hard_control(e))
            }
            DoElem::Match(_, _, arms) => {
                arms.iter().any(|arm| do_block_has_hard_control(&arm.body))
            }
            DoElem::TryCatch(_, try_body, catches, finally_body) => {
                do_block_has_hard_control(try_body)
                    || catches.iter().any(|c| do_block_has_hard_control(&c.body))
                    || finally_body
                        .as_ref()
                        .is_some_and(|f| do_block_has_hard_control(f))
            }
            DoElem::LetElse(_, _, _, fallback) | DoElem::LetExpr(_, _, _, _, fallback) => {
                do_block_has_hard_control(fallback)
            }
            _ => false,
        })
    })
}
