// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cached monad info helpers for do-block elaboration.

use super::*;
use clean_kernel::{Expr, ExprKind, Level};
use clean_parser::SurfaceArg;

impl<'a> ElabCtx<'a> {
    /// Get cached `(u, v, m)` from `do_monad_info`, or create fresh ones.
    ///
    /// When inside a do-block with a ControlStack, returns the WRAPPED monad
    /// (`do_wrapped_monad`) so that bind/pure target the outermost transformer.
    /// The base monad in `do_monad_info` is preserved for ControlStack operations
    /// that generate control flow at specific layers.
    ///
    /// When inside a plain do-block (no transformers), returns the base `(u, v, m)`.
    /// When called outside a do-block, falls back to creating fresh parameters.
    pub(super) fn get_or_create_monad_info(&mut self) -> (Level, Level, Expr) {
        if let Some(info) = &self.do_monad_info {
            // Use wrapped monad when ControlStack is active (#1818 Phase 4C).
            let m = self
                .do_wrapped_monad
                .as_ref()
                .cloned()
                .unwrap_or_else(|| info.m.clone());
            (info.u.clone(), info.v.clone(), m)
        } else {
            // Fallback: create fresh (preserves old behavior for any edge case)
            let u = self.fresh_universe_param();
            let v = self.fresh_universe_param();
            let m_ty = Expr::arrow(
                Expr::sort(Level::succ(u.clone())),
                Expr::sort(Level::succ(v.clone())),
            );
            let m = self.fresh_meta(m_ty);
            (u, v, m)
        }
    }

    /// Short-circuit `pure <arg>` when we are inside a do-block (#3435).
    ///
    /// Returns `Some(result)` only if `func` is the bare identifier `pure`
    /// (optionally wrapped in `Paren`), there is exactly one explicit
    /// argument, we are inside a do-block (`do_monad_info.is_some()`), and
    /// `pure` is NOT shadowed by a local binding or an environment constant.
    ///
    /// Rationale: `pure` is not registered as a bare constant (only
    /// `Pure.pure` is), so `elab_ident` would fall through to the
    /// auto-implicit handler and bind `pure` as a fresh FVar whose type is
    /// `current_expected_type`. Inside a do-block that expected type is the
    /// outer monadic return (e.g. `Sem Nat` = `StateT MState (Except SemError) Nat`
    /// which whnf-unfolds to `MState -> Except SemError (Prod Nat MState)`).
    /// Applying that auto-bound FVar to `s.counter : Nat` then demanded
    /// `MState`, yielding "expected MState, actual Nat" — the fault reported
    /// in issue #3435. Routing `pure x` through `mk_pure_app` reuses the
    /// do-block's cached `(u, v, m)` so universe levels and the monad
    /// metavariable stay concrete.
    pub(super) fn try_short_circuit_do_pure(
        &mut self,
        func: &SurfaceExpr,
        args: &[SurfaceArg],
    ) -> Result<Option<Expr>, ElabError> {
        if self.explicit_mode
            || self.do_monad_info.is_none()
            || args.len() != 1
            || args[0].name.is_some()
        {
            return Ok(None);
        }
        let name = match Self::unwrap_surface_parens(func) {
            SurfaceExpr::Ident(_, n) if n == &SurfaceName::generated_path("pure") => n,
            _ => return Ok(None),
        };
        // Only the prelude `pure` (a local, metaprogram value or namespace
        // member spelled `pure` is the user's own function).
        if !self.head_denotes_global(name, "pure") || self.env.get_const(name.name()).is_some() {
            return Ok(None);
        }
        // Elaborate the payload against the monad's inner result type `α` (from
        // `do`'s expected `m α`) so a leading-dot constructor payload resolves
        // its inductive head (`pure (.Continue …)` / `return .Ret …` — the
        // Control/Borrow `StepResult` builders). Without the expected type the
        // bare `elaborate` fails with `Unknown identifier: .Continue`. Mirrors
        // the same fix in `elab_pure`.
        let val_expr = match self.expected_do_result_alpha() {
            Some(alpha) => self.elaborate_with_expected_type(&args[0].expr, Some(alpha))?,
            None => self.elaborate(&args[0].expr)?,
        };
        Ok(Some(self.mk_pure_app(val_expr)))
    }

    /// The instance argument of a do-lowered monad operation:
    /// `?inst : <class>.{levels} args`, resolved NOW when the goal is
    /// determined, otherwise queued for the declaration-boundary drain
    /// (`retry_postponed_open_carrier_instances`).
    ///
    /// Until 2026-09-28 the do lowering emitted `Pure.pure` / `Bind.bind` /
    /// `StateT.get` / `MonadExcept.throw` / `OptionT.fail` with NO instance
    /// argument, against instance-less prelude AXIOMS that proved `False`
    /// (`docs/issues/2026-09-28-prelude-pure-proves-false.md`). They are
    /// Lean's class projections / `[Monad m]` definitions now, so every
    /// lowered application carries the instance Lean's elaborator would
    /// synthesize. A goal whose monad is still an unassigned metavariable is
    /// NOT searched (that would grab whichever instance comes first); it is
    /// queued, and one that never grounds is reported by the fail-closed
    /// residual guard as an unsynthesized instance goal — Lean's "typeclass
    /// instance problem is stuck".
    pub(super) fn do_instance_arg(
        &mut self,
        class: &str,
        levels: Vec<Level>,
        args: &[Expr],
    ) -> Expr {
        let goal = Expr::apps(
            Expr::const_(Name::from_string(class), levels),
            args.iter().cloned(),
        );
        let meta = self.fresh_meta(goal.clone());
        let goal_now = self.metas.instantiate(&goal);
        let open = args.iter().any(|a| {
            instance::bare_unassigned_meta(&self.metas, &self.metas.instantiate(a)).is_some()
        });
        if !open {
            if let Some(inst) = self.resolve_instance(&goal_now) {
                if let ExprKind::FVar(fvar) = meta.kind() {
                    if let Some(id) = MetaState::from_fvar(*fvar) {
                        if self.metas.assign(id, inst) {
                            return self.metas.instantiate(&meta);
                        }
                    }
                }
            }
        }
        self.postponed_open_carrier_instances
            .push((meta.clone(), goal));
        meta
    }

    /// Complete the required do goals before a convenience expression API
    /// discards its elaboration context.
    pub(crate) fn finish_required_do_obligations(&mut self) -> Result<(), ElabError> {
        self.retry_postponed_open_carrier_instances();
        self.ensure_do_pure_obligations()
    }

    /// Required Pure goals remain obligations even when lowering erased all
    /// uses of their instance. Declaration finalization is the last chance to
    /// resolve them; they must not disappear merely because a term is closed.
    pub(super) fn ensure_do_pure_obligations(&self) -> Result<(), ElabError> {
        for meta in &self.do_pure_obligations {
            let Some(id) =
                instance::bare_unassigned_meta(&self.metas, &self.metas.instantiate(meta))
            else {
                continue;
            };
            let Some(var) = self.metas.get(id) else {
                return Err(ElabError::InternalInvariant(
                    "do Pure obligation lost its metavariable".into(),
                ));
            };
            let goal = self.metas.instantiate(&var.ty);
            if !matches!(goal.get_app_fn().kind(), ExprKind::Const(name, _)
                if name == &Name::from_string("Pure"))
            {
                return Err(ElabError::InternalInvariant(
                    "do obligation is not a Pure goal".into(),
                ));
            }
            return Err(ElabError::FailedToSynthesizeInstance {
                goal: crate::error_render::term(&goal),
                detail: self.instance_failure_detail(&goal),
            });
        }
        Ok(())
    }

    /// `@Pure.pure.{u,v} m ?inst α val` — the do lowering's `pure`.
    pub(super) fn mk_pure_term(
        &mut self,
        u: Level,
        v: Level,
        m: Expr,
        alpha: Expr,
        val: Expr,
    ) -> Expr {
        let inst =
            self.do_instance_arg("Pure", vec![u.clone(), v.clone()], std::slice::from_ref(&m));
        Expr::apps(
            Expr::const_(Name::from_string("Pure.pure"), vec![u, v]),
            [m, inst, alpha, val],
        )
    }

    /// `@Bind.bind.{u,v} m ?inst α β x f` — the do lowering's `bind`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn mk_bind_term(
        &mut self,
        u: Level,
        v: Level,
        m: Expr,
        alpha: Expr,
        beta: Expr,
        x: Expr,
        f: Expr,
    ) -> Expr {
        let inst =
            self.do_instance_arg("Bind", vec![u.clone(), v.clone()], std::slice::from_ref(&m));
        Expr::apps(
            Expr::const_(Name::from_string("Bind.bind"), vec![u, v]),
            [m, inst, alpha, beta, x, f],
        )
    }

    /// `?inst : Monad.{u,v} m` — for the `[Monad m]` slot of `StateT.get`,
    /// `OptionT.fail`, `ExceptT.pure`, … in the do lowering.
    pub(super) fn do_monad_instance(&mut self, u: Level, v: Level, m: &Expr) -> Expr {
        self.do_instance_arg("Monad", vec![u, v], std::slice::from_ref(m))
    }

    /// Get cached `(PUnit.{u}, PUnit.unit.{u})` from `do_monad_info`, or create fresh.
    ///
    /// Matches Lean 4's `cachedPUnit`/`cachedPUnitUnit` in `MonadInfo`. Avoids
    /// recreating PUnit constants for each for-loop in the same do-block.
    pub(super) fn get_or_create_punit(&mut self) -> (Expr, Expr) {
        if let Some(info) = &self.do_monad_info {
            (info.cached_punit.clone(), info.cached_punit_unit.clone())
        } else {
            let punit_level = self.fresh_universe_param();
            let punit = Expr::const_(Name::from_string("PUnit"), vec![punit_level.clone()]);
            let punit_unit = Expr::const_(Name::from_string("PUnit.unit"), vec![punit_level]);
            (punit, punit_unit)
        }
    }
}

#[cfg(test)]
mod required_pure_tests {
    use super::*;
    use clean_parser::{parse_decl, parse_expr};

    #[test]
    fn failed_do_declaration_does_not_poison_next_declaration() {
        let env = Environment::with_prelude();
        let mut ctx = ElabCtx::new(&env);
        let bad = parse_decl("def bad : (fun (_ : Type) => Nat) Nat := do { 1 }").expect("parse");
        let err = ctx.elab_decl(&bad).expect_err("Pure is unavailable");
        assert!(err.to_string().contains("Pure"), "{err}");
        assert!(ctx.do_pure_obligations.is_empty());
        assert!(ctx.postponed_open_carrier_instances.is_empty());
        let good = parse_decl("def good : Nat := 1").expect("parse");
        ctx.elab_decl(&good)
            .expect("failed obligation is declaration-local");
    }

    #[test]
    fn nested_declaration_preserves_ambient_do_obligation() {
        let env = Environment::with_prelude();
        let mut ctx = ElabCtx::new(&env);
        let m = ctx.fresh_meta(Expr::arrow(Expr::type_(), Expr::type_()));
        let obligation = ctx.do_instance_arg("Pure", vec![Level::zero(), Level::zero()], &[m]);
        ctx.do_pure_obligations.push(obligation.clone());
        let good = parse_decl("def good : Nat := 1").expect("parse");
        ctx.elab_decl(&good)
            .expect("ambient constraint is not this declaration's");
        assert_eq!(ctx.do_pure_obligations, vec![obligation]);
        assert!(ctx.ensure_do_pure_obligations().is_err());
    }

    #[test]
    fn expression_api_checks_required_pure_before_discarding_context() {
        let env = Environment::with_prelude();
        let bad = parse_expr("(do { 1 } : (fun (_ : Type) => Nat) Nat)").expect("parse");
        let err = crate::elaborate(&env, &bad).expect_err("unused Pure is still required");
        assert!(err.to_string().contains("Pure"), "{err}");
        let good = parse_expr("(do { return 1 } : Id Nat)").expect("parse");
        let term = crate::elaborate(&env, &good).expect("valid expression");
        let ty = TypeChecker::new(&env)
            .infer_type(&term)
            .expect("closed expression checks");
        assert!(!ty.has_fvar_quick());
    }
}
