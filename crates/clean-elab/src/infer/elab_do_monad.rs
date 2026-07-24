// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cached monad info helpers for do-block elaboration.

use super::*;
use clean_kernel::{Expr, Level};
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
        if self.do_monad_info.is_none() || args.len() != 1 {
            return Ok(None);
        }
        let name = match Self::unwrap_surface_parens(func) {
            SurfaceExpr::Ident(_, n) if n == "pure" => n,
            _ => return Ok(None),
        };
        if self.lookup_local(name).is_some()
            || self.env.get_const(&Name::from_string(name)).is_some()
        {
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
