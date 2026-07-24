// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lazy monadic term reduction for bind chains.
//!
//! When the kernel type-checks deep monadic bind chains (e.g., 12 sequential
//! `StateT.bind` or `ExceptT.bind` calls from do-notation), eager delta
//! reduction materializes the full desugared term with O(2^N) paths for N
//! conditional branches. This module short-circuits that expansion by
//! recognizing known monadic patterns and reducing them lazily.
//!
//! Integrated into `whnf_outer_loop` between `reduce_nat` and
//! `try_unfold_definition`. Supported rewrite rules:
//!
//! - `bind (pure v) f` --> `f v`                (left identity / bind-pure)
//! - `bind (Except.ok v) f` --> `f v`           (ok-bind)
//! - `bind (Except.error e) f` --> error e       (error short-circuit)
//! - `ExceptT.bind (ExceptT.mk (pure (ok v))) f` --> `f v`
//! - `ExceptT.bind (ExceptT.mk (pure (error e))) f` --> `ExceptT.mk (pure (error e))`
//!
//! Part of #3401.

use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;
#[cfg(test)]
use std::cell::Cell;
use std::sync::LazyLock;

static BIND_BIND: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bind.bind"));
static PURE_PURE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Pure.pure"));
static ID: LazyLock<Name> = LazyLock::new(|| Name::from_string("Id"));
static STATE_T: LazyLock<Name> = LazyLock::new(|| Name::from_string("StateT"));
static STATE_T_BIND: LazyLock<Name> = LazyLock::new(|| Name::from_string("StateT.bind"));
static STATE_T_PURE: LazyLock<Name> = LazyLock::new(|| Name::from_string("StateT.pure"));
static EXCEPT: LazyLock<Name> = LazyLock::new(|| Name::from_string("Except"));
static EXCEPT_OK: LazyLock<Name> = LazyLock::new(|| Name::from_string("Except.ok"));
static EXCEPT_ERROR: LazyLock<Name> = LazyLock::new(|| Name::from_string("Except.error"));
static EXCEPT_T: LazyLock<Name> = LazyLock::new(|| Name::from_string("ExceptT"));
static EXCEPT_T_BIND: LazyLock<Name> = LazyLock::new(|| Name::from_string("ExceptT.bind"));
static EXCEPT_T_MK: LazyLock<Name> = LazyLock::new(|| Name::from_string("ExceptT.mk"));
static PROD: LazyLock<Name> = LazyLock::new(|| Name::from_string("Prod"));
static PROD_MK: LazyLock<Name> = LazyLock::new(|| Name::from_string("Prod.mk"));

#[cfg(test)]
thread_local! {
    static MONAD_REDUCE_CALLS: Cell<u64> = const { Cell::new(0) };
    static MONAD_REDUCE_REWRITES: Cell<u64> = const { Cell::new(0) };
    static MONAD_REDUCE_SHORT_CIRCUITS: Cell<u64> = const { Cell::new(0) };
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum BindKind {
    Generic,
    StateT,
    Except,
    ExceptT,
    /// The identity monad `Id` (`bind x f ≡ f x`). Also matches `Id` in its
    /// delta-unfolded spelling `fun (a : Type) => a` — the elaborator unfolds
    /// the semireducible `Id` alias when it infers the `pure`/`bind` monad
    /// argument, so the monad reaches WHNF as the identity lambda. Brick B22.
    Id,
}

impl<'env> TypeChecker<'env> {
    #[cfg(test)]
    pub(super) fn reset_monad_reduce_stats_for_tests(&self) {
        MONAD_REDUCE_CALLS.with(|v| v.set(0));
        MONAD_REDUCE_REWRITES.with(|v| v.set(0));
        MONAD_REDUCE_SHORT_CIRCUITS.with(|v| v.set(0));
    }

    #[cfg(test)]
    pub(super) fn monad_reduce_stats_for_tests(&self) -> (u64, u64, u64) {
        (
            MONAD_REDUCE_CALLS.with(Cell::get),
            MONAD_REDUCE_REWRITES.with(Cell::get),
            MONAD_REDUCE_SHORT_CIRCUITS.with(Cell::get),
        )
    }

    /// Lazy monad reduction hook for the outer WHNF loop.
    ///
    /// Recognizes monadic bind/pure forms and rewrites obvious monadic
    /// redexes (`bind (pure x) f` --> `f x`, `pure (Except ε) a` -->
    /// `Except.ok ε a`, …) before the outer loop delta-unfolds the full bind
    /// definition.
    ///
    /// Returns `Some(reduced)` ONLY when a rewrite made progress (or on a
    /// heartbeat-exhaustion bail). Returns `None` when no rewrite applies,
    /// letting the outer loop proceed to `try_unfold_definition` — the
    /// standard, Lean-parity delta path.
    ///
    /// # Soundness
    ///
    /// All rewrites correspond to definitional equalities (monad laws):
    /// - `bind (pure v) f ≡ f v`           (left identity)
    /// - `bind (error e) f ≡ error e`       (left zero)
    ///
    /// # Completeness (residual-to-zero campaign, 2026-07-02)
    ///
    /// This hook previously returned `Some(e)` (unchanged) for ANY
    /// `Pure.pure`-headed application it could not rewrite, and for any
    /// unrewritable `Bind.bind` chain. `whnf_outer_loop` treats a no-progress
    /// `Some` as FINAL — so every `@Pure.pure m inst α a` / `Bind.bind …`
    /// over a monad other than `Except`/`StateT`/`ExceptT` (e.g. `Filter`,
    /// `Ultrafilter`) was frozen and never delta-unfolded, even though the
    /// genuine value-bearing `Pure.pure` projection imports from the `.olean`
    /// (axiom-stub upgrade). That artificial freeze rejected Lean-valid
    /// `Iff.rfl`/`rfl` proofs over `pure` (`Filter.mem_pure` and the whole
    /// Order/Filter `pure` type_mismatch cluster — `(pure a).sets` could
    /// never expose `Filter.mk`). The freeze was invisible while `Pure.pure`
    /// was a value-less prelude axiom (unfold was a no-op anyway); it became
    /// an active completeness hole once the genuine projection imported.
    ///
    /// The fix — returning `None` on no-progress — only allows MORE standard
    /// delta/beta/proj reduction (the kernel's own certified machinery, which
    /// Lean's kernel — which has no monad hook at all — performs unchanged);
    /// it derives no equality that plain delta would not. In the default
    /// (proof-execution) prelude `Pure.pure`/`Bind.bind` remain value-less
    /// axioms, so unfolding is a no-op there and behavior is unchanged.
    ///
    /// Part of #3401.
    pub(super) fn try_monad_reduce(&self, e: &Expr) -> Option<Expr> {
        if !self.env.has_monad_classes() || self.heartbeat_exhausted() {
            return None;
        }

        #[cfg(test)]
        MONAD_REDUCE_CALLS.with(|v| v.set(v.get().saturating_add(1)));

        let head = e.get_app_fn();
        let ExprKind::Const(name, _) = head.kind() else {
            return None;
        };
        let args = e.get_app_args();

        // `Pure.pure (Except ε) α a` materializes to the concrete `Except`
        // monad's `pure`, which is `Except.ok ε α a`. This is the definitional
        // unfolding of the `Pure (Except ε)` instance: without it, a do-block's
        // trailing `pure x` stays stuck as `Pure.pure …` and never converts to
        // the `Except.ok x` a ground `rfl` (or an outer bind/ICmp lane fold)
        // compares against. The kernel re-checks the rewritten `Except.ok`
        // application, so this preserves soundness. (Track Q)
        if *name == *PURE_PURE && args.len() >= 3 {
            if let Some(reduced) = self.try_pure_to_except_ok(head, &args) {
                #[cfg(test)]
                MONAD_REDUCE_REWRITES.with(|v| v.set(v.get().saturating_add(1)));
                return Some(reduced);
            }
            if let Some(reduced) = self.try_pure_to_state_t(head, &args) {
                #[cfg(test)]
                MONAD_REDUCE_REWRITES.with(|v| v.set(v.get().saturating_add(1)));
                return Some(reduced);
            }
            // `Pure.pure Id α v` (or its unfolded `Pure.pure (fun a => a) α v`)
            // materializes to the identity monad's `pure`, which is `v`.
            if let Some(reduced) = self.try_pure_to_id(&args) {
                #[cfg(test)]
                MONAD_REDUCE_REWRITES.with(|v| v.set(v.get().saturating_add(1)));
                return Some(reduced);
            }
        }

        // A `Pure.pure`/`StateT.pure` head that none of the rewrites above
        // materialized: fall through to the outer loop's standard
        // `try_unfold_definition` (see the Completeness note in the doc
        // comment — the old `Some(e)` freeze here rejected Lean-valid proofs
        // over non-Except/StateT monads such as `Filter`).
        if Self::is_known_pure_head(name, args.len()) {
            #[cfg(test)]
            MONAD_REDUCE_SHORT_CIRCUITS.with(|v| v.set(v.get().saturating_add(1)));
            return None;
        }

        let (kind, ma_idx) = if *name == *STATE_T_BIND {
            (BindKind::StateT, 4)
        } else if *name == *EXCEPT_T_BIND {
            (BindKind::ExceptT, 4)
        } else if *name == *BIND_BIND {
            (self.monad_kind_from_expr(args.first().copied()?), 3)
        } else {
            return None;
        };

        if args.len() <= ma_idx + 1 {
            return None;
        }

        self.inc_heartbeat();
        if self.heartbeat_exhausted() {
            #[cfg(test)]
            MONAD_REDUCE_SHORT_CIRCUITS.with(|v| v.set(v.get().saturating_add(1)));
            return Some(e.clone());
        }

        let ma = args[ma_idx];
        let f = args[ma_idx + 1];
        let tail = &args[ma_idx + 2..];
        let ma_whnf = self.whnf_impl(ma);

        if let Some(payload) = Self::pure_payload(&ma_whnf) {
            #[cfg(test)]
            MONAD_REDUCE_REWRITES.with(|v| v.set(v.get().saturating_add(1)));
            return Some(self.reapply_tail(Expr::app(f.clone(), payload), tail));
        }

        let reduced = match kind {
            BindKind::Except => self.try_except_bind(&ma_whnf, f, tail),
            BindKind::ExceptT => self.try_except_t_bind(&ma_whnf, f, tail),
            // Identity monad: `bind x f ≡ f x`. `ma_whnf` is the (possibly
            // already `pure`-reduced) action; the terminal `pure` inside `f`
            // is separately collapsed by `try_pure_to_id`. The `pure_payload`
            // fast path above does NOT catch this when `ma` reduced to a bare
            // value (its `Pure.pure` head was already rewritten), so the Id
            // bind rule is what keeps a do-chain over `Id` progressing.
            BindKind::Id => Some(self.reapply_tail(Expr::app(f.clone(), ma_whnf.clone()), tail)),
            BindKind::Generic | BindKind::StateT => None,
        };
        if let Some(result) = reduced {
            #[cfg(test)]
            MONAD_REDUCE_REWRITES.with(|v| v.set(v.get().saturating_add(1)));
            return Some(result);
        }

        // No bind rewrite made progress: fall through to standard delta (see
        // the Completeness note in the doc comment — the old `Some(e)` freeze
        // here blocked `Bind.bind` over generic monads from ever unfolding).
        #[cfg(test)]
        MONAD_REDUCE_SHORT_CIRCUITS.with(|v| v.set(v.get().saturating_add(1)));
        None
    }

    pub(super) fn monad_kind_from_expr(&self, m: &Expr) -> BindKind {
        if Self::is_id_monad(m) {
            return BindKind::Id;
        }
        match m.get_app_fn().kind() {
            ExprKind::Const(name, _) if *name == *STATE_T => BindKind::StateT,
            ExprKind::Const(name, _) if *name == *EXCEPT_T => BindKind::ExceptT,
            ExprKind::Const(name, _) if *name == *EXCEPT => BindKind::Except,
            _ => BindKind::Generic,
        }
    }

    /// True iff `m` is the identity monad `Id` — either the folded constant
    /// `Id` (any levels) or its delta-unfolded spelling `fun (a : Type _) => a`
    /// (the identity lambda). The elaborator unfolds the semireducible `Id`
    /// alias when it infers the `pure`/`bind` monad argument (unifying against
    /// `Id.run`'s domain `Id α`), so both spellings reach the kernel. Any
    /// closed monad definitionally equal to `fun a => a` IS `Id`, so matching
    /// the identity lambda is sound. Brick B22.
    fn is_id_monad(m: &Expr) -> bool {
        match m.kind() {
            ExprKind::Const(name, _) => *name == *ID,
            ExprKind::Lam(_, _, body) => matches!(body.kind(), ExprKind::BVar(0)),
            _ => false,
        }
    }

    /// `Pure.pure Id α v ≡ v` (identity-monad `pure`). `args = [m, α, v, …]`;
    /// fires only when `m` is `Id` (folded or unfolded — [`Self::is_id_monad`]).
    /// Trailing over-saturating args are re-applied.
    ///
    /// SOUNDNESS: this is the definitional unfolding of Lean's core
    /// `instance : Monad Id` (`pure := fun x => x`); the kernel re-checks the
    /// rewritten term. It cannot over-equate — distinct payloads reduce to
    /// distinct values (`Pure.pure Id Nat 5 ↦ 5 ≠ 6`), so the wrong pin
    /// `Id.run (pure 5) = 6 := rfl` stays rejected. Same discipline as
    /// [`Self::try_pure_to_except_ok`].
    pub(super) fn try_pure_to_id(&self, args: &[&Expr]) -> Option<Expr> {
        let m = args.first()?;
        if !Self::is_id_monad(m) {
            return None;
        }
        let value = (*args.get(2)?).clone();
        Some(self.reapply_tail(value, &args[3..]))
    }

    pub(super) fn reapply_tail(&self, head: Expr, tail: &[&Expr]) -> Expr {
        tail.iter()
            .fold(head, |result, arg| Expr::app(result, (*arg).clone()))
    }

    /// Materialize `Pure.pure (Except ε) α a` into `Except.ok ε α a`.
    ///
    /// `head` is the `Pure.pure` constant (carrying its `{u, v}` levels) and
    /// `args` is `[m, α, a, …]` where the monad `m` must be `Except ε` (head
    /// `Except` applied to an error type). The resulting `Except.ok` is built at
    /// the element universe `u = levels[0]` (for `Except : Type u → Type u →
    /// Type u`, the `pure` instance's `m`-codomain universe `v` coincides with
    /// the element universe `u`). Any trailing `args` beyond `[m, α, a]` are
    /// re-applied so an over-saturated `Pure.pure … x y` keeps `y`. Returns
    /// `None` when the monad is not a concrete `Except`, leaving the generic
    /// stuck-`pure` short-circuit to fire.
    pub(super) fn try_pure_to_except_ok(&self, head: &Expr, args: &[&Expr]) -> Option<Expr> {
        let ExprKind::Const(_, levels) = head.kind() else {
            return None;
        };
        let u = levels.first().cloned()?;
        let m = args.first()?;
        // m must be `Except ε`: head `Except` applied to exactly one arg.
        let m_fn = m.get_app_fn();
        let ExprKind::Const(m_name, _) = m_fn.kind() else {
            return None;
        };
        if *m_name != *EXCEPT {
            return None;
        }
        let m_args = m.get_app_args();
        if m_args.len() != 1 {
            return None;
        }
        let eps = m_args[0].clone();
        let alpha = args.get(1)?;
        let value = args.get(2)?;
        // Except.ok.{u} ε α a
        let ok = Expr::const_(EXCEPT_OK.clone(), vec![u]);
        let ok = Expr::app(
            Expr::app(Expr::app(ok, eps), (*alpha).clone()),
            (*value).clone(),
        );
        // Re-apply any over-saturating tail args (args beyond [m, α, a]).
        Some(self.reapply_tail(ok, &args[3..]))
    }

    /// Materialize `Pure.pure (StateT σ m) α a` into the `StateT σ m` instance's
    /// `pure`: `fun (s : σ) => Pure.pure m (Prod α σ) (Prod.mk a s)`.
    ///
    /// This is the definitional unfolding of the `Pure (StateT σ m)` instance
    /// (`StateT.pure a = fun s => pure (a, s)`). Composed with the reducible
    /// `StateT.run` definition (`run x s = x s`) and the existing
    /// `Pure.pure (Except ε) → Except.ok` rewrite, it lets a monad-law `rfl`
    /// such as `Sem.run_pure : StateT.run (pure x) s = .ok (x, s)` reduce to a
    /// ground term: `StateT.run (pure x) s → (pure x) s → pure m (α×σ) (x, s) →
    /// Except.ok (x, s)`.
    ///
    /// `head` is the `Pure.pure.{u, v}` constant; `args = [StateT σ m, α, a, …]`.
    /// The introduced `fun (s : σ)` binder shifts every reused closed/loose
    /// sub-term up by one (`lift(1)`); the new `s` is `BVar(0)`. Trailing args
    /// beyond `[m, α, a]` are re-applied OUTSIDE the lambda (they are arguments
    /// the StateT action is further applied to, i.e. the state `s` — but here we
    /// instead apply the lambda to nothing and leave the tail for the caller's
    /// `reapply_tail` so `StateT.run`/application drives it). Returns `None`
    /// unless the monad is a concrete `StateT σ m`.
    ///
    /// SOUNDNESS: the emitted term is `fun s => Pure.pure m (α×σ) (a, s)`, built
    /// from core constants; the kernel re-checks it. It equals the `StateT.pure`
    /// instance body, so it is a definitional equality (monad left-identity at
    /// the StateT layer). Non-StateT monads return `None`, preserving prior
    /// behavior.
    /// Recover `(σ, baseM)` from a monad expression that is `StateT σ baseM`,
    /// accepting either the folded `StateT σ baseM` constant application or its
    /// delta-unfolded definitional lambda `fun (α : Type) => σ → baseM (Prod α
    /// σ)`. Returns `None` for any other shape.
    ///
    /// Both `σ` and `baseM` are returned in the *outer* context (i.e. with no
    /// reference to the unfolded lambda's `α` binder): `σ` does not mention `α`,
    /// and `baseM` is the head function applied to `Prod α σ`, lowered out from
    /// under the `α`/`s` binders.
    fn state_t_components(&self, m_outer: &Expr) -> Option<(Expr, Expr)> {
        // Folded form: `StateT σ baseM`.
        if let ExprKind::Const(m_name, _) = m_outer.get_app_fn().kind() {
            if *m_name == *STATE_T {
                let st_args = m_outer.get_app_args();
                if st_args.len() == 2 {
                    return Some((st_args[0].clone(), st_args[1].clone()));
                }
            }
        }
        // Unfolded form: `fun (α : Type u) => σ → baseM (Prod α σ)`.
        //   Lam(α, _, Pi(s, σ, App(baseM, App(App(Prod, BVar1=α), σ))))
        let ExprKind::Lam(_, _alpha_ty, lam_body) = m_outer.kind() else {
            return None;
        };
        // lam_body is under binder α (BVar 0 == α inside the lambda body).
        let ExprKind::Pi(_, pi_dom, pi_body) = lam_body.kind() else {
            return None;
        };
        // σ is the Pi domain; it must not reference α (BVar 0 inside the lambda).
        let sigma_in_lam = (**pi_dom).clone();
        if sigma_in_lam.loose_bvar_range() > 0 {
            // σ would reference α — not the StateT shape we model.
            return None;
        }
        // Inside pi_body, indices: BVar0 = s, BVar1 = α.
        // pi_body must be `baseM (Prod α σ)` = App(baseM, prod_app).
        let ExprKind::App(base_m, prod_app) = pi_body.kind() else {
            return None;
        };
        // prod_app must be `Prod α σ` = App(App(Prod, α), σ).
        let prod_head = prod_app.get_app_fn();
        let ExprKind::Const(prod_name, _) = prod_head.kind() else {
            return None;
        };
        if *prod_name != *PROD {
            return None;
        }
        // baseM is applied under two binders (α, s); lower it back to the outer
        // context. baseM must not reference α or s (the base monad is fixed). A
        // base monad mentioning either binder is not the canonical StateT shape.
        if base_m.loose_bvar_range() > 0 {
            return None;
        }
        let base_m_outer = (**base_m).clone();
        // σ inside the lambda is closed (checked above), so it is already valid
        // in the outer context.
        Some((sigma_in_lam, base_m_outer))
    }

    pub(super) fn try_pure_to_state_t(&self, head: &Expr, args: &[&Expr]) -> Option<Expr> {
        let ExprKind::Const(_, levels) = head.kind() else {
            return None;
        };
        // Pure.pure.{u, v}: u = element universe, v = base-monad result universe.
        let u = levels.first().cloned()?;
        let v = levels.get(1).cloned()?;
        let m_outer = args.first()?;
        // The monad `m` is `StateT σ baseM`. Because `StateT` is registered with
        // `is_reducible: true`, by the time WHNF reaches this `Pure.pure`, the
        // `StateT σ baseM` argument has typically been delta-unfolded into its
        // raw definitional lambda `fun (α : Type u) => σ → baseM (Prod α σ)`. We
        // accept either spelling: the still-folded `StateT σ baseM` Const-app, or
        // the unfolded lambda, recovering `σ` and `baseM` from each.
        let (sigma, m) = self.state_t_components(m_outer)?;
        let alpha = (*args.get(1)?).clone();
        let value = (*args.get(2)?).clone();
        let tail = &args[3..];

        // Under the new `fun (s : σ)` binder, every reused sub-term lifts by 1;
        // the bound `s` is BVar(0).
        let sigma_l = sigma.lift(1);
        let m_l = m.lift(1);
        let alpha_l = alpha.lift(1);
        let value_l = value.lift(1);
        let s_bv = Expr::bvar(0);

        // Prod α σ  and  Prod.mk α σ a s  (at universes u, u — Prod.{u,u}).
        let prod_levels = vec![u.clone(), u.clone()];
        let prod_ty = Expr::app(
            Expr::app(
                Expr::const_(PROD.clone(), prod_levels.clone()),
                alpha_l.clone(),
            ),
            sigma_l.clone(),
        );
        let prod_mk = Expr::const_(PROD_MK.clone(), prod_levels);
        let pair = Expr::app(
            Expr::app(
                Expr::app(Expr::app(prod_mk, alpha_l.clone()), sigma_l.clone()),
                value_l.clone(),
            ),
            s_bv,
        );

        // Inner pure: `Pure.pure.{u, v} m (Prod α σ) (a, s)`.
        let inner_pure = Expr::const_(PURE_PURE.clone(), vec![u, v]);
        let inner = Expr::app(Expr::app(Expr::app(inner_pure, m_l), prod_ty), pair);

        // Close the `fun (s : σ)` binder.
        let lam = Expr::lam(crate::BinderInfo::Default, sigma, inner);
        Some(self.reapply_tail(lam, tail))
    }

    pub(super) fn try_except_bind(&self, ma_whnf: &Expr, f: &Expr, tail: &[&Expr]) -> Option<Expr> {
        if let Some(payload) = Self::except_ok_payload(ma_whnf) {
            return Some(self.reapply_tail(Expr::app(f.clone(), payload), tail));
        }
        if Self::is_except_error(ma_whnf) {
            return Some(self.reapply_tail(ma_whnf.clone(), tail));
        }
        None
    }

    pub(super) fn try_except_t_bind(
        &self,
        ma_whnf: &Expr,
        f: &Expr,
        tail: &[&Expr],
    ) -> Option<Expr> {
        let inner = Self::except_t_mk_inner(ma_whnf)?;
        self.inc_heartbeat();
        if self.heartbeat_exhausted() {
            return Some(self.reapply_tail(ma_whnf.clone(), tail));
        }
        let inner_whnf = self.whnf_impl(inner);
        let inner_value = Self::pure_payload(&inner_whnf).unwrap_or(inner_whnf);
        if let Some(payload) = Self::except_ok_payload(&inner_value) {
            return Some(self.reapply_tail(Expr::app(f.clone(), payload), tail));
        }
        if Self::is_except_error(&inner_value) {
            return Some(self.reapply_tail(ma_whnf.clone(), tail));
        }
        None
    }

    pub(super) fn is_known_pure_head(name: &Name, nargs: usize) -> bool {
        (*name == *PURE_PURE && nargs >= 3) || (*name == *STATE_T_PURE && nargs >= 4)
    }

    pub(super) fn pure_payload(e: &Expr) -> Option<Expr> {
        if let ExprKind::Const(name, _) = e.get_app_fn().kind() {
            let args = e.get_app_args();
            if (*name == *PURE_PURE && args.len() >= 3)
                || (*name == *STATE_T_PURE && args.len() >= 4)
            {
                return args.last().map(|arg| (*arg).clone());
            }
        }
        None
    }

    pub(super) fn except_ok_payload(e: &Expr) -> Option<Expr> {
        if let ExprKind::Const(name, _) = e.get_app_fn().kind() {
            let args = e.get_app_args();
            if *name == *EXCEPT_OK && args.len() >= 3 {
                return args.last().map(|arg| (*arg).clone());
            }
        }
        None
    }

    pub(super) fn is_except_error(e: &Expr) -> bool {
        matches!(e.get_app_fn().kind(), ExprKind::Const(name, _) if *name == *EXCEPT_ERROR)
            && e.get_app_num_args() >= 3
    }

    pub(super) fn except_t_mk_inner(e: &Expr) -> Option<&Expr> {
        if let ExprKind::Const(name, _) = e.get_app_fn().kind() {
            let args = e.get_app_args();
            if *name == *EXCEPT_T_MK && args.len() >= 4 {
                return args.last().copied();
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Environment;
    use crate::{BinderInfo, ConstantInfo, Expr, Level, Name};

    fn monad_env() -> Environment {
        let mut env = Environment::new();
        env.init_id().expect("init_id");
        env.init_state_t().expect("init_state_t");
        env.init_except_t().expect("init_except_t");
        env.init_monad_classes().expect("init_monad_classes");
        env
    }

    fn install_stub(env: &mut Environment, name: &str, value: Expr) {
        let info = ConstantInfo::new(
            Name::from_string(name),
            vec![],
            Expr::type_(),
            Some(value),
            false,
        );
        env.extend_constants_unchecked(std::iter::once(info));
    }

    fn lam(body: Expr) -> Expr {
        Expr::lam(BinderInfo::Default, Expr::type_(), body)
    }

    fn bind_stub_value() -> Expr {
        let mut result = Expr::bvar(1);
        for _ in 0..6 {
            result = lam(result);
        }
        result
    }

    #[test]
    fn test_bind_pure_shortcut_reduces_and_counts_stats() {
        let env = monad_env();
        let tc = TypeChecker::new(&env);
        tc.reset_monad_reduce_stats_for_tests();

        // A GENERIC monad with no special rule (`Filter`, unregistered): the
        // `bind (pure v) f → f v` shortcut fires via `pure_payload` (1 rewrite)
        // and the nested `pure` is short-circuited by `is_known_pure_head`.
        // (`Id` is no longer generic — B22 gives it dedicated pure/bind rules,
        // exercised by the Id suite in `data_monad_insts` and `id_monad_e2e`.)
        let generic_monad = Expr::const_(Name::from_string("Filter"), vec![Level::zero()]);
        let pure = Expr::apps(
            Expr::const_(
                Name::from_string("Pure.pure"),
                vec![Level::zero(), Level::zero()],
            ),
            vec![generic_monad.clone(), Expr::type_(), Expr::prop()],
        );
        let k = lam(Expr::bvar(0));
        let bind = Expr::apps(
            Expr::const_(
                Name::from_string("Bind.bind"),
                vec![Level::zero(), Level::zero()],
            ),
            vec![generic_monad, Expr::type_(), Expr::type_(), pure, k],
        );

        assert_eq!(tc.whnf(&bind), Expr::prop());
        let (calls, rewrites, short_circuits) = tc.monad_reduce_stats_for_tests();
        assert!(calls >= 1, "expected at least one monad reducer call");
        assert_eq!(rewrites, 1, "expected a single bind rewrite");
        assert!(
            short_circuits >= 1,
            "expected nested pure terms to be short-circuited"
        );
    }

    /// B22: `Pure.pure Id α v` now materializes to the identity monad's `pure`
    /// (`v`) via `try_pure_to_id`, and `Bind.bind Id α β ma f` to `f ma`. This
    /// is the kernel-level driver behind `Id.run (pure 5) = 5 := rfl` — the
    /// elaborator unfolds `Id` to `fun a => a` during monad inference, so the
    /// hook accepts both spellings (see `is_id_monad`).
    #[test]
    fn test_pure_and_bind_over_id_reduce() {
        let env = monad_env();
        let tc = TypeChecker::new(&env);

        // Folded `Id`: `Pure.pure Id Nat 7 ≡ 7`.
        let id_folded = Expr::const_(Name::from_string("Id"), vec![Level::zero()]);
        let pure_folded = Expr::apps(
            Expr::const_(
                Name::from_string("Pure.pure"),
                vec![Level::zero(), Level::zero()],
            ),
            vec![id_folded.clone(), Expr::type_(), Expr::prop()],
        );
        assert_eq!(tc.whnf(&pure_folded), Expr::prop());

        // Unfolded `Id` = `fun (a : Type) => a`: same reduction.
        let id_unfolded = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
        let pure_unfolded = Expr::apps(
            Expr::const_(
                Name::from_string("Pure.pure"),
                vec![Level::zero(), Level::zero()],
            ),
            vec![id_unfolded.clone(), Expr::type_(), Expr::prop()],
        );
        assert_eq!(tc.whnf(&pure_unfolded), Expr::prop());

        // `Bind.bind Id Nat Nat (pure Prop) (fun x => x) ≡ Prop`.
        let bind = Expr::apps(
            Expr::const_(
                Name::from_string("Bind.bind"),
                vec![Level::zero(), Level::zero()],
            ),
            vec![
                id_folded,
                Expr::type_(),
                Expr::type_(),
                pure_folded,
                lam(Expr::bvar(0)),
            ],
        );
        assert_eq!(tc.whnf(&bind), Expr::prop());
    }

    /// COMPLETENESS pin (residual-to-zero campaign, 2026-07-02): a
    /// value-bearing `Pure.pure` over a monad none of the rewrites recognize
    /// must fall through to standard delta and reduce — the old `Some(e)`
    /// freeze left it stuck forever (the Order/Filter `pure` cluster:
    /// `(pure a).sets` never exposed `Filter.mk`).
    #[test]
    fn test_value_bearing_pure_over_unknown_monad_unfolds() {
        let mut env = monad_env();
        // pure := fun m α a => a  (payload projector, mirroring the genuine
        // instance-projection). Delivered through the SAME `.olean`
        // axiom-stub upgrade path production uses: the prelude's value-less
        // `Pure.pure` axiom is wholesale-replaced by a value-bearing def.
        let pure_value = lam(lam(lam(Expr::bvar(0))));
        let upgraded = env.upgrade_axiom_stubs(std::iter::once(ConstantInfo::new(
            Name::from_string("Pure.pure"),
            vec![],
            Expr::type_(),
            Some(pure_value),
            false,
        )));
        assert_eq!(upgraded, 1, "Pure.pure axiom stub must upgrade");
        let tc = TypeChecker::new(&env);

        let pure_app = Expr::apps(
            Expr::const_(Name::from_string("Pure.pure"), vec![]),
            vec![
                Expr::const_(Name::from_string("Id"), vec![Level::zero()]),
                Expr::type_(),
                Expr::prop(),
            ],
        );
        assert_eq!(
            tc.whnf(&pure_app),
            Expr::prop(),
            "value-bearing Pure.pure over an unrecognized monad must delta-unfold"
        );

        // ADVERSARIAL: distinct payloads must still be rejected — the
        // completeness fix must not equate non-def-eq pure applications.
        let pure_other = Expr::apps(
            Expr::const_(Name::from_string("Pure.pure"), vec![]),
            vec![
                Expr::const_(Name::from_string("Id"), vec![Level::zero()]),
                Expr::type_(),
                Expr::type_(),
            ],
        );
        assert!(
            !tc.is_def_eq(&pure_app, &pure_other),
            "pure applications with non-def-eq payloads must stay unequal"
        );
    }

    /// Re-pinned (residual-to-zero campaign, 2026-07-02): an unrewritable
    /// `StateT.bind` chain now falls through to STANDARD delta unfolding
    /// (Lean-parity completeness) instead of being frozen by the monad hook.
    /// The old `Some(e)`-freeze rejected Lean-valid proofs over monads the
    /// rewrites don't recognize (the Order/Filter `pure` type_mismatch
    /// cluster). Here the installed stub value ignores its bind arguments and
    /// returns the action, so full WHNF must now reach `blockedAction`.
    #[test]
    fn test_state_t_bind_unrewritable_falls_through_to_delta() {
        let mut env = monad_env();
        install_stub(&mut env, "StateT.bind", bind_stub_value());
        let tc = TypeChecker::new(&env);

        let stuck = Expr::const_(Name::from_string("blockedAction"), vec![]);
        let k = Expr::const_(Name::from_string("blockedCont"), vec![]);
        let bind = Expr::apps(
            Expr::const_(Name::from_string("StateT.bind"), vec![]),
            vec![
                Expr::type_(),
                Expr::const_(Name::from_string("Id"), vec![Level::zero()]),
                Expr::type_(),
                Expr::type_(),
                stuck.clone(),
                k,
            ],
        );

        assert_eq!(
            tc.whnf(&bind),
            stuck,
            "unrewritable StateT.bind must delta-unfold (completeness), not freeze"
        );
    }

    #[test]
    fn test_except_t_bind_routes_error_branch() {
        let mut env = monad_env();
        install_stub(&mut env, "ExceptT.bind", bind_stub_value());
        let tc = TypeChecker::new(&env);

        let err = Expr::apps(
            Expr::const_(Name::from_string("Except.error"), vec![Level::zero()]),
            vec![Expr::type_(), Expr::type_(), Expr::prop()],
        );
        let pure_err = Expr::apps(
            Expr::const_(
                Name::from_string("Pure.pure"),
                vec![Level::zero(), Level::zero()],
            ),
            vec![
                Expr::const_(Name::from_string("Id"), vec![Level::zero()]),
                Expr::apps(
                    Expr::const_(Name::from_string("Except"), vec![Level::zero()]),
                    vec![Expr::type_()],
                ),
                err,
            ],
        );
        let ma = Expr::apps(
            Expr::const_(
                Name::from_string("ExceptT.mk"),
                vec![Level::zero(), Level::zero()],
            ),
            vec![
                Expr::type_(),
                Expr::const_(Name::from_string("Id"), vec![Level::zero()]),
                Expr::type_(),
                pure_err,
            ],
        );
        let bind = Expr::apps(
            Expr::const_(Name::from_string("ExceptT.bind"), vec![]),
            vec![
                Expr::type_(),
                Expr::const_(Name::from_string("Id"), vec![Level::zero()]),
                Expr::type_(),
                Expr::type_(),
                ma.clone(),
                lam(Expr::bvar(0)),
            ],
        );

        assert_eq!(tc.whnf(&bind), ma);
    }

    #[test]
    fn test_monad_reduce_is_disabled_without_monad_classes() {
        let env = Environment::new();
        let tc = TypeChecker::new(&env);
        let e = Expr::apps(
            Expr::const_(Name::from_string("Bind.bind"), vec![]),
            vec![
                Expr::type_(),
                Expr::type_(),
                Expr::type_(),
                Expr::prop(),
                Expr::prop(),
            ],
        );
        assert!(tc.try_monad_reduce(&e).is_none());
    }

    /// `Pure.pure (Except ε) α a` materializes to `Except.ok ε α a`. Without
    /// this, a do-block's trailing `pure x` over `Except` stays a stuck
    /// `Pure.pure …` const that never converts to the `Except.ok x` a ground
    /// `rfl` (or a lane-fold bind) compares against. (Track Q)
    #[test]
    fn test_pure_over_except_reduces_to_except_ok() {
        let env = monad_env();
        let tc = TypeChecker::new(&env);

        let eps = Expr::prop();
        let except_eps = Expr::apps(
            Expr::const_(Name::from_string("Except"), vec![Level::zero()]),
            vec![eps.clone()],
        );
        let alpha = Expr::type_();
        let value = Expr::prop();
        let pure = Expr::apps(
            Expr::const_(
                Name::from_string("Pure.pure"),
                vec![Level::zero(), Level::zero()],
            ),
            vec![except_eps, alpha.clone(), value.clone()],
        );

        let expected = Expr::apps(
            Expr::const_(Name::from_string("Except.ok"), vec![Level::zero()]),
            vec![eps, alpha, value],
        );

        assert_eq!(tc.whnf(&pure), expected);
    }

    /// `Pure.pure (StateT σ baseM) α a` (folded `StateT` spelling) materializes
    /// to the `StateT` instance's `pure`: `fun (s : σ) => Pure.pure baseM (Prod
    /// α σ) (Prod.mk a s)`. This is the rewrite that lets `StateT.run (pure x) s`
    /// reduce for a monad-law `rfl`. (Track W)
    #[test]
    fn test_pure_over_state_t_materializes_state_function() {
        let env = monad_env();
        let tc = TypeChecker::new(&env);

        let sigma = Expr::type_();
        let base_m = Expr::const_(Name::from_string("Id"), vec![Level::zero()]);
        // StateT σ baseM (folded form).
        let state_t = Expr::apps(
            Expr::const_(
                Name::from_string("StateT"),
                vec![Level::zero(), Level::zero()],
            ),
            vec![sigma.clone(), base_m.clone()],
        );
        let alpha = Expr::type_();
        let value = Expr::prop();
        let pure = Expr::apps(
            Expr::const_(
                Name::from_string("Pure.pure"),
                vec![Level::zero(), Level::zero()],
            ),
            vec![state_t, alpha.clone(), value.clone()],
        );

        // Expected: fun (s : σ) => Pure.pure baseM (Prod α σ) (Prod.mk α σ a s).
        // Under the binder, BVar(0) = s; the closed sub-terms lift by 0 (no-op).
        let prod_ty = Expr::apps(
            Expr::const_(
                Name::from_string("Prod"),
                vec![Level::zero(), Level::zero()],
            ),
            vec![alpha.clone(), sigma.clone()],
        );
        let pair = Expr::apps(
            Expr::const_(
                Name::from_string("Prod.mk"),
                vec![Level::zero(), Level::zero()],
            ),
            vec![alpha.clone(), sigma.clone(), value.clone(), Expr::bvar(0)],
        );
        let inner = Expr::apps(
            Expr::const_(
                Name::from_string("Pure.pure"),
                vec![Level::zero(), Level::zero()],
            ),
            vec![base_m, prod_ty, pair],
        );
        let expected = Expr::lam(BinderInfo::Default, sigma, inner);

        // whnf reduces the outer Pure.pure to the StateT state-function. The
        // inner Pure.pure over `Id` survives verbatim because it sits UNDER the
        // introduced `fun (s : σ)` binder — weak-head normalization does not
        // reduce under binders (the B22 `try_pure_to_id` rule would collapse it
        // only once it reaches head position).
        assert_eq!(tc.whnf(&pure), expected);
    }

    /// A generic monad with no dedicated rule (`Filter`) does NOT get the
    /// `Except.ok`/`Id` rewrites — the generic stuck-`pure` short-circuit fires
    /// and leaves `Pure.pure` intact, so the concrete rewrites are scoped to
    /// their own instances only. (Pre-B22 this used `Id`; `Id` now reduces via
    /// `try_pure_to_id`, so the "still stuck" role moves to an unhandled monad.)
    #[test]
    fn test_pure_over_non_except_is_left_stuck() {
        let env = monad_env();
        let tc = TypeChecker::new(&env);

        let pure = Expr::apps(
            Expr::const_(
                Name::from_string("Pure.pure"),
                vec![Level::zero(), Level::zero()],
            ),
            vec![
                Expr::const_(Name::from_string("Filter"), vec![Level::zero()]),
                Expr::type_(),
                Expr::prop(),
            ],
        );

        // Stuck: whnf returns the unchanged `Pure.pure …` application.
        assert_eq!(tc.whnf(&pure), pure);
    }
}
