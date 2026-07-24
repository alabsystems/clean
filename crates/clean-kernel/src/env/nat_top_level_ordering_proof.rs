// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Top-level `Nat.*` ordering primitives promoted from Axiom to Theorem (#3599).
//!
//! This module registers the core namespace `Nat.*` ordering lemmas as
//! sorry-free `Declaration::Theorem`s with empty domain-specific axiom
//! closures. These were previously `Declaration::Axiom` stubs at:
//!
//! - `order.rs:131`                 `Nat.le_refl`
//! - `order_lemmas_succ.rs:42-54`   `Nat.zero_lt_succ`
//! - `order_lemmas_succ.rs:137-157` `Nat.succ_lt_succ`
//! - `order_lemmas_succ.rs:183-203` `Nat.succ_le_succ`
//! - `order_lemmas.rs:465`          `Nat.le_of_lt`
//!
//! Each of those axiom sites is now guarded by `get_const` so that when
//! `init_nat_top_level_ordering` has already registered the Theorem form,
//! the legacy Axiom registration is skipped (idempotent no-op). The Theorem
//! form therefore wins whenever any init path calls into this module.
//!
//! # Proof strategy
//!
//! All five proofs are built directly from the `Nat.le` inductive
//! constructors / recursor (`Nat.le.refl`, `Nat.le.step`, `Nat.le.rec`) —
//! kernel primitives, not `Declaration::Axiom`s. No dependency on the
//! `math-overlays` feature or any `NNVerify.*` theorems.
//!
//! 1. **`Nat.le_refl : ∀ n : Nat, LE.le @Nat instLENat n n`** —
//!    Proof: `fun n => @Nat.le.refl n`. Since `instLENat` is a reducible
//!    `Definition` with value `LE.mk @Nat Nat.le`, the typeclass projection
//!    `LE.le @Nat instLENat` reduces to `Nat.le`, so `Nat.le.refl n : Nat.le n n`
//!    has the stated type up to definitional equality.
//!
//! 2. **`Nat.succ_le_succ : ∀ n m : Nat, Nat.le n m → Nat.le (Nat.succ n) (Nat.succ m)`**
//!    (raw `Nat.le` form, matching the legacy Axiom signature) —
//!    Induction on `h : Nat.le n m` via `Nat.le.rec` with motive
//!    `fun (t : Nat) (_ : Nat.le n t) => Nat.le (Nat.succ n) (Nat.succ t)`.
//!    Refl case: `Nat.le.refl (Nat.succ n)`. Step case: `Nat.le.step ih`.
//!
//! 3. **`Nat.succ_lt_succ : ∀ n m : Nat, Nat.lt n m → Nat.lt (Nat.succ n) (Nat.succ m)`**
//!    (raw `Nat.lt` form) — By the reducible definition
//!    `Nat.lt n m := Nat.le (Nat.succ n) m`, the hypothesis reduces to
//!    `Nat.le (Nat.succ n) m` and the conclusion to
//!    `Nat.le (Nat.succ (Nat.succ n)) (Nat.succ m)`. Induction on the
//!    hypothesis via `Nat.le.rec` at parameter `Nat.succ n` with motive
//!    `fun t _ => Nat.le (Nat.succ (Nat.succ n)) (Nat.succ t)`. Refl case:
//!    `Nat.le.refl (Nat.succ (Nat.succ n))`. Step case: `Nat.le.step ih`.
//!
//! 4. **`Nat.le_of_lt : ∀ a b : Nat, LT.lt @Nat instLTNat a b → LE.le @Nat instLENat a b`**
//!    (typeclass form) — Both sides reduce through the reducible
//!    `instLTNat` / `instLENat` wrappers and the reducible `Nat.lt`
//!    definition to `Nat.le (Nat.succ a) b → Nat.le a b`. Induction on the
//!    hypothesis via `Nat.le.rec` at parameter `Nat.succ a` with motive
//!    `fun t _ => Nat.le a t`. Refl case: `Nat.le.step (Nat.le.refl a)`
//!    proving `Nat.le a (Nat.succ a)`. Step case: `Nat.le.step ih`.
//!
//! 5. **`Nat.zero_lt_succ : ∀ n : Nat, LT.lt @Nat instLTNat Nat.zero (Nat.succ n)`**
//!    (typeclass form) — The conclusion reduces to
//!    `Nat.le (Nat.succ Nat.zero) (Nat.succ n)`. Induction on `n` via
//!    `Nat.rec.{0}` (Prop motive) with base
//!    `Nat.le.refl (Nat.succ Nat.zero) : Nat.le (Nat.succ Nat.zero) (Nat.succ Nat.zero)`
//!    and step `fun k ih => Nat.le.step ih`.
//!
//! None of the proof terms reference trust markers (`sorry`, `sorryAx`,
//! `trustedArith`, `trustedAy`) or any `Declaration::Axiom`, so
//! `env.axiom_deps(name)` is empty for each of the five and
//! `env.proof_quality(name) == ProofQuality::Constructive`.
//!
//! Tracking: #3599 (Part of #3551).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::order::{nat_le_tc, nat_lt_tc};
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register the top-level `Nat.*` ordering primitives as constructive
    /// `Declaration::Theorem`s (#3599).
    ///
    /// Registers (in order, each idempotent on `get_const`):
    ///
    /// - `Nat.le_refl`       (typeclass form)
    /// - `Nat.succ_le_succ`  (raw `Nat.le` form)
    /// - `Nat.succ_lt_succ`  (raw `Nat.lt` form)
    /// - `Nat.le_of_lt`      (typeclass form)
    /// - `Nat.zero_lt_succ`  (typeclass form)
    ///
    /// Must be called *before* any of the legacy axiom registration sites
    /// (`init_nat_preorder`, `init_nat_succ_lt`, `init_nat_succ_base`,
    /// `init_trans_nat_lt_lt_le`) so the Theorem form wins. Each legacy site
    /// has a `get_const` guard and will be a no-op once we have registered
    /// the Theorem here.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment.
    /// ENSURES: On success, `self.nat_top_level_ordering_init == true`.
    /// ENSURES: Idempotent.
    pub fn init_nat_top_level_ordering(&mut self) -> Result<(), EnvError> {
        if self.nat_top_level_ordering_init {
            return Ok(());
        }
        // Dependencies:
        // - init_nat()  : Nat, Nat.zero, Nat.succ, Nat.rec
        // - init_le()   : Nat.le, Nat.le.refl, Nat.le.step, Nat.le.rec, instLENat
        // - init_lt()   : Nat.lt (reducible Definition), instLTNat (reducible)
        self.init_nat()?;
        self.init_le()?;
        self.init_lt()?;

        self.register_nat_le_refl_theorem()?;
        self.register_nat_succ_le_succ_theorem()?;
        self.register_nat_succ_lt_succ_theorem()?;
        self.register_nat_le_of_lt_theorem()?;
        self.register_nat_zero_lt_succ_theorem()?;

        self.nat_top_level_ordering_init = true;
        Ok(())
    }

    /// Check if top-level Nat ordering promotions have been initialized.
    pub(crate) fn has_nat_top_level_ordering(&self) -> bool {
        self.nat_top_level_ordering_init
    }

    // -- Individual theorem registrations --------------------------------

    /// `Nat.le_refl : forall (n : Nat), LE.le @Nat instLENat n n`.
    ///
    /// Proof: `fun (n : Nat) => @Nat.le.refl n`.
    fn register_nat_le_refl_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.le_refl");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_le_refl_ctor = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat_const.clone());

        let ty = {
            let body = nat_le_tc(n.clone(), n.clone());
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(e)
        };

        let value = {
            let body = Expr::app(nat_le_refl_ctor, n.clone());
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Nat.succ_le_succ : forall (n m : Nat), Nat.le n m -> Nat.le (Nat.succ n) (Nat.succ m)`
    /// (raw form matching the legacy Axiom signature).
    ///
    /// Proof: induction on `h : Nat.le n m` via `Nat.le.rec` with motive
    /// `fun (t : Nat) (_ : Nat.le n t) => Nat.le (Nat.succ n) (Nat.succ t)`.
    fn register_nat_succ_le_succ_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.succ_le_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
        let nat_le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
        // `Nat.le.rec` has no motive universe parameter (Prop-only elim).
        let nat_le_rec = Expr::const_(Name::from_string("Nat.le.rec"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat_const.clone());
        let (m_id, m) = b.fresh_local(nat_const.clone());
        let h_type = Expr::apps(nat_le.clone(), [n.clone(), m.clone()]);
        let (h_id, h) = b.fresh_local(h_type.clone());

        // Type: forall (n m : Nat), Nat.le n m -> Nat.le (Nat.succ n) (Nat.succ m)
        let ty = {
            let succ_n = Expr::app(nat_succ.clone(), n.clone());
            let succ_m = Expr::app(nat_succ.clone(), m.clone());
            let concl = Expr::apps(nat_le.clone(), [succ_n, succ_m]);
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), concl);
            let e = b.mk_pi(m_id, BinderInfo::Implicit, nat_const.clone(), e);
            let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_const.clone(), e);
            b.finish(e)
        };

        // motive : Nat -> Nat.le n _ -> Prop
        // motive t _ = Nat.le (Nat.succ n) (Nat.succ t)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(nat_const.clone());
            let le_n_t = Expr::apps(nat_le.clone(), [n.clone(), t.clone()]);
            let (ht_id, _ht) = mb.fresh_local(le_n_t.clone());
            let succ_n = Expr::app(nat_succ.clone(), n.clone());
            let succ_t = Expr::app(nat_succ.clone(), t.clone());
            let body = Expr::apps(nat_le.clone(), [succ_n, succ_t]);
            let lam_h = mb.mk_lam(ht_id, BinderInfo::Default, le_n_t, body);
            let lam_t = mb.mk_lam(t_id, BinderInfo::Default, nat_const.clone(), lam_h);
            mb.finish_child(lam_t)
        };

        // Refl minor: Nat.le.refl (Nat.succ n)
        let minor_refl = Expr::app(nat_le_refl, Expr::app(nat_succ.clone(), n.clone()));

        // Step minor: fun {t} (_h : Nat.le n t) (ih : Nat.le (Nat.succ n) (Nat.succ t))
        //             => @Nat.le.step (Nat.succ n) (Nat.succ t) ih
        let minor_step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = sb.fresh_local(nat_const.clone());
            let le_n_t = Expr::apps(nat_le.clone(), [n.clone(), t.clone()]);
            let (ht_id, _ht) = sb.fresh_local(le_n_t.clone());
            let succ_n = Expr::app(nat_succ.clone(), n.clone());
            let succ_t = Expr::app(nat_succ.clone(), t.clone());
            let ih_type = Expr::apps(nat_le.clone(), [succ_n.clone(), succ_t.clone()]);
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let step_app = Expr::apps(nat_le_step.clone(), [succ_n, succ_t, ih]);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, step_app);
            let lam_h = sb.mk_lam(ht_id, BinderInfo::Default, le_n_t, lam_ih);
            let lam_t = sb.mk_lam(t_id, BinderInfo::Implicit, nat_const.clone(), lam_h);
            sb.finish_child(lam_t)
        };

        // @Nat.le.rec n motive minor_refl minor_step m h
        let rec_app = Expr::apps(
            nat_le_rec,
            [
                n.clone(),
                motive,
                minor_refl,
                minor_step,
                m.clone(),
                h.clone(),
            ],
        );

        let value = {
            let e = b.mk_lam(h_id, BinderInfo::Default, h_type, rec_app);
            let e = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Nat.succ_lt_succ : forall (n m : Nat), Nat.lt n m -> Nat.lt (Nat.succ n) (Nat.succ m)`
    /// (raw form).
    ///
    /// `Nat.lt` is a reducible Definition `fun n m => Nat.le (Nat.succ n) m`,
    /// so hypothesis and conclusion reduce to bare `Nat.le` forms at
    /// `Nat.succ n` and `Nat.succ (Nat.succ n)` respectively. The proof is
    /// induction on the (reduced) hypothesis via `Nat.le.rec` at parameter
    /// `Nat.succ n` with motive `fun t _ => Nat.le (Nat.succ (Nat.succ n)) (Nat.succ t)`.
    fn register_nat_succ_lt_succ_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.succ_lt_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);
        let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
        let nat_le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
        let nat_le_rec = Expr::const_(Name::from_string("Nat.le.rec"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat_const.clone());
        let (m_id, m) = b.fresh_local(nat_const.clone());
        let h_type = Expr::apps(nat_lt.clone(), [n.clone(), m.clone()]);
        let (h_id, h) = b.fresh_local(h_type.clone());

        // Type: forall (n m : Nat), Nat.lt n m -> Nat.lt (Nat.succ n) (Nat.succ m)
        let ty = {
            let succ_n = Expr::app(nat_succ.clone(), n.clone());
            let succ_m = Expr::app(nat_succ.clone(), m.clone());
            let concl = Expr::apps(nat_lt, [succ_n, succ_m]);
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), concl);
            let e = b.mk_pi(m_id, BinderInfo::Implicit, nat_const.clone(), e);
            let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_const.clone(), e);
            b.finish(e)
        };

        let succ_n = Expr::app(nat_succ.clone(), n.clone());
        let succ_succ_n = Expr::app(nat_succ.clone(), succ_n.clone());

        // motive: fun (t : Nat) (_ : Nat.le (Nat.succ n) t) => Nat.le (Nat.succ (Nat.succ n)) (Nat.succ t)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(nat_const.clone());
            let le_sn_t = Expr::apps(nat_le.clone(), [succ_n.clone(), t.clone()]);
            let (ht_id, _ht) = mb.fresh_local(le_sn_t.clone());
            let succ_t = Expr::app(nat_succ.clone(), t.clone());
            let body = Expr::apps(nat_le.clone(), [succ_succ_n.clone(), succ_t]);
            let lam_h = mb.mk_lam(ht_id, BinderInfo::Default, le_sn_t, body);
            let lam_t = mb.mk_lam(t_id, BinderInfo::Default, nat_const.clone(), lam_h);
            mb.finish_child(lam_t)
        };

        // Refl minor: Nat.le.refl (Nat.succ (Nat.succ n))
        //   : Nat.le (Nat.succ (Nat.succ n)) (Nat.succ (Nat.succ n))
        // Motive at t = Nat.succ n reduces to
        //   Nat.le (Nat.succ (Nat.succ n)) (Nat.succ (Nat.succ n))  ✓
        let minor_refl = Expr::app(nat_le_refl, succ_succ_n.clone());

        // Step minor: fun {t} (_h : Nat.le (Nat.succ n) t) (ih : Nat.le (Nat.succ (Nat.succ n)) (Nat.succ t))
        //             => @Nat.le.step (Nat.succ (Nat.succ n)) (Nat.succ t) ih
        let minor_step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = sb.fresh_local(nat_const.clone());
            let le_sn_t = Expr::apps(nat_le.clone(), [succ_n.clone(), t.clone()]);
            let (ht_id, _ht) = sb.fresh_local(le_sn_t.clone());
            let succ_t = Expr::app(nat_succ.clone(), t.clone());
            let ih_type = Expr::apps(nat_le.clone(), [succ_succ_n.clone(), succ_t.clone()]);
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let step_app = Expr::apps(nat_le_step.clone(), [succ_succ_n.clone(), succ_t, ih]);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, step_app);
            let lam_h = sb.mk_lam(ht_id, BinderInfo::Default, le_sn_t, lam_ih);
            let lam_t = sb.mk_lam(t_id, BinderInfo::Implicit, nat_const.clone(), lam_h);
            sb.finish_child(lam_t)
        };

        // @Nat.le.rec (Nat.succ n) motive minor_refl minor_step m h
        // `h : Nat.lt n m ≡ Nat.le (Nat.succ n) m` by reducibility of Nat.lt.
        let rec_app = Expr::apps(
            nat_le_rec,
            [succ_n, motive, minor_refl, minor_step, m.clone(), h.clone()],
        );

        let value = {
            let e = b.mk_lam(h_id, BinderInfo::Default, h_type, rec_app);
            let e = b.mk_lam(m_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Nat.le_of_lt : forall {a b : Nat}, LT.lt @Nat instLTNat a b -> LE.le @Nat instLENat a b`
    /// (typeclass form).
    ///
    /// `a` and `b` are IMPLICIT — matching real Lean's
    /// `Nat.le_of_lt {n m : Nat} : n < m → n ≤ m` (Init/Data/Nat/Basic.lean).
    /// The elaborator infers `a`/`b` from the explicit hypothesis `h : a < b`,
    /// so `Nat.le_of_lt h` elaborates with no positional type arguments. The
    /// VALUE lambdas stay `Default` — the kernel type-checks the value against
    /// the implicit-Pi type regardless of lambda binder annotation.
    ///
    /// Both sides reduce to `Nat.le (Nat.succ a) b -> Nat.le a b` through
    /// reducibility of `instLTNat`, `Nat.lt`, and `instLENat`. Induction on
    /// the (reduced) hypothesis via `Nat.le.rec` at parameter `Nat.succ a`
    /// with motive `fun t _ => Nat.le a t`.
    fn register_nat_le_of_lt_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.le_of_lt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
        let nat_le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
        let nat_le_rec = Expr::const_(Name::from_string("Nat.le.rec"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat_const.clone());
        let (bv_id, bv) = b.fresh_local(nat_const.clone());
        let h_type = nat_lt_tc(a.clone(), bv.clone());
        let (h_id, h) = b.fresh_local(h_type.clone());

        // Type: forall {a b : Nat}, LT.lt @Nat instLTNat a b -> LE.le @Nat instLENat a b
        // `a`/`b` are IMPLICIT (inferred from `h`), matching real Lean.
        let ty = {
            let concl = nat_le_tc(a.clone(), bv.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), concl);
            let e = b.mk_pi(bv_id, BinderInfo::Implicit, nat_const.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Implicit, nat_const.clone(), e);
            b.finish(e)
        };

        let succ_a = Expr::app(nat_succ.clone(), a.clone());

        // motive: fun (t : Nat) (_ : Nat.le (Nat.succ a) t) => Nat.le a t
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(nat_const.clone());
            let le_sa_t = Expr::apps(nat_le.clone(), [succ_a.clone(), t.clone()]);
            let (ht_id, _ht) = mb.fresh_local(le_sa_t.clone());
            let body = Expr::apps(nat_le.clone(), [a.clone(), t.clone()]);
            let lam_h = mb.mk_lam(ht_id, BinderInfo::Default, le_sa_t, body);
            let lam_t = mb.mk_lam(t_id, BinderInfo::Default, nat_const.clone(), lam_h);
            mb.finish_child(lam_t)
        };

        // Refl minor: motive at t = Nat.succ a is `Nat.le a (Nat.succ a)`,
        // which is `@Nat.le.step a a (@Nat.le.refl a)`.
        let minor_refl = {
            let refl_a = Expr::app(nat_le_refl, a.clone());
            Expr::apps(nat_le_step.clone(), [a.clone(), a.clone(), refl_a])
        };

        // Step minor: fun {t} (_h : Nat.le (Nat.succ a) t) (ih : Nat.le a t)
        //             => @Nat.le.step a t ih
        let minor_step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = sb.fresh_local(nat_const.clone());
            let le_sa_t = Expr::apps(nat_le.clone(), [succ_a.clone(), t.clone()]);
            let (ht_id, _ht) = sb.fresh_local(le_sa_t.clone());
            let ih_type = Expr::apps(nat_le.clone(), [a.clone(), t.clone()]);
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let step_app = Expr::apps(nat_le_step.clone(), [a.clone(), t.clone(), ih]);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, step_app);
            let lam_h = sb.mk_lam(ht_id, BinderInfo::Default, le_sa_t, lam_ih);
            let lam_t = sb.mk_lam(t_id, BinderInfo::Implicit, nat_const.clone(), lam_h);
            sb.finish_child(lam_t)
        };

        // @Nat.le.rec (Nat.succ a) motive minor_refl minor_step b h
        // `h : LT.lt @Nat instLTNat a b ≡ Nat.le (Nat.succ a) b` by
        // reducibility of instLTNat and Nat.lt.
        let rec_app = Expr::apps(
            nat_le_rec,
            [
                succ_a,
                motive,
                minor_refl,
                minor_step,
                bv.clone(),
                h.clone(),
            ],
        );

        let value = {
            let e = b.mk_lam(h_id, BinderInfo::Default, h_type, rec_app);
            let e = b.mk_lam(bv_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Nat.zero_lt_succ : forall (n : Nat), LT.lt @Nat instLTNat Nat.zero (Nat.succ n)`
    /// (typeclass form).
    ///
    /// Reduces (by reducibility of `instLTNat` and `Nat.lt`) to
    /// `Nat.le (Nat.succ Nat.zero) (Nat.succ n)`. Proved by induction on `n`
    /// via `Nat.rec.{0}`:
    /// - base (`n = Nat.zero`): `Nat.le.refl (Nat.succ Nat.zero)` — the
    ///   motive at zero is `Nat.le (Nat.succ Nat.zero) (Nat.succ Nat.zero)`.
    /// - step (`n = Nat.succ k` given `ih : Nat.le (Nat.succ Nat.zero) (Nat.succ k)`):
    ///   `Nat.le.step ih : Nat.le (Nat.succ Nat.zero) (Nat.succ (Nat.succ k))`.
    fn register_nat_zero_lt_succ_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Nat.zero_lt_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
        let nat_le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
        // `Nat.rec.{0}` — Prop motive.
        let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat_const.clone());

        // Type: forall (n : Nat), LT.lt @Nat instLTNat Nat.zero (Nat.succ n)
        let ty = {
            let succ_n = Expr::app(nat_succ.clone(), n.clone());
            let body = nat_lt_tc(nat_zero.clone(), succ_n);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(e)
        };

        let succ_zero = Expr::app(nat_succ.clone(), nat_zero.clone());

        // Motive: fun (t : Nat) => Nat.le (Nat.succ Nat.zero) (Nat.succ t)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(nat_const.clone());
            let succ_t = Expr::app(nat_succ.clone(), t.clone());
            let body = Expr::apps(nat_le.clone(), [succ_zero.clone(), succ_t]);
            let lam = mb.mk_lam(t_id, BinderInfo::Default, nat_const.clone(), body);
            mb.finish_child(lam)
        };

        // Base (motive at Nat.zero): Nat.le (Nat.succ Nat.zero) (Nat.succ Nat.zero).
        //   Witness: Nat.le.refl (Nat.succ Nat.zero).
        let base = Expr::app(nat_le_refl, succ_zero.clone());

        // Step: fun (k : Nat) (ih : motive k = Nat.le (Nat.succ Nat.zero) (Nat.succ k))
        //       => @Nat.le.step (Nat.succ Nat.zero) (Nat.succ k) ih
        //       : Nat.le (Nat.succ Nat.zero) (Nat.succ (Nat.succ k)) = motive (Nat.succ k)
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(nat_const.clone());
            let succ_k = Expr::app(nat_succ.clone(), k.clone());
            let ih_type = Expr::apps(nat_le.clone(), [succ_zero.clone(), succ_k.clone()]);
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let step_app = Expr::apps(nat_le_step.clone(), [succ_zero.clone(), succ_k, ih]);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, step_app);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, nat_const.clone(), lam_ih);
            sb.finish_child(lam_k)
        };

        // @Nat.rec.{0} motive base step n
        // Result type: Nat.le (Nat.succ Nat.zero) (Nat.succ n), which is
        // definitionally equal to `LT.lt @Nat instLTNat Nat.zero (Nat.succ n)`.
        let rec_app = Expr::apps(nat_rec, [motive, base, step, n.clone()]);

        let value = {
            let e = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), rec_app);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
