// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tier A Batch 3 (#3599, Part of #3551): Nat ordering primitives.
//!
//! Registers four sorry-free `Declaration::Theorem`s over `Nat.le` whose
//! transitive non-foundational axiom closure is empty:
//!
//! - `NNVerify.Nat.succ_le_succ : forall (n m : Nat), Nat.le n m -> Nat.le (Nat.succ n) (Nat.succ m)`
//! - `NNVerify.Nat.zero_le     : forall (n : Nat), Nat.le Nat.zero n`
//! - `NNVerify.Nat.le_of_lt    : forall (n m : Nat), Nat.le (Nat.succ n) m -> Nat.le n m`
//! - `NNVerify.Nat.lt_of_succ_le : forall (n m : Nat), Nat.le (Nat.succ n) m -> Nat.lt n m`
//!
//! All four proof terms are built from the constructor / recursor machinery
//! of the `Nat.le` inductive (`Nat.le.refl`, `Nat.le.step`, `Nat.le.rec`)
//! and the `Nat.rec` recursor, all of which are kernel primitives — not
//! `Declaration::Axiom`. Therefore `env.axiom_deps(name)` is empty for each
//! and `env.proof_quality(name) == ProofQuality::Constructive`.
//!
//! # Proof sketches (see also #3599 design section)
//!
//! 1. `NNVerify.Nat.succ_le_succ` — induct on `h : Nat.le n m` via `Nat.le.rec`:
//!    - motive: `fun (t : Nat) (_ : Nat.le n t) => Nat.le (Nat.succ n) (Nat.succ t)`
//!    - refl case: `Nat.le.refl (Nat.succ n)`
//!    - step case: given `ih : Nat.le (Nat.succ n) (Nat.succ t)`, return `Nat.le.step ih`
//!
//! 2. `NNVerify.Nat.zero_le` — induct on `n` via `Nat.rec.{0}` (Prop motive):
//!    - motive: `fun (t : Nat) => Nat.le Nat.zero t`
//!    - base: `Nat.le.refl Nat.zero`
//!    - step: given `ih : Nat.le Nat.zero k`, return `Nat.le.step ih`
//!
//! 3. `NNVerify.Nat.le_of_lt` — induct on `h : Nat.le (Nat.succ n) m` via `Nat.le.rec`:
//!    - motive: `fun (t : Nat) (_ : Nat.le (Nat.succ n) t) => Nat.le n t`
//!    - refl case (t = Nat.succ n): `Nat.le.step (Nat.le.refl n)`
//!    - step case: given `ih : Nat.le n t`, return `Nat.le.step ih`
//!      The stated type uses the raw `Nat.le (Nat.succ n) m` (which is what `Nat.lt`
//!      reduces to), so the caller does not need `LT.lt` typeclass unfolding.
//!
//! 4. `NNVerify.Nat.lt_of_succ_le` — `Nat.lt n m` unfolds to `Nat.le (Nat.succ n) m`
//!    by reducible definition, so given `h : Nat.le (Nat.succ n) m` we just return `h`.
//!    The proof body is the identity lambda after definitional unfolding.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

// ---- Helper builders (kept small to respect per-function LOC limit) ----

/// Motive for `succ_le_succ`:
/// `fun (t : Nat) (_ : Nat.le n t) => Nat.le (Nat.succ n) (Nat.succ t)`.
fn build_succ_le_succ_motive(
    parent: &EnvDeclBuilder,
    nat_const: &Expr,
    nat_succ: &Expr,
    nat_le_raw: &Expr,
    n: &Expr,
) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = mb.fresh_local(nat_const.clone());
    let le_n_t = Expr::apps(nat_le_raw.clone(), [n.clone(), t.clone()]);
    let (ht_id, _ht) = mb.fresh_local(le_n_t.clone());
    let succ_n = Expr::app(nat_succ.clone(), n.clone());
    let succ_t = Expr::app(nat_succ.clone(), t.clone());
    let body = Expr::apps(nat_le_raw.clone(), [succ_n, succ_t]);
    let lam_h = mb.mk_lam(ht_id, BinderInfo::Default, le_n_t, body);
    let lam_t = mb.mk_lam(t_id, BinderInfo::Default, nat_const.clone(), lam_h);
    mb.finish_child(lam_t)
}

/// Step case for `succ_le_succ`:
/// `fun {t} (_h : Nat.le n t) (ih : Nat.le (Nat.succ n) (Nat.succ t))
///     => @Nat.le.step (Nat.succ n) (Nat.succ t) ih`.
fn build_succ_le_succ_step(
    parent: &EnvDeclBuilder,
    nat_const: &Expr,
    nat_succ: &Expr,
    nat_le_raw: &Expr,
    nat_le_step: &Expr,
    n: &Expr,
) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = sb.fresh_local(nat_const.clone());
    let le_n_t = Expr::apps(nat_le_raw.clone(), [n.clone(), t.clone()]);
    let (ht_id, _ht) = sb.fresh_local(le_n_t.clone());
    let succ_n = Expr::app(nat_succ.clone(), n.clone());
    let succ_t = Expr::app(nat_succ.clone(), t.clone());
    let ih_type = Expr::apps(nat_le_raw.clone(), [succ_n.clone(), succ_t.clone()]);
    let (ih_id, ih) = sb.fresh_local(ih_type.clone());
    let step_app = Expr::apps(nat_le_step.clone(), [succ_n, succ_t, ih]);
    let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, step_app);
    let lam_h = sb.mk_lam(ht_id, BinderInfo::Default, le_n_t, lam_ih);
    let lam_t = sb.mk_lam(t_id, BinderInfo::Implicit, nat_const.clone(), lam_h);
    sb.finish_child(lam_t)
}

/// Motive for `le_of_lt`:
/// `fun (t : Nat) (_ : Nat.le (Nat.succ n) t) => Nat.le n t`.
fn build_le_of_lt_motive(
    parent: &EnvDeclBuilder,
    nat_const: &Expr,
    nat_le_raw: &Expr,
    n: &Expr,
    succ_n: &Expr,
) -> Expr {
    let mut mb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = mb.fresh_local(nat_const.clone());
    let le_sn_t = Expr::apps(nat_le_raw.clone(), [succ_n.clone(), t.clone()]);
    let (ht_id, _ht) = mb.fresh_local(le_sn_t.clone());
    let body = Expr::apps(nat_le_raw.clone(), [n.clone(), t.clone()]);
    let lam_h = mb.mk_lam(ht_id, BinderInfo::Default, le_sn_t, body);
    let lam_t = mb.mk_lam(t_id, BinderInfo::Default, nat_const.clone(), lam_h);
    mb.finish_child(lam_t)
}

/// Step case for `le_of_lt`:
/// `fun {t} (_h : Nat.le (Nat.succ n) t) (ih : Nat.le n t) => @Nat.le.step n t ih`.
fn build_le_of_lt_step(
    parent: &EnvDeclBuilder,
    nat_const: &Expr,
    nat_le_raw: &Expr,
    nat_le_step: &Expr,
    n: &Expr,
    succ_n: &Expr,
) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let (t_id, t) = sb.fresh_local(nat_const.clone());
    let le_sn_t = Expr::apps(nat_le_raw.clone(), [succ_n.clone(), t.clone()]);
    let (ht_id, _ht) = sb.fresh_local(le_sn_t.clone());
    let ih_type = Expr::apps(nat_le_raw.clone(), [n.clone(), t.clone()]);
    let (ih_id, ih) = sb.fresh_local(ih_type.clone());
    let step_app = Expr::apps(nat_le_step.clone(), [n.clone(), t.clone(), ih]);
    let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, step_app);
    let lam_h = sb.mk_lam(ht_id, BinderInfo::Default, le_sn_t, lam_ih);
    let lam_t = sb.mk_lam(t_id, BinderInfo::Implicit, nat_const.clone(), lam_h);
    sb.finish_child(lam_t)
}

impl Environment {
    /// Initialize the Tier A Batch 3 Nat ordering primitives (#3599).
    ///
    /// Registers `NNVerify.Nat.succ_le_succ`, `NNVerify.Nat.zero_le`,
    /// `NNVerify.Nat.le_of_lt`, and `NNVerify.Nat.lt_of_succ_le` as
    /// sorry-free `Declaration::Theorem`s with `ProofQuality::Constructive`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, `self.nn_verify_tier_a_nat_ordering_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_tier_a_nat_ordering(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_tier_a_nat_ordering_init {
            return Ok(());
        }
        // `init_le` provides `Nat.le`, `Nat.le.refl`, `Nat.le.step`, and (via
        // kernel auto-generation) `Nat.le.rec`. `init_lt` provides `Nat.lt`
        // as a reducible Definition. `init_nat` provides `Nat`, `Nat.zero`,
        // `Nat.succ`, and `Nat.rec`.
        self.init_nat()?;
        self.init_le()?;
        self.init_lt()?;

        self.register_tier_a_nat_succ_le_succ()?;
        self.register_tier_a_nat_zero_le()?;
        self.register_tier_a_nat_le_of_lt()?;
        self.register_tier_a_nat_lt_of_succ_le()?;

        self.nn_verify_tier_a_nat_ordering_init = true;
        Ok(())
    }

    /// Check if Tier A Batch 3 Nat ordering primitives have been initialized.
    #[cfg(test)]
    pub(crate) fn has_nn_verify_tier_a_nat_ordering(&self) -> bool {
        self.nn_verify_tier_a_nat_ordering_init
    }

    /// `NNVerify.Nat.succ_le_succ : forall (n m : Nat), Nat.le n m -> Nat.le (Nat.succ n) (Nat.succ m)`.
    ///
    /// Proof: recursion on `h : Nat.le n m` via `Nat.le.rec` with
    /// motive `fun t _ => Nat.le (Nat.succ n) (Nat.succ t)`.
    ///
    /// Axiom closure: empty — only `Nat`, `Nat.succ`, `Nat.le`, `Nat.le.refl`,
    /// `Nat.le.step`, `Nat.le.rec`.
    fn register_tier_a_nat_succ_le_succ(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Nat.succ_le_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_le_raw = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
        let nat_le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
        // Nat.le is Prop-valued with only-to-Prop elimination, so Nat.le.rec
        // has NO motive universe parameter (see inductive_recursor.rs:89-90).
        let nat_le_rec = Expr::const_(Name::from_string("Nat.le.rec"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat_const.clone());
        let (m_id, m) = b.fresh_local(nat_const.clone());
        let h_type = Expr::apps(nat_le_raw.clone(), [n.clone(), m.clone()]);
        let (h_id, h) = b.fresh_local(h_type.clone());

        // Type: forall (n m : Nat), Nat.le n m -> Nat.le (Nat.succ n) (Nat.succ m)
        let ty = {
            let succ_n = Expr::app(nat_succ.clone(), n.clone());
            let succ_m = Expr::app(nat_succ.clone(), m.clone());
            let concl = Expr::apps(nat_le_raw.clone(), [succ_n, succ_m]);
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), concl);
            let e = b.mk_pi(m_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        let motive = build_succ_le_succ_motive(&b, &nat_const, &nat_succ, &nat_le_raw, &n);
        let minor_refl = Expr::app(nat_le_refl, Expr::app(nat_succ.clone(), n.clone()));
        let minor_step =
            build_succ_le_succ_step(&b, &nat_const, &nat_succ, &nat_le_raw, &nat_le_step, &n);

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

    /// `NNVerify.Nat.zero_le : forall (n : Nat), Nat.le Nat.zero n`.
    ///
    /// Proof: recursion on `n` via `Nat.rec.{0}` (Prop motive) with
    /// motive `fun t => Nat.le Nat.zero t`.
    ///
    /// Axiom closure: empty — only `Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec`,
    /// `Nat.le`, `Nat.le.refl`, `Nat.le.step`.
    fn register_tier_a_nat_zero_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Nat.zero_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_le_raw = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
        let nat_le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
        // `Nat.rec.{0}` — motive is Prop-valued (`Nat.le Nat.zero t : Prop`).
        let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat_const.clone());

        // Type: forall (n : Nat), Nat.le Nat.zero n
        let ty = {
            let body = Expr::apps(nat_le_raw.clone(), [nat_zero.clone(), n.clone()]);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), body);
            b.finish(e)
        };

        // Motive: fun (t : Nat) => Nat.le Nat.zero t
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(nat_const.clone());
            let body = Expr::apps(nat_le_raw.clone(), [nat_zero.clone(), t.clone()]);
            let lam = mb.mk_lam(t_id, BinderInfo::Default, nat_const.clone(), body);
            mb.finish_child(lam)
        };

        // Base: Nat.le.refl Nat.zero : Nat.le Nat.zero Nat.zero
        let base = Expr::app(nat_le_refl.clone(), nat_zero.clone());

        // Step: fun (k : Nat) (ih : Nat.le Nat.zero k) => @Nat.le.step Nat.zero k ih
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = sb.fresh_local(nat_const.clone());
            let ih_type = Expr::apps(nat_le_raw.clone(), [nat_zero.clone(), k.clone()]);
            let (ih_id, ih) = sb.fresh_local(ih_type.clone());
            let step_app = Expr::apps(nat_le_step.clone(), [nat_zero.clone(), k.clone(), ih]);
            let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_type, step_app);
            let lam_k = sb.mk_lam(k_id, BinderInfo::Default, nat_const.clone(), lam_ih);
            sb.finish_child(lam_k)
        };

        // @Nat.rec motive base step n
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

    /// `NNVerify.Nat.le_of_lt : forall (n m : Nat), Nat.le (Nat.succ n) m -> Nat.le n m`.
    ///
    /// The stated type uses the raw `Nat.le (Nat.succ n) m` (which is what
    /// `Nat.lt n m` reduces to as a reducible Definition), so callers that
    /// have `Nat.lt n m` can pass it directly.
    ///
    /// Proof: recursion on `h : Nat.le (Nat.succ n) m` via `Nat.le.rec` with
    /// parameter `Nat.succ n` and motive `fun t _ => Nat.le n t`.
    ///
    /// Axiom closure: empty — only Nat / Nat.le / Nat.le.{refl,step,rec}.
    fn register_tier_a_nat_le_of_lt(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Nat.le_of_lt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_le_raw = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
        let nat_le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
        // Nat.le.rec has NO motive universe parameter (Prop-only elim).
        let nat_le_rec = Expr::const_(Name::from_string("Nat.le.rec"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat_const.clone());
        let (m_id, m) = b.fresh_local(nat_const.clone());
        let succ_n = Expr::app(nat_succ.clone(), n.clone());
        let h_type = Expr::apps(nat_le_raw.clone(), [succ_n.clone(), m.clone()]);
        let (h_id, h) = b.fresh_local(h_type.clone());

        // Type: forall (n m : Nat), Nat.le (Nat.succ n) m -> Nat.le n m
        let ty = {
            let concl = Expr::apps(nat_le_raw.clone(), [n.clone(), m.clone()]);
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), concl);
            let e = b.mk_pi(m_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        let motive = build_le_of_lt_motive(&b, &nat_const, &nat_le_raw, &n, &succ_n);
        // Minor refl: motive applied at `t = Nat.succ n` needs `Nat.le n (Nat.succ n)`,
        // i.e. `@Nat.le.step n n (@Nat.le.refl n)`.
        let minor_refl = {
            let refl_n = Expr::app(nat_le_refl, n.clone());
            Expr::apps(nat_le_step.clone(), [n.clone(), n.clone(), refl_n])
        };
        let minor_step =
            build_le_of_lt_step(&b, &nat_const, &nat_le_raw, &nat_le_step, &n, &succ_n);

        // @Nat.le.rec (Nat.succ n) motive minor_refl minor_step m h
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

    /// `NNVerify.Nat.lt_of_succ_le : forall (n m : Nat), Nat.le (Nat.succ n) m -> Nat.lt n m`.
    ///
    /// `Nat.lt` is registered as a reducible `Declaration::Definition`:
    /// `Nat.lt n m := Nat.le (Nat.succ n) m`. The conclusion therefore reduces
    /// definitionally to the hypothesis. The proof body is the identity
    /// lambda `fun n m h => h`.
    ///
    /// Axiom closure: empty — only `Nat`, `Nat.succ`, `Nat.le`, `Nat.lt`.
    fn register_tier_a_nat_lt_of_succ_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Nat.lt_of_succ_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_le_raw = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_lt = Expr::const_(Name::from_string("Nat.lt"), vec![]);

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat_const.clone());
        let (m_id, m) = b.fresh_local(nat_const.clone());
        let succ_n = Expr::app(nat_succ.clone(), n.clone());
        let h_type = Expr::apps(nat_le_raw.clone(), [succ_n, m.clone()]);
        let (h_id, h) = b.fresh_local(h_type.clone());

        // Type: forall (n m : Nat), Nat.le (Nat.succ n) m -> Nat.lt n m
        let ty = {
            let concl = Expr::apps(nat_lt.clone(), [n.clone(), m.clone()]);
            let e = b.mk_pi(h_id, BinderInfo::Default, h_type.clone(), concl);
            let e = b.mk_pi(m_id, BinderInfo::Default, nat_const.clone(), e);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), e);
            b.finish(e)
        };

        // Value: fun (n m : Nat) (h : Nat.le (Nat.succ n) m) => h
        // The conclusion `Nat.lt n m` reduces to `Nat.le (Nat.succ n) m` by
        // the reducible definition of `Nat.lt`, so `h` has exactly the
        // expected type.
        let value = {
            let e = b.mk_lam(h_id, BinderInfo::Default, h_type, h);
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
}
