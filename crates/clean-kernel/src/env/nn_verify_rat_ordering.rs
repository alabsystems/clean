// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C008 blocker (#3503): Rat field→order bridging lemmas.
//!
//! Provides four kernel theorems that bridge Rat field operations (add,
//! mul, neg, sub) to the Rat ordering (Rat.le). These are the missing
//! inputs for the constructive `mul_nonneg_le_left` proof (#3490 T3) and
//! the `ibp_width_zero` / `ibp_tightness_base` proofs (#3490 T4, #3476).
//!
//! ## Theorems (all `Declaration::Theorem`, sorry-free)
//!
//! - `Rat.sub_self` : `∀ a, Rat.sub a a = Rat.zero`
//! - `Rat.mul_sub`  : `∀ a b c, Rat.mul a (Rat.sub b c)
//!                             = Rat.sub (Rat.mul a b) (Rat.mul a c)`
//! - `Rat.sub_nonneg_of_le` : `∀ a b, Rat.le a b → Rat.le Rat.zero (Rat.sub b a)`
//! - `Rat.le_of_sub_nonneg` : `∀ a b, Rat.le Rat.zero (Rat.sub b a) → Rat.le a b`
//!
//! ## Supporting honest axioms (registered here)
//!
//! - `Rat.add_neg_self` : `∀ a, Rat.add a (Rat.neg a) = Rat.zero`
//! - `Rat.mul_neg`      : `∀ a b, Rat.mul a (Rat.neg b) = Rat.neg (Rat.mul a b)`
//!
//! Standard ordered-field algebra (derivable from `add_left_neg`/`add_comm`
//! and `left_distrib`/`add_neg_self`). Registered here as honest
//! `Declaration::Axiom` to keep the dependent theorems short; they are
//! *not* sorry-Opaque.
//!
//! ## Strategy
//!
//! Each theorem is a `Declaration::Theorem` whose value is built from
//! foundational `Eq.subst`/`Eq.symm`/`Eq.trans` plus existing Rat field
//! and order axioms (`Rat.add_le_add_left`, `Rat.add_left_neg`,
//! `Rat.add_comm`, `Rat.add_assoc`, `Rat.add_zero`, `Rat.zero_add`,
//! `Rat.left_distrib`). Because `Rat.sub` is a reducible Definition
//! (`Rat.sub a b := Rat.add a (Rat.neg b)`), the kernel accepts
//! definitional equality between the `Rat.sub`-shaped type annotation and
//! the `Rat.add (Rat.neg ..)`-shaped proof-term body via delta+iota.
//!
//! The two non-trivial proof-term builders (`Rat.mul_sub`,
//! `Rat.le_of_sub_nonneg`) live in `nn_verify_rat_ordering_proofs.rs`
//! to keep this module under the 500-line limit.
//!
//! ## Part of
//!
//! - #3503 (this issue)
//! - Blocks #3476 (C008 ibp_tightness base+step)
//! - Blocks #3490 T3/T4

use super::decl_builder::EnvDeclBuilder;
use super::nn_verify_rat_ordering_proofs::{build_le_of_sub_nonneg_proof, build_mul_sub_proof};
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for Rat ordering proof construction.
///
/// `pub(super)` so that the split proof-term builders in
/// `nn_verify_rat_ordering_proofs` can construct terms without
/// duplicating the plumbing.
pub(super) struct RatOrdConsts {
    pub(super) rat: Expr,
    pub(super) rat_zero: Expr,
    pub(super) rat_add: Expr,
    pub(super) rat_mul: Expr,
    pub(super) rat_neg: Expr,
    pub(super) rat_sub: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_rat: Expr,
    pub(super) eq: Expr,
    pub(super) eq_refl: Expr,
    pub(super) eq_symm: Expr,
    pub(super) eq_subst: Expr,
    pub(super) eq_trans: Expr,
}

impl RatOrdConsts {
    fn new() -> Self {
        let u1 = Level::succ(Level::zero());
        Self {
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_neg: Expr::const_(Name::from_string("Rat.neg"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![u1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![u1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![u1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![u1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![u1]),
        }
    }

    pub(super) fn rat_eq(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq.clone(), [self.rat.clone(), a, b])
    }

    pub(super) fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }

    pub(super) fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }

    pub(super) fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }

    pub(super) fn neg(&self, a: Expr) -> Expr {
        Expr::app(self.rat_neg.clone(), a)
    }

    pub(super) fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }

    /// `Eq.symm.{1} @Rat @a @b h`.
    pub(super) fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }

    /// `Eq.trans.{1} @Rat @a @b @c h1 h2`.
    pub(super) fn trans(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, c, h1, h2])
    }

    /// `Eq.subst.{1} @Rat motive @a @b h_eq h_motive_a` : produces
    /// `motive b` given `h_eq : Eq a b` and `h_motive_a : motive a`.
    pub(super) fn subst(
        &self,
        motive: Expr,
        a: Expr,
        b: Expr,
        h_eq: Expr,
        h_motive_a: Expr,
    ) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h_motive_a],
        )
    }

    /// `Eq.refl.{1} @Rat a`.
    pub(super) fn refl(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.rat.clone(), a])
    }
}

impl Environment {
    /// Initialize the Rat field→order bridging lemmas (#3503).
    ///
    /// Registers two honest helper axioms (`Rat.add_neg_self`, `Rat.mul_neg`)
    /// and four `Declaration::Theorem` bridging lemmas.
    ///
    /// Depends on: `init_rat_arith`, `init_rat_ord`,
    /// `init_rat_field_inst`, `init_rat_ordered_field_axioms`, `init_eq`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, `self.nn_verify_rat_ordering_init == true`
    /// ENSURES: Idempotent
    pub fn init_nn_verify_rat_ordering(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_rat_ordering_init {
            return Ok(());
        }
        self.init_rat_arith()?;
        self.init_rat_ord()?;
        self.init_rat_field_inst()?;
        self.init_rat_ordered_field_axioms()?;
        self.init_eq()?;

        let c = RatOrdConsts::new();
        self.register_rat_add_neg_self(&c)?;
        self.register_rat_mul_neg(&c)?;

        self.register_rat_sub_self(&c)?;
        self.register_rat_mul_sub(&c)?;
        self.register_rat_sub_nonneg_of_le(&c)?;
        self.register_rat_le_of_sub_nonneg(&c)?;

        self.nn_verify_rat_ordering_init = true;
        Ok(())
    }

    /// `∀ a : Rat, Rat.add a (Rat.neg a) = Rat.zero`.
    ///
    /// WS-A ATOMIC LIVE SWITCH (step 3, payoff): over the QUOTIENT carrier this
    /// is a GENUINE kernel-checked `Declaration::Theorem` (it was an honest
    /// domain axiom over the free carrier). Registered with the SAME name + type
    /// by the quotient payoff helper.
    fn register_rat_add_neg_self(&mut self, _c: &RatOrdConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.add_neg_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.rat_quotient_payoff_into_live()
    }

    /// `Rat.mul_neg : ∀ a b : Rat, Rat.mul a (Rat.neg b) = Rat.neg (Rat.mul a b)`.
    ///
    /// #3470 Lane #2/#3: GENUINELY ELIMINATED from `Declaration::Axiom` to a
    /// kernel-checked `Declaration::Theorem`. Both `Rat.mul` and `Rat.neg` are
    /// reducible Definitions over `Rat.mk`/`Rat.num`/`Rat.denom`:
    ///
    /// ```text
    /// Rat.mul x y := Rat.mk (Int.mul (num x) (num y)) (Nat.mul (denom x) (denom y))
    /// Rat.neg x   := Rat.mk (Int.neg (num x)) (denom x)
    /// ```
    ///
    /// so, writing `D := Nat.mul (Rat.denom a) (Rat.denom b)`:
    ///
    /// ```text
    /// Rat.mul a (Rat.neg b) ≡ Rat.mk (Int.mul (num a) (Int.neg (num b))) D
    /// Rat.neg (Rat.mul a b) ≡ Rat.mk (Int.neg (Int.mul (num a) (num b)))  D
    /// ```
    ///
    /// (`Rat.num (Rat.neg b) ≡ Int.neg (num b)`, `Rat.denom (Rat.neg b) ≡ denom b`
    /// by iota on the reducible `Rat.neg`.) The two `Rat.mk` arguments are equal
    /// by the constructive `Int.neg_mul_right`:
    ///
    /// ```text
    /// Int.neg_mul_right (num a) (num b)
    ///   : Int.neg (Int.mul (num a) (num b)) = Int.mul (num a) (Int.neg (num b))
    /// ```
    ///
    /// so `Eq.symm` of it gives `a₁ = a₂` and lifting through `congrArg
    /// (fun x => Rat.mk x D)` produces the goal. Honest classification:
    /// `Constructive` (`Int.neg_mul_right` is itself a constructive Theorem).
    fn register_rat_mul_neg(&mut self, _c: &RatOrdConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_neg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // WS-A ATOMIC LIVE SWITCH: over the quotient carrier the free-carrier
        // `Rat.mk`/`Rat.num`/`Rat.denom` proof no longer type-checks (`Rat.num`
        // is gone). The quotient `Quot.ind` + `Quot.sound` proof (same public
        // name + type) is built by the construction-module helper.
        let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
        self.register_rat_q_mul_neg(&qc)
    }

    /// `Rat.sub_self : ∀ a : Rat, Rat.sub a a = Rat.zero`.
    ///
    /// Proof (sorry-free): `Rat.sub` reduces (delta) to `Rat.add a (Rat.neg a)`,
    /// which equals `Rat.zero` by `Rat.add_neg_self`.
    fn register_rat_sub_self(&mut self, c: &RatOrdConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.sub_self");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let body = c.rat_eq(c.sub(a.clone(), a), c.rat_zero.clone());
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), body);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let add_neg_self = Expr::const_(Name::from_string("Rat.add_neg_self"), vec![]);
            let body = Expr::app(add_neg_self, a);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.mul_sub : ∀ a b c,
    ///    Rat.mul a (Rat.sub b c) = Rat.sub (Rat.mul a b) (Rat.mul a c)`.
    /// Proof-term built in `nn_verify_rat_ordering_proofs`.
    fn register_rat_mul_sub(&mut self, c: &RatOrdConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_sub");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let (cv_id, cv) = b.fresh_local(c.rat.clone());
            let lhs = c.mul(a.clone(), c.sub(bv.clone(), cv.clone()));
            let rhs = c.sub(c.mul(a.clone(), bv), c.mul(a, cv));
            let body = c.rat_eq(lhs, rhs);
            let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat.clone(), body);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_mul_sub_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.sub_nonneg_of_le :
    ///    ∀ a b, Rat.le a b → Rat.le Rat.zero (Rat.sub b a)`.
    ///
    /// Proof sketch (see `build_sub_nonneg_of_le_proof` for details):
    /// `Rat.add_le_add_left a b h (-a)` + Eq.subst rewrites via
    /// `Rat.add_left_neg` and `Rat.add_comm` give `Rat.le 0 (b + (-a))`,
    /// which is definitionally `Rat.le 0 (Rat.sub b a)`.
    fn register_rat_sub_nonneg_of_le(&mut self, c: &RatOrdConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.sub_nonneg_of_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let h_ty = c.rat_le(a.clone(), bv.clone());
            let concl = c.rat_le(c.rat_zero.clone(), c.sub(bv, a));
            let (h_id, _) = b.fresh_local(h_ty.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_sub_nonneg_of_le_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.le_of_sub_nonneg :
    ///    ∀ a b, Rat.le Rat.zero (Rat.sub b a) → Rat.le a b`.
    /// Proof-term built in `nn_verify_rat_ordering_proofs`.
    fn register_rat_le_of_sub_nonneg(&mut self, c: &RatOrdConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.le_of_sub_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let h_ty = c.rat_le(c.rat_zero.clone(), c.sub(bv.clone(), a.clone()));
            let concl = c.rat_le(a.clone(), bv);
            let (h_id, _) = b.fresh_local(h_ty.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_le_of_sub_nonneg_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Check if Rat field→order lemmas have been initialized.
    pub(crate) fn has_nn_verify_rat_ordering(&self) -> bool {
        self.nn_verify_rat_ordering_init
    }
}

/// Build proof term for `Rat.sub_nonneg_of_le`.
///
/// Chain:
/// 1. `h_add : Rat.le ((-a) + a) ((-a) + b)` via
///    `Rat.add_le_add_left a b h (-a)`.
/// 2. Rewrite LHS via `Rat.add_left_neg a : (-a) + a = 0` + Eq.subst
///    with motive `λ x, Rat.le x ((-a) + b)` → `Rat.le 0 ((-a) + b)`.
/// 3. Rewrite RHS via `Rat.add_comm (-a) b : (-a) + b = b + (-a)` +
///    Eq.subst with motive `λ x, Rat.le 0 x` → `Rat.le 0 (b + (-a))`.
/// 4. Result is definitionally `Rat.le 0 (Rat.sub b a)` via delta on
///    the reducible `Rat.sub`.
fn build_sub_nonneg_of_le_proof(c: &RatOrdConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let h_ty = c.rat_le(a.clone(), bv.clone());
    let (h_id, h) = b.fresh_local(h_ty.clone());

    let neg_a = c.neg(a.clone());
    let nega_plus_a = c.add(neg_a.clone(), a.clone());
    let nega_plus_b = c.add(neg_a.clone(), bv.clone());
    let b_plus_nega = c.add(bv.clone(), neg_a.clone());

    // h_add : Rat.le ((-a) + a) ((-a) + b) via Rat.add_le_add_left a b h (-a).
    let add_le_add_left = Expr::const_(Name::from_string("Rat.add_le_add_left"), vec![]);
    let h_add = Expr::apps(add_le_add_left, [a.clone(), bv.clone(), h, neg_a.clone()]);

    // h_lneg : (-a) + a = 0 via Rat.add_left_neg a.
    let add_left_neg = Expr::const_(Name::from_string("Rat.add_left_neg"), vec![]);
    let h_lneg = Expr::app(add_left_neg, a.clone());

    // motive1 : fun x => Rat.le x ((-a) + b)
    let motive1 = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let body = c.rat_le(x, nega_plus_b.clone());
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };
    let step1 = c.subst(motive1, nega_plus_a, c.rat_zero.clone(), h_lneg, h_add);

    // h_comm : (-a) + b = b + (-a) via Rat.add_comm (-a) b.
    let add_comm = Expr::const_(Name::from_string("Rat.add_comm"), vec![]);
    let h_comm = Expr::apps(add_comm, [neg_a.clone(), bv.clone()]);

    // motive2 : fun x => Rat.le 0 x
    let motive2 = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let body = c.rat_le(c.rat_zero.clone(), x);
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };
    let body = c.subst(motive2, nega_plus_b, b_plus_nega, h_comm, step1);

    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}
