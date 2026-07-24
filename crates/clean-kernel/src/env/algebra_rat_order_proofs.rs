// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive / kernel-checked proofs of the genuinely-provable Rat ordering
//! lemmas (#3470 Lane #2/#3).
//!
//! These replace prior `Declaration::Axiom` registrations in
//! `algebra_field.rs::init_rat_linear_order` with `Declaration::Theorem`s whose
//! values are genuine kernel-checked proof terms. They are provable because
//! `Rat.le` and `Rat.lt` are *reducible* `Declaration::Definition`s over `Int`
//! comparison:
//!
//! ```text
//! Rat.le a b := Int.le (Int.mul (Rat.num a) (Int.ofNat (Rat.denom b)))
//!                      (Int.mul (Rat.num b) (Int.ofNat (Rat.denom a)))
//! Rat.lt a b := Int.lt (Int.mul (Rat.num a) (Int.ofNat (Rat.denom b)))
//!                      (Int.mul (Rat.num b) (Int.ofNat (Rat.denom a)))
//! ```
//!
//! Writing `cross x y := Int.mul (Rat.num x) (Int.ofNat (Rat.denom y))`, the
//! Rat goals delta-reduce to Int goals that some existing constructive Int
//! order theorem discharges directly:
//!
//! - `Rat.le_refl a` ≡ `Int.le (cross a a) (cross a a)` ← `Int.le_refl`.
//! - `Rat.le_total a b` ≡ `Or (Int.le (cross a b) (cross b a))
//!                            (Int.le (cross b a) (cross a b))` ← `Int.le_total`
//!   applied at `(cross a b, cross b a)`.
//! - `Rat.zero_lt_one` ≡ `Int.lt 0 1` (concrete, after num/denom iota) ←
//!   a concrete `@Int.NonNeg.mk` witness transported across the definitional
//!   reduction of `Int.sub 1 (0 + 1)` to `Int.ofNat 0`.
//! - `Rat.lt_iff_le_not_le a b` ≡
//!   `Iff (Int.lt X Y) (And (Int.le X Y) (Not (Int.le Y X)))` with
//!   `X = cross a b`, `Y = cross b a` ← `Int.lt_iff_le_not_le X Y`.
//!
//! # Honest classification
//!
//! `Int.le_refl` and `Int.le_total` are constructive `Declaration::Theorem`s,
//! so `Rat.le_refl` and `Rat.le_total` are genuinely `Constructive` (empty
//! domain-axiom closure). `Rat.zero_lt_one` is the concrete `@Int.NonNeg.mk
//! Nat.zero` witness and is also `Constructive`. `Rat.mul_pos` (registered in
//! `register_rat_mul_pos`) reduces to the constructive `Int.mul_pos` (with
//! `Int.zero_mul` / `Int.mul_one` transports) — the denominators drop out
//! because `Rat.num Rat.zero ≡ Int.zero`, so it is genuinely `Constructive` and
//! true even for the zero-denominator free `Rat.mk` carrier. `Int.lt_iff_le_not_le`
//! is itself a `Declaration::Axiom`, so `Rat.lt_iff_le_not_le` is an honest
//! `Declaration::Theorem` that classifies `AxiomDependent { Int.lt_iff_le_not_le }`
//! — the Rat-level admitted axiom is eliminated, with the residual trust pushed
//! down to the more-primitive Int
//! axiom (no new Rat axiom, no `sorry`, no fabrication).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached kernel constants for the Rat ordering proof terms.
struct RatOrderConsts {
    rat: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_mul: Expr,
    rat_num: Expr,
    rat_eff_denom: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    int: Expr,
    int_le: Expr,
    int_lt: Expr,
    int_zero: Expr,
    int_mul: Expr,
    int_of_nat: Expr,
    int_le_refl: Expr,
    int_le_total: Expr,
    int_lt_iff: Expr,
    int_mul_pos: Expr,
    int_mul_nonneg: Expr,
    int_zero_mul: Expr,
    int_mul_one: Expr,
    eq_subst: Expr,
    eq_symm: Expr,
    or_const: Expr,
    iff_const: Expr,
    and_const: Expr,
    not_const: Expr,
}

impl RatOrderConsts {
    fn new() -> Self {
        let type1 = Level::succ(Level::zero());
        Self {
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            rat_le: Expr::const_(Name::from_string("Rat.le"), vec![]),
            rat_lt: Expr::const_(Name::from_string("Rat.lt"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_num: Expr::const_(Name::from_string("Rat.num"), vec![]),
            rat_eff_denom: Expr::const_(Name::from_string("Rat.effDenom"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            int: Expr::const_(Name::from_string("Int"), vec![]),
            int_le: Expr::const_(Name::from_string("Int.le"), vec![]),
            int_lt: Expr::const_(Name::from_string("Int.lt"), vec![]),
            int_zero: Expr::const_(Name::from_string("Int.zero"), vec![]),
            int_mul: Expr::const_(Name::from_string("Int.mul"), vec![]),
            int_of_nat: Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            int_le_refl: Expr::const_(Name::from_string("Int.le_refl"), vec![]),
            int_le_total: Expr::const_(Name::from_string("Int.le_total"), vec![]),
            int_lt_iff: Expr::const_(Name::from_string("Int.lt_iff_le_not_le"), vec![]),
            int_mul_pos: Expr::const_(Name::from_string("Int.mul_pos"), vec![]),
            int_mul_nonneg: Expr::const_(Name::from_string("Int.mul_nonneg"), vec![]),
            int_zero_mul: Expr::const_(Name::from_string("Int.zero_mul"), vec![]),
            int_mul_one: Expr::const_(Name::from_string("Int.mul_one"), vec![]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![type1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![type1]),
            or_const: Expr::const_(Name::from_string("Or"), vec![]),
            iff_const: Expr::const_(Name::from_string("Iff"), vec![]),
            and_const: Expr::const_(Name::from_string("And"), vec![]),
            not_const: Expr::const_(Name::from_string("Not"), vec![]),
        }
    }

    /// `Int.le x y`.
    fn int_le(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_le.clone(), [x, y])
    }

    /// `Int.lt x y`.
    fn int_lt(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_lt.clone(), [x, y])
    }

    /// `Int.mul x y`.
    fn imul(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.int_mul.clone(), [x, y])
    }

    /// `@Eq.subst.{1} Int motive @x @y h_eq h_motive_x : motive y`.
    fn isubst(&self, motive: Expr, x: Expr, y: Expr, h_eq: Expr, h_mx: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.int.clone(), motive, x, y, h_eq, h_mx],
        )
    }

    /// `@Eq.symm.{1} Int @x @y h : Eq Int y x`.
    fn isymm(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.int.clone(), x, y, h])
    }

    /// `Rat.le a b` (the stated, not-yet-unfolded type).
    fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }

    /// `Rat.lt a b`.
    fn rat_lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }

    /// `cross x y := Int.mul (Rat.num x) (Int.ofNat (Rat.effDenom y))`.
    /// This is exactly the left/right operand shape produced when `Rat.le`
    /// / `Rat.lt` delta-reduce (now over the EFFECTIVE denominator — see the
    /// `#false-le_trans` soundness fix in `algebra.rs::init_rat_ord`), so any
    /// Int-level proof term built over it will be definitionally accepted
    /// against the `Rat.le` / `Rat.lt` stated type.
    fn cross(&self, x: Expr, y: Expr) -> Expr {
        let num_x = Expr::app(self.rat_num.clone(), x);
        let denom_y = Expr::app(
            self.int_of_nat.clone(),
            Expr::app(self.rat_eff_denom.clone(), y),
        );
        Expr::apps(self.int_mul.clone(), [num_x, denom_y])
    }
}

impl Environment {
    /// Register the genuinely-provable Rat ordering lemmas as
    /// kernel-checked `Declaration::Theorem`s, replacing the prior
    /// `Declaration::Axiom` registrations.
    ///
    /// Idempotent and order-independent: each lemma is skipped if some other
    /// initializer already registered it (whatever its declaration kind).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.init_rat_ord()` registered `Rat.le`, `Rat.lt`,
    ///           `Rat.num`, `Rat.denom`, `Rat.zero`, `Rat.one`, and the
    ///           underlying `Int.le` / `Int.lt` Definitions.
    /// ENSURES: `Rat.le_refl`, `Rat.le_total`, `Rat.zero_lt_one`,
    ///          `Rat.lt_iff_le_not_le`, `Rat.mul_pos`, `Rat.mul_nonneg` are
    ///          `Declaration::Theorem`s whose values kernel-check against their
    ///          canonical types.
    pub(crate) fn register_rat_order_proofs(&mut self) -> Result<(), EnvError> {
        self.init_rat()?;
        self.init_rat_arith()?; // Rat.mul (used by Rat.mul_pos)
        self.init_rat_ord()?;
        self.init_or()?;
        self.init_iff()?;
        self.init_and()?;
        self.init_true_false()?;
        self.init_eq()?;
        // Int order layer we delegate to:
        // - `init_int_linear_order` registers `Int.le_total` (constructive),
        //   `Int.lt_iff_le_not_le` (the still-admitted Int axiom), and pulls in
        //   `init_int_ord_lemmas` → `Int.le_refl` (constructive).
        // - `Int.NonNeg` / `Int.NonNeg.mk` come via `init_int_ord` (transitively
        //   required by `init_rat_ord` above and `init_int_linear_order`).
        self.init_int_linear_order()?;

        let c = RatOrderConsts::new();
        // WS-A ATOMIC LIVE SWITCH: `Rat.zero_lt_one` is `Rat.lt` between two
        // CONCRETE classes (`Rat.zero`/`Rat.one`), so the quotient `Rat.lt`
        // `Quot.lift` ι-reduces fully and the original `Int.NonNeg.mk` witness
        // still kernel-checks unchanged.
        self.register_rat_zero_lt_one(&c)?;
        // The order lemmas that quantify over arbitrary `a b : Rat` no longer
        // reduce by def-eq (the quotient `Rat.le`/`Rat.lt` only reduce on
        // representatives), so they are regenerated with `Quot.ind` over the
        // raw cross-multiplication toolkit in `algebra_rat_quotient.rs`.
        // `register_rat_q_order_lemmas` registers `Rat.le_refl`, `Rat.le_total`,
        // `Rat.lt_iff_le_not_le`, `Rat.le_trans`, `Rat.mul_pos`,
        // `Rat.mul_nonneg` (each idempotent / skip-if-already-a-Theorem).
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_order_lemmas(&qc)?;
        }
        Ok(())
    }

    /// `Rat.le_refl : ∀ a : Rat, Rat.le a a`.
    ///
    /// Proof: `λ a => @Int.le_refl (cross a a)`. The stated `Rat.le a a`
    /// delta-reduces to `Int.le (cross a a) (cross a a)`, which is the type
    /// of `Int.le_refl (cross a a)`.
    fn register_rat_le_refl(&mut self, c: &RatOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.le_refl");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let body = c.rat_le(a.clone(), a);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), body);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let cross_aa = c.cross(a.clone(), a.clone());
            let body = Expr::app(c.int_le_refl.clone(), cross_aa);
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

    /// `Rat.le_total : ∀ a b : Rat, Or (Rat.le a b) (Rat.le b a)`.
    ///
    /// Proof: `λ a b => @Int.le_total (cross a b) (cross b a)`. The stated
    /// goal delta-reduces to
    /// `Or (Int.le (cross a b) (cross b a)) (Int.le (cross b a) (cross a b))`,
    /// which is exactly the type of `Int.le_total (cross a b) (cross b a)`.
    fn register_rat_le_total(&mut self, c: &RatOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.le_total");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let body = Expr::apps(
                c.or_const.clone(),
                [
                    c.rat_le(a.clone(), bv.clone()),
                    c.rat_le(bv.clone(), a.clone()),
                ],
            );
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let cross_ab = c.cross(a.clone(), bv.clone());
            let cross_ba = c.cross(bv.clone(), a.clone());
            let body = Expr::apps(c.int_le_total.clone(), [cross_ab, cross_ba]);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.zero_lt_one : Rat.lt Rat.zero Rat.one`.
    ///
    /// `Rat.lt Rat.zero Rat.one` delta+iota reduces to
    /// `Int.lt (Int.mul (Rat.num 0) (ofNat (denom 1)))
    ///         (Int.mul (Rat.num 1) (ofNat (denom 0)))`, and since
    /// `Rat.num 0 ≡ Int.zero`, `Rat.num 1 ≡ Int.ofNat 1`,
    /// `Rat.denom 0 ≡ Rat.denom 1 ≡ 1`, this is `Int.lt 0 1`, i.e.
    /// (by the `Int.lt`/`Int.le` definitions)
    /// `Int.NonNeg (Int.sub (Int.ofNat 1) (Int.add (Int.ofNat 0) (Int.ofNat 1)))`.
    /// The `Int.sub` argument reduces (native Int arithmetic) to
    /// `Int.ofNat Nat.zero`, so the canonical witness
    /// `@Int.NonNeg.mk Nat.zero : Int.NonNeg (Int.ofNat Nat.zero)` closes the
    /// goal directly by definitional reduction. No `Eq.subst` is needed:
    /// the subtraction is *closed* (no free `Int` variable), so the kernel's
    /// whnf reduces it fully.
    fn register_rat_zero_lt_one(&mut self, c: &RatOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.zero_lt_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = c.rat_lt(c.rat_zero.clone(), c.rat_one.clone());
        // @Int.NonNeg.mk Nat.zero : Int.NonNeg (Int.ofNat Nat.zero)
        let value = Expr::app(
            Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        );
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.lt_iff_le_not_le : ∀ a b : Rat,
    ///    Iff (Rat.lt a b) (And (Rat.le a b) (Not (Rat.le b a)))`.
    ///
    /// Proof: `λ a b => @Int.lt_iff_le_not_le (cross a b) (cross b a)`. With
    /// `X = cross a b`, `Y = cross b a`, the components are `Rat.lt a b ≡
    /// Int.lt X Y`, `Rat.le a b ≡ Int.le X Y`, and `Rat.le b a ≡ Int.le Y X`.
    /// So the stated `Iff (Rat.lt a b) (And (Rat.le a b) (Not (Rat.le b a)))`
    /// delta-reduces to `Iff (Int.lt X Y) (And (Int.le X Y) (Not (Int.le Y X)))`,
    /// the type of `Int.lt_iff_le_not_le X Y`.
    ///
    /// HONEST: `Int.lt_iff_le_not_le` is a `Declaration::Axiom`, so this
    /// theorem classifies `AxiomDependent { Int.lt_iff_le_not_le }`, NOT
    /// `Constructive`. It still eliminates the *Rat-level* admitted axiom
    /// (replacing it with a genuine kernel-checked term), pushing the residual
    /// trust down to the single more-primitive Int axiom.
    fn register_rat_lt_iff_le_not_le(&mut self, c: &RatOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.lt_iff_le_not_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let lt_ab = c.rat_lt(a.clone(), bv.clone());
            let le_ab = c.rat_le(a.clone(), bv.clone());
            let not_le_ba = Expr::app(c.not_const.clone(), c.rat_le(bv.clone(), a.clone()));
            let body = Expr::apps(
                c.iff_const.clone(),
                [lt_ab, Expr::apps(c.and_const.clone(), [le_ab, not_le_ba])],
            );
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), body);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let cross_ab = c.cross(a.clone(), bv.clone());
            let cross_ba = c.cross(bv.clone(), a.clone());
            let body = Expr::apps(c.int_lt_iff.clone(), [cross_ab, cross_ba]);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.mul_pos : ∀ a b : Rat,
    ///    Rat.lt Rat.zero a → Rat.lt Rat.zero b → Rat.lt Rat.zero (Rat.mul a b)`.
    ///
    /// Because `Rat.num Rat.zero ≡ Int.zero` and `Rat.denom Rat.zero ≡ 1`, the
    /// denominators *cancel out* of every `Rat.lt Rat.zero _` proposition — no
    /// division / cancellation is needed (so the lemma is genuinely true for the
    /// non-normalized free `Rat.mk` carrier, unlike `Rat.le_trans` /
    /// `Rat.le_antisymm`). Writing `na := Rat.num a`, `da := Int.ofNat (Rat.denom a)`:
    ///
    /// ```text
    /// Rat.lt Rat.zero a       ≡ Int.lt (Int.mul Int.zero da) (Int.mul na (Int.ofNat 1))
    /// Rat.lt Rat.zero b       ≡ Int.lt (Int.mul Int.zero db) (Int.mul nb (Int.ofNat 1))
    /// Rat.lt Rat.zero (a*b)   ≡ Int.lt (Int.mul Int.zero D)  (Int.mul (Int.mul na nb) (Int.ofNat 1))
    /// ```
    ///
    /// where `D := Int.ofNat (Nat.mul (Rat.denom a) (Rat.denom b))`.
    ///
    /// Proof: rewrite each hypothesis to `Int.lt Int.zero na` / `Int.lt Int.zero nb`
    /// via `Int.zero_mul` (LHS) and `Int.mul_one` (RHS), apply the constructive
    /// `Int.mul_pos na nb` to obtain `Int.lt Int.zero (Int.mul na nb)`, then
    /// transport BACK onto the goal via `Eq.symm` of `Int.zero_mul D` /
    /// `Int.mul_one (Int.mul na nb)`. All four rewrites are single `@Eq.subst.{1}`
    /// steps. Honest classification: `Constructive` (`Int.mul_pos`,
    /// `Int.zero_mul`, `Int.mul_one` are all constructive Theorems).
    fn register_rat_mul_pos(&mut self, c: &RatOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_pos");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Constructive Int dependencies.
        self.register_int_mul_pos_proof()?;
        self.register_int_zero_mul_proof()?;
        self.register_int_mul_one_proof()?;

        let one = Expr::app(
            c.int_of_nat.clone(),
            Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                Expr::const_(Name::from_string("Nat.zero"), vec![]),
            ),
        );

        // Type: ∀ a b, Rat.lt 0 a → Rat.lt 0 b → Rat.lt 0 (Rat.mul a b)
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let lt0a = c.rat_lt(c.rat_zero.clone(), a.clone());
            let lt0b = c.rat_lt(c.rat_zero.clone(), bv.clone());
            let (ha_id, _ha) = b.fresh_local(lt0a.clone());
            let (hb_id, _hb) = b.fresh_local(lt0b.clone());
            let mul_ab = Expr::apps(c.rat_mul.clone(), [a.clone(), bv.clone()]);
            let concl = c.rat_lt(c.rat_zero.clone(), mul_ab);
            let e = b.mk_pi(hb_id, BinderInfo::Default, lt0b, concl);
            let e = b.mk_pi(ha_id, BinderInfo::Default, lt0a, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());

            // Hypotheses declared at the *stated* (Rat.lt) type so the kernel
            // accepts the binders; we use them through their delta-reduced
            // Int.lt shape (definitional).
            let lt0a = c.rat_lt(c.rat_zero.clone(), a.clone());
            let lt0b = c.rat_lt(c.rat_zero.clone(), bv.clone());
            let (ha_id, ha) = b.fresh_local(lt0a.clone());
            let (hb_id, hb) = b.fresh_local(lt0b.clone());

            let na = Expr::app(c.rat_num.clone(), a.clone());
            let nb = Expr::app(c.rat_num.clone(), bv.clone());
            let da = Expr::app(
                c.int_of_nat.clone(),
                Expr::app(c.rat_eff_denom.clone(), a.clone()),
            );
            let db = Expr::app(
                c.int_of_nat.clone(),
                Expr::app(c.rat_eff_denom.clone(), bv.clone()),
            );

            // ---- normalize ha : Int.lt (0*da) (na*1)  ->  Int.lt 0 na ----
            // step A: rewrite LHS via Int.zero_mul da : 0*da = 0.
            //   motive_lhs := fun x => Int.lt x (na*1)
            let mul0_da = c.imul(c.int_zero.clone(), da.clone());
            let na_1 = c.imul(na.clone(), one.clone());
            let h_zm_a = Expr::app(c.int_zero_mul.clone(), da.clone()); // 0*da = 0
            let motive_a_lhs = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = ch.fresh_local(c.int.clone());
                let body = c.int_lt(x, na_1.clone());
                let r = ch.mk_lam(x_id, BinderInfo::Default, c.int.clone(), body);
                ch.finish_child(r)
            };
            // ha1 : Int.lt 0 (na*1)
            let ha1 = c.isubst(
                motive_a_lhs,
                mul0_da.clone(),
                c.int_zero.clone(),
                h_zm_a,
                ha,
            );
            // step B: rewrite RHS via Int.mul_one na : na*1 = na.
            //   motive_rhs := fun y => Int.lt 0 y
            let h_mo_a = Expr::app(c.int_mul_one.clone(), na.clone()); // na*1 = na
            let motive_a_rhs = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (y_id, y) = ch.fresh_local(c.int.clone());
                let body = c.int_lt(c.int_zero.clone(), y);
                let r = ch.mk_lam(y_id, BinderInfo::Default, c.int.clone(), body);
                ch.finish_child(r)
            };
            // ha' : Int.lt 0 na
            let ha_norm = c.isubst(motive_a_rhs, na_1.clone(), na.clone(), h_mo_a, ha1);

            // ---- normalize hb similarly -> Int.lt 0 nb ----
            let mul0_db = c.imul(c.int_zero.clone(), db.clone());
            let nb_1 = c.imul(nb.clone(), one.clone());
            let h_zm_b = Expr::app(c.int_zero_mul.clone(), db.clone());
            let motive_b_lhs = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = ch.fresh_local(c.int.clone());
                let body = c.int_lt(x, nb_1.clone());
                let r = ch.mk_lam(x_id, BinderInfo::Default, c.int.clone(), body);
                ch.finish_child(r)
            };
            let hb1 = c.isubst(
                motive_b_lhs,
                mul0_db.clone(),
                c.int_zero.clone(),
                h_zm_b,
                hb,
            );
            let h_mo_b = Expr::app(c.int_mul_one.clone(), nb.clone());
            let motive_b_rhs = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (y_id, y) = ch.fresh_local(c.int.clone());
                let body = c.int_lt(c.int_zero.clone(), y);
                let r = ch.mk_lam(y_id, BinderInfo::Default, c.int.clone(), body);
                ch.finish_child(r)
            };
            let hb_norm = c.isubst(motive_b_rhs, nb_1.clone(), nb.clone(), h_mo_b, hb1);

            // ---- core : Int.mul_pos na nb ha' hb' : Int.lt 0 (na*nb) ----
            let na_nb = c.imul(na.clone(), nb.clone());
            let core = Expr::apps(c.int_mul_pos.clone(), [na, nb, ha_norm, hb_norm]);

            // ---- transport BACK onto the goal ----
            // goal ≡ Int.lt (0*D) ((na*nb)*1), where (under the #false-le_trans
            // soundness redefinition of `Rat.lt`) the goal's left denominator is
            // the EFFECTIVE denominator of `Rat.mul a b`:
            //   D := Int.ofNat (Rat.effDenom (Rat.mul a b)).
            // `Int.zero_mul D` reduces `0*D` to `0` for ANY closed `D`, so the
            // exact shape of `D` only has to match the goal definitionally; using
            // the effDenom form makes step C's transport land on the new goal.
            let rat_mul_ab = Expr::apps(c.rat_mul.clone(), [a.clone(), bv.clone()]);
            let big_d = Expr::app(
                c.int_of_nat.clone(),
                Expr::app(c.rat_eff_denom.clone(), rat_mul_ab),
            );
            // step C: rewrite LHS 0 -> 0*D using symm (Int.zero_mul D : 0*D = 0).
            //   h_zm_D : 0*D = 0 ; symm : 0 = 0*D
            let mul0_d = c.imul(c.int_zero.clone(), big_d.clone());
            let h_zm_d = Expr::app(c.int_zero_mul.clone(), big_d.clone());
            let h_zm_d_sym = c.isymm(mul0_d.clone(), c.int_zero.clone(), h_zm_d); // 0 = 0*D
            let motive_c_lhs = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = ch.fresh_local(c.int.clone());
                let body = c.int_lt(x, na_nb.clone());
                let r = ch.mk_lam(x_id, BinderInfo::Default, c.int.clone(), body);
                ch.finish_child(r)
            };
            // step1 : Int.lt (0*D) (na*nb)
            let step1 = c.isubst(
                motive_c_lhs,
                c.int_zero.clone(),
                mul0_d.clone(),
                h_zm_d_sym,
                core,
            );
            // step D: rewrite RHS (na*nb) -> (na*nb)*1 using symm (Int.mul_one (na*nb)).
            let nanb_1 = c.imul(na_nb.clone(), one.clone());
            let h_mo_d = Expr::app(c.int_mul_one.clone(), na_nb.clone()); // (na*nb)*1 = na*nb
            let h_mo_d_sym = c.isymm(nanb_1.clone(), na_nb.clone(), h_mo_d); // na*nb = (na*nb)*1
            let motive_d_rhs = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (y_id, y) = ch.fresh_local(c.int.clone());
                let body = c.int_lt(mul0_d.clone(), y);
                let r = ch.mk_lam(y_id, BinderInfo::Default, c.int.clone(), body);
                ch.finish_child(r)
            };
            // body : Int.lt (0*D) ((na*nb)*1) ≡ Rat.lt 0 (Rat.mul a b)
            let body = c.isubst(motive_d_rhs, na_nb.clone(), nanb_1, h_mo_d_sym, step1);

            let e = b.mk_lam(hb_id, BinderInfo::Default, lt0b, body);
            let e = b.mk_lam(ha_id, BinderInfo::Default, lt0a, e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.mul_nonneg : ∀ a b : Rat,
    ///     Rat.le Rat.zero a → Rat.le Rat.zero b → Rat.le Rat.zero (Rat.mul a b)`.
    ///
    /// The `Rat.le` analog of `register_rat_mul_pos`. Provable WITHOUT any
    /// denominator cancellation (and WITHOUT the unsound
    /// `Rat.mk_eq_mk_of_cross_eq` bridge) because `Rat.num Rat.zero ≡ Int.zero`
    /// makes the denominators drop out of every `Rat.le Rat.zero _`
    /// proposition: under the `#false-le_trans` redefinition of `Rat.le` over
    /// the EFFECTIVE denominator,
    ///   `Rat.le Rat.zero x ≡ Int.le (Int.mul Int.zero D_x) (Int.mul (num x) 1)`
    /// where `D_x := Int.ofNat (Rat.effDenom x)` and `1 := Int.ofNat
    /// (Nat.succ Nat.zero) = Int.ofNat (Rat.effDenom Rat.zero)`. Normalizing the
    /// two hypotheses (via `Int.zero_mul` / `Int.mul_one` transports through
    /// `@Eq.subst.{1}`) yields `Int.le Int.zero (num a)` and `Int.le Int.zero
    /// (num b)`; the constructive `Int.mul_nonneg` then gives `Int.le Int.zero
    /// (Int.mul (num a) (num b))`, which transports BACK onto the goal
    ///   `Int.le (Int.mul Int.zero D_ab) (Int.mul (Int.mul (num a) (num b)) 1)`
    /// (with `D_ab := Int.ofNat (Rat.effDenom (Rat.mul a b))`) via the `symm` of
    /// `Int.zero_mul` / `Int.mul_one`.
    ///
    /// Every delegate (`Int.mul_nonneg`, `Int.zero_mul`, `Int.mul_one`,
    /// `Eq.subst`, `Eq.symm`) is a constructive `Declaration::Theorem` / a
    /// foundational equality primitive, so `Rat.mul_nonneg` is genuinely
    /// `ProofQuality::Constructive` (empty domain-axiom closure) — true even for
    /// the zero-denominator free `Rat.mk` carrier. NOT an axiom, NOT a `sorry`.
    fn register_rat_mul_nonneg(&mut self, c: &RatOrderConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.mul_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Constructive Int dependencies.
        self.register_int_mul_nonneg_proof()?;
        self.register_int_zero_mul_proof()?;
        self.register_int_mul_one_proof()?;

        let one = Expr::app(
            c.int_of_nat.clone(),
            Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                Expr::const_(Name::from_string("Nat.zero"), vec![]),
            ),
        );

        // Type: ∀ a b, Rat.le 0 a → Rat.le 0 b → Rat.le 0 (Rat.mul a b)
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let le0a = c.rat_le(c.rat_zero.clone(), a.clone());
            let le0b = c.rat_le(c.rat_zero.clone(), bv.clone());
            let (ha_id, _ha) = b.fresh_local(le0a.clone());
            let (hb_id, _hb) = b.fresh_local(le0b.clone());
            let mul_ab = Expr::apps(c.rat_mul.clone(), [a.clone(), bv.clone()]);
            let concl = c.rat_le(c.rat_zero.clone(), mul_ab);
            let e = b.mk_pi(hb_id, BinderInfo::Default, le0b, concl);
            let e = b.mk_pi(ha_id, BinderInfo::Default, le0a, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());

            // Hypotheses declared at the *stated* (Rat.le) type so the kernel
            // accepts the binders; we use them through their delta-reduced
            // Int.le shape (definitional).
            let le0a = c.rat_le(c.rat_zero.clone(), a.clone());
            let le0b = c.rat_le(c.rat_zero.clone(), bv.clone());
            let (ha_id, ha) = b.fresh_local(le0a.clone());
            let (hb_id, hb) = b.fresh_local(le0b.clone());

            let na = Expr::app(c.rat_num.clone(), a.clone());
            let nb = Expr::app(c.rat_num.clone(), bv.clone());
            let da = Expr::app(
                c.int_of_nat.clone(),
                Expr::app(c.rat_eff_denom.clone(), a.clone()),
            );
            let db = Expr::app(
                c.int_of_nat.clone(),
                Expr::app(c.rat_eff_denom.clone(), bv.clone()),
            );

            // ---- normalize ha : Int.le (0*da) (na*1)  ->  Int.le 0 na ----
            // step A: rewrite LHS via Int.zero_mul da : 0*da = 0.
            //   motive_lhs := fun x => Int.le x (na*1)
            let mul0_da = c.imul(c.int_zero.clone(), da.clone());
            let na_1 = c.imul(na.clone(), one.clone());
            let h_zm_a = Expr::app(c.int_zero_mul.clone(), da.clone()); // 0*da = 0
            let motive_a_lhs = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = ch.fresh_local(c.int.clone());
                let body = c.int_le(x, na_1.clone());
                let r = ch.mk_lam(x_id, BinderInfo::Default, c.int.clone(), body);
                ch.finish_child(r)
            };
            // ha1 : Int.le 0 (na*1)
            let ha1 = c.isubst(
                motive_a_lhs,
                mul0_da.clone(),
                c.int_zero.clone(),
                h_zm_a,
                ha,
            );
            // step B: rewrite RHS via Int.mul_one na : na*1 = na.
            //   motive_rhs := fun y => Int.le 0 y
            let h_mo_a = Expr::app(c.int_mul_one.clone(), na.clone()); // na*1 = na
            let motive_a_rhs = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (y_id, y) = ch.fresh_local(c.int.clone());
                let body = c.int_le(c.int_zero.clone(), y);
                let r = ch.mk_lam(y_id, BinderInfo::Default, c.int.clone(), body);
                ch.finish_child(r)
            };
            // ha' : Int.le 0 na
            let ha_norm = c.isubst(motive_a_rhs, na_1.clone(), na.clone(), h_mo_a, ha1);

            // ---- normalize hb similarly -> Int.le 0 nb ----
            let mul0_db = c.imul(c.int_zero.clone(), db.clone());
            let nb_1 = c.imul(nb.clone(), one.clone());
            let h_zm_b = Expr::app(c.int_zero_mul.clone(), db.clone());
            let motive_b_lhs = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = ch.fresh_local(c.int.clone());
                let body = c.int_le(x, nb_1.clone());
                let r = ch.mk_lam(x_id, BinderInfo::Default, c.int.clone(), body);
                ch.finish_child(r)
            };
            let hb1 = c.isubst(
                motive_b_lhs,
                mul0_db.clone(),
                c.int_zero.clone(),
                h_zm_b,
                hb,
            );
            let h_mo_b = Expr::app(c.int_mul_one.clone(), nb.clone());
            let motive_b_rhs = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (y_id, y) = ch.fresh_local(c.int.clone());
                let body = c.int_le(c.int_zero.clone(), y);
                let r = ch.mk_lam(y_id, BinderInfo::Default, c.int.clone(), body);
                ch.finish_child(r)
            };
            let hb_norm = c.isubst(motive_b_rhs, nb_1.clone(), nb.clone(), h_mo_b, hb1);

            // ---- core : Int.mul_nonneg na nb ha' hb' : Int.le 0 (na*nb) ----
            let na_nb = c.imul(na.clone(), nb.clone());
            let core = Expr::apps(c.int_mul_nonneg.clone(), [na, nb, ha_norm, hb_norm]);

            // ---- transport BACK onto the goal ----
            // goal ≡ Int.le (0*D) ((na*nb)*1), where (under the #false-le_trans
            // soundness redefinition of `Rat.le`) the goal's left denominator is
            // the EFFECTIVE denominator of `Rat.mul a b`:
            //   D := Int.ofNat (Rat.effDenom (Rat.mul a b)).
            // `Int.zero_mul D` reduces `0*D` to `0` for ANY closed `D`, so the
            // exact shape of `D` only has to match the goal definitionally; using
            // the effDenom form makes step C's transport land on the new goal.
            let rat_mul_ab = Expr::apps(c.rat_mul.clone(), [a.clone(), bv.clone()]);
            let big_d = Expr::app(
                c.int_of_nat.clone(),
                Expr::app(c.rat_eff_denom.clone(), rat_mul_ab),
            );
            // step C: rewrite LHS 0 -> 0*D using symm (Int.zero_mul D : 0*D = 0).
            //   h_zm_D : 0*D = 0 ; symm : 0 = 0*D
            let mul0_d = c.imul(c.int_zero.clone(), big_d.clone());
            let h_zm_d = Expr::app(c.int_zero_mul.clone(), big_d.clone());
            let h_zm_d_sym = c.isymm(mul0_d.clone(), c.int_zero.clone(), h_zm_d); // 0 = 0*D
            let motive_c_lhs = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = ch.fresh_local(c.int.clone());
                let body = c.int_le(x, na_nb.clone());
                let r = ch.mk_lam(x_id, BinderInfo::Default, c.int.clone(), body);
                ch.finish_child(r)
            };
            // step1 : Int.le (0*D) (na*nb)
            let step1 = c.isubst(
                motive_c_lhs,
                c.int_zero.clone(),
                mul0_d.clone(),
                h_zm_d_sym,
                core,
            );
            // step D: rewrite RHS (na*nb) -> (na*nb)*1 using symm (Int.mul_one (na*nb)).
            let nanb_1 = c.imul(na_nb.clone(), one.clone());
            let h_mo_d = Expr::app(c.int_mul_one.clone(), na_nb.clone()); // (na*nb)*1 = na*nb
            let h_mo_d_sym = c.isymm(nanb_1.clone(), na_nb.clone(), h_mo_d); // na*nb = (na*nb)*1
            let motive_d_rhs = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (y_id, y) = ch.fresh_local(c.int.clone());
                let body = c.int_le(mul0_d.clone(), y);
                let r = ch.mk_lam(y_id, BinderInfo::Default, c.int.clone(), body);
                ch.finish_child(r)
            };
            // body : Int.le (0*D) ((na*nb)*1) ≡ Rat.le 0 (Rat.mul a b)
            let body = c.isubst(motive_d_rhs, na_nb.clone(), nanb_1, h_mo_d_sym, step1);

            let e = b.mk_lam(hb_id, BinderInfo::Default, le0b, body);
            let e = b.mk_lam(ha_id, BinderInfo::Default, le0a, e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::expr::ExprKind;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::new();
        env.register_rat_order_proofs()
            .expect("register_rat_order_proofs should succeed");
        env
    }

    /// Every target lemma is registered as a `Declaration::Theorem` carrying a
    /// proof value (NOT an Axiom / Opaque).
    #[test]
    fn test_all_four_are_theorems_with_value() {
        let env = env();
        for name in &[
            "Rat.le_refl",
            "Rat.le_total",
            "Rat.zero_lt_one",
            "Rat.lt_iff_le_not_le",
        ] {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{name} must be Declaration::Theorem, got {:?}",
                info.kind
            );
            assert!(info.value.is_some(), "{name} Theorem must retain its value");
        }
    }

    /// Each lemma kernel-type-checks at its canonical (stated) type. Because
    /// `add_decl(Declaration::Theorem ..)` runs `check_type(value, type_)` at
    /// registration, successful `register_rat_order_proofs` already proves the
    /// kernel accepted each proof term; re-inferring here pins it explicitly.
    #[test]
    fn test_all_four_kernel_type_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in &[
            "Rat.le_refl",
            "Rat.le_total",
            "Rat.zero_lt_one",
            "Rat.lt_iff_le_not_le",
        ] {
            let e = Expr::const_(Name::from_string(name), vec![]);
            let _ = tc
                .infer_type(&e)
                .unwrap_or_else(|err| panic!("{name} should kernel-type-check, got {err:?}"));
        }
    }

    /// `Rat.le_refl` is genuinely `Constructive` — its only delegate is the
    /// constructive `Int.le_refl`, so the domain-axiom closure is empty.
    #[test]
    fn test_rat_le_refl_constructive() {
        let env = env();
        let q = env
            .proof_quality(&Name::from_string("Rat.le_refl"))
            .expect("proof_quality");
        assert!(
            matches!(q, ProofQuality::Constructive),
            "Rat.le_refl must be Constructive, got {q:?}"
        );
    }

    /// `Rat.le_total` is genuinely `Constructive` — delegates to the
    /// constructive `Int.le_total`.
    #[test]
    fn test_rat_le_total_constructive() {
        let env = env();
        let q = env
            .proof_quality(&Name::from_string("Rat.le_total"))
            .expect("proof_quality");
        assert!(
            matches!(q, ProofQuality::Constructive),
            "Rat.le_total must be Constructive, got {q:?}"
        );
    }

    /// `Rat.zero_lt_one` is genuinely `Constructive` — a concrete
    /// `@Int.NonNeg.mk Nat.zero` witness, no domain axiom in its closure.
    #[test]
    fn test_rat_zero_lt_one_constructive() {
        let env = env();
        let q = env
            .proof_quality(&Name::from_string("Rat.zero_lt_one"))
            .expect("proof_quality");
        assert!(
            matches!(q, ProofQuality::Constructive),
            "Rat.zero_lt_one must be Constructive, got {q:?}"
        );
    }

    /// `Rat.lt_iff_le_not_le` is now genuinely `Constructive`: its sole former
    /// domain-axiom dependency `Int.lt_iff_le_not_le` has itself been ELIMINATED
    /// to a kernel-checked Theorem (`algebra_int_lt_iff_le_not_le_proof.rs`), so
    /// `Rat.lt_iff_le_not_le`'s transitive domain-axiom closure is now empty — a
    /// free downstream win from the Int-level elimination.
    #[test]
    fn test_rat_lt_iff_le_not_le_now_constructive() {
        let env = env();
        let deps = env
            .axiom_deps(&Name::from_string("Rat.lt_iff_le_not_le"))
            .expect("axiom_deps");
        let names: std::collections::BTreeSet<String> =
            deps.iter().map(|n| n.to_string()).collect();
        assert!(
            names.is_empty(),
            "Rat.lt_iff_le_not_le closure must now be EMPTY (Int.lt_iff_le_not_le \
             was eliminated), got {names:?}"
        );
        let q = env
            .proof_quality(&Name::from_string("Rat.lt_iff_le_not_le"))
            .expect("proof_quality");
        assert!(
            matches!(q, ProofQuality::Constructive),
            "Rat.lt_iff_le_not_le must now be Constructive, got {q:?}"
        );
    }

    /// WS-A: over the quotient carrier `Rat.le_refl` is proved by `Quot.ind`
    /// (the per-representative leaf closes with `Int.le_refl`); guard that the
    /// proof root is the `Quot.ind` eliminator, not a self-reference.
    #[test]
    fn test_rat_le_refl_proof_root_is_quot_ind() {
        let env = env();
        let info = env
            .get_const(&Name::from_string("Rat.le_refl"))
            .expect("registered");
        let value = info.value.as_ref().expect("Theorem value");
        // Outer λ over a : Rat.
        let body = match value.kind() {
            ExprKind::Lam(_, _, inner) => (**inner).clone(),
            k => panic!("expected outer λ, got {k:?}"),
        };
        let mut head = body;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(n, _) => assert_eq!(
                n.to_string(),
                "Quot.ind",
                "Rat.le_refl proof root must be Quot.ind over the quotient carrier"
            ),
            k => panic!("expected Const(Quot.ind), got {k:?}"),
        }
    }

    /// `Rat.mul_pos` is registered as a `Declaration::Theorem` carrying a value
    /// and kernel-type-checks at its canonical type.
    #[test]
    fn test_rat_mul_pos_theorem_kernel_checks() {
        let env = env();
        let info = env
            .get_const(&Name::from_string("Rat.mul_pos"))
            .expect("Rat.mul_pos should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "Rat.mul_pos must be Declaration::Theorem, got {:?}",
            info.kind
        );
        assert!(
            info.value.is_some(),
            "Rat.mul_pos Theorem must retain a value"
        );
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("Rat.mul_pos"), vec![]))
            .expect("Rat.mul_pos should kernel-type-check");
    }

    /// `Rat.mul_pos` is genuinely `Constructive` — it reduces to the constructive
    /// `Int.mul_pos` (plus `Int.zero_mul` / `Int.mul_one` transports), so its
    /// domain-axiom closure is empty.
    #[test]
    fn test_rat_mul_pos_constructive() {
        let env = env();
        let q = env
            .proof_quality(&Name::from_string("Rat.mul_pos"))
            .expect("proof_quality");
        assert!(
            matches!(q, ProofQuality::Constructive),
            "Rat.mul_pos must be Constructive, got {q:?}"
        );
    }

    /// `Rat.mul_nonneg` is registered as a `Declaration::Theorem` carrying a
    /// value and kernel-type-checks at its canonical type (the `Rat.le` analog
    /// of `Rat.mul_pos`).
    #[test]
    fn test_rat_mul_nonneg_theorem_kernel_checks() {
        let env = env();
        let info = env
            .get_const(&Name::from_string("Rat.mul_nonneg"))
            .expect("Rat.mul_nonneg should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "Rat.mul_nonneg must be Declaration::Theorem, got {:?}",
            info.kind
        );
        assert!(
            info.value.is_some(),
            "Rat.mul_nonneg Theorem must retain a value"
        );
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]))
            .expect("Rat.mul_nonneg should kernel-type-check");
    }

    /// `Rat.mul_nonneg` is genuinely `Constructive` — it reduces to the
    /// constructive `Int.mul_nonneg` (plus `Int.zero_mul` / `Int.mul_one`
    /// transports), so its domain-axiom closure is empty. This is the proof that
    /// the prior `Declaration::Axiom` has been genuinely eliminated, not
    /// restated.
    #[test]
    fn test_rat_mul_nonneg_constructive() {
        let env = env();
        let q = env
            .proof_quality(&Name::from_string("Rat.mul_nonneg"))
            .expect("proof_quality");
        assert!(
            matches!(q, ProofQuality::Constructive),
            "Rat.mul_nonneg must be Constructive, got {q:?}"
        );
    }

    /// `Rat.mul_nonneg`'s transitive closure must contain NO `Rat.`-level axiom
    /// and NO `sorry` — the residual trust is pushed down to constructive Int
    /// theorems only.
    #[test]
    fn test_rat_mul_nonneg_no_rat_axiom_no_sorry() {
        let env = env();
        let deps = env
            .axiom_deps(&Name::from_string("Rat.mul_nonneg"))
            .expect("axiom_deps");
        for n in deps.iter().map(|n| n.to_string()) {
            assert!(
                n != "sorry" && n != "sorryAx",
                "Rat.mul_nonneg must be sorry-free, reached {n}"
            );
            assert!(
                !n.starts_with("Rat."),
                "Rat.mul_nonneg must not rest on any Rat-level axiom, reached {n}"
            );
        }
    }

    /// Idempotent: a second registration is a no-op (skip-if-present).
    #[test]
    fn test_idempotent() {
        let mut env = Environment::new();
        env.register_rat_order_proofs().expect("first");
        env.register_rat_order_proofs().expect("second idempotent");
    }
}
