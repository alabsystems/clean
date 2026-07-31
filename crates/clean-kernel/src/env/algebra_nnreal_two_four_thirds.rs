// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — THE VALUE-`2^{4/3}` KEYSTONE: `(4·cbrt(1/4))³ = 16`,
//! axiom-free, WITHOUT ever evaluating the FALSE `cbrt(2)`.
//!
//! # Why this module exists (the scaling-reduction unblock)
//!
//! The §9.6 `4/3`-norm identity (`‖g‖_{4/3}⁴ = 16·count³` for `g ∈ {0,±2}`) needs
//! the per-coordinate contribution `|2|^{4/3} = 2^{4/3}` whose CUBE is `2⁴ = 16`.
//! The naive route `NNReal.pow43 2` / `NNReal.cbrt 2` is BLOCKED: the dyadic cbrt
//! carrier hardcodes `k_0 = 0` and is faithful only on `[0,1)`, so `cbrt(2)³ ≠ 2`
//! (verified FALSE at kernel level — the carrier saturates below 1).
//!
//! THE UNBLOCK (this module): stay inside the faithful `[0,1)` range. Let
//! `C := NNReal.cbrt (1/4)`. Since `1/4 ∈ [0,1)`, the landed `NNReal.cbrt_cubed`
//! gives `C³ = NNReal.ofRat (1/4)` — and `cbrt(2)` is NEVER touched. Then
//!
//! ```text
//!   (4·C)³ = 64·C³ = 64·(1/4) = 16.
//! ```
//!
//! `4·C` is exactly the value `2^{4/3}` (its cube is `2⁴`), realized as a genuine
//! `NNReal`. The cube identity is proven by the SAME regroup technique as
//! `NNReal.pow43_cubed` (`NNReal.mul_mul_mul_comm` interchange) + the landed
//! carrier mul algebra (`NNReal.ofRat_mul`/`mul_comm`/`mul_assoc`), then a pure
//! `Rat` numeral bridge `(4·4·4)·(1/4) = 16` and an `ofRat`-value congruence.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNReal.twoFourThirds : NNReal`
//!     `:= NNReal.mul (NNReal.ofRat 4 h4) (NNReal.cbrt (Rat.mk (Int.ofNat 1) 4))`.
//!   Reducible `Definition`. The value `2^{4/3}` (`= 4·cbrt(1/4)`), built ENTIRELY
//!   inside the faithful range; NEVER `NNReal.cbrt 2`.
//!
//! - `NNReal.twoFourThirds_cubed :
//!     NNReal.mul (NNReal.mul twoFourThirds twoFourThirds) twoFourThirds
//!       = NNReal.ofRat (Rat.ofNat 16) h16`.
//!   The keystone `(2^{4/3})³ = 16`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`. FORBIDDEN here: `NNReal.cbrt 2`, `NNReal.pow43 2`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the `2^{4/3}` keystone.
pub(crate) struct TwoFourThirdsConsts {
    #[cfg(test)]
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int: Expr,
    int_of_nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_mk: Expr,
    rat_ofnat: Expr,
    rat_mul: Expr,
    rat_le: Expr,
    rat_mul_comm: Expr,
    rat_mul_assoc: Expr,
    #[cfg(test)]
    rat_ofnat_mul: Expr,
    rat_le_of_ble: Expr,
    bool_true: Expr,
    bool_ty: Expr,
    rat_mul_nonneg: Expr,
    quot_mk: Expr,
    raw: Expr,
    raw_mk: Expr,
    raw_equiv: Expr,
    int_mul: Expr,
    nat_mul: Expr,
    quot_sound: Expr,
    // carrier.
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_of_rat: Expr,
    nnreal_cbrt: Expr,
    nnreal_mmm_comm: Expr,
    nnreal_cbrt_cubed: Expr,
    nnreal_two_four_thirds: Expr,
    nnreal_two_four_thirds_cubed: Expr,
    // Eq.{1}.
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    eq_subst1: Expr,
    congr_arg1: Expr,
}

impl TwoFourThirdsConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let kl = |s: &str| Expr::const_(Name::from_string(s), vec![l1.clone()]);
        Self {
            #[cfg(test)]
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            int: k("Int"),
            int_of_nat: k("Int.ofNat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_mk: k("Rat.mk"),
            rat_ofnat: k("Rat.ofNat"),
            rat_mul: k("Rat.mul"),
            rat_le: k("Rat.le"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            #[cfg(test)]
            rat_ofnat_mul: k("Rat.ofNat_mul"),
            rat_le_of_ble: k("Rat.le_of_ble_eq_true"),
            bool_true: k("Bool.true"),
            bool_ty: k("Bool"),
            rat_mul_nonneg: k("Rat.mul_nonneg"),
            quot_mk: kl("Quot.mk"),
            raw: k("Rat.Raw"),
            raw_mk: k("Rat.Raw.mk"),
            raw_equiv: k("Rat.Raw.Equiv"),
            int_mul: k("Int.mul"),
            nat_mul: k("Nat.mul"),
            quot_sound: kl("Quot.sound"),
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_cbrt: k("NNReal.cbrt"),
            nnreal_mmm_comm: k("NNReal.mul_mul_mul_comm"),
            nnreal_cbrt_cubed: k("NNReal.cbrt_cubed"),
            nnreal_two_four_thirds: k("NNReal.twoFourThirds"),
            nnreal_two_four_thirds_cubed: k("NNReal.twoFourThirds_cubed"),
            eq1: kl("Eq"),
            eq_refl1: kl("Eq.refl"),
            eq_symm1: kl("Eq.symm"),
            eq_trans1: kl("Eq.trans"),
            eq_subst1: kl("Eq.subst"),
            congr_arg1: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    // ── Nat / Rat literals ───────────────────────────────────────────────────
    fn nat_lit(&self, n: usize) -> Expr {
        let mut nat = self.nat_zero.clone();
        for _ in 0..n {
            nat = Expr::app(self.nat_succ.clone(), nat);
        }
        nat
    }
    /// `Rat.ofNat n` (= `Rat.mk (Int.ofNat n) 1`).
    fn ofnat_lit(&self, n: usize) -> Expr {
        Expr::app(self.rat_ofnat.clone(), self.nat_lit(n))
    }
    /// `1/4 := Rat.mk (Int.ofNat 1) 4`.
    fn one_quarter(&self) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.nat_lit(1)),
                self.nat_lit(4),
            ],
        )
    }
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn nonneg(&self, a: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [self.rat_zero.clone(), a])
    }
    /// `Rat.mul_comm a b : (a·b) = (b·a)`.
    fn rmul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_assoc a b c : ((a·b)·c) = (a·(b·c))`.
    fn rmul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_mul_assoc.clone(), [a, b, cc])
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn rmul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.rat_mul_nonneg.clone(), [a, b, ha, hb])
    }
    /// `ofRat((16·cnt)·(cnt·cnt)) h` plus its nonneg proof `h`. The `(16·cnt)·(cnt·cnt)`
    /// grouping is byte-for-byte `dualbound_assemble`'s `cube16` (`16 := Rat.ofNat 16`,
    /// defeq to `Rat.mk (Int.ofNat 16) 1`).
    fn cube16(&self, cnt: &Expr, hcnt: &Expr) -> (Expr, Expr) {
        let s16 = self.ofnat_lit(16);
        let h16 = self.ofnat_nonneg(16);
        let sixteen_cnt = self.rmul(s16.clone(), cnt.clone()); // 16·cnt
        let cnt_cnt = self.rmul(cnt.clone(), cnt.clone()); // cnt·cnt
        let cube_rat = self.rmul(sixteen_cnt.clone(), cnt_cnt.clone()); // (16·cnt)·(cnt·cnt)
        let h_16cnt = self.rmul_nonneg(s16, cnt.clone(), h16, hcnt.clone());
        let h_cntcnt = self.rmul_nonneg(cnt.clone(), cnt.clone(), hcnt.clone(), hcnt.clone());
        let h_cube = self.rmul_nonneg(sixteen_cnt, cnt_cnt, h_16cnt, h_cntcnt);
        let of_cube = self.ofrat(&cube_rat, &h_cube);
        (of_cube, h_cube)
    }
    /// `0 ≤ (Rat.ofNat n)` via the boolean reflection idiom.
    fn ofnat_nonneg(&self, n: usize) -> Expr {
        let lit = self.ofnat_lit(n);
        let refl = Expr::apps(
            self.eq_refl1.clone(),
            [self.bool_ty.clone(), self.bool_true.clone()],
        );
        Expr::apps(
            self.rat_le_of_ble.clone(),
            [self.rat_zero.clone(), lit, refl],
        )
    }
    /// `0 ≤ 1/4` via the boolean reflection idiom (`ble 0 (1/4)` reduces to true).
    fn quarter_nonneg(&self) -> Expr {
        let refl = Expr::apps(
            self.eq_refl1.clone(),
            [self.bool_ty.clone(), self.bool_true.clone()],
        );
        Expr::apps(
            self.rat_le_of_ble.clone(),
            [self.rat_zero.clone(), self.one_quarter(), refl],
        )
    }

    // ── Eq.{1} plumbing ──────────────────────────────────────────────────────
    fn eq_ty(&self, t: &Expr, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [t.clone(), a, b])
    }
    fn refl(&self, t: &Expr, a: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [t.clone(), a])
    }
    fn symm(&self, t: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [t.clone(), a, b, h])
    }
    fn trans(&self, t: &Expr, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [t.clone(), a, b, cc, h1, h2])
    }
    /// `@congrArg.{1,1} T T a b f h : (f a) = (f b)`.
    fn congr(&self, t: &Expr, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(self.congr_arg1.clone(), [t.clone(), t.clone(), a, b, f, h])
    }
    #[cfg(test)]
    fn rat_eq(&self, a: Expr, b: Expr) -> Expr {
        self.eq_ty(&self.rat.clone(), a, b)
    }
    fn rat_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.trans(&self.rat.clone(), a, b, cc, h1, h2)
    }

    // ── NNReal constructors ──────────────────────────────────────────────────
    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn ofrat(&self, x: &Expr, h: &Expr) -> Expr {
        Expr::apps(self.nnreal_of_rat.clone(), [x.clone(), h.clone()])
    }
    fn cbrt(&self, x: &Expr) -> Expr {
        Expr::app(self.nnreal_cbrt.clone(), x.clone())
    }
    fn eq_nn(&self, a: &Expr, b: &Expr) -> Expr {
        self.eq_ty(&self.nnreal.clone(), a.clone(), b.clone())
    }
    fn nn_trans(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
        self.trans(
            &self.nnreal.clone(),
            a.clone(),
            b.clone(),
            cc.clone(),
            h1,
            h2,
        )
    }
    /// `NNReal.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn nn_mmm(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_mmm_comm.clone(),
            [a.clone(), b.clone(), cc.clone(), d.clone()],
        )
    }
    /// `NNReal.ofRat_mul a b ha hb hab : mul (ofRat a)(ofRat b) = ofRat (a·b)`.
    fn nn_ofrat_mul(&self, a: &Expr, b: &Expr, ha: &Expr, hb: &Expr, hab: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.ofRat_mul"), vec![]),
            [a.clone(), b.clone(), ha.clone(), hb.clone(), hab.clone()],
        )
    }
    /// `mul · r` congruence: `h : a = b ⟹ mul a r = mul b r`.
    fn nn_congr_l(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, r: &Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(self.nnreal.clone());
            let body = self.nnmul(&w, r);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.congr(&self.nnreal.clone(), a.clone(), b.clone(), f, h)
    }
    /// `mul l ·` congruence: `h : a = b ⟹ mul l a = mul l b`.
    fn nn_congr_r(&self, parent: &EnvDeclBuilder, l: &Expr, a: &Expr, b: &Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(self.nnreal.clone());
            let body = self.nnmul(l, &w);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.congr(&self.nnreal.clone(), a.clone(), b.clone(), f, h)
    }
}

impl Environment {
    /// Register `NNReal.twoFourThirds` and `NNReal.twoFourThirds_cubed`. Reuses the
    /// landed `NNReal.cbrt_cubed`, `NNReal.mul_mul_mul_comm`, `NNReal.ofRat_mul`.
    /// Idempotent; foundational-only closure.
    pub fn init_algebra_nnreal_two_four_thirds(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_pow43_cubed()?; // NNReal.mul_mul_mul_comm, cbrt_cubed, ofRat_mul, mul algebra
        self.init_algebra_nnreal_sqrt_strict()?; // Rat.lt_of_ble_eq_false (1/4 < 1)
        self.register_rat_mul_comm_proof()?; // Rat.mul_comm
        self.register_rat_mul_assoc_proof()?; // Rat.mul_assoc
        self.register_rat_ofnat_mul()?; // Rat.ofNat_mul (numeral bridge)
        self.register_rat_order_proofs()?; // Rat.mul_nonneg
        self.register_rat_minmax_proofs()?; // Rat.le_of_ble_eq_true
        self.init_eq()?;

        let c = TwoFourThirdsConsts::new();
        self.register_two_four_thirds_def(&c)?;
        self.register_two_four_thirds_cubed(&c)?;
        self.register_two_four_thirds_count_cubed(&c)?;
        Ok(())
    }

    /// `NNReal.twoFourThirds : NNReal := mul (ofRat 4 h4)(cbrt (1/4))`.
    fn register_two_four_thirds_def(&mut self, c: &TwoFourThirdsConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.twoFourThirds");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let four = c.ofnat_lit(4);
        let h4 = c.ofnat_nonneg(4);
        let a = c.ofrat(&four, &h4);
        let cc = c.cbrt(&c.one_quarter());
        let value = c.nnmul(&a, &cc);
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: c.nnreal.clone(),
            value,
            is_reducible: true,
        })
    }

    /// `NNReal.twoFourThirds_cubed : (2^{4/3})³ = ofRat 16`.
    fn register_two_four_thirds_cubed(&mut self, c: &TwoFourThirdsConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.twoFourThirds_cubed");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let s16 = c.ofnat_lit(16);
        let h16 = c.ofnat_nonneg(16);
        let ofrat16 = c.ofrat(&s16, &h16);

        let ty = {
            let tft = c.nnreal_two_four_thirds.clone();
            let lhs = c.nnmul(&c.nnmul(&tft, &tft), &tft);
            c.eq_nn(&lhs, &ofrat16)
        };
        let value = build_two_four_thirds_cubed_value(c, &s16, &h16);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.twoFourThirds_count_cubed`: the materialised `4/3`-norm-to-the-4th
    /// identity (design §10.6 M1). With `Q := ofRat cnt`, `V := twoFourThirds`,
    /// the per-coordinate contribution sum over a `cnt`-element support is `Q·V`
    /// (`= cnt · 2^{4/3}`), and
    ///
    /// ```text
    ///   (Q·V)³ = (Q·Q·Q)·(V·V·V) = ofRat(cnt³)·ofRat(16) = ofRat(16·cnt³).
    /// ```
    ///
    /// The RHS `16·cnt³ := (16·cnt)·(cnt·cnt)` is byte-for-byte the
    /// `two_norm_sq_le_of_holder_chain` / `m1_ty` shape, so this is the genuine
    /// `h_m1` content (`‖g‖_{4/3}⁴ = 16·count³`), materialised — NOT a refl.
    fn register_two_four_thirds_count_cubed(
        &mut self,
        c: &TwoFourThirdsConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.twoFourThirds_count_cubed");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cnt_id, cnt) = b.fresh_local(c.rat.clone());
            let hcnt_ty = c.nonneg(cnt.clone());
            let (hcnt_id, hcnt) = b.fresh_local(hcnt_ty.clone());
            let q = c.ofrat(&cnt, &hcnt);
            let v = c.nnreal_two_four_thirds.clone();
            let qv = c.nnmul(&q, &v);
            let lhs = c.nnmul(&c.nnmul(&qv, &qv), &qv);
            // RHS = ofRat ((16·cnt)·(cnt·cnt)) h.
            let cube = c.cube16(&cnt, &hcnt);
            let concl = c.eq_nn(&lhs, &cube.0);
            let e = b.mk_pi(hcnt_id, BinderInfo::Default, hcnt_ty, concl);
            b.finish(b.mk_pi(cnt_id, BinderInfo::Default, c.rat.clone(), e))
        };
        let value = build_two_four_thirds_count_cubed_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `ofRat a ha = ofRat b hb` from a `Rat` equality `h_eq : a = b`. The nonneg
/// argument is a `Prop`, so proof-irrelevant; transport the VALUE via `Eq.subst`
/// over `fun z => Π (hz : 0≤z), ofRat a ha = ofRat z hz`. (Mirrors desquare's
/// `ofrat_value_congr`.)
fn ofrat_value_congr(
    c: &TwoFourThirdsConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    b: &Expr,
    ha: &Expr,
    hb: &Expr,
    h_eq: Expr,
) -> Expr {
    let motive = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let inner = {
            let mut di = EnvDeclBuilder::child_of(&d);
            let hz_ty = c.nonneg(z.clone());
            let (hz_id, hz) = di.fresh_local(hz_ty.clone());
            let body = c.eq_nn(&c.ofrat(a, ha), &c.ofrat(&z, &hz));
            di.finish_child(di.mk_pi(hz_id, BinderInfo::Default, hz_ty, body))
        };
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), inner))
    };
    let base = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let ha_ty = c.nonneg(a.clone());
        let (hz_id, _hz) = d.fresh_local(ha_ty.clone());
        let body = c.refl(&c.nnreal.clone(), c.ofrat(a, ha));
        d.finish_child(d.mk_lam(hz_id, BinderInfo::Default, ha_ty, body))
    };
    let transported = Expr::apps(
        c.eq_subst1.clone(),
        [c.rat.clone(), motive, a.clone(), b.clone(), h_eq, base],
    );
    Expr::apps(transported, [hb.clone()])
}

/// The pure-`Rat` numeral bridge `(((4·4)·4)·(1/4)) = 16`.
///
/// `1/4 = Rat.mk (Int.ofNat 1) 4`, `4 = Rat.ofNat 4`, `16 = Rat.ofNat 16`. The
/// product `(((4·4)·4)·(1/4))` cross-multiplies (over the quotient `Rat`) to a
/// raw rep `Raw.mk (64·1) (1·4)` whose `Raw.Equiv` to `Raw.mk 16 1` is the Int
/// cross-product `(64·1)·1 = 16·4` (both `Int.ofNat 64`). Discharged by
/// `Quot.sound` + `Eq.refl`, exactly the `Rat.nine_mul_inv_nine` template.
fn build_rat_64_quarter_bridge(c: &TwoFourThirdsConsts, parent: &EnvDeclBuilder) -> Expr {
    let four = c.ofnat_lit(4);
    let quarter = c.one_quarter();
    let s16 = c.ofnat_lit(16);

    // lhs_goal := (((4·4)·4)·(1/4))  (left-nested cube of 4, times 1/4).
    let ff = c.rmul(four.clone(), four.clone()); // 4·4
    let fff = c.rmul(ff.clone(), four.clone()); // (4·4)·4
    let lhs_goal = c.rmul(fff.clone(), quarter.clone()); // ((4·4)·4)·(1/4)

    // Build the Quot.sound bridge raw_l ~ raw_r, raw_l defeq to lhs_goal,
    // raw_r defeq to 16.
    //   numerator of lhs_goal product = ((ofNat4 · ofNat4) · ofNat4) · ofNat1
    //   effDenom of lhs_goal product  = ((1·1)·1)·4
    //   raw_r = Raw.mk (ofNat 16) 1.
    let of4 = Expr::app(c.int_of_nat.clone(), c.nat_lit(4));
    let of1 = Expr::app(c.int_of_nat.clone(), c.nat_lit(1));
    let of16 = Expr::app(c.int_of_nat.clone(), c.nat_lit(16));
    let im = |a: Expr, b: Expr| Expr::apps(c.int_mul.clone(), [a, b]);
    let nm = |a: Expr, b: Expr| Expr::apps(c.nat_mul.clone(), [a, b]);
    let prod_num = im(im(im(of4.clone(), of4.clone()), of4.clone()), of1.clone());
    let prod_den = nm(
        nm(nm(c.nat_lit(1), c.nat_lit(1)), c.nat_lit(1)),
        c.nat_lit(4),
    );
    let raw_l = Expr::apps(c.raw_mk.clone(), [prod_num, prod_den]);
    let raw_r = Expr::apps(c.raw_mk.clone(), [of16.clone(), c.nat_lit(1)]);

    // Equiv obligation reduces (cross-product) to Int `64·1 = 16·4`, both
    // `Int.ofNat 64`. Eq.refl Int (Int.ofNat 64) discharges through Raw.Equiv defeq.
    let equiv_proof = Expr::apps(
        c.eq_refl1.clone(),
        [
            c.int.clone(),
            Expr::app(c.int_of_nat.clone(), c.nat_lit(64)),
        ],
    );
    let _ = &raw_r;
    let sound = Expr::apps(
        c.quot_sound.clone(),
        [
            c.raw.clone(),
            c.raw_equiv.clone(),
            raw_l.clone(),
            raw_r.clone(),
            equiv_proof,
        ],
    );

    let quot_mk_l = Expr::apps(
        c.quot_mk.clone(),
        [c.raw.clone(), c.raw_equiv.clone(), raw_l],
    );
    let quot_mk_r = Expr::apps(
        c.quot_mk.clone(),
        [c.raw.clone(), c.raw_equiv.clone(), raw_r],
    );
    let _ = parent;
    // lhs_goal defeq quot_mk_l ; 16 defeq quot_mk_r.
    let to_l = c.refl(&c.rat.clone(), lhs_goal.clone());
    let from_r = c.refl(&c.rat.clone(), s16.clone());
    let step1 = c.rat_trans(
        lhs_goal.clone(),
        quot_mk_l.clone(),
        quot_mk_r.clone(),
        to_l,
        sound,
    );
    c.rat_trans(lhs_goal, quot_mk_r, s16, step1, from_r)
}

/// The full `(2^{4/3})³ = ofRat 16` proof term.
fn build_two_four_thirds_cubed_value(c: &TwoFourThirdsConsts, s16: &Expr, h16: &Expr) -> Expr {
    let bd = EnvDeclBuilder::new();

    let four = c.ofnat_lit(4);
    let h4 = c.ofnat_nonneg(4);
    let quarter = c.one_quarter();
    let hq = c.quarter_nonneg();

    // A := ofRat 4 ; C := cbrt(1/4) ; pw := twoFourThirds (defeq A·C).
    let a = c.ofrat(&four, &h4);
    let cbrt = c.cbrt(&quarter);
    let pw = c.nnreal_two_four_thirds.clone();

    // ac := A·C  (defeq pw).
    let ac = c.nnmul(&a, &cbrt);
    let lhs = c.nnmul(&c.nnmul(&pw, &pw), &pw);

    // ── Regroup (A·C)·(A·C)·(A·C) → ((A·A)·A)·((C·C)·C) ── (mirror pow43_cubed)
    let aa = c.nnmul(&a, &a);
    let cc = c.nnmul(&cbrt, &cbrt);
    let acac = c.nnmul(&ac, &ac); // (A·C)·(A·C)
    let aacc = c.nnmul(&aa, &cc); // (A·A)·(C·C)
    let i1 = c.nn_mmm(&a, &cbrt, &a, &cbrt); // (A·C)·(A·C) = (A·A)·(C·C)
    let aaa = c.nnmul(&aa, &a); // (A·A)·A
    let ccc = c.nnmul(&cc, &cbrt); // (C·C)·C
    let i2 = c.nn_mmm(&aa, &cc, &a, &cbrt); // ((A·A)·(C·C))·(A·C) = ((A·A)·A)·((C·C)·C)
    let aacc_ac = c.nnmul(&aacc, &ac);
    let aaa_ccc = c.nnmul(&aaa, &ccc);

    let left_rw = c.nn_congr_l(&bd, &acac, &aacc, &ac, i1); // (acac)·ac = (aacc)·ac
    let acac_ac = c.nnmul(&acac, &ac); // = lhs once pw≡A·C
    let step_regroup = c.nn_trans(&acac_ac, &aacc_ac, &aaa_ccc, left_rw, i2);

    // ── C-cube : (C·C)·C = ofRat(1/4)   (cbrt_cubed (1/4) hq hq1). ──
    // hq1 : 1/4 < 1.
    let hq1 = build_quarter_lt_one(c);
    let ccc_eq_ofq = Expr::apps(
        c.nnreal_cbrt_cubed.clone(),
        [quarter.clone(), hq.clone(), hq1],
    ); // (C·C)·C = ofRat(1/4)
    let of_q = c.ofrat(&quarter, &hq);

    // ── A-cube : (A·A)·A = ofRat((4·4)·4). ──
    let ff = c.rmul(four.clone(), four.clone()); // 4·4
    let fff = c.rmul(ff.clone(), four.clone()); // (4·4)·4
    let h_ff = c.rmul_nonneg(four.clone(), four.clone(), h4.clone(), h4.clone());
    let h_fff = c.rmul_nonneg(ff.clone(), four.clone(), h_ff.clone(), h4.clone());
    let of_ff = c.ofrat(&ff, &h_ff);
    let of_fff = c.ofrat(&fff, &h_fff);
    let aa_eq_offf = c.nn_ofrat_mul(&four, &four, &h4, &h4, &h_ff); // A·A = ofRat(4·4)
    let aaa_to_off_a = c.nn_congr_l(&bd, &aa, &of_ff, &a, aa_eq_offf); // (A·A)·A = ofRat(4·4)·A
    let off_a = c.nnmul(&of_ff, &a);
    let off_a_eq = c.nn_ofrat_mul(&ff, &four, &h_ff, &h4, &h_fff); // ofRat(4·4)·ofRat 4 = ofRat((4·4)·4)
    let aaa_eq_offf = c.nn_trans(&aaa, &off_a, &of_fff, aaa_to_off_a, off_a_eq);

    // ── Combine: ((A·A)·A)·((C·C)·C) = ofRat((4·4)·4)·ofRat(1/4) = ofRat(((4·4)·4)·(1/4)). ──
    // first rewrite (C·C)·C → ofRat(1/4) via ccc_eq_ofq, congr_mul_right.
    let aaa_ofq = c.nnmul(&aaa, &of_q); // ((A·A)·A)·ofRat(1/4)
    let ccc_to_ofq = c.nn_congr_r(&bd, &aaa, &ccc, &of_q, ccc_eq_ofq); // aaa·ccc = aaa·ofRat(1/4)
                                                                       // then rewrite (A·A)·A → ofRat((4·4)·4) via aaa_eq_offf, congr_mul_left.
    let offf_ofq = c.nnmul(&of_fff, &of_q); // ofRat((4·4)·4)·ofRat(1/4)
    let aaa_ofq_to_offf_ofq = c.nn_congr_l(&bd, &aaa, &of_fff, &of_q, aaa_eq_offf);
    // ofRat((4·4)·4)·ofRat(1/4) = ofRat(((4·4)·4)·(1/4))   ofRat_mul (fff)(1/4).
    let prod_rat = c.rmul(fff.clone(), quarter.clone()); // ((4·4)·4)·(1/4)
    let h_prod = c.rmul_nonneg(fff.clone(), quarter.clone(), h_fff.clone(), hq.clone());
    let of_prod = c.ofrat(&prod_rat, &h_prod);
    let offf_ofq_eq = c.nn_ofrat_mul(&fff, &quarter, &h_fff, &hq, &h_prod);

    // chain the combine: aaa_ccc = aaa·ofRat(1/4) = ofRat((4·4)·4)·ofRat(1/4) = ofRat(prod).
    let comb1 = c.nn_trans(
        &aaa_ccc,
        &aaa_ofq,
        &offf_ofq,
        ccc_to_ofq,
        aaa_ofq_to_offf_ofq,
    );
    let comb = c.nn_trans(&aaa_ccc, &offf_ofq, &of_prod, comb1, offf_ofq_eq);

    // ── ofRat(prod) = ofRat 16 via the Rat numeral bridge + ofRat-value congr. ──
    let rat_bridge = build_rat_64_quarter_bridge(c, &bd); // prod = 16
    let prod_to_16 = ofrat_value_congr(c, &bd, &prod_rat, s16, &h_prod, h16, rat_bridge);
    let ofrat16 = c.ofrat(s16, h16);

    // FULL: lhs = aaa_ccc (step_regroup) = ofRat(prod) (comb) = ofRat 16 (prod_to_16).
    let chain1 = c.nn_trans(&lhs, &aaa_ccc, &of_prod, step_regroup, comb);
    let full = c.nn_trans(&lhs, &of_prod, &ofrat16, chain1, prod_to_16);
    bd.finish(full)
}

/// The full `(ofRat cnt · twoFourThirds)³ = ofRat((16·cnt)·(cnt·cnt))` proof.
///
/// Mirrors `build_two_four_thirds_cubed_value`, but with `Q := ofRat cnt`
/// (abstract `cnt`) for the `A`-role and `V := twoFourThirds` for the `C`-role.
/// The `V`-cube uses the landed `NNReal.twoFourThirds_cubed` (`V³ = ofRat 16`)
/// instead of `cbrt_cubed`; the `Q`-cube is two `ofRat_mul`s; the final fold
/// combines to `ofRat(cnt³)·ofRat(16) = ofRat(cnt³·16)`, then a pure-`Rat` bridge
/// `(((cnt·cnt)·cnt)·16) = (16·cnt)·(cnt·cnt)` + `ofRat`-value congruence.
fn build_two_four_thirds_count_cubed_value(c: &TwoFourThirdsConsts) -> Expr {
    let mut bd = EnvDeclBuilder::new();
    let (cnt_id, cnt) = bd.fresh_local(c.rat.clone());
    let hcnt_ty = c.nonneg(cnt.clone());
    let (hcnt_id, hcnt) = bd.fresh_local(hcnt_ty.clone());

    // Q := ofRat cnt ; V := twoFourThirds ; qv := Q·V.
    let q = c.ofrat(&cnt, &hcnt);
    let v = c.nnreal_two_four_thirds.clone();
    let qv = c.nnmul(&q, &v);
    let lhs = c.nnmul(&c.nnmul(&qv, &qv), &qv);

    // ── Regroup (Q·V)·(Q·V)·(Q·V) → ((Q·Q)·Q)·((V·V)·V) ──
    let qq = c.nnmul(&q, &q);
    let vv = c.nnmul(&v, &v);
    let qvqv = c.nnmul(&qv, &qv); // (Q·V)·(Q·V)
    let qqvv = c.nnmul(&qq, &vv); // (Q·Q)·(V·V)
    let i1 = c.nn_mmm(&q, &v, &q, &v); // (Q·V)·(Q·V) = (Q·Q)·(V·V)
    let qqq = c.nnmul(&qq, &q); // (Q·Q)·Q
    let vvv = c.nnmul(&vv, &v); // (V·V)·V
    let i2 = c.nn_mmm(&qq, &vv, &q, &v); // ((Q·Q)·(V·V))·(Q·V) = ((Q·Q)·Q)·((V·V)·V)
    let qqvv_qv = c.nnmul(&qqvv, &qv);
    let qqq_vvv = c.nnmul(&qqq, &vvv);

    let left_rw = c.nn_congr_l(&bd, &qvqv, &qqvv, &qv, i1);
    let qvqv_qv = c.nnmul(&qvqv, &qv);
    let step_regroup = c.nn_trans(&qvqv_qv, &qqvv_qv, &qqq_vvv, left_rw, i2);

    // ── V-cube : (V·V)·V = ofRat 16   (landed twoFourThirds_cubed). ──
    let s16 = c.ofnat_lit(16);
    let h16 = c.ofnat_nonneg(16);
    let of16 = c.ofrat(&s16, &h16);
    let vvv_eq_of16 = c.nnreal_two_four_thirds_cubed.clone(); // (V·V)·V = ofRat 16

    // ── Q-cube : (Q·Q)·Q = ofRat((cnt·cnt)·cnt). ──
    let cc = c.rmul(cnt.clone(), cnt.clone()); // cnt·cnt
    let ccc = c.rmul(cc.clone(), cnt.clone()); // (cnt·cnt)·cnt
    let h_cc = c.rmul_nonneg(cnt.clone(), cnt.clone(), hcnt.clone(), hcnt.clone());
    let h_ccc = c.rmul_nonneg(cc.clone(), cnt.clone(), h_cc.clone(), hcnt.clone());
    let of_cc = c.ofrat(&cc, &h_cc);
    let of_ccc = c.ofrat(&ccc, &h_ccc);
    let qq_eq_ofcc = c.nn_ofrat_mul(&cnt, &cnt, &hcnt, &hcnt, &h_cc); // Q·Q = ofRat(cnt·cnt)
    let qqq_to_ofcc_q = c.nn_congr_l(&bd, &qq, &of_cc, &q, qq_eq_ofcc); // (Q·Q)·Q = ofRat(cnt·cnt)·Q
    let ofcc_q = c.nnmul(&of_cc, &q);
    let ofcc_q_eq = c.nn_ofrat_mul(&cc, &cnt, &h_cc, &hcnt, &h_ccc); // ofRat(cnt·cnt)·ofRat cnt = ofRat((cnt·cnt)·cnt)
    let qqq_eq_ofccc = c.nn_trans(&qqq, &ofcc_q, &of_ccc, qqq_to_ofcc_q, ofcc_q_eq);

    // ── Combine: ((Q·Q)·Q)·((V·V)·V) = ofRat((cnt·cnt)·cnt)·ofRat(16)
    //             = ofRat(((cnt·cnt)·cnt)·16). ──
    let qqq_of16 = c.nnmul(&qqq, &of16); // ((Q·Q)·Q)·ofRat 16
    let vvv_to_of16 = c.nn_congr_r(&bd, &qqq, &vvv, &of16, vvv_eq_of16); // qqq·vvv = qqq·ofRat 16
    let ofccc_of16 = c.nnmul(&of_ccc, &of16); // ofRat((cnt·cnt)·cnt)·ofRat 16
    let qqq_of16_to_ofccc_of16 = c.nn_congr_l(&bd, &qqq, &of_ccc, &of16, qqq_eq_ofccc);
    // ofRat((cnt·cnt)·cnt)·ofRat 16 = ofRat(((cnt·cnt)·cnt)·16)   ofRat_mul (ccc) 16.
    let prod_rat = c.rmul(ccc.clone(), s16.clone()); // ((cnt·cnt)·cnt)·16
    let h_prod = c.rmul_nonneg(ccc.clone(), s16.clone(), h_ccc.clone(), h16.clone());
    let of_prod = c.ofrat(&prod_rat, &h_prod);
    let ofccc_of16_eq = c.nn_ofrat_mul(&ccc, &s16, &h_ccc, &h16, &h_prod);

    let comb1 = c.nn_trans(
        &qqq_vvv,
        &qqq_of16,
        &ofccc_of16,
        vvv_to_of16,
        qqq_of16_to_ofccc_of16,
    );
    let comb = c.nn_trans(&qqq_vvv, &ofccc_of16, &of_prod, comb1, ofccc_of16_eq);

    // ── ofRat(prod) = ofRat((16·cnt)·(cnt·cnt)) via Rat bridge + ofRat-value congr. ──
    let (cube_target, h_cube) = c.cube16(&cnt, &hcnt); // ofRat((16·cnt)·(cnt·cnt))
    let cube_rat = c.rmul(
        c.rmul(s16.clone(), cnt.clone()),
        c.rmul(cnt.clone(), cnt.clone()),
    ); // (16·cnt)·(cnt·cnt)
    let rat_bridge = build_rat_count_cube_bridge(c, &bd, &cnt); // ((cnt·cnt)·cnt)·16 = (16·cnt)·(cnt·cnt)
    let prod_to_cube =
        ofrat_value_congr(c, &bd, &prod_rat, &cube_rat, &h_prod, &h_cube, rat_bridge);

    // FULL: lhs = qqq_vvv (step_regroup) = ofRat(prod) (comb) = cube_target (prod_to_cube).
    let chain1 = c.nn_trans(&lhs, &qqq_vvv, &of_prod, step_regroup, comb);
    let full = c.nn_trans(&lhs, &of_prod, &cube_target, chain1, prod_to_cube);

    let e = bd.mk_lam(hcnt_id, BinderInfo::Default, hcnt_ty, full);
    bd.finish(bd.mk_lam(cnt_id, BinderInfo::Default, c.rat.clone(), e))
}

/// The pure-`Rat` bridge `(((cnt·cnt)·cnt)·16) = (16·cnt)·(cnt·cnt)`.
///
/// ```text
/// ((cnt·cnt)·cnt)·16
///  = 16·((cnt·cnt)·cnt)        mul_comm
///  = 16·(cnt·(cnt·cnt))        congr_r 16 (mul_comm (cnt·cnt) cnt)
///  = (16·cnt)·(cnt·cnt)        symm(mul_assoc 16 cnt (cnt·cnt))
/// ```
fn build_rat_count_cube_bridge(
    c: &TwoFourThirdsConsts,
    parent: &EnvDeclBuilder,
    cnt: &Expr,
) -> Expr {
    let rat = c.rat.clone();
    let s16 = c.ofnat_lit(16);
    let cc = c.rmul(cnt.clone(), cnt.clone()); // cnt·cnt
    let ccc = c.rmul(cc.clone(), cnt.clone()); // (cnt·cnt)·cnt
    let cnt_cc = c.rmul(cnt.clone(), cc.clone()); // cnt·(cnt·cnt)
    let lhs0 = c.rmul(ccc.clone(), s16.clone()); // ((cnt·cnt)·cnt)·16

    // r1 : ((cnt·cnt)·cnt)·16 = 16·((cnt·cnt)·cnt)   mul_comm.
    let r1 = c.rmul_comm(ccc.clone(), s16.clone());
    let m1 = c.rmul(s16.clone(), ccc.clone()); // 16·((cnt·cnt)·cnt)

    // r2 : 16·((cnt·cnt)·cnt) = 16·(cnt·(cnt·cnt))   congr_r 16 (mul_comm (cnt·cnt) cnt).
    let comm = c.rmul_comm(cc.clone(), cnt.clone()); // (cnt·cnt)·cnt = cnt·(cnt·cnt)
    let f_r2 = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(rat.clone());
        let body = c.rmul(s16.clone(), w);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, rat.clone(), body))
    };
    let r2 = c.congr(&rat, ccc.clone(), cnt_cc.clone(), f_r2, comm);
    let m2 = c.rmul(s16.clone(), cnt_cc.clone()); // 16·(cnt·(cnt·cnt))

    // r3 : 16·(cnt·(cnt·cnt)) = (16·cnt)·(cnt·cnt)   symm(mul_assoc 16 cnt (cnt·cnt)).
    let target = c.rmul(c.rmul(s16.clone(), cnt.clone()), cc.clone()); // (16·cnt)·(cnt·cnt)
    let assoc = c.rmul_assoc(s16.clone(), cnt.clone(), cc.clone()); // (16·cnt)·(cnt·cnt) = 16·(cnt·(cnt·cnt))
    let r3 = c.symm(&rat, target.clone(), m2.clone(), assoc); // m2 = target

    let ch = c.rat_trans(lhs0.clone(), m1.clone(), m2.clone(), r1, r2);
    c.rat_trans(lhs0, m2, target, ch, r3)
}

/// `1/4 < 1` via `Rat.lt_of_ble_eq_false 1 (1/4) (h : ble 1 (1/4) = false)`.
/// `ble 1 (1/4)` native-reduces to `false` on the concrete reps, so
/// `Eq.refl Bool.false` discharges it; the result is `Rat.lt (1/4) 1`.
fn build_quarter_lt_one(c: &TwoFourThirdsConsts) -> Expr {
    let one = c.ofnat_lit(1);
    let quarter = c.one_quarter();
    let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
    let refl_false = Expr::apps(c.eq_refl1.clone(), [c.bool_ty.clone(), bool_false]);
    Expr::apps(
        Expr::const_(Name::from_string("Rat.lt_of_ble_eq_false"), vec![]),
        [one, quarter, refl_false],
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_two_four_thirds()
            .expect("init_algebra_nnreal_two_four_thirds");
        env.init_algebra_nnreal_two_four_thirds()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_two_four_thirds_cubed_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("NNReal.twoFourThirds_cubed");
        let info = env.get_const(&nm).expect("registered");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("NNReal.twoFourThirds_cubed must kernel-check: {e:?}"));
    }

    #[test]
    fn test_two_four_thirds_def_present() {
        let env = env();
        let nm = Name::from_string("NNReal.twoFourThirds");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Definition, "must be Definition");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("NNReal.twoFourThirds must kernel-check");
    }

    const THEOREMS: &[&str] = &[
        "NNReal.twoFourThirds_cubed",
        "NNReal.twoFourThirds_count_cubed",
    ];

    #[test]
    fn test_two_four_thirds_count_cubed_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("NNReal.twoFourThirds_count_cubed");
        let info = env.get_const(&nm).expect("registered");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("count-cube must kernel-check: {e:?}"));
    }

    #[test]
    fn test_two_four_thirds_cubed_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
