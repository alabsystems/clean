// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami dual `(4/3, 4)` two-point base — the σ-route attack on the HARD
//! analytic crux lemma (A) and its bankable sub-bricks.
//!
//! # The target (A)
//!
//! Over the homogeneity `a = 1` slice (`pow43Gen x = x · cbrtGen x = x^{4/3}`):
//!
//! ```text
//!   (A)   pow43Gen(1+t) + pow43Gen(1−t)  ≥  2 + (4/9)·t².
//! ```
//!
//! `½`-scaled this is EXACTLY the `hA` hypothesis consumed by the landed
//! assembly `BoolAnalysis.two_point_base_43_of_A` at `α := pow43Gen(1+t)`,
//! `β := pow43Gen(1−t)`, `S := 1 + (2/9)·t²` (so `H := ½·(α+β)`, `hA : ofRat S ≤ H`).
//!
//! # The σ-route (skeleton — see the agent task brief)
//!
//! Let `s := cbrtGen(1+t)`, `r := cbrtGen(1−t)`. Then `s³ = ofRat(1+t)`,
//! `r³ = ofRat(1−t)` (via `cbrtGen_cubed_at`), so `s³ + r³ = ofRat 2`. And
//! `pow43Gen(1+t) = ofRat(1+t)·s = s³·s = s⁴`, likewise `pow43Gen(1−t) = r⁴`.
//! Hence with `t = (s³−r³)/2` on the surface `s³+r³=2`:
//!
//! ```text
//!   (A) ⟺ s⁴ + r⁴ ≥ 2 + (4/9)t² ⟺ 9(s⁴+r⁴) + 4·s³r³ ≥ 22   [the ALL-NONNEG LHS' ≥ 22].
//! ```
//!
//! With `σ := s + r` the degree-9 ring identity holds in the `NNReal`
//! commutative semiring (verified by hand): on the surface `s³+r³=2`,
//!
//! ```text
//!   27·σ³·LHS' = 27·σ³·22 + (σ−2)²·Q2(σ),
//!   Q2(σ) = 4σ⁷+16σ⁶+21σ⁵−4σ⁴−100σ³+48σ²+46σ−8.
//! ```
//!
//! Since `(σ−2)²·Q2(σ) ≥ 0` and `27σ³ > 0`, `LHS' ≥ 22`. Two side-facts:
//!   (i)  `σ ≥ 5/4` (from `σ³ = 2 + 3srσ ≥ 2` and `(5/4)³ = 125/64 < 2`).
//!   (ii) `Q2(σ) ≥ 0` for `σ ≥ 5/4` (substitute `σ = 5/4 + w`, w ≥ 0; the
//!        expanded coefficients are all NONNEGATIVE rationals).
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! The two SELF-CONTAINED side-conditions of the σ-route, both
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only):
//!
//! - **`BoolAnalysis.two_point_sigma_ge_five_fourths`** (step (i), packaged):
//!   `∀ σ : NNReal, NNReal.le (ofRat 2) ((σ·σ)·σ) → NNReal.le (ofRat (5/4)) σ`.
//!   I.e. `σ³ ≥ 2 ⟹ σ ≥ 5/4`, via `(5/4)³ = 125/64 ≤ 2 ≤ σ³` and
//!   `NNReal.le_of_cube_le_cube`.
//!
//! - **`BoolAnalysis.two_point_q2_nonneg`** (step (ii)): `∀ w : NNReal,
//!   NNReal.le (ofRat 0) (Q2poly w)` where `Q2poly w` is the
//!   manifestly-nonnegative-coefficient expansion of `Q2(5/4+w)`,
//!   `Σ_{i=0}^{7} cᵢ·wⁱ` with the (verified) nonneg rationals
//!   `260577/4096, 329859/1024, 227313/256, 75195/64, 12411/16, 1089/4, 51, 4`.
//!   Proved by a `le_self_add` floor on the (positive) constant term `c₀`.
//!
//! NO `sorry` / `add_decl_unchecked` / `add_decl_structural` / `native_decide` /
//! `unsafe` / Axiom. FORBIDDEN: `Rat.dist`, `Real`/`Real.sqrt`.
//!
//! The two registered bricks DISCHARGE the two side-conditions of the σ-route.
//! The remaining (not-yet-landed) work is the degree-9 `NNReal`-semiring identity
//! itself (additive reformulation in nonneg variables) plus the cbrtGen
//! scale-witness plumbing establishing `s³+r³ = ofRat 2` and
//! `pow43Gen(1±t) = s⁴/r⁴`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached carrier atoms + smart-constructors for the σ-route sub-bricks.
struct LemmaAConsts {
    int_of_nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    rat_le: Expr,
    rat_mul_nonneg: Expr,
    rat_le_of_ble_eq_true: Expr,
    bool_c: Expr,
    bool_true: Expr,
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    eq_subst1: Expr,
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_add: Expr,
    nnreal_le: Expr,
    nnreal_of_rat: Expr,
    nnreal_ofrat_le_ofrat: Expr,
    nnreal_ofrat_mul: Expr,
    nnreal_le_trans: Expr,
    nnreal_le_self_add: Expr,
    nnreal_le_of_cube_le_cube: Expr,
    nnreal_cube_superadd: Expr,
    // PIECE-1 scale-witness plumbing (cbrtGen / pow43Gen / ofRat_add).
    rat_add: Expr,
    nnreal_cbrt_gen: Expr,
    nnreal_cbrt_gen_cubed_at: Expr,
    nnreal_pow43_gen: Expr,
    nnreal_ofrat_add: Expr,
}

impl LemmaAConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let kl = |s: &str| Expr::const_(Name::from_string(s), vec![l1.clone()]);
        Self {
            int_of_nat: k("Int.ofNat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            rat_le: k("Rat.le"),
            rat_mul_nonneg: k("Rat.mul_nonneg"),
            rat_le_of_ble_eq_true: k("Rat.le_of_ble_eq_true"),
            bool_c: k("Bool"),
            bool_true: k("Bool.true"),
            eq1: kl("Eq"),
            eq_refl1: kl("Eq.refl"),
            eq_symm1: kl("Eq.symm"),
            eq_trans1: kl("Eq.trans"),
            eq_subst1: kl("Eq.subst"),
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_add: k("NNReal.add"),
            nnreal_le: k("NNReal.le"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_ofrat_le_ofrat: k("NNReal.ofRat_le_ofRat"),
            nnreal_ofrat_mul: k("NNReal.ofRat_mul"),
            nnreal_le_trans: k("NNReal.le.trans"),
            nnreal_le_self_add: k("NNReal.le_self_add"),
            nnreal_le_of_cube_le_cube: k("NNReal.le_of_cube_le_cube"),
            nnreal_cube_superadd: k("NNReal.cube_superadd"),
            rat_add: k("Rat.add"),
            nnreal_cbrt_gen: k("NNReal.cbrtGen"),
            nnreal_cbrt_gen_cubed_at: k("NNReal.cbrtGen_cubed_at"),
            nnreal_pow43_gen: k("NNReal.pow43Gen"),
            nnreal_ofrat_add: k("NNReal.ofRat_add"),
        }
    }

    // ── Rat literal constructors ─────────────────────────────────────────────
    /// A `Nat` numeral built as the kernel-native `Literal::Nat` node (NOT a
    /// unary `Nat.succ` tower): O(limbs) to construct AND the form the native
    /// arith reducers (`get_nat_val`/`checked_mul_big`) recognise, so the
    /// `Rat.ble`/`Rat.mul` ground reductions over our LARGE coefficients
    /// (e.g. `260577/4096`) stay O(limbs) instead of SIGBUS-overflowing the
    /// kernel on a 260k-deep succ tower.
    fn nat_lit(&self, n: u64) -> Expr {
        Expr::nat_lit(n)
    }
    /// `Rat.mk (Int.ofNat num) den`.
    fn frac(&self, num: u64, den: u64) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.nat_lit(num)),
                self.nat_lit(den),
            ],
        )
    }
    fn rmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a.clone(), b.clone()])
    }
    fn rle(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a.clone(), b.clone()])
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn rmul_nonneg(&self, a: &Expr, b: &Expr, ha: &Expr, hb: &Expr) -> Expr {
        Expr::apps(
            self.rat_mul_nonneg.clone(),
            [a.clone(), b.clone(), ha.clone(), hb.clone()],
        )
    }
    fn refl_true(&self) -> Expr {
        Expr::apps(
            self.eq_refl1.clone(),
            [self.bool_c.clone(), self.bool_true.clone()],
        )
    }
    /// `0 ≤ Rat.mk (Int.ofNat num) den` for a positive literal fraction.
    fn lit_nonneg(&self, num: u64, den: u64) -> Expr {
        Expr::apps(
            self.rat_le_of_ble_eq_true.clone(),
            [self.rat_zero.clone(), self.frac(num, den), self.refl_true()],
        )
    }
    /// `0 ≤ Rat.zero` (`Rat.ble 0 0 = true`).
    fn zero_nonneg(&self) -> Expr {
        Expr::apps(
            self.rat_le_of_ble_eq_true.clone(),
            [
                self.rat_zero.clone(),
                self.rat_zero.clone(),
                self.refl_true(),
            ],
        )
    }
    /// `a ≤ b` (Rat) for positive literal fractions `a,b`, via boolean reflection.
    fn lit_le(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.rat_le_of_ble_eq_true.clone(),
            [a.clone(), b.clone(), self.refl_true()],
        )
    }

    // ── NNReal constructors ──────────────────────────────────────────────────
    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn nnadd(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a.clone(), b.clone()])
    }
    fn nnle(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a.clone(), b.clone()])
    }
    /// `mul (mul a a) a` (left-nested cube), matching `cube_le_cube_of_le`.
    fn nncube(&self, a: &Expr) -> Expr {
        self.nnmul(&self.nnmul(a, a), a)
    }
    fn ofrat(&self, x: &Expr, h: &Expr) -> Expr {
        Expr::apps(self.nnreal_of_rat.clone(), [x.clone(), h.clone()])
    }
    /// `NNReal.ofRat (num/den) (nonneg)`.
    fn of_frac(&self, num: u64, den: u64) -> Expr {
        self.ofrat(&self.frac(num, den), &self.lit_nonneg(num, den))
    }
    /// `NNReal.ofRat Rat.zero (0 ≤ 0)`.
    fn of_zero(&self) -> Expr {
        self.ofrat(&self.rat_zero.clone(), &self.zero_nonneg())
    }
    /// `ofRat_le_ofRat a b ha hb (a≤b) : NNReal.le (ofRat a ha)(ofRat b hb)`.
    fn ofrat_le_ofrat(&self, a: &Expr, b: &Expr, ha: &Expr, hb: &Expr, hle: Expr) -> Expr {
        Expr::apps(
            self.nnreal_ofrat_le_ofrat.clone(),
            [a.clone(), b.clone(), ha.clone(), hb.clone(), hle],
        )
    }
    /// `NNReal.ofRat_mul a b ha hb hab : ofRat a · ofRat b = ofRat (a·b)`.
    fn ofrat_mul(&self, a: &Expr, b: &Expr, ha: &Expr, hb: &Expr, hab: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_ofrat_mul.clone(),
            [a.clone(), b.clone(), ha.clone(), hb.clone(), hab.clone()],
        )
    }
    /// `NNReal.le.trans a b c (a≤b)(b≤c) : a ≤ c`.
    fn le_trans(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.nnreal_le_trans.clone(),
            [a.clone(), b.clone(), cc.clone(), h1, h2],
        )
    }
    /// `NNReal.le_self_add a b : NNReal.le a (NNReal.add a b)`.
    fn le_self_add(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_le_self_add.clone(), [a.clone(), b.clone()])
    }
    /// `NNReal.cube_superadd u v : NNReal.le (u³ + v³) ((u+v)³)`
    /// (cubes left-nested `(a·a)·a`).
    fn cube_superadd(&self, u: &Expr, v: &Expr) -> Expr {
        Expr::apps(self.nnreal_cube_superadd.clone(), [u.clone(), v.clone()])
    }
    /// `NNReal.le_of_cube_le_cube a b (a³≤b³) : NNReal.le a b`.
    fn le_of_cube_le_cube(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.nnreal_le_of_cube_le_cube.clone(),
            [a.clone(), b.clone(), h],
        )
    }

    // ── PIECE-1 scale-witness plumbing (Rat add + cbrtGen / pow43Gen) ─────────
    /// `Rat.add a b`.
    fn radd(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a.clone(), b.clone()])
    }
    /// `NNReal.cbrtGen s r hs` — the scaled cube-root carrier value.
    fn cbrt_gen(&self, s: &Expr, r: &Expr, hs: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_cbrt_gen.clone(),
            [s.clone(), r.clone(), hs.clone()],
        )
    }
    /// `NNReal.pow43Gen x s r hx hs := ofRat x hx · cbrtGen s r hs` (reducible).
    fn pow43_gen(&self, x: &Expr, s: &Expr, r: &Expr, hx: &Expr, hs: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_pow43_gen.clone(),
            [x.clone(), s.clone(), r.clone(), hx.clone(), hs.clone()],
        )
    }
    /// `NNReal.cbrtGen_cubed_at x s r hx hs hr hr1 heq :
    ///    ((c·c)·c) = ofRat x hx`  where `c := cbrtGen s r hs` (left-nested cube).
    #[allow(clippy::too_many_arguments)]
    fn cbrt_gen_cubed_at(
        &self,
        x: &Expr,
        s: &Expr,
        r: &Expr,
        hx: &Expr,
        hs: &Expr,
        hr: &Expr,
        hr1: &Expr,
        heq: &Expr,
    ) -> Expr {
        Expr::apps(
            self.nnreal_cbrt_gen_cubed_at.clone(),
            [
                x.clone(),
                s.clone(),
                r.clone(),
                hx.clone(),
                hs.clone(),
                hr.clone(),
                hr1.clone(),
                heq.clone(),
            ],
        )
    }
    /// `NNReal.ofRat_add a b ha hb hab : add (ofRat a)(ofRat b) = ofRat (a+b)`.
    fn ofrat_add(&self, a: &Expr, b: &Expr, ha: &Expr, hb: &Expr, hab: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_ofrat_add.clone(),
            [a.clone(), b.clone(), ha.clone(), hb.clone(), hab.clone()],
        )
    }
    // ── Eq.{1} over NNReal ────────────────────────────────────────────────────
    fn eq_nn(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.eq1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone()],
        )
    }
    fn refl_nn(&self, a: &Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.nnreal.clone(), a.clone()])
    }
    fn symm_nn(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_symm1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone(), h],
        )
    }
    fn trans_nn(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [
                self.nnreal.clone(),
                a.clone(),
                b.clone(),
                cc.clone(),
                h1,
                h2,
            ],
        )
    }
    fn subst_nn(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.nnreal.clone(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }
    /// `p·a = q·a` from `h : p = q` (NNReal), via `Eq.subst` on the left factor.
    fn congr_mul_left(
        &self,
        parent: &EnvDeclBuilder,
        p: &Expr,
        q: &Expr,
        a: &Expr,
        h: Expr,
    ) -> Expr {
        let pa = self.nnmul(p, a);
        let motive = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = m.fresh_local(self.nnreal.clone());
            let body = self.eq_nn(&pa, &self.nnmul(&z, a));
            m.finish_child(m.mk_lam(z_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.subst_nn(motive, p, q, h, self.refl_nn(&pa))
    }

    /// `a·p = a·q` from `h : p = q` (NNReal), via `Eq.subst` on the right factor.
    fn congr_mul_right(
        &self,
        parent: &EnvDeclBuilder,
        a: &Expr,
        p: &Expr,
        q: &Expr,
        h: Expr,
    ) -> Expr {
        let ap = self.nnmul(a, p);
        let motive = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = m.fresh_local(self.nnreal.clone());
            let body = self.eq_nn(&ap, &self.nnmul(a, &z));
            m.finish_child(m.mk_lam(z_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.subst_nn(motive, p, q, h, self.refl_nn(&ap))
    }

    /// `p+a = q+a` from `h : p = q` (NNReal `add`), via `Eq.subst` on the left
    /// summand.
    fn congr_add_left(
        &self,
        parent: &EnvDeclBuilder,
        p: &Expr,
        q: &Expr,
        a: &Expr,
        h: Expr,
    ) -> Expr {
        let pa = self.nnadd(p, a);
        let motive = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = m.fresh_local(self.nnreal.clone());
            let body = self.eq_nn(&pa, &self.nnadd(&z, a));
            m.finish_child(m.mk_lam(z_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.subst_nn(motive, p, q, h, self.refl_nn(&pa))
    }

    /// `a+p = a+q` from `h : p = q` (NNReal `add`), via `Eq.subst` on the right
    /// summand.
    fn congr_add_right(
        &self,
        parent: &EnvDeclBuilder,
        a: &Expr,
        p: &Expr,
        q: &Expr,
        h: Expr,
    ) -> Expr {
        let ap = self.nnadd(a, p);
        let motive = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = m.fresh_local(self.nnreal.clone());
            let body = self.eq_nn(&ap, &self.nnadd(a, &z));
            m.finish_child(m.mk_lam(z_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.subst_nn(motive, p, q, h, self.refl_nn(&ap))
    }

    /// `Eq Rat a b` (homogeneous equality at `Rat`).
    fn eq_rat(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), a.clone(), b.clone()])
    }
    /// `@Eq.subst Rat motive a b h_eq h` (transport at `Rat`).
    fn subst_rat(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat.clone(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }

    /// `ofRat a ha = ofRat b hb` from `he : Eq Rat a b`. The nonneg proof is a
    /// `Prop`, hence proof-irrelevant, so we transport over the dependent
    /// `ofRat`'s VALUE argument with a `∀ (hz : 0≤z)`-quantified motive: the base
    /// `refl (ofRat a ha)` retypes against any `ofRat a hz` (proof irrelevance),
    /// and `Eq.subst he` swaps `a → b`. Applying the result to `hb` closes it.
    fn ofrat_bridge(&self, a: &Expr, b: &Expr, ha: &Expr, hb: &Expr, he: Expr) -> Expr {
        let parent = EnvDeclBuilder::new();
        let of_a = self.ofrat(a, ha);
        // motive : fun (z : Rat) => ∀ (hz : 0 ≤ z), Eq NNReal (ofRat a ha)(ofRat z hz).
        let motive = {
            let mut m = EnvDeclBuilder::child_of(&parent);
            let (z_id, z) = m.fresh_local(self.rat.clone());
            let hz_ty = self.rle(&self.rat_zero.clone(), &z);
            let (hz_id, hz) = m.fresh_local(hz_ty.clone());
            let body = self.eq_nn(&of_a, &self.ofrat(&z, &hz));
            let inner = m.mk_pi(hz_id, BinderInfo::Default, hz_ty, body);
            m.finish_child(m.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), inner))
        };
        // base : ∀ (hz : 0 ≤ a), Eq NNReal (ofRat a ha)(ofRat a hz)
        //      := fun hz => Eq.refl (ofRat a ha)   [ofRat a hz ≡ ofRat a ha by PI].
        let base = {
            let mut bb = EnvDeclBuilder::child_of(&parent);
            let hz_ty = self.rle(&self.rat_zero.clone(), a);
            let (hz_id, _hz) = bb.fresh_local(hz_ty.clone());
            let refl = self.refl_nn(&of_a);
            bb.finish_child(bb.mk_lam(hz_id, BinderInfo::Default, hz_ty, refl))
        };
        // transported : ∀ (hz : 0 ≤ b), Eq NNReal (ofRat a ha)(ofRat b hz).
        let transported = self.subst_rat(motive, a, b, he, base);
        // apply to hb.
        Expr::app(transported, hb.clone())
    }
}

impl Environment {
    /// Initialize the σ-route sub-bricks of the two-point base lemma (A).
    ///
    /// Pulls in the (A)-conditional assembly + leg (B) + all bricks (via
    /// `init_boolean_analysis_two_point_base_legs`), the `NNReal` order/algebra
    /// surface, then registers the two self-contained σ-route side-conditions.
    /// Idempotent. No axiom added or removed.
    pub fn init_boolean_analysis_two_point_base_lemma_a(&mut self) -> Result<(), EnvError> {
        // The assembly + leg (B) + the full leg-brick surface (also Rat order +
        // NNReal.ofRat_mul + ofRat_le_ofRat + le.trans + Rat.mul_nonneg).
        self.init_boolean_analysis_two_point_base_legs()?;
        // NNReal order bricks used by the σ-route sub-lemmas.
        self.init_algebra_nnreal_le_self_add()?; // NNReal.le_self_add
        self.init_algebra_nnreal_reverse_cube()?; // NNReal.le_of_cube_le_cube
        self.init_algebra_nnreal_cube_superadd()?; // NNReal.cube_superadd
                                                   // PIECE-1 scale-witness plumbing deps.
        self.init_algebra_nnreal_cbrt_gen()?; // cbrtGen, cbrtGen_cubed_at, pow43Gen
        self.init_algebra_nnreal_finsum_ofrat()?; // NNReal.ofRat_add
        self.init_eq()?;

        let c = LemmaAConsts::new();
        self.register_two_point_sigma_ge_five_fourths(&c)?;
        self.register_two_point_q2_nonneg(&c)?;
        self.register_two_point_sigma_cube_ge_two(&c)?;
        // PIECE 1 — scale-witness plumbing.
        self.register_two_point_s3_r3_eq_two(&c)?;
        self.register_two_point_pow43_eq_s4(&c)?;
        Ok(())
    }

    /// `BoolAnalysis.two_point_sigma_ge_five_fourths` — step (i) of the σ-route.
    fn register_two_point_sigma_ge_five_fourths(
        &mut self,
        c: &LemmaAConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.two_point_sigma_ge_five_fourths");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_sigma_ge_five_fourths(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.two_point_q2_nonneg` — step (ii) of the σ-route.
    fn register_two_point_q2_nonneg(&mut self, c: &LemmaAConsts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.two_point_q2_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_q2_nonneg(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.two_point_sigma_cube_ge_two` — the surface→cube step that
    /// feeds step (i): `∀ s r : NNReal, ofRat 2 ≤ s³+r³ → ofRat 2 ≤ (s+r)³`.
    /// Composed with `two_point_sigma_ge_five_fourths` it yields `σ ≥ 5/4` from
    /// the surface `s³+r³ = ofRat 2` directly (`σ³ ≥ s³+r³ = 2` via
    /// `NNReal.cube_superadd`).
    fn register_two_point_sigma_cube_ge_two(&mut self, c: &LemmaAConsts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.two_point_sigma_cube_ge_two");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_sigma_cube_ge_two(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.two_point_s3_r3_eq_two` (PIECE 1) — the surface equation
    /// `s³ + r³ = ofRat 2` from the two cube facts + the rational `xp+xm = 2`.
    fn register_two_point_s3_r3_eq_two(&mut self, c: &LemmaAConsts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.two_point_s3_r3_eq_two");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_s3_r3_eq_two(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.two_point_pow43_eq_s4` (PIECE 1) — `pow43Gen x s r = s⁴`
    /// where `s := cbrtGen s r hs`, via the reducible `pow43Gen` unfold + the
    /// cube fact `s³ = ofRat x` (`cbrtGen_cubed_at`).
    fn register_two_point_pow43_eq_s4(&mut self, c: &LemmaAConsts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.two_point_pow43_eq_s4");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_pow43_eq_s4(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `(type, value)` of the surface→cube step:
/// `∀ s r : NNReal, ofRat 2 ≤ s³+r³ → ofRat 2 ≤ (s+r)³`.
///
/// Proof. `cube_superadd s r : s³+r³ ≤ (s+r)³`; chain `ofRat 2 ≤ s³+r³ ≤ (s+r)³`
/// by `le.trans`.
fn build_sigma_cube_ge_two(c: &LemmaAConsts) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (s_id, s) = b.fresh_local(c.nnreal.clone());
        let (r_id, r) = b.fresh_local(c.nnreal.clone());
        let of2 = c.of_frac(2, 1);
        let sum_cubes = c.nnadd(&c.nncube(&s), &c.nncube(&r));
        let sigma = c.nnadd(&s, &r);
        let sigma_cube = c.nncube(&sigma);
        let hyp_ty = c.nnle(&of2, &sum_cubes);
        let (h_id, _h) = b.fresh_local(hyp_ty.clone());
        let concl = c.nnle(&of2, &sigma_cube);
        let e = b.mk_pi(h_id, BinderInfo::Default, hyp_ty, concl);
        let e = b.mk_pi(r_id, BinderInfo::Default, c.nnreal.clone(), e);
        b.finish(b.mk_pi(s_id, BinderInfo::Default, c.nnreal.clone(), e))
    };
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (s_id, s) = b.fresh_local(c.nnreal.clone());
        let (r_id, r) = b.fresh_local(c.nnreal.clone());
        let of2 = c.of_frac(2, 1);
        let sum_cubes = c.nnadd(&c.nncube(&s), &c.nncube(&r));
        let sigma = c.nnadd(&s, &r);
        let sigma_cube = c.nncube(&sigma);
        let hyp_ty = c.nnle(&of2, &sum_cubes);
        let (h_id, h) = b.fresh_local(hyp_ty.clone());

        // superadd : s³+r³ ≤ (s+r)³.
        let superadd = c.cube_superadd(&s, &r);
        // body : ofRat 2 ≤ (s+r)³ := le.trans (ofRat 2)(s³+r³)((s+r)³) h superadd.
        let body = c.le_trans(&of2, &sum_cubes, &sigma_cube, h, superadd);

        let e = b.mk_lam(h_id, BinderInfo::Default, hyp_ty, body);
        let e = b.mk_lam(r_id, BinderInfo::Default, c.nnreal.clone(), e);
        b.finish(b.mk_lam(s_id, BinderInfo::Default, c.nnreal.clone(), e))
    };
    (ty, value)
}

// ─── PIECE 1 — scale-witness plumbing ────────────────────────────────────────

/// `(type, value)` of PIECE-1 brick `two_point_s3_r3_eq_two`:
///
/// ```text
///   ∀ (cc dd : NNReal)(xp xm : Rat)
///     (hxp : 0≤xp)(hxm : 0≤xm)(hsum : 0≤(xp+xm))
///     (hc : ((cc·cc)·cc) = ofRat xp hxp)        -- cc³ = ofRat(1+t)
///     (hd : ((dd·dd)·dd) = ofRat xm hxm)        -- dd³ = ofRat(1−t)
///     (he : Eq Rat (xp+xm) 2),                  -- (1+t)+(1−t) = 2
///       Eq NNReal (add ((cc·cc)·cc) ((dd·dd)·dd)) (ofRat 2 h2).
/// ```
///
/// Proof chain (all `Eq.subst`/`Eq.trans`, no analysis):
///   `cc³ + dd³ =[hc on left] ofRat xp + dd³ =[hd on right] ofRat xp + ofRat xm`
///   `=[ofRat_add] ofRat (xp+xm) hsum =[ofrat_bridge he] ofRat 2 h2`.
fn build_s3_r3_eq_two(c: &LemmaAConsts) -> (Expr, Expr) {
    // shared binder schema
    let schema = |b: &mut EnvDeclBuilder| {
        let (cc_id, cc) = b.fresh_local(c.nnreal.clone());
        let (dd_id, dd) = b.fresh_local(c.nnreal.clone());
        let (xp_id, xp) = b.fresh_local(c.rat.clone());
        let (xm_id, xm) = b.fresh_local(c.rat.clone());
        let hxp_ty = c.rle(&c.rat_zero.clone(), &xp);
        let (hxp_id, hxp) = b.fresh_local(hxp_ty.clone());
        let hxm_ty = c.rle(&c.rat_zero.clone(), &xm);
        let (hxm_id, hxm) = b.fresh_local(hxm_ty.clone());
        let sum = c.radd(&xp, &xm);
        let hsum_ty = c.rle(&c.rat_zero.clone(), &sum);
        let (hsum_id, hsum) = b.fresh_local(hsum_ty.clone());
        let cc3 = c.nncube(&cc);
        let dd3 = c.nncube(&dd);
        let hc_ty = c.eq_nn(&cc3, &c.ofrat(&xp, &hxp));
        let (hc_id, hc) = b.fresh_local(hc_ty.clone());
        let hd_ty = c.eq_nn(&dd3, &c.ofrat(&xm, &hxm));
        let (hd_id, hd) = b.fresh_local(hd_ty.clone());
        let two = c.frac(2, 1);
        let he_ty = c.eq_rat(&sum, &two);
        let (he_id, he) = b.fresh_local(he_ty.clone());
        (
            (
                cc_id, dd_id, xp_id, xm_id, hxp_id, hxm_id, hsum_id, hc_id, hd_id, he_id,
            ),
            (
                cc, dd, xp, xm, hxp, hxm, hsum, hc, hd, he, sum, cc3, dd3, hxp_ty, hxm_ty, hsum_ty,
                hc_ty, hd_ty, he_ty,
            ),
        )
    };

    let two_h = c.lit_nonneg(2, 1);
    let of2 = c.of_frac(2, 1);

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (ids, vals) = schema(&mut b);
        let (cc_id, dd_id, xp_id, xm_id, hxp_id, hxm_id, hsum_id, hc_id, hd_id, he_id) = ids;
        let (
            _cc,
            _dd,
            _xp,
            _xm,
            _hxp,
            _hxm,
            _hsum,
            _hc,
            _hd,
            _he,
            _sum,
            cc3,
            dd3,
            hxp_ty,
            hxm_ty,
            hsum_ty,
            hc_ty,
            hd_ty,
            he_ty,
        ) = vals;
        let concl = c.eq_nn(&c.nnadd(&cc3, &dd3), &of2);
        let e = b.mk_pi(he_id, BinderInfo::Default, he_ty, concl);
        let e = b.mk_pi(hd_id, BinderInfo::Default, hd_ty, e);
        let e = b.mk_pi(hc_id, BinderInfo::Default, hc_ty, e);
        let e = b.mk_pi(hsum_id, BinderInfo::Default, hsum_ty, e);
        let e = b.mk_pi(hxm_id, BinderInfo::Default, hxm_ty, e);
        let e = b.mk_pi(hxp_id, BinderInfo::Default, hxp_ty, e);
        let e = b.mk_pi(xm_id, BinderInfo::Default, c.rat.clone(), e);
        let e = b.mk_pi(xp_id, BinderInfo::Default, c.rat.clone(), e);
        let e = b.mk_pi(dd_id, BinderInfo::Default, c.nnreal.clone(), e);
        b.finish(b.mk_pi(cc_id, BinderInfo::Default, c.nnreal.clone(), e))
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (ids, vals) = schema(&mut b);
        let (cc_id, dd_id, xp_id, xm_id, hxp_id, hxm_id, hsum_id, hc_id, hd_id, he_id) = ids;
        let (
            _cc,
            _dd,
            xp,
            xm,
            hxp,
            hxm,
            hsum,
            hc,
            hd,
            he,
            sum,
            cc3,
            dd3,
            hxp_ty,
            hxm_ty,
            hsum_ty,
            hc_ty,
            hd_ty,
            he_ty,
        ) = vals;

        let of_xp = c.ofrat(&xp, &hxp);
        let of_xm = c.ofrat(&xm, &hxm);

        // step1 : cc³ + dd³ = ofRat xp + dd³   (rewrite LEFT summand via hc).
        let lhs0 = c.nnadd(&cc3, &dd3);
        let mid1 = c.nnadd(&of_xp, &dd3);
        let step1 = c.congr_add_left(&b, &cc3, &of_xp, &dd3, hc);
        // step2 : ofRat xp + dd³ = ofRat xp + ofRat xm   (rewrite RIGHT summand via hd).
        let mid2 = c.nnadd(&of_xp, &of_xm);
        let step2 = c.congr_add_right(&b, &of_xp, &dd3, &of_xm, hd);
        // s12 : cc³ + dd³ = ofRat xp + ofRat xm.
        let s12 = c.trans_nn(&lhs0, &mid1, &mid2, step1, step2);

        // step3 : ofRat xp + ofRat xm = ofRat (xp+xm) hsum  (NNReal.ofRat_add).
        let of_sum = c.ofrat(&sum, &hsum);
        let step3 = c.ofrat_add(&xp, &xm, &hxp, &hxm, &hsum);
        // s13 : cc³ + dd³ = ofRat (xp+xm) hsum.
        let s13 = c.trans_nn(&lhs0, &mid2, &of_sum, s12, step3);

        // step4 : ofRat (xp+xm) hsum = ofRat 2 h2  (ofrat_bridge along he).
        let two = c.frac(2, 1);
        let step4 = c.ofrat_bridge(&sum, &two, &hsum, &two_h, he);
        // body : cc³ + dd³ = ofRat 2 h2.
        let body = c.trans_nn(&lhs0, &of_sum, &of2, s13, step4);

        let e = b.mk_lam(he_id, BinderInfo::Default, he_ty, body);
        let e = b.mk_lam(hd_id, BinderInfo::Default, hd_ty, e);
        let e = b.mk_lam(hc_id, BinderInfo::Default, hc_ty, e);
        let e = b.mk_lam(hsum_id, BinderInfo::Default, hsum_ty, e);
        let e = b.mk_lam(hxm_id, BinderInfo::Default, hxm_ty, e);
        let e = b.mk_lam(hxp_id, BinderInfo::Default, hxp_ty, e);
        let e = b.mk_lam(xm_id, BinderInfo::Default, c.rat.clone(), e);
        let e = b.mk_lam(xp_id, BinderInfo::Default, c.rat.clone(), e);
        let e = b.mk_lam(dd_id, BinderInfo::Default, c.nnreal.clone(), e);
        b.finish(b.mk_lam(cc_id, BinderInfo::Default, c.nnreal.clone(), e))
    };

    (ty, value)
}

/// `(type, value)` of PIECE-1 brick `two_point_pow43_eq_s4`:
///
/// ```text
///   ∀ (x s r : Rat)(hx : 0≤x)(hs : 0≤s)(hr : 0≤r)(hr1 : r<1)
///     (heq : Eq Rat x (((s·s)·s)·r)),
///       Eq NNReal (pow43Gen x s r hx hs) ((((cc·cc)·cc)·cc))
///   where cc := cbrtGen s r hs.
/// ```
///
/// Proof. `pow43Gen x s r hx hs ≡ ofRat x hx · cc` (reducible `pow43Gen` unfold,
/// DEFEQ). `cbrtGen_cubed_at` gives `(cc·cc)·cc = ofRat x hx`; its symm rewrites
/// the LEFT factor `ofRat x hx` of `ofRat x hx · cc` into `(cc·cc)·cc`, yielding
/// `pow43Gen … = ((cc·cc)·cc)·cc = cc⁴`. The defeq `pow43Gen ≡ ofRat x · cc` is
/// discharged by stating the goal LHS as `pow43Gen …` and seeding the rewrite's
/// base `refl` at `ofRat x · cc` (kernel unifies them).
fn build_pow43_eq_s4(c: &LemmaAConsts) -> (Expr, Expr) {
    let lt = |a: &Expr, b: &Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.lt"), vec![]),
            [a.clone(), b.clone()],
        )
    };
    let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
    // ((s·s)·s)·r over Rat.
    let sss_r = |s: &Expr, r: &Expr| {
        let ss = c.rmul(s, s);
        let sss = c.rmul(&ss, s);
        c.rmul(&sss, r)
    };

    let schema = |b: &mut EnvDeclBuilder| {
        let (x_id, x) = b.fresh_local(c.rat.clone());
        let (s_id, s) = b.fresh_local(c.rat.clone());
        let (r_id, r) = b.fresh_local(c.rat.clone());
        let hx_ty = c.rle(&c.rat_zero.clone(), &x);
        let (hx_id, hx) = b.fresh_local(hx_ty.clone());
        let hs_ty = c.rle(&c.rat_zero.clone(), &s);
        let (hs_id, hs) = b.fresh_local(hs_ty.clone());
        let hr_ty = c.rle(&c.rat_zero.clone(), &r);
        let (hr_id, hr) = b.fresh_local(hr_ty.clone());
        let hr1_ty = lt(&r, &rat_one);
        let (hr1_id, hr1) = b.fresh_local(hr1_ty.clone());
        let sssr = sss_r(&s, &r);
        let heq_ty = c.eq_rat(&x, &sssr);
        let (heq_id, heq) = b.fresh_local(heq_ty.clone());
        (
            (x_id, s_id, r_id, hx_id, hs_id, hr_id, hr1_id, heq_id),
            (
                x, s, r, hx, hs, hr, hr1, heq, hx_ty, hs_ty, hr_ty, hr1_ty, heq_ty,
            ),
        )
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (ids, vals) = schema(&mut b);
        let (x_id, s_id, r_id, hx_id, hs_id, hr_id, hr1_id, heq_id) = ids;
        let (x, s, r, hx, hs, _hr, _hr1, _heq, hx_ty, hs_ty, hr_ty, hr1_ty, heq_ty) = vals;
        let cc = c.cbrt_gen(&s, &r, &hs);
        let cc4 = c.nnmul(&c.nncube(&cc), &cc); // ((cc·cc)·cc)·cc
        let pw = c.pow43_gen(&x, &s, &r, &hx, &hs);
        let concl = c.eq_nn(&pw, &cc4);
        let e = b.mk_pi(heq_id, BinderInfo::Default, heq_ty, concl);
        let e = b.mk_pi(hr1_id, BinderInfo::Default, hr1_ty, e);
        let e = b.mk_pi(hr_id, BinderInfo::Default, hr_ty, e);
        let e = b.mk_pi(hs_id, BinderInfo::Default, hs_ty, e);
        let e = b.mk_pi(hx_id, BinderInfo::Default, hx_ty, e);
        let e = b.mk_pi(r_id, BinderInfo::Default, c.rat.clone(), e);
        let e = b.mk_pi(s_id, BinderInfo::Default, c.rat.clone(), e);
        b.finish(b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e))
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (ids, vals) = schema(&mut b);
        let (x_id, s_id, r_id, hx_id, hs_id, hr_id, hr1_id, heq_id) = ids;
        let (x, s, r, hx, hs, hr, hr1, heq, hx_ty, hs_ty, hr_ty, hr1_ty, heq_ty) = vals;
        let cc = c.cbrt_gen(&s, &r, &hs);
        let cc3 = c.nncube(&cc);
        let of_x = c.ofrat(&x, &hx);
        // cube : (cc·cc)·cc = ofRat x hx   (cbrtGen_cubed_at).
        let cube = c.cbrt_gen_cubed_at(&x, &s, &r, &hx, &hs, &hr, &hr1, &heq);
        // cube_symm : ofRat x hx = (cc·cc)·cc.
        let cube_symm = c.symm_nn(&cc3, &of_x, cube);
        // congr_mul_left rewrites the LEFT factor of  (ofRat x hx) · cc :
        //   (ofRat x hx)·cc = ((cc·cc)·cc)·cc  = cc⁴.
        // The goal LHS `pow43Gen x s r hx hs` is reducible-defeq to `ofRat x · cc`,
        // so this term (typed `ofRat x · cc = cc⁴`) checks against `pow43Gen = cc⁴`.
        let body = c.congr_mul_left(&b, &of_x, &cc3, &cc, cube_symm);

        let e = b.mk_lam(heq_id, BinderInfo::Default, heq_ty, body);
        let e = b.mk_lam(hr1_id, BinderInfo::Default, hr1_ty, e);
        let e = b.mk_lam(hr_id, BinderInfo::Default, hr_ty, e);
        let e = b.mk_lam(hs_id, BinderInfo::Default, hs_ty, e);
        let e = b.mk_lam(hx_id, BinderInfo::Default, hx_ty, e);
        let e = b.mk_lam(r_id, BinderInfo::Default, c.rat.clone(), e);
        let e = b.mk_lam(s_id, BinderInfo::Default, c.rat.clone(), e);
        b.finish(b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e))
    };

    (ty, value)
}

/// `(type, value)` of step (i): `σ³ ≥ ofRat 2 ⟹ σ ≥ ofRat (5/4)`.
///
/// Proof. With `q := ofRat (5/4)`, `q³ ≤ ofRat 2` (the cube-fold to `ofRat
/// (125/64)` via two `ofRat_mul`, then the literal `125/64 ≤ 2`). Chain
/// `q³ ≤ ofRat 2 ≤ σ³` (`le.trans` with the hypothesis), then
/// `NNReal.le_of_cube_le_cube q σ` lifts to `q ≤ σ`.
fn build_sigma_ge_five_fourths(c: &LemmaAConsts) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (sig_id, sig) = b.fresh_local(c.nnreal.clone());
        let of2 = c.of_frac(2, 1);
        let sig_cube = c.nncube(&sig);
        let hyp_ty = c.nnle(&of2, &sig_cube);
        let (h_id, _h) = b.fresh_local(hyp_ty.clone());
        let q = c.of_frac(5, 4);
        let concl = c.nnle(&q, &sig);
        let e = b.mk_pi(h_id, BinderInfo::Default, hyp_ty, concl);
        b.finish(b.mk_pi(sig_id, BinderInfo::Default, c.nnreal.clone(), e))
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (sig_id, sig) = b.fresh_local(c.nnreal.clone());
        let of2 = c.of_frac(2, 1);
        let sig_cube = c.nncube(&sig);
        let hyp_ty = c.nnle(&of2, &sig_cube);
        let (h_id, h) = b.fresh_local(hyp_ty.clone());
        let q = c.of_frac(5, 4);
        let q_cube = c.nncube(&q);

        // q3_le_2 : q³ ≤ ofRat 2.
        let q3_le_2 = build_q_cube_le_two(c, &b);
        // q3_le_sig3 : q³ ≤ σ³ := le.trans q³ (ofRat 2) σ³ q3_le_2 h.
        let q3_le_sig3 = c.le_trans(&q_cube, &of2, &sig_cube, q3_le_2, h.clone());
        // q ≤ σ := le_of_cube_le_cube q σ q3_le_sig3.
        let body = c.le_of_cube_le_cube(&q, &sig, q3_le_sig3);

        let e = b.mk_lam(h_id, BinderInfo::Default, hyp_ty, body);
        b.finish(b.mk_lam(sig_id, BinderInfo::Default, c.nnreal.clone(), e))
    };

    (ty, value)
}

/// `q³ ≤ ofRat 2` for `q := ofRat (5/4)`. Build `eq : q³ = ofRat (125/64)`
/// (cube fold), then transport `ofRat (125/64) ≤ ofRat 2` along `eq` symm.
fn build_q_cube_le_two(c: &LemmaAConsts, parent: &EnvDeclBuilder) -> Expr {
    let q = c.of_frac(5, 4);
    let q_cube = c.nncube(&q);
    let of_12564 = c.of_frac(125, 64);
    let of2 = c.of_frac(2, 1);

    // eq : q³ = ofRat (125/64).
    let eq = build_q_cube_eq_125_64(c, parent);

    // base : ofRat (125/64) ≤ ofRat 2  (literal `125/64 ≤ 2`).
    let f12564 = c.frac(125, 64);
    let f2 = c.frac(2, 1);
    let h12564 = c.lit_nonneg(125, 64);
    let h2 = c.lit_nonneg(2, 1);
    let base = c.ofrat_le_ofrat(&f12564, &f2, &h12564, &h2, c.lit_le(&f12564, &f2));

    // motive : fun z => NNReal.le z (ofRat 2). Transport along `eq symm`
    // (ofRat(125/64) = q³) so the proof's LHS `ofRat(125/64)` rewrites to `q³`.
    let motive = {
        let mut m = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = m.fresh_local(c.nnreal.clone());
        let body = c.nnle(&z, &of2);
        m.finish_child(m.mk_lam(z_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let eq_symm = c.symm_nn(&q_cube, &of_12564, eq);
    c.subst_nn(motive, &of_12564, &q_cube, eq_symm, base)
}

/// `q³ = ofRat (125/64)` for `q := ofRat (5/4)`. Two `ofRat_mul` collapses:
///   `(q·q)·q = ofRat((5/4)·(5/4))·q = ofRat(((5/4)·(5/4))·(5/4))`,
/// then `ofRat(((5/4)·(5/4))·(5/4)) = ofRat(125/64)` (the ground product equals
/// `mk 125 64`, i.e. `Eq.refl` after componentwise `Rat.mul`).
fn build_q_cube_eq_125_64(c: &LemmaAConsts, parent: &EnvDeclBuilder) -> Expr {
    let f54 = c.frac(5, 4);
    let h54 = c.lit_nonneg(5, 4);
    let q = c.ofrat(&f54, &h54);

    let f54_54 = c.rmul(&f54, &f54); // (5/4)·(5/4)
    let h_qq_nn = c.rmul_nonneg(&f54, &f54, &h54, &h54); // 0 ≤ (5/4)·(5/4)
    let of_qq = c.ofrat(&f54_54, &h_qq_nn);

    // m1 : ofRat(5/4)·ofRat(5/4) = ofRat((5/4)·(5/4)).
    let m1 = c.ofrat_mul(&f54, &f54, &h54, &h54, &h_qq_nn);

    let f_cube = c.rmul(&f54_54, &f54); // ((5/4)·(5/4))·(5/4)
    let h_cube_nn = c.rmul_nonneg(&f54_54, &f54, &h_qq_nn, &h54); // 0 ≤ that
    let of_cube = c.ofrat(&f_cube, &h_cube_nn);

    // m2 : ofRat((5/4)·(5/4))·ofRat(5/4) = ofRat(((5/4)·(5/4))·(5/4)).
    let m2 = c.ofrat_mul(&f54_54, &f54, &h_qq_nn, &h54, &h_cube_nn);

    let qq = c.nnmul(&q, &q);
    let q_cube = c.nnmul(&qq, &q);
    let ofqq_q = c.nnmul(&of_qq, &q);

    // (q·q)·q =[congr_mul_left m1] ofRat((5/4)·(5/4))·q =[m2] ofRat(((5/4)·(5/4))·(5/4)).
    let cl = c.congr_mul_left(parent, &qq, &of_qq, &q, m1);
    let fwd = c.trans_nn(&q_cube, &ofqq_q, &of_cube, cl, m2);

    // bridge : ofRat(((5/4)·(5/4))·(5/4)) = ofRat(125/64). The ground product
    // reduces componentwise to `mk 125 64`, defeq to the literal — `Eq.refl`.
    let of_12564 = c.of_frac(125, 64);
    let bridge = build_ofrat_value_refl(c, &of_cube, &of_12564);

    c.trans_nn(&q_cube, &of_cube, &of_12564, fwd, bridge)
}

/// `ofRat a ha = ofRat b hb` when the underlying `Rat` values are defeq after
/// ground reduction (nonneg proofs are `Prop`, proof-irrelevant), via
/// `Eq.refl (ofRat a ha)` whose type unifies with `ofRat a ha = ofRat b hb`.
fn build_ofrat_value_refl(c: &LemmaAConsts, of_a: &Expr, _of_b: &Expr) -> Expr {
    c.refl_nn(of_a)
}

/// The (verified) nonnegative coefficients of `Q2(5/4+w)` as `(num, den)`,
/// ordered `c₀ .. c₇` (coefficient of `wⁱ`).
const Q2_COEFFS: [(u64, u64); 8] = [
    (260577, 4096),
    (329859, 1024),
    (227313, 256),
    (75195, 64),
    (12411, 16),
    (1089, 4),
    (51, 1),
    (4, 1),
];

/// `(type, value)` of step (ii): `∀ w : NNReal, ofRat 0 ≤ Q2poly w`.
///
/// `Q2poly w := ofRat c₀ + (c₁·w + (c₂·w² + … + c₇·w⁷))`  (RIGHT-associated, so
/// the top `add` has the floor `ofRat c₀` on the left). Then
///   `ofRat 0 ≤ ofRat c₀`  (`ofRat_le_ofRat`, `0 ≤ c₀`)
///   `ofRat c₀ ≤ Q2poly w` (`le_self_add (ofRat c₀) rest`),
/// `le.trans` closes `ofRat 0 ≤ Q2poly w`.
fn build_q2_nonneg(c: &LemmaAConsts) -> (Expr, Expr) {
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (w_id, w) = b.fresh_local(c.nnreal.clone());
        let poly = build_q2_poly(c, &w);
        let concl = c.nnle(&c.of_zero(), &poly);
        b.finish(b.mk_pi(w_id, BinderInfo::Default, c.nnreal.clone(), concl))
    };
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (w_id, w) = b.fresh_local(c.nnreal.clone());
        let poly = build_q2_poly(c, &w);

        let (c0n, c0d) = Q2_COEFFS[0];
        let of_c0 = c.of_frac(c0n, c0d);
        let rest = build_q2_poly_tail(c, &w, 1);

        // floor1 : ofRat 0 ≤ ofRat c0  (Rat `0 ≤ c0`).
        let zero = c.rat_zero.clone();
        let fc0 = c.frac(c0n, c0d);
        let h0 = c.zero_nonneg();
        let hc0 = c.lit_nonneg(c0n, c0d);
        let floor1 = c.ofrat_le_ofrat(&zero, &fc0, &h0, &hc0, c.lit_le(&zero, &fc0));

        // floor2 : ofRat c0 ≤ poly := le_self_add (ofRat c0) rest.
        let floor2 = c.le_self_add(&of_c0, &rest);

        let body = c.le_trans(&c.of_zero(), &of_c0, &poly, floor1, floor2);
        b.finish(b.mk_lam(w_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    (ty, value)
}

/// `w^i` (left-nested `((w·w)·…)·w`, `w^0 := ofRat 1`).
fn pow_w(c: &LemmaAConsts, w: &Expr, i: usize) -> Expr {
    if i == 0 {
        return c.of_frac(1, 1);
    }
    let mut e = w.clone();
    for _ in 1..i {
        e = c.nnmul(&e, w);
    }
    e
}

/// `cᵢ · wⁱ` as an NNReal (`ofRat cᵢ · w^i`); for `i = 0` it is just `ofRat c₀`.
fn term_i(c: &LemmaAConsts, w: &Expr, i: usize) -> Expr {
    let (n, d) = Q2_COEFFS[i];
    let coeff = c.of_frac(n, d);
    if i == 0 {
        coeff
    } else {
        c.nnmul(&coeff, &pow_w(c, w, i))
    }
}

/// `Q2poly w := c₀ + (c₁w + (c₂w² + … + c₇w⁷))` (RIGHT-associated).
fn build_q2_poly(c: &LemmaAConsts, w: &Expr) -> Expr {
    let head = term_i(c, w, 0);
    let tail = build_q2_poly_tail(c, w, 1);
    c.nnadd(&head, &tail)
}

/// The right-associated tail from index `start`:
/// `c_start·w^start + (c_{start+1}·w^{start+1} + … + c₇·w⁷)`.
fn build_q2_poly_tail(c: &LemmaAConsts, w: &Expr, start: usize) -> Expr {
    let last = Q2_COEFFS.len() - 1;
    let mut acc = term_i(c, w, last);
    let mut i = last;
    while i > start {
        i -= 1;
        acc = c.nnadd(&term_i(c, w, i), &acc);
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "BoolAnalysis.two_point_sigma_ge_five_fourths",
        "BoolAnalysis.two_point_q2_nonneg",
        "BoolAnalysis.two_point_sigma_cube_ge_two",
        "BoolAnalysis.two_point_s3_r3_eq_two",
        "BoolAnalysis.two_point_pow43_eq_s4",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_two_point_base_lemma_a()
            .expect("init_boolean_analysis_two_point_base_lemma_a");
        env.init_boolean_analysis_two_point_base_lemma_a()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_lemma_a_bricks_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_lemma_a_bricks_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
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

    /// The (A)-conditional assembly is pulled in by our init; confirm it stays
    /// registered + foundational alongside our bricks.
    #[test]
    fn test_lemma_a_assembly_present() {
        let env = env();
        for name in [
            "BoolAnalysis.two_point_base_43_of_A",
            "BoolAnalysis.two_point_S_cube_ge_moment",
        ] {
            let nm = Name::from_string(name);
            assert!(env.get_const(&nm).is_some(), "{name} must be present");
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only"
            );
        }
    }
}
