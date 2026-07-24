// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — THE NNReal DE-SQUARE ASSEMBLY: converting the squared
//! dual-HC bound `W² ≤ 16·x³` (over `Rat`) into the per-coordinate dual-HC
//! `W ≤ 4·x^{3/2}` over the genuine `NNReal` carrier.
//!
//! # Why this module exists
//!
//! `algebra_nnreal_reverse_square_sq.rs` lands the reverse-square keystone
//! `NNReal.le_of_sq_le_sq : NNReal.le (mul a a)(mul b b) → NNReal.le a b`.
//! `boolean_analysis_kkl_dualbound_assemble.rs` lands the SQUARED rational shadow
//! `(‖T_{1/3}g‖₂²)² ≤ 16·count³`. THIS module is the bridge that takes that
//! squared `Rat` bound across the square root onto `NNReal`, producing the sharp
//! per-coordinate bound `W ≤ 4·x^{3/2}` (`x^{3/2} = NNReal.pow32 x`).
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNReal.sq_mul : ∀ p q : NNReal,
//!     NNReal.mul (NNReal.mul p q)(NNReal.mul p q)
//!       = NNReal.mul (NNReal.mul p p)(NNReal.mul q q)`.
//!   The pure commutative-monoid square-of-product regroup, built from the landed
//!   `NNReal.mul_comm` / `NNReal.mul_assoc` (no carrier descent).
//!
//! - **Lemma A** `NNReal.pow32_four_sq : ∀ (x : Rat)(h0 : 0≤x)(h1 : x<1)(hc : 0≤16·x³),
//!     NNReal.mul (NNReal.mul (ofRat 4) (pow32 x h0)) (NNReal.mul (ofRat 4) (pow32 x h0))
//!       = NNReal.ofRat (16·x³) hc`,
//!   where `16·x³ := (16·x)·(x·x)` matches the squared-bound shadow's `cube16`.
//!   PROOF: with `A := ofRat 4`, `X := ofRat x`, `S := sqrtRat x`,
//!   `4·pow32 x = A·(X·S)`, and
//!   `(A·(X·S))·(A·(X·S)) = (A·A)·((X·S)·(X·S))` (`sq_mul A (X·S)`)
//!                        = (A·A)·((X·X)·(S·S))   (`sq_mul X S` under the right factor)
//!                        = (A·A)·((X·X)·X)        (`sqrtRat_mul_self`: S·S = ofRat x)
//!   then `A·A = ofRat(4·4)`, `X·X = ofRat(x·x)`, and three `ofRat_mul` collapses
//!   plus a pure-`Rat` numeral/regroup bridge `(4·4)·((x·x)·x) = (16·x)·(x·x)`
//!   land `ofRat((16·x)·(x·x))`.
//!
//! - **Lemma B (THE DE-SQUARE)** `NNReal.le_four_pow32_of_sq_le :
//!     ∀ (W x : Rat)(hW : 0≤W)(h0 : 0≤x)(h1 : x<1),
//!       Rat.le (W·W) (16·x³) →
//!         NNReal.le (NNReal.ofRat W hW)
//!                   (NNReal.mul (NNReal.ofRat 4 _)(NNReal.pow32 x h0))`.
//!   PROOF: `(ofRat W)·(ofRat W) = ofRat(W·W)` (`ofRat_mul`) `≤ ofRat(16·x³)`
//!   (`ofRat_le_ofRat` on the `Rat` hypothesis) `= (4·pow32 x)·(4·pow32 x)`
//!   (Lemma A, symm); then `NNReal.le_of_sq_le_sq` strips the square, giving
//!   `ofRat W ≤ 4·pow32 x = 4·x^{3/2}`. Instantiating `x := Inf_i`, `W := ‖T_{1/3}g‖₂²`
//!   this is the per-coordinate dual-HC bound `W ≤ 4·Inf_i^{3/2}`.
//!
//! # Numerals
//!
//! `4 := Rat.ofNat 4`, `16 := Rat.ofNat 16` (defeq to `Rat.mk (Int.ofNat ·) 1`,
//! the squared-bound shadow's `lit16` form). `4·4 = 16` is closed via
//! `Rat.ofNat_mul 4 4` (`Nat.mul 4 4 ≡ 16` ι-reduces), all defeq-clean — no axiom.
//!
//! # x=1 boundary (the dictator)
//!
//! `NNReal.sqrtRat_mul_self` carries `x<1` (the dyadic-floor squeeze is faithful
//! on `[0,1)`), so Lemma A / Lemma B are scoped to `x<1`. The tight dictator
//! `Inf=1` sits on the boundary; closing it needs a non-strict `sqrtRat_mul_self`
//! at `x=1` (or a direct `W≤4` boundary lemma). See the Stage-C status note —
//! that residual is NOT discharged here.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the de-square assembly.
pub(crate) struct DesqConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_ofnat: Expr,
    rat_mul: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_mul_comm: Expr,
    rat_mul_assoc: Expr,
    rat_ofnat_mul: Expr,
    rat_le_of_ble: Expr,
    bool_true: Expr,
    bool_ty: Expr,
    rat_ble: Expr,
    // carrier.
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_of_rat: Expr,
    nnreal_sqrt: Expr,
    nnreal_pow32: Expr,
    nnreal_le: Expr,
    nnreal_mul_comm: Expr,
    nnreal_mul_assoc: Expr,
    nnreal_ofrat_mul: Expr,
    nnreal_sqrt_mul_self: Expr,
    nnreal_ofrat_le: Expr,
    nnreal_le_of_sq: Expr,
    sq_mul_thm: Expr,
    pow32_four_sq_thm: Expr,
    // Eq / logic at level 1 (NNReal : Sort 1, Rat : Sort 1).
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    congr_arg1: Expr,
}

impl DesqConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_ofnat: k("Rat.ofNat"),
            rat_mul: k("Rat.mul"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            rat_ofnat_mul: k("Rat.ofNat_mul"),
            rat_le_of_ble: k("Rat.le_of_ble_eq_true"),
            bool_true: k("Bool.true"),
            bool_ty: k("Bool"),
            rat_ble: k("Rat.ble"),
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_sqrt: k("NNReal.sqrtRat"),
            nnreal_pow32: k("NNReal.pow32"),
            nnreal_le: k("NNReal.le"),
            nnreal_mul_comm: k("NNReal.mul_comm"),
            nnreal_mul_assoc: k("NNReal.mul_assoc"),
            nnreal_ofrat_mul: k("NNReal.ofRat_mul"),
            nnreal_sqrt_mul_self: k("NNReal.sqrtRat_mul_self"),
            nnreal_ofrat_le: k("NNReal.ofRat_le_ofRat"),
            nnreal_le_of_sq: k("NNReal.le_of_sq_le_sq"),
            sq_mul_thm: k("NNReal.sq_mul"),
            pow32_four_sq_thm: k("NNReal.pow32_four_sq"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg1: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    // ── Rat constructors ─────────────────────────────────────────────────────
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn rlt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn nonneg(&self, a: Expr) -> Expr {
        self.rle(self.rat_zero.clone(), a)
    }
    /// `Rat.ofNat n` for a small literal `n`, with `n` built from `Nat` successors.
    fn ofnat_lit(&self, n: usize) -> Expr {
        let mut nat = self.nat_zero.clone();
        for _ in 0..n {
            nat = Expr::app(self.nat_succ.clone(), nat);
        }
        Expr::app(self.rat_ofnat.clone(), nat)
    }
    fn nat_lit(&self, n: usize) -> Expr {
        let mut nat = self.nat_zero.clone();
        for _ in 0..n {
            nat = Expr::app(self.nat_succ.clone(), nat);
        }
        nat
    }
    /// `x³` in the cube16-matching grouping: `(16·x)·(x·x)` if scaled, here the
    /// bare cube `(x·x)·x`. We keep two helpers; see `cube16`.
    fn cube16(&self, x: &Expr) -> Expr {
        // (16·x)·(x·x) — byte-identical to dualbound_assemble's `cube16` with
        // `16 := Rat.ofNat 16` (defeq to `Rat.mk (Int.ofNat 16) 1`).
        let s16 = self.ofnat_lit(16);
        self.rmul(self.rmul(s16, x.clone()), self.rmul(x.clone(), x.clone()))
    }
    /// `Rat.mul_comm a b : Eq Rat (a·b)(b·a)`.
    fn rmul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_assoc a b c : Eq Rat ((a·b)·c)(a·(b·c))`.
    fn rmul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_mul_assoc.clone(), [a, b, cc])
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
    /// `@congrArg.{1,1} T T a b f h : Eq T (f a)(f b)`.
    fn congr(&self, t: &Expr, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(self.congr_arg1.clone(), [t.clone(), t.clone(), a, b, f, h])
    }

    // ── NNReal constructors ──────────────────────────────────────────────────
    fn nnmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a, b])
    }
    fn ofrat(&self, x: Expr, h: Expr) -> Expr {
        Expr::apps(self.nnreal_of_rat.clone(), [x, h])
    }
    fn sqrt(&self, x: Expr) -> Expr {
        Expr::app(self.nnreal_sqrt.clone(), x)
    }
    fn pow32(&self, x: Expr, h0: Expr) -> Expr {
        Expr::apps(self.nnreal_pow32.clone(), [x, h0])
    }
    fn nnle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a, b])
    }
    fn eq_nn(&self, a: Expr, b: Expr) -> Expr {
        self.eq_ty(&self.nnreal, a, b)
    }
    /// NNReal `Eq.symm`.
    fn nn_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.symm(&self.nnreal.clone(), a, b, h)
    }
    /// NNReal `Eq.trans`.
    fn nn_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.trans(&self.nnreal.clone(), a, b, cc, h1, h2)
    }
    /// `mul · r` congruence: `h : a = b ⟹ mul a r = mul b r`.
    fn nn_congr_l(&self, parent: &EnvDeclBuilder, a: Expr, b: Expr, r: &Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(self.nnreal.clone());
            let body = self.nnmul(w, r.clone());
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.congr(&self.nnreal.clone(), a, b, f, h)
    }
    /// `mul l ·` congruence: `h : a = b ⟹ mul l a = mul l b`.
    fn nn_congr_r(&self, parent: &EnvDeclBuilder, l: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(self.nnreal.clone());
            let body = self.nnmul(l.clone(), w);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.congr(&self.nnreal.clone(), a, b, f, h)
    }
    /// `NNReal.mul_comm a b : mul a b = mul b a`.
    fn nn_mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnreal_mul_comm.clone(), [a, b])
    }
    /// `NNReal.mul_assoc a b c : mul a (mul b c) = mul (mul a b) c`.
    fn nn_mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.nnreal_mul_assoc.clone(), [a, b, cc])
    }
    /// `NNReal.ofRat_mul a b ha hb hab : mul (ofRat a)(ofRat b) = ofRat (a·b)`.
    fn nn_ofrat_mul(&self, a: Expr, b: Expr, ha: Expr, hb: Expr, hab: Expr) -> Expr {
        Expr::apps(self.nnreal_ofrat_mul.clone(), [a, b, ha, hb, hab])
    }
    /// `NNReal.sqrtRat_mul_self x h0 h1 : mul (sqrtRat x)(sqrtRat x) = ofRat x h0`.
    fn nn_sqrt_mul_self(&self, x: Expr, h0: Expr, h1: Expr) -> Expr {
        Expr::apps(self.nnreal_sqrt_mul_self.clone(), [x, h0, h1])
    }
    /// `NNReal.ofRat_le_ofRat a b ha hb hle : NNReal.le (ofRat a)(ofRat b)`.
    fn nn_ofrat_le(&self, a: Expr, b: Expr, ha: Expr, hb: Expr, hle: Expr) -> Expr {
        Expr::apps(self.nnreal_ofrat_le.clone(), [a, b, ha, hb, hle])
    }
    /// `NNReal.le_of_sq_le_sq a b hsq : NNReal.le a b` (hsq : le (mul a a)(mul b b)).
    fn nn_le_of_sq(&self, a: Expr, b: Expr, hsq: Expr) -> Expr {
        Expr::apps(self.nnreal_le_of_sq.clone(), [a, b, hsq])
    }

    /// `0 ≤ (Rat.ofNat n)` via the boolean reflection idiom
    /// `Rat.le_of_ble_eq_true 0 (ofNat n) refl`. `Rat.ble 0 (ofNat n)` native-reduces
    /// to `true` on the concrete `Rat.mk` rep.
    fn ofnat_nonneg(&self, n: usize) -> Expr {
        let lit = self.ofnat_lit(n);
        let refl = Expr::apps(
            self.eq_refl1.clone(),
            [self.bool_ty.clone(), self.bool_true.clone()],
        );
        let _ = &self.rat_ble; // documents the intended Eq Bool target (carried by defeq)
        Expr::apps(
            self.rat_le_of_ble.clone(),
            [self.rat_zero.clone(), lit, refl],
        )
    }
    /// `0 ≤ a·b` from `0 ≤ a`, `0 ≤ b`.
    fn rmul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        let mul_nonneg = Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]);
        Expr::apps(mul_nonneg, [a, b, ha, hb])
    }
}

impl Environment {
    /// Register the NNReal de-square assembly:
    /// `NNReal.sq_mul`, `NNReal.pow32_four_sq` (Lemma A),
    /// `NNReal.le_four_pow32_of_sq_le` (Lemma B). Idempotent; axiom-free.
    pub fn init_algebra_nnreal_desquare(&mut self) -> Result<(), EnvError> {
        // Carrier + landed bricks.
        self.init_algebra_nnreal_pow32()?; // NNReal.pow32 (+ ofRat, sqrtRat, mul)
        self.init_algebra_nnreal_sqrt_identity()?; // sqrtRat_mul_self
        self.init_algebra_nnreal_reverse_square_algebra()?; // ofRat_mul, mul_comm, mul_assoc
        self.init_algebra_nnreal_reverse_square_sq()?; // le_of_sq_le_sq
        self.init_algebra_nnreal_le()?; // ofRat_le_ofRat, NNReal.le
        self.register_rat_mul_comm_proof()?; // Rat.mul_comm
        self.register_rat_mul_assoc_proof()?; // Rat.mul_assoc
        self.register_rat_ofnat_mul()?; // Rat.ofNat_mul (numeral bridge 4·4 = 16)
        self.register_rat_order_proofs()?; // Rat.mul_nonneg
        self.register_rat_minmax_proofs()?; // Rat.le_of_ble_eq_true (0 ≤ ofNat n)
        self.init_eq()?;

        let c = DesqConsts::new();
        self.register_nnreal_sq_mul(&c)?;
        self.register_nnreal_pow32_four_sq(&c)?;
        self.register_nnreal_le_four_pow32_of_sq_le(&c)?;
        Ok(())
    }

    /// `NNReal.sq_mul : ∀ p q, mul (mul p q)(mul p q) = mul (mul p p)(mul q q)`.
    fn register_nnreal_sq_mul(&mut self, c: &DesqConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.sq_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(c.nnreal.clone());
            let (q_id, q) = b.fresh_local(c.nnreal.clone());
            let pq = c.nnmul(p.clone(), q.clone());
            let lhs = c.nnmul(pq.clone(), pq.clone());
            let rhs = c.nnmul(c.nnmul(p.clone(), p.clone()), c.nnmul(q.clone(), q.clone()));
            let concl = c.eq_nn(lhs, rhs);
            let e = b.mk_pi(q_id, BinderInfo::Default, c.nnreal.clone(), concl);
            let e = b.mk_pi(p_id, BinderInfo::Default, c.nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_sq_mul(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.pow32_four_sq` (Lemma A).
    fn register_nnreal_pow32_four_sq(&mut self, c: &DesqConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.pow32_four_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let h0_ty = c.nonneg(x.clone());
            let (h0_id, h0) = b.fresh_local(h0_ty.clone());
            let h1_ty = c.rlt(x.clone(), c.rat_one.clone());
            let (h1_id, _h1) = b.fresh_local(h1_ty.clone());
            let hc_ty = c.nonneg(c.cube16(&x));
            let (hc_id, hc) = b.fresh_local(hc_ty.clone());

            let four = c.ofnat_lit(4);
            let h4 = c.ofnat_nonneg(4);
            let four_nn = c.ofrat(four.clone(), h4);
            let fp = c.nnmul(four_nn.clone(), c.pow32(x.clone(), h0.clone()));
            let lhs = c.nnmul(fp.clone(), fp.clone());
            let rhs = c.ofrat(c.cube16(&x), hc.clone());
            let concl = c.eq_nn(lhs, rhs);
            let _ = four;

            let e = b.mk_pi(hc_id, BinderInfo::Default, hc_ty, concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, e);
            let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_pow32_four_sq(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.le_four_pow32_of_sq_le` (Lemma B — the de-square).
    fn register_nnreal_le_four_pow32_of_sq_le(&mut self, c: &DesqConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.le_four_pow32_of_sq_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (w_id, w) = b.fresh_local(c.rat.clone());
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let hw_ty = c.nonneg(w.clone());
            let (hw_id, hw) = b.fresh_local(hw_ty.clone());
            let h0_ty = c.nonneg(x.clone());
            let (h0_id, h0) = b.fresh_local(h0_ty.clone());
            let h1_ty = c.rlt(x.clone(), c.rat_one.clone());
            let (h1_id, _h1) = b.fresh_local(h1_ty.clone());
            let hsq_ty = c.rle(c.rmul(w.clone(), w.clone()), c.cube16(&x));
            let (hsq_id, _hsq) = b.fresh_local(hsq_ty.clone());

            let four = c.ofnat_lit(4);
            let h4 = c.ofnat_nonneg(4);
            let four_nn = c.ofrat(four, h4);
            let lhs = c.ofrat(w.clone(), hw.clone());
            let rhs = c.nnmul(four_nn, c.pow32(x.clone(), h0.clone()));
            let concl = c.nnle(lhs, rhs);

            let e = b.mk_pi(hsq_id, BinderInfo::Default, hsq_ty, concl);
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, e);
            let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
            let e = b.mk_pi(hw_id, BinderInfo::Default, hw_ty, e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(w_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = build_le_four_pow32(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `NNReal.sq_mul` proof: `(p·q)·(p·q) = (p·p)·(q·q)`.
///
/// Chain (all NNReal `Eq`, via `mul_comm`/`mul_assoc` + the two `congr` helpers):
/// ```text
/// (p·q)·(p·q)
///  = p·(q·(p·q))        symm(mul_assoc p q (p·q))
///  = p·((q·p)·q)        congr_r p (mul_assoc q p q)
///  = p·((p·q)·q)        congr_r p (congr_l (mul_comm q p) q)
///  = p·(p·(q·q))        congr_r p (symm(mul_assoc p q q))
///  = (p·p)·(q·q)        mul_assoc p p (q·q)
/// ```
fn build_sq_mul(c: &DesqConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (p_id, p) = b.fresh_local(c.nnreal.clone());
    let (q_id, q) = b.fresh_local(c.nnreal.clone());

    let pq = c.nnmul(p.clone(), q.clone());
    let lhs = c.nnmul(pq.clone(), pq.clone()); // (p·q)·(p·q)
    let pp = c.nnmul(p.clone(), p.clone());
    let qq = c.nnmul(q.clone(), q.clone());
    let rhs = c.nnmul(pp.clone(), qq.clone()); // (p·p)·(q·q)

    let qp = c.nnmul(q.clone(), p.clone());
    let q_pq = c.nnmul(q.clone(), pq.clone()); // q·(p·q)
    let qp_q = c.nnmul(qp.clone(), q.clone()); // (q·p)·q
    let pq_q = c.nnmul(pq.clone(), q.clone()); // (p·q)·q
    let p_qq = c.nnmul(p.clone(), qq.clone()); // p·(q·q)

    // t0 = (p·q)·(p·q) ; t1 = p·(q·(p·q)) ; t2 = p·((q·p)·q) ; t3 = p·((p·q)·q) ;
    // t4 = p·(p·(q·q)) ; rhs = (p·p)·(q·q).
    let t1 = c.nnmul(p.clone(), q_pq.clone());
    let t2 = c.nnmul(p.clone(), qp_q.clone());
    let t3 = c.nnmul(p.clone(), pq_q.clone());
    let t4 = c.nnmul(p.clone(), p_qq.clone());

    // s01 : lhs = t1  (symm of mul_assoc p q (p·q) : p·(q·(p·q)) = (p·q)·(p·q)).
    let assoc_lhs = c.nn_mul_assoc(p.clone(), q.clone(), pq.clone()); // t1 = lhs
    let s01 = c.nn_symm(t1.clone(), lhs.clone(), assoc_lhs);

    // s12 : t1 = t2  (congr_r p (mul_assoc q p q : q·(p·q) = (q·p)·q)).
    let assoc_qpq = c.nn_mul_assoc(q.clone(), p.clone(), q.clone()); // q·(p·q) = (q·p)·q
    let s12 = c.nn_congr_r(&b, &p, q_pq.clone(), qp_q.clone(), assoc_qpq);

    // s23 : t2 = t3  (congr_r p (congr_l (mul_comm q p : q·p = p·q) q : (q·p)·q = (p·q)·q)).
    let comm_qp = c.nn_mul_comm(q.clone(), p.clone()); // q·p = p·q
    let inner23 = c.nn_congr_l(&b, qp.clone(), pq.clone(), &q, comm_qp); // (q·p)·q = (p·q)·q
    let s23 = c.nn_congr_r(&b, &p, qp_q.clone(), pq_q.clone(), inner23);

    // s34 : t3 = t4  (congr_r p (symm(mul_assoc p q q : p·(q·q) = (p·q)·q))).
    let assoc_pqq = c.nn_mul_assoc(p.clone(), q.clone(), q.clone()); // p·(q·q) = (p·q)·q
    let symm_pqq = c.nn_symm(p_qq.clone(), pq_q.clone(), assoc_pqq); // (p·q)·q = p·(q·q)
    let s34 = c.nn_congr_r(&b, &p, pq_q.clone(), p_qq.clone(), symm_pqq);

    // s4r : t4 = rhs  (mul_assoc p p (q·q) : p·(p·(q·q)) = (p·p)·(q·q)).
    let s4r = c.nn_mul_assoc(p.clone(), p.clone(), qq.clone());

    // chain.
    let ch = c.nn_trans(lhs.clone(), t1.clone(), t2.clone(), s01, s12);
    let ch = c.nn_trans(lhs.clone(), t2.clone(), t3.clone(), ch, s23);
    let ch = c.nn_trans(lhs.clone(), t3.clone(), t4.clone(), ch, s34);
    let proof = c.nn_trans(lhs, t4, rhs, ch, s4r);

    let e = b.mk_lam(q_id, BinderInfo::Default, c.nnreal.clone(), proof);
    let e = b.mk_lam(p_id, BinderInfo::Default, c.nnreal.clone(), e);
    b.finish(e)
}

/// Lemma A `NNReal.pow32_four_sq` proof value.
///
/// `A := ofRat 4`, `X := ofRat x`, `S := sqrtRat x`. `pow32 x h0 ≡ X·S` (reducible),
/// so `4·pow32 = A·(X·S)`. Chain:
/// ```text
/// (A·(X·S))·(A·(X·S))
///  = (A·A)·((X·S)·(X·S))   sq_mul A (X·S)
///  = (A·A)·((X·X)·(S·S))   congr_r (A·A) (sq_mul X S)
///  = (A·A)·((X·X)·(ofRat x))   congr_r (A·A) (congr_r (X·X) (sqrtRat_mul_self x))
///  = (A·A)·(ofRat(x·x)·ofRat x)   congr_r (A·A) (congr_l (ofRat_mul x x) (ofRat x))
///  = (A·A)·(ofRat((x·x)·x))     congr_r (A·A) (ofRat_mul (x·x) x)
///  = ofRat(4·4)·ofRat((x·x)·x)  congr_l (ofRat_mul 4 4) (ofRat((x·x)·x))
///  = ofRat((4·4)·((x·x)·x))     ofRat_mul (4·4) ((x·x)·x)
///  = ofRat((16·x)·(x·x))        congr (ofRat) (Rat bridge (4·4)·((x·x)·x) = (16·x)·(x·x))
/// ```
fn build_pow32_four_sq(c: &DesqConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let h0_ty = c.nonneg(x.clone());
    let (h0_id, h0) = b.fresh_local(h0_ty.clone());
    let h1_ty = c.rlt(x.clone(), c.rat_one.clone());
    let (h1_id, h1) = b.fresh_local(h1_ty.clone());
    let hc_ty = c.nonneg(c.cube16(&x));
    let (hc_id, hc) = b.fresh_local(hc_ty.clone());

    // Numerals + nonneg.
    let four = c.ofnat_lit(4);
    let h4 = c.ofnat_nonneg(4);
    let big_a = c.ofrat(four.clone(), h4.clone()); // A = ofRat 4
    let big_x = c.ofrat(x.clone(), h0.clone()); // X = ofRat x
    let big_s = c.sqrt(x.clone()); // S = sqrtRat x

    let xs = c.nnmul(big_x.clone(), big_s.clone()); // X·S = pow32 x (reducible)
    let fp = c.nnmul(big_a.clone(), xs.clone()); // A·(X·S) = 4·pow32 x
    let lhs = c.nnmul(fp.clone(), fp.clone());

    // 1) sq_mul A (X·S) : (A·(X·S))·(A·(X·S)) = (A·A)·((X·S)·(X·S)).
    let aa = c.nnmul(big_a.clone(), big_a.clone());
    let xs_xs = c.nnmul(xs.clone(), xs.clone());
    let t1 = c.nnmul(aa.clone(), xs_xs.clone());
    let s1 = Expr::apps(c.sq_mul_thm.clone(), [big_a.clone(), xs.clone()]);

    // 2) congr_r (A·A) (sq_mul X S : (X·S)·(X·S) = (X·X)·(S·S)).
    let xx = c.nnmul(big_x.clone(), big_x.clone());
    let ss = c.nnmul(big_s.clone(), big_s.clone());
    let xx_ss = c.nnmul(xx.clone(), ss.clone());
    let t2 = c.nnmul(aa.clone(), xx_ss.clone());
    let sq_xs = Expr::apps(c.sq_mul_thm.clone(), [big_x.clone(), big_s.clone()]);
    let s2 = c.nn_congr_r(&b, &aa, xs_xs.clone(), xx_ss.clone(), sq_xs);

    // 3) S·S = ofRat x   (sqrtRat_mul_self x h0 h1).
    let of_x = c.ofrat(x.clone(), h0.clone());
    let xx_ofx = c.nnmul(xx.clone(), of_x.clone());
    let t3 = c.nnmul(aa.clone(), xx_ofx.clone());
    let ss_eq = c.nn_sqrt_mul_self(x.clone(), h0.clone(), h1.clone()); // S·S = ofRat x
    let inner3 = c.nn_congr_r(&b, &xx, ss.clone(), of_x.clone(), ss_eq); // (X·X)·(S·S) = (X·X)·(ofRat x)
    let s3 = c.nn_congr_r(&b, &aa, xx_ss.clone(), xx_ofx.clone(), inner3);

    // 4) X·X = ofRat(x·x)   (ofRat_mul x x h0 h0 hxx).
    let xxr = c.rmul(x.clone(), x.clone());
    let hxx = c.rmul_nonneg(x.clone(), x.clone(), h0.clone(), h0.clone()); // 0 ≤ x·x
    let of_xx = c.ofrat(xxr.clone(), hxx.clone()); // ofRat(x·x)
    let ofxx_ofx = c.nnmul(of_xx.clone(), of_x.clone());
    let t4 = c.nnmul(aa.clone(), ofxx_ofx.clone());
    let xx_eq = c.nn_ofrat_mul(x.clone(), x.clone(), h0.clone(), h0.clone(), hxx.clone()); // X·X = ofRat(x·x)
    let inner4 = c.nn_congr_l(&b, xx.clone(), of_xx.clone(), &of_x, xx_eq); // (X·X)·(ofRat x) = ofRat(x·x)·(ofRat x)
    let s4 = c.nn_congr_r(&b, &aa, xx_ofx.clone(), ofxx_ofx.clone(), inner4);

    // 5) ofRat(x·x)·ofRat x = ofRat((x·x)·x)   (ofRat_mul (x·x) x hxx h0 hxxx).
    let xxx = c.rmul(xxr.clone(), x.clone()); // (x·x)·x
    let hxxx = c.rmul_nonneg(xxr.clone(), x.clone(), hxx.clone(), h0.clone()); // 0 ≤ (x·x)·x
    let of_xxx = c.ofrat(xxx.clone(), hxxx.clone());
    let t5 = c.nnmul(aa.clone(), of_xxx.clone());
    let collapse5 = c.nn_ofrat_mul(
        xxr.clone(),
        x.clone(),
        hxx.clone(),
        h0.clone(),
        hxxx.clone(),
    ); // = ofRat((x·x)·x)
    let s5 = c.nn_congr_r(&b, &aa, ofxx_ofx.clone(), of_xxx.clone(), collapse5);

    // 6) A·A = ofRat(4·4)   (ofRat_mul 4 4 h4 h4 h44).
    let fourfour = c.rmul(four.clone(), four.clone()); // 4·4
    let h44 = c.rmul_nonneg(four.clone(), four.clone(), h4.clone(), h4.clone());
    let of_44 = c.ofrat(fourfour.clone(), h44.clone());
    let of44_ofxxx = c.nnmul(of_44.clone(), of_xxx.clone());
    let t6 = of44_ofxxx.clone();
    let aa_eq = c.nn_ofrat_mul(
        four.clone(),
        four.clone(),
        h4.clone(),
        h4.clone(),
        h44.clone(),
    ); // A·A = ofRat(4·4)
    let s6 = c.nn_congr_l(&b, aa.clone(), of_44.clone(), &of_xxx, aa_eq); // (A·A)·(ofRat((x·x)·x)) = ofRat(4·4)·(ofRat((x·x)·x))

    // 7) ofRat(4·4)·ofRat((x·x)·x) = ofRat((4·4)·((x·x)·x))  (ofRat_mul (4·4) ((x·x)·x)).
    let prod_rat = c.rmul(fourfour.clone(), xxx.clone()); // (4·4)·((x·x)·x)
    let hprod = c.rmul_nonneg(fourfour.clone(), xxx.clone(), h44.clone(), hxxx.clone());
    let of_prod = c.ofrat(prod_rat.clone(), hprod.clone());
    let t7 = of_prod.clone();
    let s7 = c.nn_ofrat_mul(
        fourfour.clone(),
        xxx.clone(),
        h44.clone(),
        hxxx.clone(),
        hprod.clone(),
    );

    // 8) ofRat((4·4)·((x·x)·x)) = ofRat((16·x)·(x·x))  via Rat bridge + congr (ofRat ·).
    //    The two `ofRat` args differ only in their Rat value & the nonneg proof; we
    //    transport along the Rat equality with `Eq.subst` over the motive
    //    `fun (z : Rat) => ofRat((4·4)·((x·x)·x)) = ofRat z (cast h)` — but the
    //    nonneg proof is index-dependent. Cleaner: prove the goal RHS `ofRat(cube16) hc`
    //    equals `of_prod` by `Eq.subst` ON THE NONNEG-IRRELEVANT `ofRat` via a Rat
    //    equality, packaged through `NNReal.ofRat`'s proof-irrelevance in the
    //    `0≤` argument (Prop). See `ofrat_value_congr`.
    let cube = c.cube16(&x);
    let rat_bridge = build_rat_cube_bridge(c, &b, &x, &four); // (4·4)·((x·x)·x) = (16·x)·(x·x)
    let s8 = ofrat_value_congr(c, &b, &prod_rat, &cube, &hprod, &hc, rat_bridge);
    let target = c.ofrat(cube.clone(), hc.clone());

    // chain t0..target.
    let ch = c.nn_trans(lhs.clone(), t1.clone(), t2.clone(), s1, s2);
    let ch = c.nn_trans(lhs.clone(), t2.clone(), t3.clone(), ch, s3);
    let ch = c.nn_trans(lhs.clone(), t3.clone(), t4.clone(), ch, s4);
    let ch = c.nn_trans(lhs.clone(), t4.clone(), t5.clone(), ch, s5);
    let ch = c.nn_trans(lhs.clone(), t5.clone(), t6.clone(), ch, s6);
    let ch = c.nn_trans(lhs.clone(), t6.clone(), t7.clone(), ch, s7);
    let proof = c.nn_trans(lhs, t7, target, ch, s8);

    let e = b.mk_lam(hc_id, BinderInfo::Default, hc_ty, proof);
    let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, e);
    let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
    let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// The pure-`Rat` bridge `(4·4)·((x·x)·x) = (16·x)·(x·x)`.
///
/// `4·4 = 16` from `Rat.ofNat_mul 4 4 : ofNat(4·4) = (ofNat 4)·(ofNat 4)` symm
/// (with `ofNat(Nat.mul 4 4) ≡ ofNat 16 = 16` defeq). Then reassociate the cube:
/// `(4·4)·((x·x)·x) → 16·((x·x)·x) → 16·(x·(x·x))?` … we instead chain via
/// `mul_assoc`/`mul_comm`. Concretely:
/// ```text
/// (4·4)·((x·x)·x)
///  = 16·((x·x)·x)        congr_l (4·4 = 16) ((x·x)·x)
///  = 16·(x·(x·x))        congr_r 16 (mul_comm (x·x) x : (x·x)·x = x·(x·x))
///  = (16·x)·(x·x)        mul_assoc 16 x (x·x)
/// ```
fn build_rat_cube_bridge(c: &DesqConsts, parent: &EnvDeclBuilder, x: &Expr, four: &Expr) -> Expr {
    let rat = c.rat.clone();
    let fourfour = c.rmul(four.clone(), four.clone()); // 4·4
    let s16 = c.ofnat_lit(16);
    let xxr = c.rmul(x.clone(), x.clone()); // x·x
    let xxx = c.rmul(xxr.clone(), x.clone()); // (x·x)·x
    let x_xx = c.rmul(x.clone(), xxr.clone()); // x·(x·x)

    // e_44_16 : (4·4) = 16. From ofNat_mul 4 4 : ofNat(4·4) = (ofNat 4)·(ofNat 4),
    //   symm gives (ofNat 4)·(ofNat 4) = ofNat(4·4) ≡ ofNat 16 = 16 (defeq).
    let nat4 = c.nat_lit(4);
    let ofnat_mul44 = Expr::apps(c.rat_ofnat_mul.clone(), [nat4.clone(), nat4.clone()]);
    // ofnat_mul44 : ofNat(4·4) = (ofNat 4)·(ofNat 4) ≡ 4·4. Its LHS `ofNat(Nat.mul 4 4)`
    //   ι-reduces to `ofNat 16 = 16`, so symm has type `(4·4) = 16` up to defeq.
    let e_44_16 = c.symm(&rat, s16.clone(), fourfour.clone(), ofnat_mul44);

    // r1 : (4·4)·((x·x)·x) = 16·((x·x)·x).
    let r1 = c.congr(
        &rat,
        fourfour.clone(),
        s16.clone(),
        {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(rat.clone());
            let body = c.rmul(w, xxx.clone());
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, rat.clone(), body))
        },
        e_44_16,
    );
    let lhs0 = c.rmul(fourfour.clone(), xxx.clone()); // (4·4)·((x·x)·x)
    let m1 = c.rmul(s16.clone(), xxx.clone()); // 16·((x·x)·x)

    // r2 : 16·((x·x)·x) = 16·(x·(x·x))   congr_r 16 (mul_comm (x·x) x).
    let comm = c.rmul_comm(xxr.clone(), x.clone()); // (x·x)·x = x·(x·x)
    let r2 = c.congr(
        &rat,
        xxx.clone(),
        x_xx.clone(),
        {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(rat.clone());
            let body = c.rmul(s16.clone(), w);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, rat.clone(), body))
        },
        comm,
    );
    let m2 = c.rmul(s16.clone(), x_xx.clone()); // 16·(x·(x·x))

    // r3 : 16·(x·(x·x)) = (16·x)·(x·x)   symm(mul_assoc 16 x (x·x)).
    //   mul_assoc 16 x (x·x) : (16·x)·(x·x) = 16·(x·(x·x)); we need the reverse.
    let target = c.rmul(c.rmul(s16.clone(), x.clone()), xxr.clone()); // (16·x)·(x·x)
    let assoc_16 = c.rmul_assoc(s16.clone(), x.clone(), xxr.clone()); // target = m2
    let r3 = c.symm(&rat, target.clone(), m2.clone(), assoc_16); // m2 = target

    let ch = c.trans(&rat, lhs0.clone(), m1.clone(), m2.clone(), r1, r2);
    c.trans(&rat, lhs0, m2, target, ch, r3)
}

/// `ofRat a ha = ofRat b hb` from a `Rat` equality `h_eq : a = b`.
///
/// `NNReal.ofRat`'s nonneg argument is a `Prop` (`Rat.le 0 ·`), so it is
/// proof-irrelevant; transport the VALUE along `h_eq` via `Eq.subst` on the
/// motive `fun (z : Rat) => Π (hz : 0≤z), ofRat a ha = ofRat z hz`, then apply to
/// `hb`. We avoid dependent-motive pain by transporting the whole `ofRat a ha`
/// against `ofRat z hz` where the proof field is the bound `hz`.
fn ofrat_value_congr(
    c: &DesqConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    b: &Expr,
    ha: &Expr,
    hb: &Expr,
    h_eq: Expr, // a = b
) -> Expr {
    // motive z := Π (hz : 0≤z), Eq NNReal (ofRat a ha)(ofRat z hz).
    let motive = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let inner = {
            let mut di = EnvDeclBuilder::child_of(&d);
            let hz_ty = c.nonneg(z.clone());
            let (hz_id, hz) = di.fresh_local(hz_ty.clone());
            let body = c.eq_nn(c.ofrat(a.clone(), ha.clone()), c.ofrat(z.clone(), hz));
            di.finish_child(di.mk_pi(hz_id, BinderInfo::Default, hz_ty, body))
        };
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), inner))
    };
    // base : Π (hz : 0≤a), ofRat a ha = ofRat a hz  — by refl on the value
    //   (the proof fields are proof-irrelevant Props, so refl typechecks).
    let base = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let ha_ty = c.nonneg(a.clone());
        let (hz_id, _hz) = d.fresh_local(ha_ty.clone());
        let body = c.refl(&c.nnreal.clone(), c.ofrat(a.clone(), ha.clone()));
        d.finish_child(d.mk_lam(hz_id, BinderInfo::Default, ha_ty, body))
    };
    // subst motive a b h_eq base : Π (hz : 0≤b), ofRat a ha = ofRat b hz.
    let eq_subst = Expr::const_(
        Name::from_string("Eq.subst"),
        vec![Level::succ(Level::zero())],
    );
    let transported = Expr::apps(
        eq_subst,
        [c.rat.clone(), motive, a.clone(), b.clone(), h_eq, base],
    );
    // apply to hb : ofRat a ha = ofRat b hb.
    Expr::apps(transported, [hb.clone()])
}

/// Lemma B `NNReal.le_four_pow32_of_sq_le` proof value.
///
/// `(ofRat W)·(ofRat W) = ofRat(W·W)` (`ofRat_mul`) `≤ ofRat(16·x³)`
/// (`ofRat_le_ofRat` + the `Rat` hyp) `= (4·pow32)·(4·pow32)` (Lemma A, symm);
/// then `le_of_sq_le_sq` ⟹ `ofRat W ≤ 4·pow32`.
fn build_le_four_pow32(c: &DesqConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (w_id, w) = b.fresh_local(c.rat.clone());
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let hw_ty = c.nonneg(w.clone());
    let (hw_id, hw) = b.fresh_local(hw_ty.clone());
    let h0_ty = c.nonneg(x.clone());
    let (h0_id, h0) = b.fresh_local(h0_ty.clone());
    let h1_ty = c.rlt(x.clone(), c.rat_one.clone());
    let (h1_id, h1) = b.fresh_local(h1_ty.clone());
    let cube = c.cube16(&x);
    let hsq_ty = c.rle(c.rmul(w.clone(), w.clone()), cube.clone());
    let (hsq_id, hsq) = b.fresh_local(hsq_ty.clone());

    // Numerals.
    let four = c.ofnat_lit(4);
    let h4 = c.ofnat_nonneg(4);
    let four_nn = c.ofrat(four.clone(), h4.clone());
    let of_w = c.ofrat(w.clone(), hw.clone()); // ofRat W
    let pow = c.pow32(x.clone(), h0.clone());
    let fp = c.nnmul(four_nn.clone(), pow.clone()); // 4·pow32 = RHS target

    // a := ofRat W ; b := 4·pow32. Goal: NNReal.le a b.
    // hsq_nn : NNReal.le (mul a a)(mul b b).

    // (1) mul a a = ofRat(W·W)   (ofRat_mul W W hw hw hww).
    let ww = c.rmul(w.clone(), w.clone());
    let hww = c.rmul_nonneg(w.clone(), w.clone(), hw.clone(), hw.clone());
    let of_ww = c.ofrat(ww.clone(), hww.clone());
    let aa = c.nnmul(of_w.clone(), of_w.clone());
    let e_aa = c.nn_ofrat_mul(w.clone(), w.clone(), hw.clone(), hw.clone(), hww.clone()); // mul a a = ofRat(W·W)

    // (2) NNReal.le (ofRat(W·W))(ofRat(16·x³))   (ofRat_le_ofRat W·W cube hww hc hsq).
    let hc = c.rmul_nonneg(
        // 0 ≤ 16·x³ = (16·x)·(x·x): mul_nonneg of (16·x) and (x·x).
        c.rmul(c.ofnat_lit(16), x.clone()),
        c.rmul(x.clone(), x.clone()),
        c.rmul_nonneg(c.ofnat_lit(16), x.clone(), c.ofnat_nonneg(16), h0.clone()),
        c.rmul_nonneg(x.clone(), x.clone(), h0.clone(), h0.clone()),
    );
    let of_cube = c.ofrat(cube.clone(), hc.clone());
    let le_ofrat = c.nn_ofrat_le(
        ww.clone(),
        cube.clone(),
        hww.clone(),
        hc.clone(),
        hsq.clone(),
    );

    // (3) ofRat(16·x³) = mul b b   (Lemma A symm).
    //   Lemma A: (4·pow32)·(4·pow32) = ofRat(16·x³); symm gives ofRat(16·x³) = (4·pow32)².
    let bb = c.nnmul(fp.clone(), fp.clone());
    let lemma_a = Expr::apps(
        c.pow32_four_sq_thm.clone(),
        [x.clone(), h0.clone(), h1.clone(), hc.clone()],
    ); // bb = of_cube
    let a_symm = c.nn_symm(bb.clone(), of_cube.clone(), lemma_a); // of_cube = bb

    // Transport (2) along (1) on the LHS and (3) on the RHS to get
    //   NNReal.le (mul a a)(mul b b).
    // step_lhs : NNReal.le (mul a a)(ofRat(16·x³))  — subst ofRat(W·W) → mul a a along symm e_aa.
    let e_aa_symm = c.nn_symm(aa.clone(), of_ww.clone(), e_aa); // ofRat(W·W) = mul a a
    let motive_lhs = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.nnreal.clone());
        let body = c.nnle(z, of_cube.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let eq_subst = Expr::const_(
        Name::from_string("Eq.subst"),
        vec![Level::succ(Level::zero())],
    );
    let step_lhs = Expr::apps(
        eq_subst.clone(),
        [
            c.nnreal.clone(),
            motive_lhs,
            of_ww.clone(),
            aa.clone(),
            e_aa_symm,
            le_ofrat,
        ],
    );
    // step_rhs : NNReal.le (mul a a)(mul b b)  — subst ofRat(16·x³) → mul b b along a_symm.
    let motive_rhs = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.nnreal.clone());
        let body = c.nnle(aa.clone(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let hsq_nn = Expr::apps(
        eq_subst,
        [
            c.nnreal.clone(),
            motive_rhs,
            of_cube.clone(),
            bb.clone(),
            a_symm,
            step_lhs,
        ],
    );

    // le_of_sq_le_sq a b hsq_nn : NNReal.le a b.
    let proof = c.nn_le_of_sq(of_w.clone(), fp.clone(), hsq_nn);

    let e = b.mk_lam(hsq_id, BinderInfo::Default, hsq_ty, proof);
    let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, e);
    let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
    let e = b.mk_lam(hw_id, BinderInfo::Default, hw_ty, e);
    let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "NNReal.sq_mul",
        "NNReal.pow32_four_sq",
        "NNReal.le_four_pow32_of_sq_le",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_desquare()
            .expect("init_algebra_nnreal_desquare");
        env.init_algebra_nnreal_desquare().expect("idempotent");
        env
    }

    #[test]
    fn test_desquare_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_desquare_constructive_empty_closure() {
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
