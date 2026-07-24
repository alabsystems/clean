// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the MATERIALISED `4/3`-norm identity M1 (§10.6 wall),
//! axiom-free, at the genuine `NNReal` level.
//!
//! # What M1 is (and why it is NOT a refl)
//!
//! For the flat derivative bump `g ∈ {0,±2}` on the cube, the (un-normalised)
//! `4/3`-norm is the sum of the per-coordinate contributions `|g x|^{4/3}`, which
//! is `2^{4/3}` on the disagreement support and `0` off it:
//!
//! ```text
//!   ‖g‖_{4/3} = Σ_x |g x|^{4/3} = (#support)·2^{4/3} = cnt · 2^{4/3},
//!   ‖g‖_{4/3}⁴ = (Σ_x |g x|^{4/3})³ = (cnt · 2^{4/3})³ = 16·cnt³.
//! ```
//!
//! The genuine content is the MATERIALISED `NNReal` equation: the *actual sum*
//! `Σ_j (2^{4/3} · ofRat(h j))` over a nonneg indicator `h : Fin m → Rat` (whose
//! count `cnt := Fin.sum m h` is a genuine `Fin.sum`, NOT a free binder) has cube
//! equal to `ofRat(16·cnt³)`. There is NO `b43 := 16·cnt³` defined-then-refl'd:
//! the `16·cnt³` is *derived* from the materialised sum via the landed
//! `NNReal.twoFourThirds_count_cubed` keystone (whose own `(cnt·2^{4/3})³ = 16cnt³`
//! is proven through the `cbrt(1/4)` carrier algebra, never `cbrt 2`).
//!
//! When instantiated at `m := 2^n`, `h := ind∘disagree∘hcDecode`, the count
//! `Fin.sum (2^n) (ind∘disagree∘hcDecode)` δ-reduces to
//! `BoolAnalysis.subsetSum n (ind∘disagree)` — the real disagreement count — so
//! this is the genuine `‖D_i f‖_{4/3}⁴ = 16·count³`, materialised.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `BoolAnalysis.deriv_norm_sum_eq_count_smul` (STEP 3, the support sum-eval):
//!   ```text
//!     ∀ (m : Nat)(h : Fin m → Rat)(hg : ∀ j, 0 ≤ h j)(hsum : 0 ≤ Fin.sum m h),
//!       NNReal.finSum m (fun j => NNReal.mul twoFourThirds (NNReal.ofRat (h j)(hg j)))
//!         = NNReal.mul (NNReal.ofRat (Fin.sum m h) hsum) twoFourThirds
//!   ```
//!   `finSum_smul` (pull `2^{4/3}`) ∘ `congrArg` of `finSum_ofRat` (the
//!   `NNReal`-indicator sum collapses to `ofRat cnt`) ∘ `NNReal.mul_comm`.
//!
//! - `BoolAnalysis.m1_norm_cubed_materialized` (STEP 4, the genuine M1):
//!   ```text
//!     ∀ (m : Nat)(h : Fin m → Rat)(hg)(hsum),
//!       (Σcontribution)³ = NNReal.ofRat ((16·cnt)·(cnt·cnt)) hpos      (cnt := Fin.sum m h)
//!   ```
//!   STEP 3 rewrites `Σcontribution → ofRat cnt · 2^{4/3}` (cubed by `congrArg`),
//!   then `NNReal.twoFourThirds_count_cubed cnt hsum` supplies
//!   `(ofRat cnt · 2^{4/3})³ = ofRat(16·cnt³)`.
//!
//! Each is `Declaration::Theorem`, `ProofQuality::Constructive`, with an empty
//! admitted-axiom closure (foundational only). NO `sorry` /
//! `add_decl_unchecked` / `add_decl_structural`. FORBIDDEN here: total
//! `NNReal.toRat`, `NNReal.cbrt 2`, `Real`/`Real.sqrt`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the materialised M1 norm.
pub(crate) struct M1NormConsts {
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_mul: Expr,
    rat_le: Expr,
    rat_mul_nonneg: Expr,
    rat_ofnat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    rat_le_of_ble: Expr,
    bool_ty: Expr,
    bool_true: Expr,
    fin: Expr,
    fin_sum: Expr,
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_of_rat: Expr,
    nnreal_finsum: Expr,
    nnreal_tft: Expr,
    nnreal_finsum_smul: Expr,
    nnreal_finsum_ofrat: Expr,
    nnreal_mul_comm: Expr,
    nnreal_tft_count_cubed: Expr,
    // Eq.{1}.
    eq1: Expr,
    eq_trans1: Expr,
    congr_arg1: Expr,
}

impl M1NormConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let kl = |s: &str| Expr::const_(Name::from_string(s), vec![l1.clone()]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_mul: k("Rat.mul"),
            rat_le: k("Rat.le"),
            rat_mul_nonneg: k("Rat.mul_nonneg"),
            rat_ofnat: k("Rat.ofNat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            rat_le_of_ble: k("Rat.le_of_ble_eq_true"),
            bool_ty: k("Bool"),
            bool_true: k("Bool.true"),
            fin: k("Fin"),
            fin_sum: k("Fin.sum"),
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_finsum: k("NNReal.finSum"),
            nnreal_tft: k("NNReal.twoFourThirds"),
            nnreal_finsum_smul: k("NNReal.finSum_smul"),
            nnreal_finsum_ofrat: k("NNReal.finSum_ofRat"),
            nnreal_mul_comm: k("NNReal.mul_comm"),
            nnreal_tft_count_cubed: k("NNReal.twoFourThirds_count_cubed"),
            eq1: kl("Eq"),
            eq_trans1: kl("Eq.trans"),
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
    /// `Rat.ofNat n`.
    fn ofnat_lit(&self, n: usize) -> Expr {
        Expr::app(self.rat_ofnat.clone(), self.nat_lit(n))
    }
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn nonneg(&self, a: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [self.rat_zero.clone(), a])
    }
    fn rmul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.rat_mul_nonneg.clone(), [a, b, ha, hb])
    }
    /// `0 ≤ (Rat.ofNat n)` via the boolean reflection idiom.
    fn ofnat_nonneg(&self, n: usize) -> Expr {
        let lit = self.ofnat_lit(n);
        let refl = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [self.bool_ty.clone(), self.bool_true.clone()],
        );
        Expr::apps(
            self.rat_le_of_ble.clone(),
            [self.rat_zero.clone(), lit, refl],
        )
    }

    // ── Fin / NNReal constructors ────────────────────────────────────────────
    fn fin_to(&self, m: &Expr, t: &Expr) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            Expr::app(self.fin.clone(), m.clone()),
            t.clone(),
        )
    }
    fn fin_sum(&self, m: &Expr, h: &Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [m.clone(), h.clone()])
    }
    fn ofrat(&self, x: &Expr, hx: &Expr) -> Expr {
        Expr::apps(self.nnreal_of_rat.clone(), [x.clone(), hx.clone()])
    }
    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn finsum(&self, m: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.nnreal_finsum.clone(), [m.clone(), f.clone()])
    }
    fn tft(&self) -> Expr {
        self.nnreal_tft.clone()
    }
    /// The per-coordinate contribution function `fun j => mul tft (ofRat (h j)(hg j))`.
    fn contribution_fn(&self, parent: &EnvDeclBuilder, m: &Expr, h: &Expr, hg: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_m = Expr::app(self.fin.clone(), m.clone());
        let (j_id, j) = b.fresh_local(fin_m.clone());
        let hj = Expr::app(hg.clone(), j.clone()); // hg j : 0 ≤ h j
        let body = self.nnmul(
            &self.tft(),
            &self.ofrat(&Expr::app(h.clone(), j.clone()), &hj),
        );
        b.finish_child(b.mk_lam(j_id, BinderInfo::Default, fin_m, body))
    }
    /// The `ofRat∘h` function `fun j => ofRat (h j)(hg j)`.
    fn ofrat_h_fn(&self, parent: &EnvDeclBuilder, m: &Expr, h: &Expr, hg: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_m = Expr::app(self.fin.clone(), m.clone());
        let (j_id, j) = b.fresh_local(fin_m.clone());
        let hj = Expr::app(hg.clone(), j.clone());
        let body = self.ofrat(&Expr::app(h.clone(), j.clone()), &hj);
        b.finish_child(b.mk_lam(j_id, BinderInfo::Default, fin_m, body))
    }

    // ── Eq.{1} plumbing over NNReal ──────────────────────────────────────────
    fn eq_nn(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.eq1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone()],
        )
    }
    fn nn_trans(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
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
    /// `@congrArg.{1,1} NNReal NNReal a b f h : (f a) = (f b)`.
    fn nn_congr(&self, a: &Expr, b: &Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg1.clone(),
            [
                self.nnreal.clone(),
                self.nnreal.clone(),
                a.clone(),
                b.clone(),
                f,
                h,
            ],
        )
    }
    /// `fun w : NNReal => mul l w` (for congr on the right factor).
    fn f_mul_left(&self, parent: &EnvDeclBuilder, l: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(self.nnreal.clone());
        let body = self.nnmul(l, &w);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.nnreal.clone(), body))
    }
    /// `fun w : NNReal => (w·w)·w` (cube congruence motive).
    fn f_cube(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(self.nnreal.clone());
        let body = self.nnmul(&self.nnmul(&w, &w), &w);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.nnreal.clone(), body))
    }
}

impl Environment {
    /// Register `BoolAnalysis.deriv_norm_sum_eq_count_smul` and
    /// `BoolAnalysis.m1_norm_cubed_materialized`. Idempotent; foundational-only.
    pub fn init_boolean_analysis_kkl_m1_norm(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_two_four_thirds()?; // tft, twoFourThirds_count_cubed, carrier
        self.init_algebra_nnreal_finsum_smul()?; // NNReal.finSum_smul
        self.init_algebra_nnreal_finsum_ofrat()?; // NNReal.finSum_ofRat (+ ofRat_add)
        self.init_algebra_nnreal_reverse_square()?; // NNReal.mul_comm
        self.register_rat_order_proofs()?; // Rat.mul_nonneg
        self.register_rat_minmax_proofs()?; // Rat.le_of_ble_eq_true
        self.init_eq()?;

        let c = M1NormConsts::new();
        self.register_deriv_norm_sum_eq_count_smul(&c)?;
        self.register_m1_norm_cubed_materialized(&c)?;
        Ok(())
    }

    /// STEP 3 — `BoolAnalysis.deriv_norm_sum_eq_count_smul`.
    fn register_deriv_norm_sum_eq_count_smul(&mut self, c: &M1NormConsts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.deriv_norm_sum_eq_count_smul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = sum_eval_type(c);
        let value = build_sum_eval(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// STEP 4 — `BoolAnalysis.m1_norm_cubed_materialized`.
    fn register_m1_norm_cubed_materialized(&mut self, c: &M1NormConsts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.m1_norm_cubed_materialized");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = m1_type(c);
        let value = build_m1(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `∀ m h hg hsum, Σ_j (tft · ofRat(h j)) = (ofRat cnt) · tft`.
fn sum_eval_type(c: &M1NormConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (h_id, h) = b.fresh_local(c.fin_to(&m, &c.rat));
    let hg_ty = forall_nonneg_ty(c, &b, &m, &h);
    let (hg_id, hg) = b.fresh_local(hg_ty.clone());
    let cnt = c.fin_sum(&m, &h);
    let hsum_ty = c.nonneg(cnt.clone());
    let (hsum_id, hsum) = b.fresh_local(hsum_ty.clone());

    let contribution = c.contribution_fn(&b, &m, &h, &hg);
    let lhs = c.finsum(&m, &contribution);
    let rhs = c.nnmul(&c.ofrat(&cnt, &hsum), &c.tft());
    let concl = c.eq_nn(&lhs, &rhs);

    let e = b.mk_pi(hsum_id, BinderInfo::Default, hsum_ty, concl);
    let e = b.mk_pi(hg_id, BinderInfo::Default, hg_ty, e);
    let e = b.mk_pi(h_id, BinderInfo::Default, c.fin_to(&m, &c.rat), e);
    b.finish(b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e))
}

/// `∀ m h hg hsum, (Σcontribution)³ = ofRat((16·cnt)·(cnt·cnt))`.
fn m1_type(c: &M1NormConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (h_id, h) = b.fresh_local(c.fin_to(&m, &c.rat));
    let hg_ty = forall_nonneg_ty(c, &b, &m, &h);
    let (hg_id, hg) = b.fresh_local(hg_ty.clone());
    let cnt = c.fin_sum(&m, &h);
    let hsum_ty = c.nonneg(cnt.clone());
    let (hsum_id, hsum) = b.fresh_local(hsum_ty.clone());

    let contribution = c.contribution_fn(&b, &m, &h, &hg);
    let s = c.finsum(&m, &contribution);
    let lhs = c.nnmul(&c.nnmul(&s, &s), &s); // (Σ)³
    let (rhs, _hcube) = cube16(c, &cnt, &hsum);
    let concl = c.eq_nn(&lhs, &rhs);

    let e = b.mk_pi(hsum_id, BinderInfo::Default, hsum_ty, concl);
    let e = b.mk_pi(hg_id, BinderInfo::Default, hg_ty, e);
    let e = b.mk_pi(h_id, BinderInfo::Default, c.fin_to(&m, &c.rat), e);
    b.finish(b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e))
}

/// `∀ j : Fin m, 0 ≤ h j`.
fn forall_nonneg_ty(c: &M1NormConsts, parent: &EnvDeclBuilder, m: &Expr, h: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let fin_m = Expr::app(c.fin.clone(), m.clone());
    let (j_id, j) = d.fresh_local(fin_m.clone());
    let body = c.nonneg(Expr::app(h.clone(), j));
    d.finish_child(d.mk_pi(j_id, BinderInfo::Default, fin_m, body))
}

/// `ofRat((16·cnt)·(cnt·cnt)) hpos` + its nonneg proof `hpos`
/// (byte-identical grouping to `twoFourThirds_count_cubed`'s `cube16`).
fn cube16(c: &M1NormConsts, cnt: &Expr, hcnt: &Expr) -> (Expr, Expr) {
    let s16 = c.ofnat_lit(16);
    let h16 = c.ofnat_nonneg(16);
    let sixteen_cnt = c.rmul(s16.clone(), cnt.clone());
    let cnt_cnt = c.rmul(cnt.clone(), cnt.clone());
    let cube_rat = c.rmul(sixteen_cnt.clone(), cnt_cnt.clone());
    let h_16cnt = c.rmul_nonneg(s16, cnt.clone(), h16, hcnt.clone());
    let h_cntcnt = c.rmul_nonneg(cnt.clone(), cnt.clone(), hcnt.clone(), hcnt.clone());
    let h_cube = c.rmul_nonneg(sixteen_cnt, cnt_cnt, h_16cnt, h_cntcnt);
    let of_cube = c.ofrat(&cube_rat, &h_cube);
    (of_cube, h_cube)
}

/// STEP-3 proof term: `Σ(tft·ofRat h) = (ofRat cnt)·tft`.
fn build_sum_eval(c: &M1NormConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (h_id, h) = b.fresh_local(c.fin_to(&m, &c.rat));
    let hg_ty = forall_nonneg_ty(c, &b, &m, &h);
    let (hg_id, hg) = b.fresh_local(hg_ty.clone());
    let cnt = c.fin_sum(&m, &h);
    let hsum_ty = c.nonneg(cnt.clone());
    let (hsum_id, hsum) = b.fresh_local(hsum_ty.clone());

    let body = sum_eval_body(c, &b, &m, &h, &hg, &cnt, &hsum);

    let e = b.mk_lam(hsum_id, BinderInfo::Default, hsum_ty, body);
    let e = b.mk_lam(hg_id, BinderInfo::Default, hg_ty, e);
    let e = b.mk_lam(h_id, BinderInfo::Default, c.fin_to(&m, &c.rat), e);
    b.finish(b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e))
}

/// The inner `Σ(tft·ofRat h) = (ofRat cnt)·tft` proof (also reused by STEP 4).
fn sum_eval_body(
    c: &M1NormConsts,
    parent: &EnvDeclBuilder,
    m: &Expr,
    h: &Expr,
    hg: &Expr,
    cnt: &Expr,
    hsum: &Expr,
) -> Expr {
    let tft = c.tft();
    let ofrat_h = c.ofrat_h_fn(parent, m, h, hg); // fun j => ofRat (h j)
    let contribution = c.contribution_fn(parent, m, h, hg); // fun j => tft·ofRat(h j)

    // r1 : Σ(tft·ofRat h) = tft·Σ(ofRat h)   [finSum_smul m tft (ofRat_h)].
    let lhs = c.finsum(m, &contribution);
    let sum_ofrat_h = c.finsum(m, &ofrat_h); // Σ(ofRat h)
    let tft_sum = c.nnmul(&tft, &sum_ofrat_h); // tft·Σ(ofRat h)
    let r1 = Expr::apps(
        c.nnreal_finsum_smul.clone(),
        [m.clone(), tft.clone(), ofrat_h],
    );

    // r2 : Σ(ofRat h) = ofRat cnt   [finSum_ofRat m h hg hsum].
    let of_cnt = c.ofrat(cnt, hsum);
    let r2 = Expr::apps(
        c.nnreal_finsum_ofrat.clone(),
        [m.clone(), h.clone(), hg.clone(), hsum.clone()],
    );
    // r2' : tft·Σ(ofRat h) = tft·ofRat cnt   [congrArg (mul tft) r2].
    let f_tft = c.f_mul_left(parent, &tft);
    let tft_of_cnt = c.nnmul(&tft, &of_cnt);
    let r2c = c.nn_congr(&sum_ofrat_h, &of_cnt, f_tft, r2);

    // r3 : tft·ofRat cnt = ofRat cnt·tft   [mul_comm tft (ofRat cnt)].
    let of_cnt_tft = c.nnmul(&of_cnt, &tft);
    let r3 = Expr::apps(c.nnreal_mul_comm.clone(), [tft.clone(), of_cnt.clone()]);

    // chain: lhs = tft·Σ = tft·ofRat cnt = ofRat cnt·tft.
    let s1 = c.nn_trans(&lhs, &tft_sum, &tft_of_cnt, r1, r2c);
    c.nn_trans(&lhs, &tft_of_cnt, &of_cnt_tft, s1, r3)
}

/// STEP-4 proof term: `(Σcontribution)³ = ofRat((16·cnt)·(cnt·cnt))`.
fn build_m1(c: &M1NormConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (h_id, h) = b.fresh_local(c.fin_to(&m, &c.rat));
    let hg_ty = forall_nonneg_ty(c, &b, &m, &h);
    let (hg_id, hg) = b.fresh_local(hg_ty.clone());
    let cnt = c.fin_sum(&m, &h);
    let hsum_ty = c.nonneg(cnt.clone());
    let (hsum_id, hsum) = b.fresh_local(hsum_ty.clone());

    let tft = c.tft();
    let contribution = c.contribution_fn(&b, &m, &h, &hg);
    let s = c.finsum(&m, &contribution); // Σcontribution
    let of_cnt = c.ofrat(&cnt, &hsum);
    let qv = c.nnmul(&of_cnt, &tft); // ofRat cnt · tft

    // h_sum : Σcontribution = ofRat cnt · tft  (STEP 3 inlined).
    let h_sum = sum_eval_body(c, &b, &m, &h, &hg, &cnt, &hsum);

    // cube_congr : (Σ)³ = (ofRat cnt · tft)³   [congrArg (·³) h_sum].
    let f_cube = c.f_cube(&b);
    let s_cubed = c.nnmul(&c.nnmul(&s, &s), &s);
    let qv_cubed = c.nnmul(&c.nnmul(&qv, &qv), &qv);
    let cube_congr = c.nn_congr(&s, &qv, f_cube, h_sum);

    // count_cubed : (ofRat cnt · tft)³ = ofRat((16·cnt)·(cnt·cnt))
    //   [twoFourThirds_count_cubed cnt hsum].
    let (rhs, _hcube) = cube16(c, &cnt, &hsum);
    let count_cubed = Expr::apps(
        c.nnreal_tft_count_cubed.clone(),
        [cnt.clone(), hsum.clone()],
    );

    // chain: (Σ)³ = (ofRat cnt·tft)³ = ofRat(16cnt³).
    let full = c.nn_trans(&s_cubed, &qv_cubed, &rhs, cube_congr, count_cubed);

    let e = b.mk_lam(hsum_id, BinderInfo::Default, hsum_ty, full);
    let e = b.mk_lam(hg_id, BinderInfo::Default, hg_ty, e);
    let e = b.mk_lam(h_id, BinderInfo::Default, c.fin_to(&m, &c.rat), e);
    b.finish(b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "BoolAnalysis.deriv_norm_sum_eq_count_smul",
        "BoolAnalysis.m1_norm_cubed_materialized",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_m1_norm()
            .expect("init_boolean_analysis_kkl_m1_norm");
        env.init_boolean_analysis_kkl_m1_norm().expect("idempotent");
        env
    }

    #[test]
    fn test_m1_norm_lemmas_kernel_check() {
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
    fn test_m1_norm_lemmas_constructive_empty_closure() {
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
