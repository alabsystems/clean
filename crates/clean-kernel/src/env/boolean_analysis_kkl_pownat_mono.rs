// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL bridge — the `Rat.powNat` exponent-monotonicity primitive.
//!
//! This is the load-bearing arithmetic atom of the **spectral low-band
//! extraction** half of the O'Donnell §9.6 hypercontractive bridge. The bridge
//! needs to bound the UNWEIGHTED level-`≤k` Fourier mass of a function by the
//! NOISE-weighted full mass `Σ_S (ρ²)^{|S|}·A(S)²` (`= ‖T_ρ a‖₂²` un-normalized,
//! the `noise_spectral_level` interface). Term-by-term that extraction is
//! `A(S)² ≤ (ρ⁻²)^k·(ρ²)^{|S|}·A(S)²` for `|S| ≤ k` — which, after clearing the
//! positive `(ρ²)^{|S|}`, is exactly `(ρ⁻²)^{|S|} ≤ (ρ⁻²)^k`, i.e. `powNat`
//! monotone in the exponent for a base `≥ 1`.
//!
//! ```text
//! Rat.powNat_le_powNat_right : ∀ (b : Rat) (m n : Nat),
//!   Rat.le Rat.one b → Nat.le m n → Rat.le (Rat.powNat b m) (Rat.powNat b n)
//! ```
//!
//! i.e. `1 ≤ b → m ≤ n → b^m ≤ b^n` over `Rat`. The `Rat` analogue of the landed
//! `Nat.pow_le_pow_right` (`algebra_nat_pow_le_pow_right_proof.rs`). It is the
//! genuine missing primitive: the `Rat.powNat` ladder has `powNat_zero`,
//! `powNat_succ`, `powNat_add`, and `powNat_nonneg`, but NO exponent-monotonicity
//! lemma — the precise rung the spectral level-restriction pivots through.
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! Induction on the `Nat.le m n` witness via `@Nat.le.rec` (parameter `m`),
//! motive `λ (t : Nat) (_ : Nat.le m t) => Rat.le (b^m) (b^t)`:
//!
//! - **refl minor**: `Rat.le_refl (b^m) : b^m ≤ b^m`.
//! - **step minor**: given `t`, `_ : m ≤ t`, `ih : b^m ≤ b^t`, the goal
//!   `b^m ≤ b^(succ t)` reduces (one ι-step of `Rat.powNat`'s `Nat.rec` carrier)
//!   to `b^m ≤ b·b^t`. We chain `ih` with the one-step monotonicity
//!   `b^t ≤ b·b^t` through `Rat.le_trans`. The one-step fact is built by
//!   transporting `Rat.mul_le_mul_of_nonneg_right (b^t) 1 b h1 h_bt_nonneg :
//!   1·b^t ≤ b·b^t` along `Rat.one_mul (b^t) : 1·b^t = b^t` (motive `λx, x ≤
//!   b·b^t`), where `h_bt_nonneg : 0 ≤ b^t` is `Rat.powNat_nonneg b t h_b_nonneg`
//!   and `h_b_nonneg : 0 ≤ b` is `Rat.le_trans 0 1 b zero_le_one h1`.
//!
//! Every leaf (`Rat.le_refl`, `Rat.le_trans`, `Rat.mul_le_mul_of_nonneg_right`,
//! `Rat.one_mul`, `Rat.powNat_nonneg`, `zero_le_one`, `Eq.subst`, `Nat.le.rec`,
//! `Nat.le.refl`) is `Constructive` with empty closure, so this primitive is too.
//! No axiom is added or removed. Idempotent.

use super::boolean_analysis_hc_bounds_proofs::HcBoundsConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Self-contained atoms for the `powNat` monotonicity primitive. Shares the
/// `HcBoundsConsts` Rat-order surface so all terms stay byte-identical to the
/// on-branch `powNat_nonneg` / hc-bound infrastructure.
struct PowNatMonoConsts {
    hc: HcBoundsConsts,
    nat: Expr,
    pow_nat: Expr,
    nat_le: Expr,
    nat_le_rec: Expr,
    rat_le_refl: Expr,
    pow_nat_nonneg: Expr,
}

impl PowNatMonoConsts {
    fn new() -> Self {
        Self {
            hc: HcBoundsConsts::new(),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            pow_nat: Expr::const_(Name::from_string("Rat.powNat"), vec![]),
            nat_le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            nat_le_rec: Expr::const_(Name::from_string("Nat.le.rec"), vec![]),
            rat_le_refl: Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
            pow_nat_nonneg: Expr::const_(Name::from_string("Rat.powNat_nonneg"), vec![]),
        }
    }

    fn rat(&self) -> Expr {
        self.hc.rat()
    }
    fn zero(&self) -> Expr {
        self.hc.zero()
    }
    fn one(&self) -> Expr {
        self.hc.one()
    }
    fn pow(&self, b: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [b.clone(), k.clone()])
    }
    fn nat_le_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        self.hc.le(a, b)
    }
    /// `Rat.le_refl a : a ≤ a`.
    fn rat_le_refl_of(&self, a: Expr) -> Expr {
        Expr::app(self.rat_le_refl.clone(), a)
    }
    /// `Rat.powNat_nonneg b k h : 0 ≤ b^k`.
    fn pow_nonneg(&self, b: Expr, k: Expr, h: Expr) -> Expr {
        Expr::apps(self.pow_nat_nonneg.clone(), [b, k, h])
    }
}

/// `∀ (b : Rat) (m n : Nat), 1 ≤ b → m ≤ n → b^m ≤ b^n`.
fn build_type(c: &PowNatMonoConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (bv_id, bv) = b.fresh_local(c.rat());
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let h1_ty = c.rat_le(c.one(), bv.clone());
    let (h1_id, _h1) = b.fresh_local(h1_ty.clone());
    let hmn_ty = c.nat_le_of(m.clone(), n.clone());
    let (hmn_id, _hmn) = b.fresh_local(hmn_ty.clone());
    let concl = c.rat_le(c.pow(&bv, &m), c.pow(&bv, &n));
    let e = b.mk_pi(hmn_id, BinderInfo::Default, hmn_ty, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// Body: `λ b m n (h1 : 1 ≤ b) (hmn : m ≤ n) => @Nat.le.rec m motive refl step n hmn`.
fn build_value(c: &PowNatMonoConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (bv_id, bv) = b.fresh_local(c.rat());
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let h1_ty = c.rat_le(c.one(), bv.clone());
    let (h1_id, h1) = b.fresh_local(h1_ty.clone());
    let hmn_ty = c.nat_le_of(m.clone(), n.clone());
    let (hmn_id, hmn) = b.fresh_local(hmn_ty.clone());

    let pow_b_m = c.pow(&bv, &m);

    // h_b_nonneg : 0 ≤ b   := Rat.le_trans 0 1 b zero_le_one h1
    let h_b_nonneg = c.hc.ltrans(
        c.zero(),
        c.one(),
        bv.clone(),
        c.hc.zero_le_one(),
        h1.clone(),
    );

    // motive : λ (t : Nat) (_ : Nat.le m t) => Rat.le (b^m) (b^t)
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.nat.clone());
        let le_m_t = c.nat_le_of(m.clone(), t.clone());
        let (ht_id, _ht) = mb.fresh_local(le_m_t.clone());
        let body = c.rat_le(pow_b_m.clone(), c.pow(&bv, &t));
        let lam_h = mb.mk_lam(ht_id, BinderInfo::Default, le_m_t, body);
        let lam_t = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), lam_h);
        mb.finish_child(lam_t)
    };

    // refl minor : Rat.le_refl (b^m) : b^m ≤ b^m
    let minor_refl = c.rat_le_refl_of(pow_b_m.clone());

    // step minor : λ {t} (_ : m ≤ t) (ih : b^m ≤ b^t) =>
    //   Rat.le_trans (b^m) (b^t) (b·b^t) ih step_le : b^m ≤ b·b^t  (≡ b^(succ t))
    // where step_le : b^t ≤ b·b^t
    //   := subst_le_left (motive λx, x ≤ b·b^t) (from 1·b^t) (to b^t)
    //        (Rat.one_mul (b^t) : 1·b^t = b^t)
    //        (Rat.mul_le_mul_of_nonneg_right (b^t) 1 b h1 (0 ≤ b^t) : 1·b^t ≤ b·b^t)
    let minor_step = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = sb.fresh_local(c.nat.clone());
        let le_m_t = c.nat_le_of(m.clone(), t.clone());
        let (ht_id, _ht) = sb.fresh_local(le_m_t.clone());
        let pow_b_t = c.pow(&bv, &t);
        let ih_ty = c.rat_le(pow_b_m.clone(), pow_b_t.clone());
        let (ih_id, ih) = sb.fresh_local(ih_ty.clone());

        let b_mul_pow_b_t = c.hc.mul(bv.clone(), pow_b_t.clone()); // b·b^t  (≡ b^(succ t))
        let one_mul_pow_b_t = c.hc.mul(c.one(), pow_b_t.clone()); // 1·b^t

        // h_bt_nonneg : 0 ≤ b^t
        let h_bt_nonneg = c.pow_nonneg(bv.clone(), t.clone(), h_b_nonneg.clone());
        // mlr (b^t) 1 b h1 h_bt_nonneg : 1·b^t ≤ b·b^t
        let mlr = c.hc.mlr(
            pow_b_t.clone(),
            c.one(),
            bv.clone(),
            h1.clone(),
            h_bt_nonneg,
        );
        // one_mul (b^t) : 1·b^t = b^t
        let one_mul_eq = c.hc.one_mul(pow_b_t.clone());
        // step_le : b^t ≤ b·b^t
        let step_le = c.hc.subst_le_left(
            &sb,
            b_mul_pow_b_t.clone(),
            one_mul_pow_b_t,
            pow_b_t.clone(),
            one_mul_eq,
            mlr,
        );
        // Rat.le_trans (b^m) (b^t) (b·b^t) ih step_le
        let body =
            c.hc.ltrans(pow_b_m.clone(), pow_b_t.clone(), b_mul_pow_b_t, ih, step_le);
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
        let lam_h = sb.mk_lam(ht_id, BinderInfo::Default, le_m_t, lam_ih);
        let lam_t = sb.mk_lam(t_id, BinderInfo::Implicit, c.nat.clone(), lam_h);
        sb.finish_child(lam_t)
    };

    // @Nat.le.rec m motive refl step n hmn
    let rec_app = Expr::apps(
        c.nat_le_rec.clone(),
        [
            m.clone(),
            motive,
            minor_refl,
            minor_step,
            n.clone(),
            hmn.clone(),
        ],
    );
    let e = b.mk_lam(hmn_id, BinderInfo::Default, hmn_ty, rec_app);
    let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

// ───────────── antitone version (fractional base 0 ≤ b ≤ 1) ─────────────────
//
//   Rat.powNat_le_powNat_right_antitone : ∀ (b : Rat) (m n : Nat),
//     Rat.le Rat.zero b → Rat.le b Rat.one → Nat.le m n
//       → Rat.le (Rat.powNat b n) (Rat.powNat b m)
//
// i.e. `0 ≤ b ≤ 1 → m ≤ n → b^n ≤ b^m` — `Rat.powNat` ANTITONE in the exponent
// for a base in `[0,1]`. This is the rung the low-band spectral extraction uses
// in its clean `(ρ²)^k · M^{≤k}(a) ≤ ‖T_ρ a‖₂²` form: each level-`≤k` term obeys
// `(1/9)^k·A(S)² ≤ (1/9)^{|S|}·A(S)²` because `(1/9)^k ≤ (1/9)^{|S|}` when
// `|S| ≤ k` — exactly this antitone bound at base `ρ² = 1/9 ∈ [0,1]`. No
// fractional-base inverse identity is needed.
//
// Same `@Nat.le.rec` induction on the `m ≤ n` witness, motive
// `λ (t : Nat) (_ : m ≤ t) => b^t ≤ b^m` (note the DIRECTION is flipped). The
// step minor shows the one-step DECREASE `b^(succ t) ≤ b^t`, i.e. `b·b^t ≤ b^t`,
// from `b ≤ 1` and `0 ≤ b^t`: `mlr (b^t) b 1 (b ≤ 1) (0 ≤ b^t) : b·b^t ≤ 1·b^t`,
// transported along `one_mul (b^t) : 1·b^t = b^t` (motive `λx, b·b^t ≤ x`) — then
// chained with `ih : b^t ≤ b^m` via `Rat.le_trans` to land `b^(succ t) ≤ b^m`.

/// `∀ (b : Rat) (m n : Nat), 0 ≤ b → b ≤ 1 → m ≤ n → b^n ≤ b^m`.
fn build_antitone_type(c: &PowNatMonoConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (bv_id, bv) = b.fresh_local(c.rat());
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let h0_ty = c.rat_le(c.zero(), bv.clone());
    let (h0_id, _h0) = b.fresh_local(h0_ty.clone());
    let h1_ty = c.rat_le(bv.clone(), c.one());
    let (h1_id, _h1) = b.fresh_local(h1_ty.clone());
    let hmn_ty = c.nat_le_of(m.clone(), n.clone());
    let (hmn_id, _hmn) = b.fresh_local(hmn_ty.clone());
    let concl = c.rat_le(c.pow(&bv, &n), c.pow(&bv, &m));
    let e = b.mk_pi(hmn_id, BinderInfo::Default, hmn_ty, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, e);
    let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// Body: `λ b m n (h0 : 0 ≤ b) (h1 : b ≤ 1) (hmn : m ≤ n) =>
///          @Nat.le.rec m motive refl step n hmn`.
fn build_antitone_value(c: &PowNatMonoConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (bv_id, bv) = b.fresh_local(c.rat());
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let h0_ty = c.rat_le(c.zero(), bv.clone());
    let (h0_id, h0) = b.fresh_local(h0_ty.clone());
    let h1_ty = c.rat_le(bv.clone(), c.one());
    let (h1_id, h1) = b.fresh_local(h1_ty.clone());
    let hmn_ty = c.nat_le_of(m.clone(), n.clone());
    let (hmn_id, hmn) = b.fresh_local(hmn_ty.clone());

    let pow_b_m = c.pow(&bv, &m);

    // motive : λ (t : Nat) (_ : m ≤ t) => Rat.le (b^t) (b^m)   (DIRECTION flipped)
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.nat.clone());
        let le_m_t = c.nat_le_of(m.clone(), t.clone());
        let (ht_id, _ht) = mb.fresh_local(le_m_t.clone());
        let body = c.rat_le(c.pow(&bv, &t), pow_b_m.clone());
        let lam_h = mb.mk_lam(ht_id, BinderInfo::Default, le_m_t, body);
        let lam_t = mb.mk_lam(t_id, BinderInfo::Default, c.nat.clone(), lam_h);
        mb.finish_child(lam_t)
    };

    // refl minor : Rat.le_refl (b^m) : b^m ≤ b^m
    let minor_refl = c.rat_le_refl_of(pow_b_m.clone());

    // step minor : λ {t} (_ : m ≤ t) (ih : b^t ≤ b^m) =>
    //   Rat.le_trans (b·b^t) (b^t) (b^m) step_le ih : b·b^t ≤ b^m  (≡ b^(succ t) ≤ b^m)
    // where step_le : b·b^t ≤ b^t
    //   := subst_le_right (motive λx, b·b^t ≤ x) (from 1·b^t) (to b^t)
    //        (Rat.one_mul (b^t) : 1·b^t = b^t)
    //        (Rat.mul_le_mul_of_nonneg_right (b^t) b 1 h1 (0 ≤ b^t) : b·b^t ≤ 1·b^t)
    let minor_step = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = sb.fresh_local(c.nat.clone());
        let le_m_t = c.nat_le_of(m.clone(), t.clone());
        let (ht_id, _ht) = sb.fresh_local(le_m_t.clone());
        let pow_b_t = c.pow(&bv, &t);
        let ih_ty = c.rat_le(pow_b_t.clone(), pow_b_m.clone());
        let (ih_id, ih) = sb.fresh_local(ih_ty.clone());

        let b_mul_pow_b_t = c.hc.mul(bv.clone(), pow_b_t.clone()); // b·b^t  (≡ b^(succ t))
        let one_mul_pow_b_t = c.hc.mul(c.one(), pow_b_t.clone()); // 1·b^t

        // h_bt_nonneg : 0 ≤ b^t   := powNat_nonneg b t h0
        let h_bt_nonneg = c.pow_nonneg(bv.clone(), t.clone(), h0.clone());
        // mlr (b^t) b 1 h1 h_bt_nonneg : b·b^t ≤ 1·b^t   (b·a ≤ c·a from b ≤ c, here b≤1)
        let mlr = c.hc.mlr(
            pow_b_t.clone(),
            bv.clone(),
            c.one(),
            h1.clone(),
            h_bt_nonneg,
        );
        // one_mul (b^t) : 1·b^t = b^t
        let one_mul_eq = c.hc.one_mul(pow_b_t.clone());
        // step_le : b·b^t ≤ b^t   (rewrite the RHS 1·b^t → b^t)
        let step_le = c.hc.subst_le_right(
            &sb,
            b_mul_pow_b_t.clone(),
            one_mul_pow_b_t,
            pow_b_t.clone(),
            one_mul_eq,
            mlr,
        );
        // Rat.le_trans (b·b^t) (b^t) (b^m) step_le ih : b·b^t ≤ b^m
        let body =
            c.hc.ltrans(b_mul_pow_b_t, pow_b_t.clone(), pow_b_m.clone(), step_le, ih);
        let lam_ih = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
        let lam_h = sb.mk_lam(ht_id, BinderInfo::Default, le_m_t, lam_ih);
        let lam_t = sb.mk_lam(t_id, BinderInfo::Implicit, c.nat.clone(), lam_h);
        sb.finish_child(lam_t)
    };

    // @Nat.le.rec m motive refl step n hmn
    let rec_app = Expr::apps(
        c.nat_le_rec.clone(),
        [
            m.clone(),
            motive,
            minor_refl,
            minor_step,
            n.clone(),
            hmn.clone(),
        ],
    );
    let e = b.mk_lam(hmn_id, BinderInfo::Default, hmn_ty, rec_app);
    let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, e);
    let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

impl Environment {
    /// Register `Rat.powNat_le_powNat_right` — the `Rat.powNat`
    /// exponent-monotonicity primitive `1 ≤ b → m ≤ n → b^m ≤ b^n`. Induction on
    /// the `Nat.le m n` witness via `@Nat.le.rec`. Kernel-checked, constructive,
    /// empty admitted-axiom closure. Idempotent.
    pub(crate) fn register_rat_pow_nat_le_pow_nat_right(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.powNat_le_powNat_right");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_le()?; // Nat.le, Nat.le.refl, Nat.le.rec
        self.register_rat_pow_nat()?; // Rat.powNat
        self.register_rat_pow_nat_nonneg()?; // Rat.powNat_nonneg
        self.register_rat_order_proofs()?; // Rat.le_refl
        self.register_rat_le_trans_proof()?; // Rat.le_trans
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_le_mul_of_nonneg_right
        self.init_boolean_analysis_hc_bounds()?; // zero_le_one + HcBoundsConsts surface

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = PowNatMonoConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_type(&c),
            value: build_value(&c),
        })
    }

    /// Register `Rat.powNat_le_powNat_right_antitone` — the `Rat.powNat`
    /// exponent-ANTITONE primitive `0 ≤ b → b ≤ 1 → m ≤ n → b^n ≤ b^m`, for a
    /// base in `[0,1]`. The rung the low-band spectral extraction uses at base
    /// `ρ² = 1/9` (`(1/9)^k ≤ (1/9)^{|S|}` for `|S| ≤ k`). Induction on the
    /// `Nat.le m n` witness via `@Nat.le.rec`. Kernel-checked, constructive, empty
    /// admitted-axiom closure. Idempotent.
    pub(crate) fn register_rat_pow_nat_le_pow_nat_right_antitone(
        &mut self,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.powNat_le_powNat_right_antitone");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_le()?; // Nat.le, Nat.le.refl, Nat.le.rec
        self.register_rat_pow_nat()?; // Rat.powNat
        self.register_rat_pow_nat_nonneg()?; // Rat.powNat_nonneg
        self.register_rat_order_proofs()?; // Rat.le_refl
        self.register_rat_le_trans_proof()?; // Rat.le_trans
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_le_mul_of_nonneg_right
        self.init_boolean_analysis_hc_bounds()?; // zero_le_one + HcBoundsConsts surface

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = PowNatMonoConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_antitone_type(&c),
            value: build_antitone_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_rat_pow_nat_le_pow_nat_right()
            .expect("register_rat_pow_nat_le_pow_nat_right");
        env.register_rat_pow_nat_le_pow_nat_right()
            .expect("idempotent");
        env
    }

    fn check_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        let deps = env.axiom_deps(&nm).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(names.is_empty(), "{name} must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
    }

    #[test]
    fn test_pow_nat_le_pow_nat_right_is_constructive_theorem() {
        check_constructive(&env(), "Rat.powNat_le_powNat_right");
    }

    #[test]
    fn test_pow_nat_le_pow_nat_right_antitone_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_rat_pow_nat_le_pow_nat_right_antitone()
            .expect("register_rat_pow_nat_le_pow_nat_right_antitone");
        env.register_rat_pow_nat_le_pow_nat_right_antitone()
            .expect("idempotent");
        check_constructive(&env, "Rat.powNat_le_powNat_right_antitone");
    }
}
