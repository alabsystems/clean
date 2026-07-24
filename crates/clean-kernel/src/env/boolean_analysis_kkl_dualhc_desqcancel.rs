// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC — **STEP 4 de-square cancellation core**: the pure-`Rat`
//! algebraic lemma that turns the STEP-2 ⊕ STEP-3 chain
//! `(half·W)⁴ ≤ Y·W²` into the squared dual-HC `W² ≤ 16·Y`.
//!
//! ## What this proves
//!
//! ```text
//! BoolAnalysis.dualhc_step4_desq_cancel :
//!   ∀ (W Y : Rat),
//!     Rat.le Rat.zero Y
//!   → Rat.le (pow4 (Rat.mul half W)) (Rat.mul Y (Rat.mul W W))
//!   → Rat.le (Rat.mul W W) (Rat.mul (Rat.mul four four) Y)
//! ```
//!
//! with `half := Rat.inv Rat.two`, `four := Rat.mk (Int.ofNat 4) 1`,
//! `pow4 t := (t·t)·(t·t)`. Reading: `(half·W)⁴ ≤ Y·W²` ⟹ `W² ≤ 16·Y`. The
//! constant `16 = 4·4` is exactly the `½⁴` the half-derivative scaling emits, so
//! when STEP 4 instantiates `Y := m³·8^n` (`m = 2^n·Inf_i`, `8^n` from STEP 3)
//! and `W := Σ_x (T_{1/3}(D_i f) x)²`, this is the squared per-coordinate dual-HC
//! `W² ≤ 16·8^n·m³` (the obstruction report's `(‖T_{1/3}g‖₂²)² ≤ 16·Inf_i³`, in
//! the un-normalized cube where `m`/`8^n` carry the `2^n` measure factors).
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! Let `P := pow4 half = (half·half)·(half·half)`, `S := W·W`. Two structural
//! facts:
//!
//! - **`pow4 (half·W) = P·(S·S)`** — two `Rat.mul_mul_mul_comm`: first
//!   `(half·W)·(half·W) = (half·half)·(W·W) = (half·half)·S`, then
//!   `((half·half)·S)·((half·half)·S) = ((half·half)·(half·half))·(S·S) = P·(S·S)`.
//! - **`16·P = 1`** (`sixteen_pow4_half_eq_one`): `(four·four)·((h·h)·(h·h)) =
//!   (four·(h·h))·(four·(h·h)) = 1·1 = 1` (`mul_mul_mul_comm` + `four_half_sq_eq_one`
//!   twice + `mul_one`).
//!
//! Transport the hypothesis along the first fact to `P·(S·S) ≤ Y·S`; regroup
//! `P·(S·S) = (P·S)·S = S·(P·S)` and `Y·S = S·Y` (`mul_assoc`/`mul_comm`), so
//! `S·(P·S) ≤ S·Y`. Trichotomy `Rat.lt_or_eq_of_le 0 S (Rat.sq_nonneg W)`:
//!
//! - `S = 0`: goal `S ≤ 16·Y` is `0 ≤ 16·Y` (subst), discharged by
//!   `Rat.mul_nonneg (four·four) Y (0≤16) (0≤Y)` (`0≤16 = mul_nonneg four four
//!   (0≤four) (0≤four)`).
//! - `0 < S`: `Rat.le_of_mul_le_mul_left_pos (P·S) Y S hS h : P·S ≤ Y`; then
//!   `Rat.mul_le_mul_of_nonneg_left 16 (P·S) Y (P·S ≤ Y) (0≤16) : 16·(P·S) ≤ 16·Y`;
//!   `16·(P·S) = (16·P)·S = 1·S = S` (`mul_assoc` symm + `congrArg (·S) (16·P=1)`
//!   + `one_mul`), so `Eq.subst` lands `S ≤ 16·Y`.
//!
//! Every leaf is `Constructive` with empty closure, so this lemma is too. No
//! axiom is added or removed.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms. `half`/`four`/`pow4` spellings are byte-identical to the step2 /
/// descent modules so the instantiation is def-eq.
struct DesqConsts {
    order: OrderConsts,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_two: Expr,
    rat_inv: Expr,
    rat_one: Expr,
    mul_comm: Expr,
    mul_assoc: Expr,
    mul_one: Expr,
    one_mul: Expr,
    mul_mul_mul_comm: Expr,
    mul_nonneg: Expr,
    sq_nonneg: Expr,
    mul_le_left: Expr,
    le_of_mul_le_mul: Expr,
    lt_or_eq_of_le: Expr,
    four_half_sq_eq_one: Expr,
    le_of_ble: Expr,
    congr_arg: Expr,
    rat_lt: Expr,
    or_rec: Expr,
}

impl DesqConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_two: k("Rat.two"),
            rat_inv: k("Rat.inv"),
            rat_one: k("Rat.one"),
            mul_comm: k("Rat.mul_comm"),
            mul_assoc: k("Rat.mul_assoc"),
            mul_one: k("Rat.mul_one"),
            one_mul: k("Rat.one_mul"),
            mul_mul_mul_comm: k("Rat.mul_mul_mul_comm"),
            mul_nonneg: k("Rat.mul_nonneg"),
            sq_nonneg: k("Rat.sq_nonneg"),
            mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            le_of_mul_le_mul: k("Rat.le_of_mul_le_mul_left_pos"),
            lt_or_eq_of_le: k("Rat.lt_or_eq_of_le"),
            four_half_sq_eq_one: k("BoolAnalysis.four_half_sq_eq_one"),
            le_of_ble: k("Rat.le_of_ble_eq_true"),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            rat_lt: k("Rat.lt"),
            or_rec: k("Or.rec"),
        }
    }

    fn rat(&self) -> Expr {
        self.rat.clone()
    }
    fn zero(&self) -> Expr {
        self.order.rat_zero.clone()
    }
    fn one(&self) -> Expr {
        self.rat_one.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
    }
    fn le0(&self, a: Expr) -> Expr {
        self.le(self.zero(), a)
    }
    /// `Rat.lt a b` (the bare function, matching `lt_or_eq_of_le` /
    /// `le_of_mul_le_mul_left_pos` hypotheses).
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn eq(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_eq(a, b)
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.order.symm(a, b, h)
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.order.trans(a, b, cc, h1, h2)
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_ma: Expr) -> Expr {
        self.order.subst(motive, a, b, h_eq, h_ma)
    }
    fn half(&self) -> Expr {
        Expr::app(self.rat_inv.clone(), self.rat_two.clone())
    }
    fn four(&self) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let mut four_nat = self.nat_zero.clone();
        for _ in 0..4 {
            four_nat = Expr::app(self.nat_succ.clone(), four_nat);
        }
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), four_nat), one],
        )
    }
    fn pow4(&self, t: Expr) -> Expr {
        let s = self.mul(t.clone(), t);
        self.mul(s.clone(), s)
    }
    /// `Rat.mul_comm a b`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    /// `Rat.mul_one a : a·1 = a`.
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::app(self.mul_one.clone(), a)
    }
    /// `Rat.one_mul a : 1·a = a`.
    fn one_mul(&self, a: Expr) -> Expr {
        Expr::app(self.one_mul.clone(), a)
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.mul_mul_mul_comm.clone(), [a, b, cc, d])
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.mul_nonneg.clone(), [a, b, ha, hb])
    }
    /// `Rat.sq_nonneg a : 0 ≤ a·a`.
    fn sq_nonneg(&self, a: Expr) -> Expr {
        Expr::app(self.sq_nonneg.clone(), a)
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c (hbc:b≤c)(ha:0≤a) : a·b ≤ a·c`.
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, ha: Expr) -> Expr {
        Expr::apps(self.mul_le_left.clone(), [a, b, cc, hbc, ha])
    }
    /// `Rat.le_of_mul_le_mul_left_pos a b c (hc:0<c)(h:c·a≤c·b) : a ≤ b`.
    fn le_of_mul_le_mul(&self, a: Expr, b: Expr, cc: Expr, hc: Expr, h: Expr) -> Expr {
        Expr::apps(self.le_of_mul_le_mul.clone(), [a, b, cc, hc, h])
    }
    /// `Rat.lt_or_eq_of_le a b h : Or (a<b) (a=b)`.
    fn lt_or_eq_of_le(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.lt_or_eq_of_le.clone(), [a, b, h])
    }
    /// `congrArg.{1,1} Rat Rat a b f h : f a = f b`.
    fn congr_arg(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(self.congr_arg.clone(), [self.rat(), self.rat(), a, b, f, h])
    }
    /// `0 ≤ four` via `Rat.le_of_ble_eq_true 0 four (Eq.refl Bool.true)`.
    fn nonneg_four(&self) -> Expr {
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let eq_refl_bool = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [bool_c, btrue],
        );
        Expr::apps(
            self.le_of_ble.clone(),
            [self.zero(), self.four(), eq_refl_bool],
        )
    }
    /// Build `fun (t : Rat) => f(t)`.
    fn lam_rat<F: Fn(Expr) -> Expr>(&self, parent: &EnvDeclBuilder, f: F) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = d.fresh_local(self.rat());
        let body = f(t);
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, self.rat(), body))
    }
}

impl Environment {
    /// Register the STEP-4 de-square cancellation core. Idempotent;
    /// kernel-checked, `Constructive`, empty domain-axiom closure.
    pub fn init_boolean_analysis_kkl_dualhc_desqcancel(&mut self) -> Result<(), EnvError> {
        self.register_dualhc_step4_desq_cancel()?;
        Ok(())
    }

    /// `BoolAnalysis.dualhc_step4_desq_cancel` — see the module docs.
    /// `0≤Y → (half·W)⁴ ≤ Y·W² → W² ≤ 16·Y`. Kernel-checked, `Constructive`,
    /// empty admitted-axiom closure. Idempotent.
    pub fn register_dualhc_step4_desq_cancel(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_step4_desq_cancel");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_order_toolkit()?; // mul_nonneg, sq_nonneg, mul_le_mul_of_nonneg_left
        self.init_algebra_rat_halves()?; // Rat.two, Rat.inv
        self.init_rat_field_inst()?; // mul_comm, mul_assoc, mul_one, one_mul
        self.register_rat_mul_comm_proof()?;
        self.register_rat_mul_assoc_proof()?;
        self.register_rat_mul_mul_mul_comm_theorem()?;
        self.register_rat_le_of_mul_le_mul_left_pos()?;
        self.register_rat_lt_or_eq_of_le()?;
        self.register_rat_minmax_proofs()?; // Rat.le_of_ble_eq_true
        self.init_boolean_analysis_kkl_dualhc_half2()?; // four_half_sq_eq_one
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = DesqConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_desq(&c, false),
            value: build_desq(&c, true),
        })
    }
}

/// `16·pow4(half) = 1`, as a closed proof term.
/// `(four·four)·((h·h)·(h·h)) = (four·(h·h))·(four·(h·h)) = 1·1 = 1`.
fn sixteen_pow4_half_eq_one(c: &DesqConsts, parent: &EnvDeclBuilder) -> Expr {
    let four = c.four();
    let half = c.half();
    let hh = c.mul(half.clone(), half.clone()); // h·h
    let sixteen = c.mul(four.clone(), four.clone()); // 4·4
    let p = c.mul(hh.clone(), hh.clone()); // (h·h)·(h·h) = pow4 half
    let four_hh = c.mul(four.clone(), hh.clone()); // 4·(h·h)

    // s1 : (4·4)·((h·h)·(h·h)) = (4·(h·h))·(4·(h·h))   [mmmc 4 4 (h·h) (h·h)]
    let s1 = c.mmmc(four.clone(), four.clone(), hh.clone(), hh.clone());
    // four_half_sq_eq_one : 4·(h·h) = 1
    let fhse = c.four_half_sq_eq_one.clone();
    // s2 : (4·(h·h))·(4·(h·h)) = 1·(4·(h·h))   [congrArg (·(4·(h·h))) fhse]
    let f2 = c.lam_rat(parent, |t| c.mul(t, four_hh.clone()));
    let s2 = c.congr_arg(four_hh.clone(), c.one(), f2, fhse.clone());
    // s3 : 1·(4·(h·h)) = 1·1   [congrArg (1·_) fhse]
    let f3 = c.lam_rat(parent, |t| c.mul(c.one(), t));
    let s3 = c.congr_arg(four_hh.clone(), c.one(), f3, fhse);
    // s4 : 1·1 = 1   [mul_one 1]
    let s4 = c.mul_one(c.one());

    // chain: 16·P = (4·hh)·(4·hh) = 1·(4·hh) = 1·1 = 1
    let one_four_hh = c.mul(c.one(), four_hh.clone()); // 1·(4·(h·h))
    let one_one = c.mul(c.one(), c.one()); // 1·1
    let sixteen_p = c.mul(sixteen, p); // (4·4)·((h·h)·(h·h))
    let fhh_fhh = c.mul(four_hh.clone(), four_hh.clone()); // (4·(h·h))·(4·(h·h))
    let v12 = c.trans(sixteen_p, fhh_fhh.clone(), one_four_hh.clone(), s1, s2);
    let v123 = c.trans(
        c.mul(
            c.mul(four.clone(), four.clone()),
            c.mul(hh.clone(), hh.clone()),
        ),
        one_four_hh.clone(),
        one_one.clone(),
        v12,
        s3,
    );
    c.trans(
        c.mul(c.mul(four.clone(), four), c.mul(hh.clone(), hh)),
        one_one,
        c.one(),
        v123,
        s4,
    )
}

/// Build the type (`for_value = false`) or proof (`for_value = true`).
fn build_desq(c: &DesqConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (w_id, w) = b.fresh_local(c.rat());
    let (y_id, y) = b.fresh_local(c.rat());

    let half = c.half();
    let four = c.four();
    let sixteen = c.mul(four.clone(), four.clone());
    let s = c.mul(w.clone(), w.clone()); // S := W·W
    let hw = c.mul(half.clone(), w.clone()); // half·W
    let pow4_hw = c.pow4(hw.clone());
    let y_s = c.mul(y.clone(), s.clone()); // Y·S
    let sixteen_y = c.mul(sixteen.clone(), y.clone()); // 16·Y

    let h0y = c.le0(y.clone());
    let hyp = c.le(pow4_hw.clone(), y_s.clone());
    let concl = c.le(s.clone(), sixteen_y.clone());

    let (h0y_id, h0y_v) = b.fresh_local(h0y.clone());
    let (hyp_id, hyp_v) = b.fresh_local(hyp.clone());

    let tail = if for_value {
        let hh = c.mul(half.clone(), half.clone()); // h·h
        let p = c.mul(hh.clone(), hh.clone()); // P := pow4 half

        // FACT A: pow4(half·W) = P·(S·S).
        //   a1 : (half·W)·(half·W) = (h·h)·(W·W)   [mmmc half W half W]
        let a1 = c.mmmc(half.clone(), w.clone(), half.clone(), w.clone());
        let hw_hw = c.mul(hw.clone(), hw.clone()); // (half·W)·(half·W)
        let hh_s = c.mul(hh.clone(), s.clone()); // (h·h)·(W·W) = (h·h)·S
                                                 //   a2 : ((h·h)·S)·((h·h)·S) = ((h·h)·(h·h))·(S·S) = P·(S·S)  [mmmc (h·h) S (h·h) S]
        let a2 = c.mmmc(hh.clone(), s.clone(), hh.clone(), s.clone());
        //   pow4(half·W) = (half·W·half·W)·(half·W·half·W)
        //   step: congrArg (t => t·t) a1 : (hw·hw)·(hw·hw) = (hh·S)·(hh·S)
        let f_sq = c.lam_rat(&b, |t| c.mul(t.clone(), t));
        let a_sq = c.congr_arg(hw_hw.clone(), hh_s.clone(), f_sq, a1);
        // pow4_hw = (hw·hw)·(hw·hw)  (def-eq); chain (hw·hw)·(hw·hw) = (hh·S)·(hh·S) = P·(S·S)
        let hhs_hhs = c.mul(hh_s.clone(), hh_s.clone()); // (hh·S)·(hh·S)
        let p_ss = c.mul(p.clone(), c.mul(s.clone(), s.clone())); // P·(S·S)
        let fact_a = c.trans(pow4_hw.clone(), hhs_hhs.clone(), p_ss.clone(), a_sq, a2);

        // Transport hyp `pow4(half·W) ≤ Y·S` along fact_a to `P·(S·S) ≤ Y·S`.
        //   motive t := t ≤ Y·S
        let motive_t = c.lam_rat(&b, |t| c.le(t, y_s.clone()));
        let hyp_ps = c.subst(motive_t, pow4_hw.clone(), p_ss.clone(), fact_a, hyp_v);

        // Regroup `P·(S·S) = (P·S)·S` (symm mul_assoc) then `= S·(P·S)` (mul_comm).
        let ps = c.mul(p.clone(), s.clone()); // P·S
        let ps_s = c.mul(ps.clone(), s.clone()); // (P·S)·S
        let assoc = c.mul_assoc(p.clone(), s.clone(), s.clone()); // (P·S)·S = P·(S·S)
        let assoc_sym = c.symm(ps_s.clone(), p_ss.clone(), assoc); // P·(S·S) = (P·S)·S
        let s_ps = c.mul(s.clone(), ps.clone()); // S·(P·S)
        let comm1 = c.mul_comm(ps.clone(), s.clone()); // (P·S)·S = S·(P·S)
        let lhs_eq = c.trans(p_ss.clone(), ps_s.clone(), s_ps.clone(), assoc_sym, comm1); // P·(S·S) = S·(P·S)
                                                                                          //   Y·S = S·Y
        let s_y = c.mul(s.clone(), y.clone()); // S·Y
        let comm2 = c.mul_comm(y.clone(), s.clone()); // Y·S = S·Y
                                                      // Transport hyp_ps `P·(S·S) ≤ Y·S` to `S·(P·S) ≤ S·Y`:
                                                      //   first along lhs_eq (motive t => t ≤ Y·S) → S·(P·S) ≤ Y·S
        let motive_l = c.lam_rat(&b, |t| c.le(t, y_s.clone()));
        let hyp1 = c.subst(motive_l, p_ss.clone(), s_ps.clone(), lhs_eq, hyp_ps);
        //   then along comm2 (motive t => S·(P·S) ≤ t) → S·(P·S) ≤ S·Y
        let motive_r = c.lam_rat(&b, |t| c.le(s_ps.clone(), t));
        let hyp2 = c.subst(motive_r, y_s.clone(), s_y.clone(), comm2, hyp1); // S·(P·S) ≤ S·Y

        // 0 ≤ S := sq_nonneg W ; trichotomy.
        let h0s = c.sq_nonneg(w.clone());
        let tri = c.lt_or_eq_of_le(c.zero(), s.clone(), h0s.clone());

        // 0 ≤ 16 := mul_nonneg four four (0≤four)(0≤four).
        let nn16 = c.mul_nonneg(four.clone(), four.clone(), c.nonneg_four(), c.nonneg_four());

        // Or.rec: P_l := 0<S → goal ; P_r := 0=S → goal.
        // CASE 0 < S: cancel to P·S ≤ Y, scale by 16, rewrite 16·(P·S)=S.
        let case_lt = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (hlt_id, hlt) = d.fresh_local(c.lt(c.zero(), s.clone()));
            // le_of_mul_le_mul_left_pos (P·S) Y S hlt hyp2 : P·S ≤ Y
            let ps_le_y = c.le_of_mul_le_mul(ps.clone(), y.clone(), s.clone(), hlt, hyp2.clone());
            // mul_le_mul_of_nonneg_left 16 (P·S) Y (P·S≤Y) (0≤16) : 16·(P·S) ≤ 16·Y
            let scaled = c.mul_le_left(
                sixteen.clone(),
                ps.clone(),
                y.clone(),
                ps_le_y,
                nn16.clone(),
            ); // 16·(P·S) ≤ 16·Y
               // 16·(P·S) = (16·P)·S = 1·S = S
            let sixteen_ps = c.mul(sixteen.clone(), ps.clone()); // 16·(P·S)
            let sixteen_p = c.mul(sixteen.clone(), p.clone()); // 16·P
            let sixteen_p_s = c.mul(sixteen_p.clone(), s.clone()); // (16·P)·S
            let assoc16 = c.mul_assoc(sixteen.clone(), p.clone(), s.clone()); // (16·P)·S = 16·(P·S)
            let assoc16_sym = c.symm(sixteen_p_s.clone(), sixteen_ps.clone(), assoc16); // 16·(P·S) = (16·P)·S
            let p16eq1 = sixteen_pow4_half_eq_one(c, &d); // 16·P = 1
            let f16 = c.lam_rat(&d, |t| c.mul(t, s.clone()));
            let cong16 = c.congr_arg(sixteen_p.clone(), c.one(), f16, p16eq1); // (16·P)·S = 1·S
            let one_s = c.mul(c.one(), s.clone()); // 1·S
            let one_mul_s = c.one_mul(s.clone()); // 1·S = S
                                                  // chain: 16·(P·S) = (16·P)·S = 1·S = S
            let e1 = c.trans(
                sixteen_ps.clone(),
                sixteen_p_s.clone(),
                one_s.clone(),
                assoc16_sym,
                cong16,
            );
            let eq_to_s = c.trans(sixteen_ps.clone(), one_s.clone(), s.clone(), e1, one_mul_s); // 16·(P·S) = S
                                                                                                // transport `scaled : 16·(P·S) ≤ 16·Y` along eq_to_s (motive t => t ≤ 16·Y) → S ≤ 16·Y
            let motive_c = c.lam_rat(&d, |t| c.le(t, sixteen_y.clone()));
            let res = c.subst(motive_c, sixteen_ps, s.clone(), eq_to_s, scaled);
            d.finish_child(d.mk_lam(hlt_id, BinderInfo::Default, c.lt(c.zero(), s.clone()), res))
        };
        // CASE 0 = S: goal S ≤ 16·Y. Subst S := 0 makes goal 0 ≤ 16·Y = nn(16·Y).
        let case_eq = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (heq_id, heq) = d.fresh_local(c.eq(c.zero(), s.clone()));
            // 0 ≤ 16·Y := mul_nonneg 16 Y (0≤16)(0≤Y)
            let nn16y = c.mul_nonneg(sixteen.clone(), y.clone(), nn16.clone(), h0y_v.clone());
            // transport along heq (0 = S): motive t => t ≤ 16·Y, at a=0 gives 0≤16Y, at b=S gives S≤16Y
            let motive_e = c.lam_rat(&d, |t| c.le(t, sixteen_y.clone()));
            let res = c.subst(motive_e, c.zero(), s.clone(), heq, nn16y);
            d.finish_child(d.mk_lam(heq_id, BinderInfo::Default, c.eq(c.zero(), s.clone()), res))
        };

        // Or.rec.{0} (0<S) (0=S) (motive := fun _ => S ≤ 16·Y) case_lt case_eq tri.
        let p_lt = c.lt(c.zero(), s.clone());
        let p_eq = c.eq(c.zero(), s.clone());
        let or_motive = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let or_ty = Expr::apps(
                Expr::const_(Name::from_string("Or"), vec![]),
                [p_lt.clone(), p_eq.clone()],
            );
            let (h_id, _h) = d.fresh_local(or_ty.clone());
            d.finish_child(d.mk_lam(h_id, BinderInfo::Default, or_ty, concl.clone()))
        };
        Expr::apps(
            c.or_rec.clone(),
            [p_lt, p_eq, or_motive, case_lt, case_eq, tri],
        )
    } else {
        concl
    };

    let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
        if for_value {
            b.mk_lam(id, BinderInfo::Default, ty, body)
        } else {
            b.mk_pi(id, BinderInfo::Default, ty, body)
        }
    };
    let e = bind(&b, hyp_id, hyp, tail);
    let e = bind(&b, h0y_id, h0y, e);
    let e = bind(&b, y_id, c.rat(), e);
    let e = bind(&b, w_id, c.rat(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_dualhc_desqcancel()
            .expect("init_boolean_analysis_kkl_dualhc_desqcancel");
        env.init_boolean_analysis_kkl_dualhc_desqcancel()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_dualhc_step4_desq_cancel_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.dualhc_step4_desq_cancel");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }
}
