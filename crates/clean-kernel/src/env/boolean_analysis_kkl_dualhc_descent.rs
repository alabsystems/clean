// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC — the per-coordinate **DESCENT** brick (de-square via the
//! landed `IsRpow32` carrier).
//!
//! The verified dual-HC route bounds the per-coordinate spectral quantity
//! `W := ‖T_{1/3} D_i f‖₂²` by its SQUARE first:
//!
//! ```text
//!   W·W  ≤  16·Inf_i³            (rational — R2's 4th-power Hölder + spectral glue)
//! ```
//!
//! and then DE-SQUARES per coordinate (this brick) — never via Cauchy–Schwarz on
//! the SUM (the fatal `√n` of `2026-06-18-kkl-root-free-obstruction.md`), but
//! pointwise through the faithful `3/2`-power carrier. With `IsRpow32 Inf_i r_i`
//! (`r_i² = Inf_i³`, `0 ≤ r_i` — the carrier authorised as obstruction option
//! (a)), `16·Inf_i³ = (4·r_i)²`, so `Rat.le_of_sq_le_sq` gives the LINEAR bound
//!
//! ```text
//!   W  ≤  4·r_i .
//! ```
//!
//! Summing this linearly (NO Cauchy–Schwarz) through the landed n-free charge
//! `Σ_i r_i ≤ s·I[f]` (`kkl_sum_rpow32_influence_le`) yields the sharp, `n`-free
//! `Σ_i W^{≤k}[D_i f] ≤ 4·s·I[f]` — exactly the `h_dual` hypothesis the landed
//! `kkl_lowband_mass_of_dual_hc` assembly consumes.
//!
//! ## What this proves
//!
//! ```text
//! BoolAnalysis.le_four_rpow32_of_sq_le_16_cube :
//!   ∀ (W x r : Rat),
//!     Rat.le Rat.zero W                                  -- 0 ≤ W
//!   → BoolAnalysis.IsRpow32 x r                          -- r = x^{3/2}
//!   → Rat.le (Rat.mul W W)
//!            (Rat.mul (Rat.mul four four) (Rat.mul (Rat.mul x x) x))   -- W² ≤ 16·x³
//!   → Rat.le W (Rat.mul four r)                          -- W ≤ 4·r
//! ```
//!
//! where `four := Rat.mk (Int.ofNat 4) 1` and `16 := four·four`. The RHS of the
//! hypothesis spells `x³` as `(x·x)·x` (matching `IsRpow32`'s defining relation
//! `r·r = (x·x)·x`) and `16` as `four·four`, so the de-square is purely
//! structural — no numeral evaluation is relied on.
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! 1. `0 ≤ r` := `And.left` of `IsRpow32 x r` (def-eq unfold).
//! 2. `0 ≤ 4·r` := `Rat.mul_nonneg four r (0≤four) (0≤r)`.
//! 3. `(4·r)·(4·r) = (4·4)·(r·r)` := `Rat.mul_mul_mul_comm four r four r`.
//! 4. `(4·4)·(r·r) = (4·4)·((x·x)·x)` := `congrArg ((4·4)·_) (rpow32_sq x r h)`.
//! 5. chain (3,4): `(4·r)² = 16·x³`; `symm` gives `16·x³ = (4·r)²`.
//! 6. `Eq.subst` transports the hypothesis `W² ≤ 16·x³` along (5) to `W² ≤ (4·r)²`.
//! 7. `Rat.le_of_sq_le_sq W (4·r) (0≤W) (0≤4·r) (6)` : `W ≤ 4·r`.
//!
//! Every leaf (`And.left`, `Rat.mul_nonneg`, `Rat.mul_mul_mul_comm`, `congrArg`,
//! `Rat.le_of_sq_le_sq`, `BoolAnalysis.rpow32_sq`, `Eq.subst`/`symm`) is
//! `Constructive` with empty closure, so this brick is too. No axiom is added or
//! removed. `0 ≤ four` is `Rat.le_of_ble_eq_true … (Eq.refl Bool.true)` (the
//! concrete `Rat.ble 0 4` native-reduces to `true`).

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct DescentConsts {
    order: OrderConsts,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    is_rpow32: Expr,
    rpow32_sq: Expr,
    mul_nonneg: Expr,
    mul_mul_mul_comm: Expr,
    le_of_sq_le_sq: Expr,
    le_of_ble: Expr,
    congr_arg: Expr,
}

impl DescentConsts {
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
            is_rpow32: k("BoolAnalysis.IsRpow32"),
            rpow32_sq: k("BoolAnalysis.rpow32_sq"),
            mul_nonneg: k("Rat.mul_nonneg"),
            mul_mul_mul_comm: k("Rat.mul_mul_mul_comm"),
            le_of_sq_le_sq: k("Rat.le_of_sq_le_sq"),
            le_of_ble: k("Rat.le_of_ble_eq_true"),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn rat(&self) -> Expr {
        self.rat.clone()
    }
    fn zero(&self) -> Expr {
        self.order.rat_zero.clone()
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
    fn eq(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_eq(a, b)
    }
    /// `four := Rat.mk (Int.ofNat 4) 1`.
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
    /// `x³` spelled `(x·x)·x` — matching `IsRpow32`'s defining relation.
    fn cube(&self, x: &Expr) -> Expr {
        self.mul(self.mul(x.clone(), x.clone()), x.clone())
    }
    fn is_rpow32_of(&self, x: &Expr, r: &Expr) -> Expr {
        Expr::apps(self.is_rpow32.clone(), [x.clone(), r.clone()])
    }
    /// `BoolAnalysis.rpow32_sq x r h : r·r = (x·x)·x`.
    fn rpow32_sq_of(&self, x: &Expr, r: &Expr, h: Expr) -> Expr {
        Expr::apps(self.rpow32_sq.clone(), [x.clone(), r.clone(), h])
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.mul_nonneg.clone(), [a, b, ha, hb])
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mul_mul_mul_comm(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.mul_mul_mul_comm.clone(), [a, b, cc, d])
    }
    /// `Rat.le_of_sq_le_sq a b ha hb hsq : a ≤ b`.
    fn le_of_sq_le_sq(&self, a: Expr, bb: Expr, ha: Expr, hb: Expr, hsq: Expr) -> Expr {
        Expr::apps(self.le_of_sq_le_sq.clone(), [a, bb, ha, hb, hsq])
    }
    fn symm(&self, a: Expr, bb: Expr, h: Expr) -> Expr {
        self.order.symm(a, bb, h)
    }
    fn subst(&self, motive: Expr, a: Expr, bb: Expr, h_eq: Expr, h_ma: Expr) -> Expr {
        self.order.subst(motive, a, bb, h_eq, h_ma)
    }
    fn congr_arg(&self, a: Expr, bb: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat(), self.rat(), a, bb, f, h],
        )
    }
    /// `And.left (0≤r) (r·r=x³) h : 0 ≤ r`.  (`And.left` is Prop-monomorphic —
    /// no universe params.)
    fn and_left(&self, p: Expr, q: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("And.left"), vec![]),
            [p, q, h],
        )
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
}

impl Environment {
    /// Register the per-coordinate dual-HC descent brick. Idempotent;
    /// kernel-checked, `Constructive`, empty domain-axiom closure.
    pub fn init_boolean_analysis_kkl_dualhc_descent(&mut self) -> Result<(), EnvError> {
        self.register_le_four_rpow32_of_sq_le_16_cube()?;
        Ok(())
    }

    /// `BoolAnalysis.le_four_rpow32_of_sq_le_16_cube` — see the module docs.
    /// `0≤W → IsRpow32 x r → W² ≤ 16·x³ → W ≤ 4·r`. Kernel-checked,
    /// `Constructive`, empty closure. Idempotent.
    pub fn register_le_four_rpow32_of_sq_le_16_cube(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.le_four_rpow32_of_sq_le_16_cube");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_order_toolkit()?; // mul_nonneg, le_of_sq_le_sq surface
        self.init_boolean_analysis_kkl_nnrpow()?; // IsRpow32, rpow32_sq
        self.register_rat_minmax_proofs()?; // Rat.le_of_ble_eq_true
        self.init_boolean_analysis_order_toolkit_b1d()?; // Rat.le_of_sq_le_sq
        self.init_rat_field_inst()?; // Rat.mul_mul_mul_comm

        let c = DescentConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_descent(&c, false),
            value: build_descent(&c, true),
        })
    }
}

/// Build the type (`for_value = false`) or proof value (`for_value = true`).
fn build_descent(c: &DescentConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (w_id, w) = b.fresh_local(c.rat());
    let (x_id, x) = b.fresh_local(c.rat());
    let (r_id, r) = b.fresh_local(c.rat());

    let four = c.four();
    let four_r = c.mul(four.clone(), r.clone()); // 4·r
    let sixteen = c.mul(four.clone(), four.clone()); // 4·4 (= 16)
    let cube_x = c.cube(&x); // (x·x)·x
    let ww = c.mul(w.clone(), w.clone()); // W·W
    let sixteen_cube = c.mul(sixteen.clone(), cube_x.clone()); // 16·x³

    let h0w = c.le0(w.clone()); // 0 ≤ W
    let hrp = c.is_rpow32_of(&x, &r); // IsRpow32 x r
    let hsq = c.le(ww.clone(), sixteen_cube.clone()); // W² ≤ 16·x³
    let concl = c.le(w.clone(), four_r.clone()); // W ≤ 4·r

    let (h0w_id, h0w_v) = b.fresh_local(h0w.clone());
    let (hrp_id, hrp_v) = b.fresh_local(hrp.clone());
    let (hsq_id, hsq_v) = b.fresh_local(hsq.clone());

    let tail = if for_value {
        // 0 ≤ r := And.left (0≤r) (r·r=x³) hrp.
        let rr = c.mul(r.clone(), r.clone());
        let nn = c.le0(r.clone());
        let rel = c.eq(rr.clone(), cube_x.clone());
        let nn_r = c.and_left(nn, rel, hrp_v.clone());
        // 0 ≤ 4·r := mul_nonneg four r (0≤four) (0≤r).
        let nn_4r = c.mul_nonneg(four.clone(), r.clone(), c.nonneg_four(), nn_r);

        // (4·r)·(4·r) = (4·4)·(r·r)   [mul_mul_mul_comm four r four r]
        let fr_fr = c.mul(four_r.clone(), four_r.clone()); // (4r)²
        let mmmc = c.mul_mul_mul_comm(four.clone(), r.clone(), four.clone(), r.clone());
        // (4·4)·(r·r) = (4·4)·((x·x)·x)   [congrArg ((4·4)·_) (rpow32_sq x r hrp)]
        let rel_h = c.rpow32_sq_of(&x, &r, hrp_v); // r·r = (x·x)·x
        let mul_16 = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = d.fresh_local(c.rat());
            let body = c.mul(sixteen.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        let cg = c.congr_arg(rr.clone(), cube_x.clone(), mul_16, rel_h); // (4·4)·(r·r) = (4·4)·x³
                                                                         // eq_full : (4·r)² = 16·x³   via trans (mmmc, cg)
        let sixteen_rr = c.mul(sixteen.clone(), rr.clone()); // (4·4)·(r·r)
        let eq_full = c.order.trans(
            fr_fr.clone(),
            sixteen_rr.clone(),
            sixteen_cube.clone(),
            mmmc,
            cg,
        ); // (4r)² = 16·x³
           // symm : 16·x³ = (4·r)²
        let eq_sym = c.symm(fr_fr.clone(), sixteen_cube.clone(), eq_full);
        // h_sq2 : W² ≤ (4·r)²   via subst hsq along eq_sym (motive fun t => W² ≤ t)
        let h_sq2 = {
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = d.fresh_local(c.rat());
                let body = c.le(ww.clone(), t);
                d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
            };
            c.subst(motive, sixteen_cube.clone(), fr_fr.clone(), eq_sym, hsq_v)
        };
        // W ≤ 4·r := le_of_sq_le_sq W (4·r) (0≤W) (0≤4·r) h_sq2
        c.le_of_sq_le_sq(w.clone(), four_r.clone(), h0w_v, nn_4r, h_sq2)
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
    let e = bind(&b, hsq_id, hsq, tail);
    let e = bind(&b, hrp_id, hrp, e);
    let e = bind(&b, h0w_id, h0w, e);
    let e = bind(&b, r_id, c.rat(), e);
    let e = bind(&b, x_id, c.rat(), e);
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
        env.init_boolean_analysis_kkl_dualhc_descent()
            .expect("init_boolean_analysis_kkl_dualhc_descent");
        env.init_boolean_analysis_kkl_dualhc_descent()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_le_four_rpow32_of_sq_le_16_cube_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.le_four_rpow32_of_sq_le_16_cube");
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
