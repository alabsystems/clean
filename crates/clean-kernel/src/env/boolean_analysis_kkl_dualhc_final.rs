// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC — **FINAL**: the per-coordinate LINEAR dual-HC `W ≤ 4·r`, the
//! de-square of STEP 4's `W² ≤ 16·(m³·8^n)` through the faithful `IsRpow32`
//! carrier.
//!
//! ## What this proves
//!
//! With `W := subsetSum n (fun y => (T_{1/3} D_i f y)²)` (STEP 4's un-normalized
//! 2-norm-squared), `m := subsetSum n (fun x => (D_i f x · D_i f x)·(½·½))`
//! (STEP 2's measure `= 2^n·Inf_i`), and `X := m · (Rat.powNat 2 n)` (so
//! `X³ = m³·(2^n)³ = m³·8^n`, the STEP-4 RHS cube), for ANY `r` with
//! `IsRpow32 X r` (i.e. `0≤r ∧ r² = X³`):
//!
//! ```text
//! BoolAnalysis.dualhc_final_le :
//!   ∀ (n : Nat) (f : BoolFn n) (i : Fin n) (r : Rat),
//!     BoolAnalysis.IsRpow32 (Rat.mul m (Rat.powNat 2 n)) r
//!   → Rat.le W (Rat.mul four r)
//! ```
//!
//! i.e. `W ≤ 4·r` where `r = X^{3/2}` and `X = m·2^n = 4^n·Inf_i` (un-normalized).
//! This is the per-coordinate LINEAR dual-HC bound — the de-squared output the
//! KKL low-band charge sums (LINEARLY, no Cauchy–Schwarz). It carries the
//! un-normalized `X = 4^n·Inf_i`; the sharp `‖T_{1/3} D_i f‖₂² ≤ 4·Inf_i^{3/2}`
//! is its `Expect`-normalized shadow (the `2^n`-measure normalization is the one
//! remaining bookkeeping bridge — see the epilogue).
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! Two rungs:
//!
//! 1. **cube-reassoc** `dualhc_pow8_eq_two_pow_cube : Rat.powNat 8 n =
//!    ((Rat.powNat 2 n · Rat.powNat 2 n) · Rat.powNat 2 n)` (`Nat.rec`; base via
//!    `mul_one`, step via `pow_nat_succ` + `mul_mul_mul_comm` + the literal
//!    `8 = (2·2)·2` from `Rat.ofNat_mul` twice). Then `m³·8^n = X³` where
//!    `X := m·2^n` (`mul_mul_mul_comm`/`mul_assoc` regroup transported along the
//!    cube-reassoc), so STEP 4's `W² ≤ 16·(m³·8^n)` rewrites to `W² ≤ 16·(X·X·X)`
//!    = `(4·4)·((X·X)·X)`, the descent brick's hypothesis shape.
//! 2. **descent** `le_four_rpow32_of_sq_le_16_cube W X r (0≤W) (IsRpow32 X r)
//!    (W² ≤ 16·X³) : W ≤ 4·r`. `0≤W := Fin.sum_nonneg` of `(Tg)² ≥ 0`.
//!
//! Every leaf is a landed `Constructive` empty-closure Theorem, so FINAL is too.
//! No axiom is added or removed.
//!
//! ## NORMALIZATION epilogue (the sole remaining bridge to the sharp KKL charge)
//!
//! `X = m·2^n = (2^n·Inf_i)·2^n = 4^n·Inf_i`, so `r = X^{3/2} = (4^n·Inf_i)^{3/2}
//! = 8^n·Inf_i^{3/2}` and the bound is `W ≤ 4·8^n·Inf_i^{3/2}`. Since `W` is the
//! UN-normalized 2-norm (`W = 4^n·W_norm` where `W_norm := ‖T_{1/3} D_i f‖₂² =
//! Expect_y (Tg)²`), dividing both sides by `4^n` recovers the sharp
//! `W_norm ≤ 4·2^n·Inf_i^{3/2}` — wait, the `2^n` powers must be tracked exactly:
//! the `Expect`-normalized operator `T_{1/3}^norm = (1/2^n)·noiseOp` divides the
//! density too, so the sharp shadow `W_norm² ≤ 16·Inf_i³` ⟹ `W_norm ≤ 4·Inf_i^{3/2}`
//! follows once the `Expect`/`subsetSum` measure powers are threaded. That single
//! `2^n`-bookkeeping bridge (`W = c·W_norm`, `X = c'·Inf_i`, common-power cancel)
//! is the EXACT remaining piece to the sharp per-coordinate charge.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the FINAL descent + cube-reassoc.
struct FinalConsts {
    order: OrderConsts,
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_ofnat: Expr,
    rat_one: Expr,
    half_inv: Expr,
    rat_two: Expr,
    pow_nat: Expr,
    bool_fn: Expr,
    hcpoint: Expr,
    fin: Expr,
    hc_flip: Expr,
    pm: Expr,
    noise_op: Expr,
    subset_sum: Expr,
    fin_sum_nonneg: Expr,
    sq_nonneg: Expr,
    is_rpow32: Expr,
    descent: Expr,
    step4: Expr,
    pow8_cube: Expr,
    pow_nat_succ: Expr,
    mul_one: Expr,
    mul_comm: Expr,
    mul_assoc: Expr,
    mmmc: Expr,
    ofnat_mul: Expr,
    congr_arg: Expr,
    nat_rec: Expr,
}

impl FinalConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_ofnat: k("Rat.ofNat"),
            rat_one: k("Rat.one"),
            half_inv: k("Rat.inv"),
            rat_two: k("Rat.two"),
            pow_nat: k("Rat.powNat"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            fin: k("Fin"),
            hc_flip: k("BoolAnalysis.hcFlip"),
            pm: k("BoolAnalysis.pm"),
            noise_op: k("BoolAnalysis.noiseOp"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            fin_sum_nonneg: k("Fin.sum_nonneg"),
            sq_nonneg: k("Rat.sq_nonneg"),
            is_rpow32: k("BoolAnalysis.IsRpow32"),
            descent: k("BoolAnalysis.le_four_rpow32_of_sq_le_16_cube"),
            step4: k("BoolAnalysis.dualhc_step4_sq_le"),
            pow8_cube: k("BoolAnalysis.dualhc_pow8_eq_two_pow_cube"),
            pow_nat_succ: k("Rat.powNat_succ"),
            mul_one: k("Rat.mul_one"),
            mul_comm: k("Rat.mul_comm"),
            mul_assoc: k("Rat.mul_assoc"),
            mmmc: k("Rat.mul_mul_mul_comm"),
            ofnat_mul: k("Rat.ofNat_mul"),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
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
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        self.order.sub(a, b)
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
        Expr::app(self.half_inv.clone(), self.rat_two.clone())
    }
    /// `ofNat m := Rat.ofNat m` (≡ `Rat.mk (Int.ofNat m) 1`).
    fn ofnat(&self, m: Expr) -> Expr {
        Expr::app(self.rat_ofnat.clone(), m)
    }
    fn nat_lit(&self, n: u32) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..n {
            e = Expr::app(self.nat_succ.clone(), e);
        }
        e
    }
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    /// `four := Rat.mk (Int.ofNat 4) 1`. Byte-matches the descent's `four`.
    fn four(&self) -> Expr {
        let one = self.nat_lit(1);
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), self.nat_lit(4)), one],
        )
    }
    /// `Rat.powNat (Rat.mk (Int.ofNat k) 1) n` for a Nat literal `k`. Matches
    /// `Hc24Consts::pow8` (base = `Rat` literal) byte-for-byte at k=8/2.
    fn pow_lit(&self, k: u32, n: &Expr) -> Expr {
        let one = self.nat_lit(1);
        let base = Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), self.nat_lit(k)), one],
        );
        Expr::apps(self.pow_nat.clone(), [base, n.clone()])
    }
    fn pow2_nat(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.nat_lit(2), n.clone()])
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn fin_pow(&self, n: &Expr) -> Expr {
        self.fin_of(&self.pow2_nat(n))
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat())
    }
    fn pm_of(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    fn flip(&self, n: &Expr, x: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.hc_flip.clone(), [n.clone(), x.clone(), i.clone()])
    }
    fn rho_third(&self) -> Expr {
        let one_nat = self.nat_lit(1);
        let three_nat = self.nat_lit(3);
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), one_nat), three_nat],
        )
    }
    fn deriv_lam(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let fx = Expr::app(f.clone(), x.clone());
        let fflip = Expr::app(f.clone(), self.flip(n, &x, i));
        let body = self.sub(self.pm_of(fx), self.pm_of(fflip));
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    fn op(&self, n: &Expr, g: &Expr) -> Expr {
        Expr::apps(
            self.noise_op.clone(),
            [self.rho_third(), n.clone(), g.clone()],
        )
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn fin_sum_nonneg(&self, n_pow: &Expr, f: Expr, per: Expr) -> Expr {
        Expr::apps(self.fin_sum_nonneg.clone(), [n_pow.clone(), f, per])
    }
    fn sq_nonneg(&self, a: Expr) -> Expr {
        Expr::app(self.sq_nonneg.clone(), a)
    }
    fn is_rpow32_of(&self, x: &Expr, r: &Expr) -> Expr {
        Expr::apps(self.is_rpow32.clone(), [x.clone(), r.clone()])
    }
    /// `Rat.pow_nat_succ b k : b^(k+1) = b·b^k`.
    fn pownat_succ(&self, b: Expr, k: Expr) -> Expr {
        Expr::apps(self.pow_nat_succ.clone(), [b, k])
    }
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::app(self.mul_one.clone(), a)
    }
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    fn mmmc(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.mmmc.clone(), [a, b, cc, d])
    }
    /// `Rat.ofNat_mul m n : ofNat(Nat.mul m n) = ofNat m · ofNat n`.
    fn ofnat_mul(&self, m: Expr, n: Expr) -> Expr {
        Expr::apps(self.ofnat_mul.clone(), [m, n])
    }
    fn congr_arg(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(self.congr_arg.clone(), [self.rat(), self.rat(), a, b, f, h])
    }
    fn lam_rat<F: Fn(Expr) -> Expr>(&self, parent: &EnvDeclBuilder, f: F) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = d.fresh_local(self.rat());
        let body = f(t);
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, self.rat(), body))
    }
}

impl Environment {
    /// Register the FINAL per-coordinate dual-HC + its cube-reassoc bridge.
    /// Idempotent; kernel-checked, `Constructive`, empty domain-axiom closure.
    pub fn init_boolean_analysis_kkl_dualhc_final(&mut self) -> Result<(), EnvError> {
        self.register_dualhc_pow8_eq_two_pow_cube()?;
        self.register_dualhc_final_le()?;
        Ok(())
    }

    /// `BoolAnalysis.dualhc_pow8_eq_two_pow_cube : ∀ n,
    ///   Rat.powNat 8 n = ((Rat.powNat 2 n · Rat.powNat 2 n) · Rat.powNat 2 n)`.
    /// `Nat.rec`; see the module docs. Kernel-checked, `Constructive`, empty
    /// closure. Idempotent.
    pub fn register_dualhc_pow8_eq_two_pow_cube(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_pow8_eq_two_pow_cube");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_rat_pow_nat()?;
        self.register_rat_pow_nat_succ_theorem()?;
        self.init_rat_field_inst()?;
        self.register_rat_mul_comm_proof()?;
        self.register_rat_mul_assoc_proof()?;
        self.register_rat_mul_mul_mul_comm_theorem()?;
        self.register_rat_ofnat_mul()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = FinalConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_cube_reassoc(&c, false),
            value: build_cube_reassoc(&c, true),
        })
    }

    /// `BoolAnalysis.dualhc_final_le` — see the module docs. `IsRpow32 (m·2^n) r
    /// → W ≤ 4·r`. Kernel-checked, `Constructive`, empty admitted-axiom closure.
    /// Idempotent.
    pub fn register_dualhc_final_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_final_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.register_subset_sum()?;
        self.init_fin_sum()?;
        self.init_boolean_analysis_order_toolkit()?; // sq_nonneg
        self.init_algebra_rat_halves()?;
        self.init_rat_field_inst()?;
        self.register_rat_mul_comm_proof()?;
        self.register_rat_mul_assoc_proof()?;
        self.register_rat_mul_mul_mul_comm_theorem()?;
        self.register_rat_pow_nat()?;
        self.init_boolean_analysis_kkl_nnrpow()?; // IsRpow32
        self.init_boolean_analysis_kkl_dualhc_descent()?; // le_four_rpow32_of_sq_le_16_cube
        self.register_dualhc_step4_sq_le()?;
        self.register_dualhc_pow8_eq_two_pow_cube()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = FinalConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_final(&c, false),
            value: build_final(&c, true),
        })
    }
}

// Term builders in the sibling include to keep this file under the 500-line cap.
include!("boolean_analysis_kkl_dualhc_final_build.rs");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_dualhc_final()
            .expect("init_boolean_analysis_kkl_dualhc_final");
        env.init_boolean_analysis_kkl_dualhc_final()
            .expect("idempotent");
        env
    }

    fn assert_ct(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "{name} closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_dualhc_pow8_eq_two_pow_cube_is_constructive_theorem() {
        assert_ct(&env(), "BoolAnalysis.dualhc_pow8_eq_two_pow_cube");
    }

    #[test]
    fn test_dualhc_final_le_is_constructive_theorem() {
        assert_ct(&env(), "BoolAnalysis.dualhc_final_le");
    }
}
