// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC — **STEP 4 (assembly)**: the un-normalized squared per-coordinate
//! dual-HC `W² ≤ 16·8^n·m³`, chaining STEP 2 ⊕ STEP-4-glue ⊕ STEP 3 ⊕ the fold
//! bridge ⊕ the de-square cancellation.
//!
//! ## What this proves
//!
//! Writing `g := D_i f` (as the lambda `fun x => pm(f x) − pm(f(hcFlip n x i))`),
//! `T := noiseOp (1/3) n`, `Tg := T g`, `ttg := T (T g)` (STEP 2's weight `w`),
//! `W := subsetSum n (fun y => (Tg y)·(Tg y))` (the un-normalized 2-norm-squared
//! of `Tg`), and `m := subsetSum n (fun x => (g x·g x)·(half·half))` (STEP 2's
//! support measure `= Σ_x e² = #disagree = 2^n·Inf_i`):
//!
//! ```text
//! BoolAnalysis.dualhc_step4_sq_le :
//!   ∀ (n : Nat) (f : BoolFn n) (i : Fin n),
//!     Rat.le (Rat.mul W W)
//!            (Rat.mul (Rat.mul four four)
//!                     (Rat.mul (Rat.mul m (Rat.mul m m)) (Rat.powNat 8 n)))
//! ```
//!
//! i.e. `W² ≤ 16·(m³·8^n)`. This is the obstruction report's squared
//! per-coordinate dual-HC `(‖T_{1/3} D_i f‖₂²)² ≤ 16·Inf_i³`, expressed in the
//! un-normalized `subsetSum` cube where `m = 2^n·Inf_i` and the `8^n` carries the
//! operator measure — so the rational identity it encodes is exactly
//! `16·m³·8^n = 16·(2^n·Inf_i)³·8^n = 16·64^n·Inf_i³` (the `64^n` is the
//! un-normalized measure factor that the NORMALIZATION layer clears to land the
//! sharp `W_norm² ≤ 16·Inf_i³`; see the module epilogue).
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! Feed `dualhc_step4_desq_cancel W (m³·8^n)` (`0≤Y → (half·W)⁴ ≤ Y·W² → W² ≤
//! 16·Y`) with `Y := m³·8^n`:
//!
//! - **`0 ≤ Y`** := `Rat.mul_nonneg m³ 8^n (0≤m³) (0≤8^n)`; `0≤m³` from STEP 2's
//!   `m ≥ 0` (`Fin.sum_nonneg` of `(g·g)·(half·half) ≥ 0`) cubed (`mul_nonneg`);
//!   `0≤8^n` = `Rat.powNat_nonneg 8 n (0≤8)`.
//! - **`(half·W)⁴ ≤ Y·W²`** by `Eq.subst`/`Eq.subst` transports of:
//!   1. **STEP 2** at `w := ttg`: `(Σ_x (g·half)·ttg)⁴ ≤ m³·Σ_x (ttg x)⁴`.
//!   2. **STEP-4-glue** at `g`: `Σ_x (g·half)·ttg = half·W`; subst the LHS base.
//!   3. **STEP 3 + fold**: `Σ_x (ttg x)⁴ = Σ_jx pow4(noiseFn (1/3) n Tg jx) ≤
//!      8^n·W` (the fold bridge `noiseFn_eq_noiseOp` rewrites the STEP-3 LHS
//!      summand to `pow4(ttg(decode jx))`, then `subsetSum`/`Fin.sum` are def-eq);
//!      so `m³·Σ_x (ttg x)⁴ ≤ m³·(8^n·W²)` (`Rat.mul_le_mul_of_nonneg_left`,
//!      `0≤m³`), reassoc to `(m³·8^n)·W² = Y·W²`.
//!
//! Every leaf is a landed `Constructive` empty-closure Theorem, so this assembly
//! is `Constructive` with EMPTY admitted-axiom closure. No axiom is added or
//! removed.
//!
//! ## NORMALIZATION epilogue (the precise remaining gap to `W ≤ 4·r_i`)
//!
//! The descent brick `le_four_rpow32_of_sq_le_16_cube` consumes `W² ≤ 16·x³` with
//! `IsRpow32 x r` to emit `W ≤ 4·r`. Here `x³ = m³·8^n = 64^n·Inf_i³`, NOT
//! `Inf_i³`. Landing the SHARP `W_norm ≤ 4·Inf_i^{3/2}` therefore needs the
//! NORMALIZATION bridge that (a) relates the un-normalized `W` and `m` to the
//! `Expect`-normalized `W_norm := ‖T_{1/3} D_i f‖₂²` and `Inf_i`, and (b) clears
//! the common `64^n` measure power so the descent's `x := Inf_i`. That bridge is
//! the EXACT next unbuilt piece (see the report). The squared inequality PROVEN
//! here is the genuine analytic content; the residual is `2^n`-bookkeeping.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the STEP-4 assembly. All spellings byte-match step2 / glue /
/// step3 / desqcancel so every leaf instance is def-eq.
struct AsmConsts {
    order: OrderConsts,
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_two: Expr,
    rat_inv: Expr,
    pow_nat: Expr,
    bool_fn: Expr,
    hcpoint: Expr,
    fin: Expr,
    hc_flip: Expr,
    pm: Expr,
    noise_op: Expr,
    noise_fn: Expr,
    subset_sum: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    subset_sum_congr: Expr,
    fin_sum_nonneg: Expr,
    mul_nonneg: Expr,
    sq_nonneg: Expr,
    pow_nat_nonneg: Expr,
    mul_le_left: Expr,
    mul_assoc: Expr,
    congr_arg: Expr,
    le_of_ble: Expr,
    // landed dual-HC leaves.
    step2: Expr,
    step4_glue: Expr,
    step3: Expr,
    fold: Expr,
    desq: Expr,
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
impl AsmConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let nat_succ = k("Nat.succ");
        let nat_zero = k("Nat.zero");
        Self {
            order: OrderConsts::new(),
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero,
            nat_succ,
            nat_pow: k("Nat.pow"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_two: k("Rat.two"),
            rat_inv: k("Rat.inv"),
            pow_nat: k("Rat.powNat"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            fin: k("Fin"),
            hc_flip: k("BoolAnalysis.hcFlip"),
            pm: k("BoolAnalysis.pm"),
            noise_op: k("BoolAnalysis.noiseOp"),
            noise_fn: k("BoolAnalysis.noiseFn"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            #[cfg(test)]
            subset_sum_congr: k("BoolAnalysis.subsetSum_congr"),
            fin_sum_nonneg: k("Fin.sum_nonneg"),
            mul_nonneg: k("Rat.mul_nonneg"),
            sq_nonneg: k("Rat.sq_nonneg"),
            pow_nat_nonneg: k("Rat.powNat_nonneg"),
            mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            mul_assoc: k("Rat.mul_assoc"),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            le_of_ble: k("Rat.le_of_ble_eq_true"),
            step2: k("BoolAnalysis.dualhc_step2_holder_inst"),
            step4_glue: k("BoolAnalysis.dualhc_step4_half_inner_eq"),
            step3: k("BoolAnalysis.dualhc_step3_op_fourth_le"),
            fold: k("BoolAnalysis.noiseFn_eq_noiseOp"),
            desq: k("BoolAnalysis.dualhc_step4_desq_cancel"),
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
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        self.order.sub(a, b)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
    }
    #[cfg(test)]
    fn le0(&self, a: Expr) -> Expr {
        self.le(self.zero(), a)
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.order.symm(a, b, h)
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_ma: Expr) -> Expr {
        self.order.subst(motive, a, b, h_eq, h_ma)
    }
    fn half(&self) -> Expr {
        Expr::app(self.rat_inv.clone(), self.rat_two.clone())
    }
    fn rho_third(&self) -> Expr {
        let one_nat = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let mut three_nat = self.nat_zero.clone();
        for _ in 0..3 {
            three_nat = Expr::app(self.nat_succ.clone(), three_nat);
        }
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), one_nat), three_nat],
        )
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
    /// `Rat.powNat (Rat.mk (Int.ofNat 8) 1) n` — byte-matches `Hc24Consts::pow8`
    /// (whose base is the `Rat` literal `8`, NOT the `Nat` numeral).
    fn pow8(&self, n: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [self.rat_eight(), n.clone()])
    }
    /// `2^n := Nat.pow 2 n`.
    fn pow2(&self, n: &Expr) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let two = Expr::app(self.nat_succ.clone(), one);
        Expr::apps(self.nat_pow.clone(), [two, n.clone()])
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn fin_pow(&self, n: &Expr) -> Expr {
        self.fin_of(&self.pow2(n))
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    #[cfg(test)]
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat())
    }
    fn pm_of(&self, b: Expr) -> Expr {
        Expr::app(self.pm.clone(), b)
    }
    fn flip(&self, n: &Expr, x: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.hc_flip.clone(), [n.clone(), x.clone(), i.clone()])
    }
    /// `deriv_lam := fun (x:HCPoint n) => pm(f x) − pm(f(hcFlip n x i))` — `D_i f`
    /// as a function. `g x` β-reduces to step2's inlined `D_i f x`, so the two
    /// `subsetSum` integrands are def-eq.
    fn deriv_lam(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let fx = Expr::app(f.clone(), x.clone());
        let fflip = Expr::app(f.clone(), self.flip(n, &x, i));
        let body = self.sub(self.pm_of(fx), self.pm_of(fflip));
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `noiseOp (1/3) n g`.
    fn op(&self, n: &Expr, g: &Expr) -> Expr {
        Expr::apps(
            self.noise_op.clone(),
            [self.rho_third(), n.clone(), g.clone()],
        )
    }
    /// `noiseFn (1/3) n F`.
    fn noise_fn(&self, n: &Expr, fcn: &Expr) -> Expr {
        Expr::apps(
            self.noise_fn.clone(),
            [self.rho_third(), n.clone(), fcn.clone()],
        )
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    /// `subsetSum_congr n G H pw`.
    #[cfg(test)]
    fn ssum_congr(&self, n: &Expr, g: Expr, h: Expr, pw: Expr) -> Expr {
        Expr::apps(self.subset_sum_congr.clone(), [n.clone(), g, h, pw])
    }
    fn sq(&self, t: Expr) -> Expr {
        self.mul(t.clone(), t)
    }
    fn pow4(&self, t: Expr) -> Expr {
        let s = self.sq(t);
        self.mul(s.clone(), s)
    }
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.mul_nonneg.clone(), [a, b, ha, hb])
    }
    fn sq_nonneg(&self, a: Expr) -> Expr {
        Expr::app(self.sq_nonneg.clone(), a)
    }
    /// `Fin.sum_nonneg N f per : 0 ≤ Fin.sum N f`. (subsetSum δ-unfolds to Fin.sum.)
    fn fin_sum_nonneg(&self, n_pow: &Expr, f: Expr, per: Expr) -> Expr {
        Expr::apps(self.fin_sum_nonneg.clone(), [n_pow.clone(), f, per])
    }
    /// `Rat.powNat_nonneg b n h : 0 ≤ powNat b n`.
    fn pow_nat_nonneg(&self, b: Expr, n: &Expr, h: Expr) -> Expr {
        Expr::apps(self.pow_nat_nonneg.clone(), [b, n.clone(), h])
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c hbc ha : a·b ≤ a·c`.
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, ha: Expr) -> Expr {
        Expr::apps(self.mul_le_left.clone(), [a, b, cc, hbc, ha])
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    fn congr_arg(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(self.congr_arg.clone(), [self.rat(), self.rat(), a, b, f, h])
    }
    /// `0 ≤ b` for a concrete `Rat.mk` literal `b`, via `le_of_ble_eq_true`.
    fn nonneg_lit(&self, b: Expr) -> Expr {
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let eq_refl_bool = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [bool_c, btrue],
        );
        Expr::apps(self.le_of_ble.clone(), [self.zero(), b, eq_refl_bool])
    }
    fn lam_rat<F: Fn(Expr) -> Expr>(&self, parent: &EnvDeclBuilder, f: F) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = d.fresh_local(self.rat());
        let body = f(t);
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, self.rat(), body))
    }
    fn lam_hcp<F: Fn(&EnvDeclBuilder, &Expr) -> Expr>(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        f: F,
    ) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let body = f(&d, &x);
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `eight := Rat.mk (Int.ofNat 8) 1` — the `Rat` literal `8` for powNat_nonneg's
    /// base nonneg side. NOTE: `powNat`'s base is `8 : Rat = Rat.mk (ofNat 8) 1`.
    fn rat_eight(&self) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let mut eight_nat = self.nat_zero.clone();
        for _ in 0..8 {
            eight_nat = Expr::app(self.nat_succ.clone(), eight_nat);
        }
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), eight_nat), one],
        )
    }
}

impl Environment {
    /// Register STEP 4 assembly (`dualhc_step4_sq_le`). Idempotent; kernel-checked,
    /// `Constructive`, empty domain-axiom closure.
    pub fn init_boolean_analysis_kkl_dualhc_step4_assemble(&mut self) -> Result<(), EnvError> {
        self.register_dualhc_step4_sq_le()?;
        Ok(())
    }

    /// `BoolAnalysis.dualhc_step4_sq_le` — the un-normalized squared dual-HC
    /// `W² ≤ 16·(m³·8^n)`. See the module docs. Kernel-checked, `Constructive`,
    /// empty admitted-axiom closure. Idempotent.
    pub fn register_dualhc_step4_sq_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_step4_sq_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // pm, hcFlip, BoolFn, HCPoint
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.init_fin_sum()?; // Fin.sum_nonneg
        self.init_boolean_analysis_order_toolkit()?; // mul_nonneg, sq_nonneg, mul_le_mul_of_nonneg_left
        self.init_algebra_rat_halves()?;
        self.init_rat_field_inst()?; // mul_assoc
        self.register_rat_mul_assoc_proof()?;
        self.register_rat_pow_nat()?; // Rat.powNat, powNat_nonneg
        self.register_rat_minmax_proofs()?; // le_of_ble_eq_true
                                            // dual-HC leaves
        self.register_dualhc_step2_holder_inst()?;
        self.register_dualhc_step4_half_inner_eq()?;
        self.register_dualhc_step3_op_fourth_le()?;
        self.register_noise_fn_eq_noise_op()?;
        self.register_dualhc_step4_desq_cancel()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = AsmConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_assemble(&c, false),
            value: build_assemble(&c, true),
        })
    }
}

// The assembly term builder lives in a sibling include to keep this file under
// the 500-line convention.
include!("boolean_analysis_kkl_dualhc_step4_assemble_build.rs");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_dualhc_step4_assemble()
            .expect("init_boolean_analysis_kkl_dualhc_step4_assemble");
        env.init_boolean_analysis_kkl_dualhc_step4_assemble()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_dualhc_step4_sq_le_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.dualhc_step4_sq_le");
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
