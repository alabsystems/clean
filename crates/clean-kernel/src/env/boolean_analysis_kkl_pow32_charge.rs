// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Stage C, the half-power CONSUMER chain.
//!
//! # Why this module exists
//!
//! The sharp KKL retirement needs the `n`-FREE per-coordinate charge
//! `Σ_i Inf_i^{3/2} ≤ ε^{1/2}·I[f]`. Its per-coordinate step is the half-power
//! bound `0 ≤ x ≤ ε ⟹ x^{3/2} ≤ ε^{1/2}·x`, whose KEY non-circular discharge
//! SQUARES both nonneg sides to the purely RATIONAL cube
//!
//! ```text
//!   (x^{3/2})² = x³ = (x·x)·x,     (ε^{1/2}·x)² = ε·x² = ε·(x·x),
//!   so   x^{3/2} ≤ ε^{1/2}·x   ⟺   (x·x)·x ≤ ε·(x·x).
//! ```
//!
//! The rational shadow `(x·x)·x ≤ ε·(x·x)` is the landed axiom-free
//! `BoolAnalysis.cube_le_eps_sq_mul`. THIS module lifts that shadow into the
//! `NNReal` carrier through `NNReal.ofRat_le_ofRat`, producing the
//! `NNReal`-level squared comparison `ofRat (x³) ≤ ofRat (ε·x²)` — the exact
//! reduced goal of the squaring route, and the carrier-side root of the
//! half-power consumer chain.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! ```text
//! NNReal.cube_le_eps_sq_mul_ofRat :
//!   ∀ (x ε : Rat) (hx : Rat.le 0 x) (he : Rat.le 0 ε) (hxe : Rat.le x ε),
//!     NNReal.le (NNReal.ofRat (Rat.mul (Rat.mul x x) x) hxxx)
//!               (NNReal.ofRat (Rat.mul ε (Rat.mul x x)) hexx)
//! ```
//!
//! where `hxxx : 0 ≤ (x·x)·x` and `hexx : 0 ≤ ε·(x·x)` are the nonneg side
//! conditions (`Rat.mul_nonneg` of `Rat.sq_nonneg x`). The `NNReal.le` is then
//! `NNReal.ofRat_le_ofRat … (cube_le_eps_sq_mul x ε hx hxe)`.
//!
//! # Proof (constructive, empty admitted-axiom closure)
//!
//! - `hxx : 0 ≤ x·x`       := `Rat.sq_nonneg x`.
//! - `hxxx : 0 ≤ (x·x)·x`  := `Rat.mul_nonneg (x·x) x hxx hx`.
//! - `hexx : 0 ≤ ε·(x·x)`  := `Rat.mul_nonneg ε (x·x) he hxx`.
//! - `hcube : (x·x)·x ≤ ε·(x·x)` := `BoolAnalysis.cube_le_eps_sq_mul x ε hx hxe`.
//! - conclusion := `NNReal.ofRat_le_ofRat ((x·x)·x) (ε·(x·x)) hxxx hexx hcube`.
//!
//! Each leaf is `Constructive` with empty closure, so the lemma is too.
//!
//! # Status of the FULL consumer chain (the genuine remaining KKL content)
//!
//! This rung is the carrier-side root. The per-coordinate half-power bound
//! itself (`NNReal.pow32 x ≤ NNReal.mul (sqrtRat ε) (ofRat x)`) requires the
//! reverse-square INVERSION over the genuine `NNReal` Quot carrier — given
//! `a·a = ofRat p`, `b·b = ofRat q`, `p ≤ q`, `0 ≤ a`, `0 ≤ b`, conclude
//! `a ≤ b` — OR, equivalently, `sqrtRat` MONOTONE in `x` (the dyadic-floor
//! monotonicity `dyadicNum x n ≤ dyadicNum y n` for `x ≤ y`, a fresh `Nat.rec`
//! induction) together with `NNReal.mul` commutativity + right-monotonicity.
//! Neither the NNReal reverse-square nor the NNReal mul-algebra exists yet;
//! both are genuine sub-builds (comparable to a Stage-B rung). The summed
//! consumer `Σ_i Inf_i^{3/2} ≤ ε^{1/2}·I[f]` additionally needs an
//! `NNReal`-valued `Fin.sum` (`Fin.sum` is monomorphic over `Rat`). See the
//! Stage-C status note in `designs/2026-06-18-kkl-real-sqrt-layer-plan.md`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared atoms for the half-power consumer chain.
struct Pow32ChargeConsts {
    rat: Expr,
    rat_zero: Expr,
    rat_le: Expr,
    rat_mul: Expr,
    sq_nonneg: Expr,
    mul_nonneg: Expr,
    cube_le: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    nnreal: Expr,
    nnreal_le: Expr,
    nnreal_of_rat: Expr,
    ofrat_le_ofrat: Expr,
}

impl Pow32ChargeConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_le: k("Rat.le"),
            rat_mul: k("Rat.mul"),
            sq_nonneg: k("Rat.sq_nonneg"),
            mul_nonneg: k("Rat.mul_nonneg"),
            cube_le: k("BoolAnalysis.cube_le_eps_sq_mul"),
            #[cfg(test)]
            nnreal: k("NNReal"),
            nnreal_le: k("NNReal.le"),
            nnreal_of_rat: k("NNReal.ofRat"),
            ofrat_le_ofrat: k("NNReal.ofRat_le_ofRat"),
        }
    }

    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn le0(&self, a: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [self.rat_zero.clone(), a])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    /// `Rat.sq_nonneg a : 0 ≤ a·a`.
    fn sq_nonneg_of(&self, a: Expr) -> Expr {
        Expr::app(self.sq_nonneg.clone(), a)
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn mul_nonneg_of(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.mul_nonneg.clone(), [a, b, ha, hb])
    }
    /// `BoolAnalysis.cube_le_eps_sq_mul x ε hx hxe : (x·x)·x ≤ ε·(x·x)`.
    fn cube_le_of(&self, x: Expr, eps: Expr, hx: Expr, hxe: Expr) -> Expr {
        Expr::apps(self.cube_le.clone(), [x, eps, hx, hxe])
    }
    /// `NNReal.ofRat a ha : NNReal`.
    fn of_rat(&self, a: Expr, ha: Expr) -> Expr {
        Expr::apps(self.nnreal_of_rat.clone(), [a, ha])
    }
    /// `NNReal.ofRat_le_ofRat a b ha hb hle : NNReal.le (ofRat a ha)(ofRat b hb)`.
    fn ofrat_le_of(&self, a: Expr, b: Expr, ha: Expr, hb: Expr, hle: Expr) -> Expr {
        Expr::apps(self.ofrat_le_ofrat.clone(), [a, b, ha, hb, hle])
    }
}

impl Environment {
    /// Register the half-power consumer chain bricks. Idempotent.
    pub fn init_boolean_analysis_kkl_pow32_charge(&mut self) -> Result<(), EnvError> {
        self.register_nnreal_cube_le_eps_sq_mul_ofrat()?;
        Ok(())
    }

    /// `NNReal.cube_le_eps_sq_mul_ofRat` — the `NNReal`-level squared shadow of
    /// the half-power bound: `ofRat (x³) ≤ ofRat (ε·x²)` under `0 ≤ x ≤ ε`.
    /// Constructive, empty admitted-axiom closure. Idempotent.
    pub fn register_nnreal_cube_le_eps_sq_mul_ofrat(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.cube_le_eps_sq_mul_ofRat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Leaves (each a checked Theorem with empty closure).
        self.init_boolean_analysis_kkl_halfpower()?; // cube_le_eps_sq_mul
        self.init_boolean_analysis_order_toolkit()?; // Rat.sq_nonneg
        self.register_rat_order_proofs()?; // Rat.mul_nonneg
        self.init_algebra_nnreal_le()?; // NNReal.le, NNReal.ofRat_le_ofRat, NNReal.ofRat

        let c = Pow32ChargeConsts::new();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let hx_ty = c.le0(x.clone());
            let (hx_id, _hx) = b.fresh_local(hx_ty.clone());
            let he_ty = c.le0(eps.clone());
            let (he_id, _he) = b.fresh_local(he_ty.clone());
            let hxe_ty = c.le(x.clone(), eps.clone());
            let (hxe_id, _hxe) = b.fresh_local(hxe_ty.clone());

            let xx = c.mul(x.clone(), x.clone());
            let xxx = c.mul(xx.clone(), x.clone()); // (x·x)·x
            let exx = c.mul(eps.clone(), xx.clone()); // ε·(x·x)
                                                      // nonneg side proofs (appear in the ofRat applications in the type).
            let hxx = c.sq_nonneg_of(x.clone());
            let hxxx = c.mul_nonneg_of(xx.clone(), x.clone(), hxx.clone(), _hx.clone());
            let hexx = c.mul_nonneg_of(eps.clone(), xx.clone(), _he.clone(), hxx);
            let lhs = c.of_rat(xxx, hxxx);
            let rhs = c.of_rat(exx, hexx);
            let concl = Expr::apps(c.nnreal_le.clone(), [lhs, rhs]);

            let e = b.mk_pi(hxe_id, BinderInfo::Default, hxe_ty, concl);
            let e = b.mk_pi(he_id, BinderInfo::Default, he_ty, e);
            let e = b.mk_pi(hx_id, BinderInfo::Default, hx_ty, e);
            let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (eps_id, eps) = b.fresh_local(c.rat.clone());
            let hx_ty = c.le0(x.clone());
            let (hx_id, hx) = b.fresh_local(hx_ty.clone());
            let he_ty = c.le0(eps.clone());
            let (he_id, he) = b.fresh_local(he_ty.clone());
            let hxe_ty = c.le(x.clone(), eps.clone());
            let (hxe_id, hxe) = b.fresh_local(hxe_ty.clone());

            let xx = c.mul(x.clone(), x.clone());
            let xxx = c.mul(xx.clone(), x.clone());
            let exx = c.mul(eps.clone(), xx.clone());
            let hxx = c.sq_nonneg_of(x.clone());
            let hxxx = c.mul_nonneg_of(xx.clone(), x.clone(), hxx.clone(), hx.clone());
            let hexx = c.mul_nonneg_of(eps.clone(), xx.clone(), he.clone(), hxx);
            let hcube = c.cube_le_of(x.clone(), eps.clone(), hx, hxe);
            let body = c.ofrat_le_of(xxx, exx, hxxx, hexx, hcube);

            let e = b.mk_lam(hxe_id, BinderInfo::Default, hxe_ty, body);
            let e = b.mk_lam(he_id, BinderInfo::Default, he_ty, e);
            let e = b.mk_lam(hx_id, BinderInfo::Default, hx_ty, e);
            let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
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
    use crate::tc::TypeChecker;

    const LEMMAS: &[&str] = &["NNReal.cube_le_eps_sq_mul_ofRat"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_pow32_charge()
            .expect("init_boolean_analysis_kkl_pow32_charge");
        env.init_boolean_analysis_kkl_pow32_charge()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_kkl_pow32_charge_all_constructive_theorems() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in LEMMAS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            let value = info.value.clone().expect("proof present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be empty (foundational-only): {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
