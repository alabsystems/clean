// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC — **STEP 3**: the operator 4-norm bound for the dual route,
//! `hc24_at_third` instantiated at the **once-applied** noise operator
//! `T_{1/3} g = noiseOp (1/3) n g`.
//!
//! ## What this proves
//!
//! ```text
//! BoolAnalysis.dualhc_step3_op_fourth_le :
//!   ∀ (n : Nat) (g : HCPoint n → Rat),
//!     Fin.sum (2^n) (fun jx => pow4 (noiseFn (1/3) n (noiseOp (1/3) n g) jx))
//!       ≤ (Rat.powNat 8 n)
//!         · sq (Fin.sum (2^n) (fun jx => sq (noiseOp (1/3) n g (hcDecode n jx))))
//! ```
//!
//! with `pow4 t := (t·t)·(t·t)`, `sq t := t·t`, `1/3 := Rat.mk (Int.ofNat 1) 3`
//! (byte-for-byte `hc24_at_third`'s `ρ_hc`). Reading: writing `Tg := noiseOp
//! (1/3) n g` (the un-normalized once-applied operator `T_{1/3} g`) and `T²g :=
//! noiseFn (1/3) n Tg` (the twice-applied operator, the same `2^n·T_{1/3}(T_{1/3}
//! g)` carrier `noiseFn` packages), STEP 3 is
//!
//! ```text
//!   Σ_x (T²g x)⁴  ≤  8^n · (Σ_x (Tg x)²)²  =  8^n · W²
//! ```
//!
//! where `W := Σ_x (Tg x)²` is the (un-normalized) 2-norm-squared of the
//! once-applied operator — exactly STEP 2's intended weight `w := T²g` summed to
//! the 4th power on the LHS, and the squared spectral quantity `W` of the
//! per-coordinate dual-HC on the RHS. This is the **operator 4-norm upper bound**
//! the dual-HC chain pivots through: `hc24_at_third` is the forward `(2→4)`
//! operator bound `‖T_{1/3}F‖₄⁴ ≤ 8^n·(‖F‖₂²)²`; instantiating its FREE function
//! argument `F` at `F := Tg` turns `‖F‖₂²` into `W = ‖Tg‖₂²` and the LHS into the
//! 4th-power sum of `T²g`, the weight STEP 4 feeds back through STEP 2.
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! The body is literally `hc24_at_third n (noiseOp (1/3) n g)` — the landed
//! `hc24_at_third : ∀ n F, <hc24 concl at ρ=1/3>` applied at `F := noiseOp (1/3)
//! n g`. The stated type is `hc24_core_concl` at that same `F` (built through the
//! shared `hc24_core_concl`/`Hc24Consts`), so the application inhabits it
//! directly. `hc24_at_third` is `Constructive` with empty closure (leaves:
//! `hc24_core`, `Rat.le_of_ble_eq_true`, `Eq.refl`); `noiseOp` is a reducible
//! Definition; so STEP 3 is `Constructive` with EMPTY admitted-axiom closure. No
//! axiom is added or removed.

use super::boolean_analysis_hc24_core_base::{hc24_core_concl, Hc24Consts};
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// `ρ_hc := Rat.mk (Int.ofNat 1) 3` (= 1/3). Byte-for-byte `hc24_at_third`'s
/// `rho_third`, so the instantiated conclusion is def-eq to `hc24_at_third`'s.
fn rho_third() -> Expr {
    let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let one_nat = Expr::app(nat_succ.clone(), nat_zero.clone());
    let mut three_nat = nat_zero;
    for _ in 0..3 {
        three_nat = Expr::app(nat_succ.clone(), three_nat);
    }
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mk"), vec![]),
        [Expr::app(int_of_nat, one_nat), three_nat],
    )
}

/// `noiseOp (1/3) n g` — the un-normalized once-applied operator `T_{1/3} g`.
fn noise_op_third(n: &Expr, g: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.noiseOp"), vec![]),
        [rho_third(), n.clone(), g.clone()],
    )
}

impl Environment {
    /// Register STEP 3 (`dualhc_step3_op_fourth_le`). Idempotent; kernel-checked,
    /// `Constructive`, empty domain-axiom closure.
    pub fn init_boolean_analysis_kkl_dualhc_step3(&mut self) -> Result<(), EnvError> {
        self.register_dualhc_step3_op_fourth_le()?;
        Ok(())
    }

    /// `BoolAnalysis.dualhc_step3_op_fourth_le` — see the module docs. The
    /// operator 4-norm bound `Σ_x (T²g)⁴ ≤ 8^n·W²`. Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_dualhc_step3_op_fourth_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_step3_op_fourth_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_hc24_at_third()?; // the forward (2→4) operator bound at ρ=1/3
        self.register_noise_op()?; // noiseOp (the once-applied operator carrier)
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let hc = Hc24Consts::new();

        // Type: ∀ (n) (g : HCPoint n → Rat), <hc24 concl at ρ=1/3, F := noiseOp 1/3 n g>.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(hc.nat.clone());
            let (g_id, g) = b.fresh_local(hc.f_type(&n));
            let tg = noise_op_third(&n, &g);
            let concl = hc24_core_concl(&hc, &b, &rho_third(), &n, &tg);
            let e = b.mk_pi(g_id, BinderInfo::Default, hc.f_type(&n), concl);
            let e = b.mk_pi(n_id, BinderInfo::Default, hc.nat.clone(), e);
            b.finish(e)
        };

        // Value: fun (n) (g) => hc24_at_third n (noiseOp (1/3) n g).
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(hc.nat.clone());
            let (g_id, g) = b.fresh_local(hc.f_type(&n));
            let tg = noise_op_third(&n, &g);
            let body = Expr::apps(
                Expr::const_(Name::from_string("BoolAnalysis.hc24_at_third"), vec![]),
                [n.clone(), tg],
            );
            let e = b.mk_lam(g_id, BinderInfo::Default, hc.f_type(&n), body);
            let e = b.mk_lam(n_id, BinderInfo::Default, hc.nat.clone(), e);
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

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_dualhc_step3()
            .expect("init_boolean_analysis_kkl_dualhc_step3");
        env.init_boolean_analysis_kkl_dualhc_step3()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_dualhc_step3_op_fourth_le_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.dualhc_step3_op_fourth_le");
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
