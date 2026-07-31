// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — `Rat.powNat_nonneg`, a reusable nonnegativity
//! lemma for the `Rat.powNat` recurrence used by the `hc24_core` step's `8^n`
//! coefficient bounds.
//!
//! ```text
//! Rat.powNat_nonneg : ∀ (b : Rat) (k : Nat), Rat.le 0 b → Rat.le 0 (Rat.powNat b k)
//! ```
//!
//! Proof: `Nat.rec` over `k` with motive `fun k => 0 ≤ powNat b k`.
//! - base `powNat b 0 ≡ 1`, `0 ≤ 1` (defeq through `Rat.le_refl`-free
//!   `HcBoundsConsts.zero_le_one`);
//! - step `powNat b (k+1) ≡ b·powNat b k`, `Rat.mul_nonneg b (powNat b k) h_b ih`.
//!
//! Both reduction equations are defeq (single ι-step of the `Nat.rec` carrier),
//! so no `powNat_zero` / `powNat_succ` rewrite is needed.
//!
//! Kernel-checked, `ProofQuality::Constructive` (empty domain-axiom closure).

use super::boolean_analysis_hc_bounds_proofs::HcBoundsConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Rat.powNat_nonneg`. Idempotent; axiom-free.
    pub(crate) fn register_rat_pow_nat_nonneg(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.register_rat_pow_nat()?; // Rat.powNat
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_nonneg, le surface
        self.init_boolean_analysis_hc_bounds()?; // zero_le_one
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }

        let name = Name::from_string("Rat.powNat_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (type_, value) = build_pow_nat_nonneg();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

fn build_pow_nat_nonneg() -> (Expr, Expr) {
    let hc = HcBoundsConsts::new();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let pow_nat = Expr::const_(Name::from_string("Rat.powNat"), vec![]);
    let _nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let pow = |b: &Expr, k: &Expr| Expr::apps(pow_nat.clone(), [b.clone(), k.clone()]);
    let le0 = |x: Expr| hc.le(zero.clone(), x);

    // ── Type: ∀ b k, 0 ≤ b → 0 ≤ powNat b k.
    let ty = {
        let mut bld = EnvDeclBuilder::new();
        let (b_id, bv) = bld.fresh_local(rat.clone());
        let (k_id, k) = bld.fresh_local(nat.clone());
        let hb_ty = le0(bv.clone());
        let (hb_id, _) = bld.fresh_local(hb_ty.clone());
        let concl = le0(pow(&bv, &k));
        let e = bld.mk_pi(hb_id, BinderInfo::Default, hb_ty, concl);
        let e = bld.mk_pi(k_id, BinderInfo::Default, nat.clone(), e);
        let e = bld.mk_pi(b_id, BinderInfo::Default, rat.clone(), e);
        bld.finish(e)
    };

    // ── Proof: fun b k hb => Nat.rec base step k.
    let value = {
        let mut bld = EnvDeclBuilder::new();
        let (b_id, bv) = bld.fresh_local(rat.clone());
        let (k_id, k) = bld.fresh_local(nat.clone());
        let hb_ty = le0(bv.clone());
        let (hb_id, hb) = bld.fresh_local(hb_ty.clone());

        // motive : fun (m : Nat) => 0 ≤ powNat b m   (Sort 0)
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&bld);
            let (m_id, m) = mb.fresh_local(nat.clone());
            let body = le0(pow(&bv, &m));
            mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, nat.clone(), body))
        };

        // base : 0 ≤ powNat b 0   (defeq to 0 ≤ 1)
        let base = hc.zero_le_one();

        // step : fun (m : Nat) (ih : 0 ≤ powNat b m) => mul_nonneg b (powNat b m) hb ih
        let step = {
            let mut sb = EnvDeclBuilder::child_of(&bld);
            let (m_id, m) = sb.fresh_local(nat.clone());
            let ih_ty = le0(pow(&bv, &m));
            let (ih_id, ih) = sb.fresh_local(ih_ty.clone());
            // mul_nonneg b (powNat b m) hb ih : 0 ≤ b·powNat b m  (defeq 0 ≤ powNat b (m+1))
            let body = Expr::apps(
                Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]),
                [bv.clone(), pow(&bv, &m), hb.clone(), ih],
            );
            let lam = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
            sb.finish_child(sb.mk_lam(m_id, BinderInfo::Default, nat.clone(), lam))
        };

        // @Nat.rec.{0} motive base step k
        let rec = Expr::apps(
            Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            [motive, base, step, k.clone()],
        );

        let e = bld.mk_lam(hb_id, BinderInfo::Default, hb_ty, rec);
        let e = bld.mk_lam(k_id, BinderInfo::Default, nat.clone(), e);
        let e = bld.mk_lam(b_id, BinderInfo::Default, rat.clone(), e);
        bld.finish(e)
    };

    (ty, value)
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    #[test]
    fn test_pow_nat_nonneg_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_rat_pow_nat_nonneg().expect("register");
        env.register_rat_pow_nat_nonneg().expect("idempotent");
        let name = Name::from_string("Rat.powNat_nonneg");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("powNat_nonneg proof must check against its type");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
    }
}
