// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Rat.powNat` base-multiplicativity — `(a·b)^k = a^k · b^k`.
//!
//! The noise semigroup `noiseDensityW_compose` folds the two single-power
//! weights `ρ^{|S|}·ρ^{|S|}` (one from each density) into the squared-base
//! weight `(ρ·ρ)^{|S|}` of `noiseDensityW (ρ²)`. The clean algebraic identity it
//! turns on is
//!
//! ```text
//! Rat.powNat_mul_base : ∀ (a b : Rat) (k : Nat),
//!   Rat.powNat (Rat.mul a b) k = Rat.mul (Rat.powNat a k) (Rat.powNat b k)
//! ```
//!
//! (specialized at `a = b = ρ` gives `(ρ·ρ)^k = ρ^k·ρ^k`, the weight-fold).
//!
//! `Nat.rec` on `k` (mirrors `Rat.powNat_add`):
//! - base `k = 0`: `(a·b)^0 ≡ 1` and `a^0·b^0 ≡ 1·1`, so the goal is
//!   `1 = 1·1`, closed by `Eq.symm (Rat.mul_one 1)`.
//! - step `k+1`, ih `(a·b)^k = a^k·b^k`: `(a·b)^(k+1) ≡ (a·b)·(a·b)^k`
//!   (`powNat_succ`, ι), then
//!     (a·b)·(a·b)^k = (a·b)·(a^k·b^k)   [congr (a·b)· ih]
//!                   = (a·a^k)·(b·b^k)   [Rat.mul_mul_mul_comm a b a^k b^k]
//!                   ≡ a^(k+1)·b^(k+1)   [powNat_succ reversed, def-eq].
//!
//! Every cited brick (`Rat.mul_one`, `Rat.mul_mul_mul_comm`, the `Rat.powNat`
//! recursor, Eq built-ins) is constructive with an empty admitted-axiom closure,
//! so this is `ProofQuality::Constructive`, empty closure. No axiom added/removed.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `Rat.powNat_mul_base : ∀ (a b : Rat) (k : Nat),
    ///   Rat.powNat (Rat.mul a b) k = Rat.mul (Rat.powNat a k) (Rat.powNat b k)`.
    /// See module docs. Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub(crate) fn register_rat_pow_nat_mul_base_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.powNat_mul_base");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?; // Rat.mul, Rat.one, Rat.mul_one
        self.register_rat_pow_nat()?; // Rat.powNat
        {
            // Rat.mul_mul_mul_comm's proof references Rat.mul_assoc / Rat.mul_comm.
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }
        self.register_rat_mul_mul_mul_comm_theorem()?; // Rat.mul_mul_mul_comm
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let (ty, value) = build();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Register `Rat.powNat_one_base : ∀ (k : Nat),
    ///   Rat.powNat Rat.one k = Rat.one`.
    ///
    /// `Nat.rec` on `k`:
    /// - base `k = 0`: `1^0 ≡ 1`, goal `1 = 1`, `Eq.refl 1`.
    /// - step `k+1`, ih `1^k = 1`: `1^(k+1) ≡ 1·1^k` (`powNat_succ`, ι), then
    ///     `1·1^k = 1·1`  [congr (1·) ih]
    ///           = 1      [Rat.mul_one 1].
    ///
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub(crate) fn register_rat_pow_nat_one_base_theorem(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.powNat_one_base");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?; // Rat.mul, Rat.one
        self.register_rat_pow_nat()?; // Rat.powNat
        {
            // Rat.mul_one / Rat.one_mul live in the structural quotient registrar.
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_one_base();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

fn build_one_base() -> (Expr, Expr) {
    let l0 = Level::zero();
    let l1 = Level::succ(l0.clone());
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
    let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
    let pow_nat = Expr::const_(Name::from_string("Rat.powNat"), vec![]);
    let mul_one = Expr::const_(Name::from_string("Rat.mul_one"), vec![]);
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![l0.clone()]);
    let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]);
    let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]);

    let mul = |a: Expr, b: Expr| Expr::apps(rat_mul.clone(), [a, b]);
    let pow = |a: &Expr, k: &Expr| Expr::apps(pow_nat.clone(), [a.clone(), k.clone()]);
    let eq_rat = |a: Expr, b: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            [rat.clone(), a, b],
        )
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (k_id, k) = b.fresh_local(nat.clone());
        let concl = eq_rat(pow(&rat_one, &k), rat_one.clone());
        let e = b.mk_pi(k_id, BinderInfo::Default, nat.clone(), concl);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();

        // motive : fun (k : Nat) => 1^k = 1
        let motive = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = d.fresh_local(nat.clone());
            let body = eq_rat(pow(&rat_one, &k), rat_one.clone());
            d.finish_child(d.mk_lam(k_id, BinderInfo::Default, nat.clone(), body))
        };

        // base : 1^0 = 1  (def-eq 1 = 1)  := Eq.refl 1
        let base = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            [rat.clone(), rat_one.clone()],
        );

        // step : fun (k) (ih : 1^k = 1) => 1^(k+1) = 1
        //   (1^(k+1) ≡ 1·1^k def-eq via powNat_succ)
        let step = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = d.fresh_local(nat.clone());
            let ih_ty = eq_rat(pow(&rat_one, &k), rat_one.clone());
            let (ih_id, ih) = d.fresh_local(ih_ty.clone());

            let pow_one_k = pow(&rat_one, &k);
            let one_pow = mul(rat_one.clone(), pow_one_k.clone()); // 1·1^k  (= 1^(k+1) def-eq)
            let one_one = mul(rat_one.clone(), rat_one.clone()); // 1·1

            // leg1 : 1·1^k = 1·1   congr (1·) ih
            let g_left = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (z_id, z) = e.fresh_local(rat.clone());
                let body = mul(rat_one.clone(), z);
                e.finish_child(e.mk_lam(z_id, BinderInfo::Default, rat.clone(), body))
            };
            let leg1 = Expr::apps(
                congr_arg.clone(),
                [
                    rat.clone(),
                    rat.clone(),
                    pow_one_k.clone(),
                    rat_one.clone(),
                    g_left,
                    ih,
                ],
            );
            // leg2 : 1·1 = 1   Rat.mul_one 1
            let leg2 = Expr::app(mul_one.clone(), rat_one.clone());
            // chain : 1·1^k = 1·1 = 1   (LHS ≡ 1^(k+1) def-eq)
            let body = Expr::apps(
                eq_trans.clone(),
                [rat.clone(), one_pow, one_one, rat_one.clone(), leg1, leg2],
            );
            let r = d.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
            d.finish_child(d.mk_lam(k_id, BinderInfo::Default, nat.clone(), r))
        };

        let mut d = EnvDeclBuilder::child_of(&b);
        let (k_id, k) = d.fresh_local(nat.clone());
        let rec_app = Expr::apps(nat_rec.clone(), [motive, base, step, k.clone()]);
        let val = d.finish_child(d.mk_lam(k_id, BinderInfo::Default, nat.clone(), rec_app));
        b.finish(val)
    };

    (ty, value)
}

fn build() -> (Expr, Expr) {
    let l0 = Level::zero();
    let l1 = Level::succ(l0.clone());
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
    let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
    let pow_nat = Expr::const_(Name::from_string("Rat.powNat"), vec![]);
    let mul_one = Expr::const_(Name::from_string("Rat.mul_one"), vec![]);
    let mmmc = Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]);
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![l0.clone()]);
    let eq_symm = Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]);
    let eq_trans = Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]);
    let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]);

    let mul = |a: Expr, b: Expr| Expr::apps(rat_mul.clone(), [a, b]);
    let pow = |a: &Expr, k: &Expr| Expr::apps(pow_nat.clone(), [a.clone(), k.clone()]);
    let eq_rat = |a: Expr, b: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            [rat.clone(), a, b],
        )
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(rat.clone());
        let (bv_id, bv) = b.fresh_local(rat.clone());
        let (k_id, k) = b.fresh_local(nat.clone());
        let lhs = pow(&mul(a.clone(), bv.clone()), &k);
        let rhs = mul(pow(&a, &k), pow(&bv, &k));
        let concl = eq_rat(lhs, rhs);
        let e = b.mk_pi(k_id, BinderInfo::Default, nat.clone(), concl);
        let e = b.mk_pi(bv_id, BinderInfo::Default, rat.clone(), e);
        let e = b.mk_pi(a_id, BinderInfo::Default, rat.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(rat.clone());
        let (bv_id, bv) = b.fresh_local(rat.clone());
        let ab = mul(a.clone(), bv.clone());

        // motive : fun (k : Nat) => (a·b)^k = a^k·b^k
        let motive = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = d.fresh_local(nat.clone());
            let body = eq_rat(pow(&ab, &k), mul(pow(&a, &k), pow(&bv, &k)));
            d.finish_child(d.mk_lam(k_id, BinderInfo::Default, nat.clone(), body))
        };

        // base : (a·b)^0 = a^0·b^0  (def-eq to 1 = 1·1)
        //   = Eq.symm (Rat.mul_one 1) : 1 = 1·1
        let base = {
            let one_one = mul(rat_one.clone(), rat_one.clone());
            let mo = Expr::app(mul_one.clone(), rat_one.clone()); // 1·1 = 1
            Expr::apps(eq_symm.clone(), [rat.clone(), one_one, rat_one.clone(), mo])
        };

        // step : fun (k) (ih : (a·b)^k = a^k·b^k) => (a·b)·(a·b)^k = a^(k+1)·b^(k+1)
        //   (def-eq via powNat_succ both ends).
        let step = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = d.fresh_local(nat.clone());
            let ih_ty = eq_rat(pow(&ab, &k), mul(pow(&a, &k), pow(&bv, &k)));
            let (ih_id, ih) = d.fresh_local(ih_ty.clone());

            let pow_abk = pow(&ab, &k);
            let pak = pow(&a, &k);
            let pbk = pow(&bv, &k);
            let pak_pbk = mul(pak.clone(), pbk.clone());

            // leg1 : (a·b)·(a·b)^k = (a·b)·(a^k·b^k)   congr ((a·b)·) ih
            let g_left = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (z_id, z) = e.fresh_local(rat.clone());
                let body = mul(ab.clone(), z);
                e.finish_child(e.mk_lam(z_id, BinderInfo::Default, rat.clone(), body))
            };
            let leg1 = Expr::apps(
                congr_arg.clone(),
                [
                    rat.clone(),
                    rat.clone(),
                    pow_abk.clone(),
                    pak_pbk.clone(),
                    g_left,
                    ih,
                ],
            );

            // leg2 : (a·b)·(a^k·b^k) = (a·a^k)·(b·b^k)   Rat.mul_mul_mul_comm a b a^k b^k
            let leg2 = Expr::apps(
                mmmc.clone(),
                [a.clone(), bv.clone(), pak.clone(), pbk.clone()],
            );

            // chain: (a·b)·(a·b)^k = (a·b)·(a^k·b^k) = (a·a^k)·(b·b^k)
            //   (the RHS ≡ a^(k+1)·b^(k+1) def-eq, since a^(k+1) ≡ a·a^k etc.)
            let ab_pakpbk = mul(ab.clone(), pak_pbk.clone());
            let target = mul(mul(a.clone(), pak.clone()), mul(bv.clone(), pbk.clone()));
            let body = Expr::apps(
                eq_trans.clone(),
                [
                    rat.clone(),
                    mul(ab.clone(), pow_abk.clone()),
                    ab_pakpbk,
                    target,
                    leg1,
                    leg2,
                ],
            );
            let r = d.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
            d.finish_child(d.mk_lam(k_id, BinderInfo::Default, nat.clone(), r))
        };

        let body = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (k_id, k) = d.fresh_local(nat.clone());
            let rec_app = Expr::apps(nat_rec.clone(), [motive, base, step, k.clone()]);
            d.finish_child(d.mk_lam(k_id, BinderInfo::Default, nat.clone(), rec_app))
        };
        let val = b.mk_lam(bv_id, BinderInfo::Default, rat.clone(), body);
        let val = b.mk_lam(a_id, BinderInfo::Default, rat.clone(), val);
        b.finish(val)
    };

    (ty, value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_rat_pow_nat_mul_base_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_rat_pow_nat_mul_base_theorem()
            .expect("register_rat_pow_nat_mul_base_theorem");
        env.register_rat_pow_nat_mul_base_theorem()
            .expect("idempotent");
        let nm = Name::from_string("Rat.powNat_mul_base");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("powNat_mul_base proof must check against its type");
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

    #[test]
    fn test_rat_pow_nat_one_base_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_rat_pow_nat_one_base_theorem()
            .expect("register_rat_pow_nat_one_base_theorem");
        env.register_rat_pow_nat_one_base_theorem()
            .expect("idempotent");
        let nm = Name::from_string("Rat.powNat_one_base");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("powNat_one_base proof must check against its type");
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
