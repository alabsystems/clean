// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Stage B3 cast brick: `Rat.ofNat_mul`.
//!
//! # Why this module exists
//!
//! The dyadic-floor square invariant `(Rat.ofNat k_n)² ≤ x · 4^n`
//! (`Rat.dyadicNum`, `algebra_nnreal_sqrt_dyadic.rs`) relates the SQUARE of a
//! `Nat` cast, `Rat.ofNat (k)·Rat.ofNat (k)`, to the cast of the product,
//! `Rat.ofNat (Nat.mul k k)`. The live `Rat` is the QUOTIENT carrier
//! (`Rat := Quot Rat.Raw.Equiv`) and `Rat.mul` is a checked binary `Quot.lift`,
//! so this cast-multiplicativity is NOT `Eq.refl` — it needs a `Quot.sound`.
//!
//! - `Rat.ofNat_mul : ∀ (m n : Nat),`
//!   `   Eq Rat (Rat.ofNat (Nat.mul m n)) (Rat.mul (Rat.ofNat m) (Rat.ofNat n))`
//!
//! # Proof shape (mirrors the on-main axiom-free `Rat.add_natCast`)
//!
//! `Rat.ofNat m ≡ Rat.mk (Int.ofNat m) 1 ≡ Quot.mk (Raw.mk (ofNat m) 1)`.
//! `Rat.mul` lifts to `Raw.mk (num p · num q) (effDenom p · effDenom q)`, so
//! `Rat.mul (mk (ofNat m) 1) (mk (ofNat n) 1)`
//!   `≡ Quot.mk (Raw.mk (Int.mul (ofNat m) (ofNat n)) (Nat.mul 1 1))`.
//! Picking
//!   `raw_l := Raw.mk (Int.ofNat (Nat.mul m n)) 1`,
//!   `raw_r := Raw.mk (Int.mul (ofNat m) (ofNat n)) (Nat.mul 1 1)`,
//! the user goal sides are DEFEQ to `Quot.mk raw_l` (LHS) and `Quot.mk raw_r`
//! (RHS). `Quot.sound raw_l raw_r equiv` closes it, where the `Rat.Raw.Equiv`
//! obligation reduces (both effDenoms ≡ 1) to
//!   `Eq Int (ofNat (m·n) · ofNat 1) ((ofNat m · ofNat n) · ofNat 1)`,
//! built by `congrArg (· · ofNat 1) (Int.ofNat_mul m n)`. `Int.ofNat_mul` is the
//! on-main pure-`Eq.refl` cast (`Int.ofNat (m·n) = Int.mul (ofNat m)(ofNat n)`).
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only — `Quot.sound`). NO `sorry` /
//! `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles for the `Rat.ofNat_mul` cast brick.
struct OfNatMulConsts {
    nat: Expr,
    int: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_mul: Expr,
    int_ofnat: Expr,
    int_mul: Expr,
    int_ofnat_mul: Expr,
    rat_ofnat: Expr,
    rat_mul: Expr,
    raw_mk: Expr,
    raw: Expr,
    raw_equiv: Expr,
    quot_mk: Expr,
    quot_sound: Expr,
    eq1: Expr,
    eq_refl: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl OfNatMulConsts {
    fn new() -> Self {
        let lvl1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            int: k("Int"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_mul: k("Nat.mul"),
            int_ofnat: k("Int.ofNat"),
            int_mul: k("Int.mul"),
            int_ofnat_mul: k("Int.ofNat_mul"),
            rat_ofnat: k("Rat.ofNat"),
            rat_mul: k("Rat.mul"),
            raw_mk: k("Rat.Raw.mk"),
            raw: k("Rat.Raw"),
            raw_equiv: k("Rat.Raw.Equiv"),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![lvl1.clone()]),
            quot_sound: Expr::const_(Name::from_string("Quot.sound"), vec![lvl1.clone()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![lvl1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![lvl1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![lvl1.clone(), lvl1]),
        }
    }

    fn nat_one(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    fn nmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_mul.clone(), [a, b])
    }
    fn of_nat(&self, n: Expr) -> Expr {
        Expr::app(self.int_ofnat.clone(), n)
    }
    fn imul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.int_mul.clone(), [a, b])
    }
    fn rofnat(&self, n: Expr) -> Expr {
        Expr::app(self.rat_ofnat.clone(), n)
    }
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn raw_mk(&self, n: Expr, d: Expr) -> Expr {
        Expr::apps(self.raw_mk.clone(), [n, d])
    }
    fn quot_mk(&self, l: Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.raw.clone(), self.raw_equiv.clone(), l],
        )
    }
    fn quot_sound(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.quot_sound.clone(),
            [self.raw.clone(), self.raw_equiv.clone(), a, b, h],
        )
    }
    fn eq_rat(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), x, y])
    }
    fn refl_rat(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.rat.clone(), x])
    }
    fn trans_rat(&self, x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), x, y, z, h1, h2])
    }
    /// `@congrArg Int Int a b f h : Eq Int (f a)(f b)`.
    fn congr_int(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.int.clone(), self.int.clone(), a, b, f, h],
        )
    }
}

impl Environment {
    /// Register `Rat.ofNat_mul`. Idempotent; axiom-free.
    pub fn register_rat_ofnat_mul(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.ofNat_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?; // Rat.mk, Rat.mul, Rat.Raw.*, Quot machinery
        self.init_rat_arith()?; // ensures live Rat.mul (Quot.lift) is registered
        self.register_rat_ofnat()?; // Rat.ofNat
        self.register_int_ofnat_mul_proof()?; // Int.ofNat_mul (pure refl)

        let c = OfNatMulConsts::new();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let lhs = c.rofnat(c.nmul(m.clone(), n.clone()));
            let rhs = c.rmul(c.rofnat(m.clone()), c.rofnat(n.clone()));
            let concl = c.eq_rat(lhs, rhs);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());

            let one = c.nat_one();
            let of_m = c.of_nat(m.clone());
            let of_n = c.of_nat(n.clone());
            let of_mn = c.of_nat(c.nmul(m.clone(), n.clone())); // Int.ofNat (m·n)
            let prod = c.imul(of_m.clone(), of_n.clone()); // Int.mul (ofNat m)(ofNat n)

            // h_int : Eq Int (ofNat (m·n)) (ofNat m · ofNat n)   (Int.ofNat_mul, refl)
            let h_int = Expr::apps(c.int_ofnat_mul.clone(), [m.clone(), n.clone()]);

            // equiv : Eq Int (ofNat (m·n) · ofNat 1) ((ofNat m · ofNat n) · ofNat 1)
            //   via congrArg (· · ofNat 1) h_int.
            let one_i = c.of_nat(one.clone());
            let mul_right_one = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = d.fresh_local(c.int.clone());
                let body = c.imul(w, one_i.clone());
                d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.int.clone(), body))
            };
            let equiv = c.congr_int(of_mn.clone(), prod.clone(), mul_right_one, h_int);

            // Raw reps.
            let raw_l = c.raw_mk(of_mn.clone(), one.clone());
            let raw_r = c.raw_mk(prod.clone(), c.nmul(one.clone(), one.clone()));

            // Quot.sound raw_l raw_r equiv : Quot.mk raw_l = Quot.mk raw_r.
            let sound = c.quot_sound(raw_l.clone(), raw_r.clone(), equiv);

            // Retarget to the user goal via trans against refls (both defeq).
            let lhs_goal = c.rofnat(c.nmul(m.clone(), n.clone()));
            let rhs_goal = c.rmul(c.rofnat(m.clone()), c.rofnat(n.clone()));
            let quot_l = c.quot_mk(raw_l);
            let quot_r = c.quot_mk(raw_r);
            let to_quot_l = c.refl_rat(lhs_goal.clone()); // lhs_goal = quot_l (defeq)
            let from_quot_r = c.refl_rat(rhs_goal.clone()); // quot_r = rhs_goal (defeq)
            let step1 = c.trans_rat(
                lhs_goal.clone(),
                quot_l.clone(),
                quot_r.clone(),
                to_quot_l,
                sound,
            );
            let proof = c.trans_rat(lhs_goal, quot_r, rhs_goal, step1, from_quot_r);

            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), proof);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

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
        env.register_rat_ofnat_mul()
            .expect("register_rat_ofnat_mul");
        env.register_rat_ofnat_mul().expect("idempotent");
        env
    }

    #[test]
    fn test_rat_ofnat_mul_kernel_checks() {
        let env = env();
        let nm = Name::from_string("Rat.ofNat_mul");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("Rat.ofNat_mul must kernel-check");
    }

    #[test]
    fn test_rat_ofnat_mul_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("Rat.ofNat_mul");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be foundational-only: {:?}",
            env.axiom_deps(&nm)
        );
    }
}
