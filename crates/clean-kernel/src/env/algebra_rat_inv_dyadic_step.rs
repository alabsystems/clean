// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — dyadic `Rat.inv` positivity + step factorization
//! (Stage B3, sqrt run #3).
//!
//! # Why this module exists
//!
//! The dyadic scaled approximation `a_n = ofNat (k_n) · inv (ofNat 2^n)` and its
//! Cauchy modulus (plan `designs/2026-06-18-kkl-real-sqrt-layer-plan.md` §8.4
//! item 4) consume two concrete `Rat.inv` facts about the dyadic denominator
//! `D_n := Rat.ofNat (Nat.pow 2 n)`:
//!
//! - **positivity** `0 < inv D_n` (so the scaled term is nonneg / the bridge
//!   applies), and
//! - **the step factorization** `inv D_{n+1} = inv D_n · inv (ofNat 2)` — the
//!   gear the telescoping geometric sum turns on.
//!
//! Both are built axiom-free from the rung-4a bricks (`Rat.inv_pos`,
//! `Rat.mul_inv`) + the landed Archimedean positivity (`Rat.one_le_ofNat_two_pow`)
//! + the cast-multiplicativity `Rat.ofNat_mul`.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.zero_lt_ofNat_two_pow : ∀ n : Nat,
//!       Rat.lt Rat.zero (Rat.ofNat (Nat.pow 2 n))`.
//! - `Rat.zero_lt_inv_two_pow : ∀ n : Nat,
//!       Rat.lt Rat.zero (Rat.inv (Rat.ofNat (Nat.pow 2 n)))`.
//! - `Rat.inv_two_pow_succ :
//!       ∀ n : Nat, @Eq Rat (Rat.inv (Rat.ofNat (Nat.pow 2 (Nat.succ n))))
//!         (Rat.mul (Rat.inv (Rat.ofNat (Nat.pow 2 n))) (Rat.inv (Rat.ofNat 2)))`.
//!
//! Every declaration is a checked `Theorem` through `self.add_decl`; every
//! theorem's transitive admitted-axiom closure is empty (foundational only).
//! NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.
//!
//! # Key DEFEQ
//!
//! `Nat.pow 2 (succ n) ≡ Nat.mul (Nat.pow 2 n) 2` (ι-reduction of the `Nat.rec`
//! body `fun _ ih => Nat.mul ih 2`), so `Rat.ofNat (Nat.pow 2 (succ n)) ≡
//! Rat.ofNat (Nat.mul (Nat.pow 2 n) 2)` definitionally. The step factorization
//! transports `Rat.ofNat_mul (Nat.pow 2 n) 2 : ofNat (Nat.mul (2^n) 2) =
//! ofNat (2^n) · ofNat 2` through `congrArg Rat.inv`, then applies
//! `Rat.mul_inv (ofNat 2^n)(ofNat 2)` (with both factors `≠ 0` from positivity).
//! Likewise `Rat.ofNat 2 ≡ Rat.ofNat (Nat.pow 2 1)` (via `2^1 ≡ Nat.mul 1 2 ≡ 2`)
//! gives `0 < ofNat 2`.
//!
//! # Universe note
//!
//! `Eq`/`Eq.symm`/`Eq.trans`/`congrArg` over `Rat : Sort 1` are at universe 1.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the dyadic inv step layer.
pub(crate) struct InvStepConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_inv: Expr,
    rat_lt: Expr,
    rat_ofnat: Expr,
    rat_ofnat_mul: Expr,
    rat_mul_inv: Expr,
    rat_inv_pos: Expr,
    rat_ne_zero_of_pos: Expr,
    rat_zero_lt_one: Expr,
    rat_one_le_ofnat_two_pow: Expr,
    rat_lt_of_lt_of_le: Expr,
    eq_rat: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl InvStepConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_inv: k("Rat.inv"),
            rat_lt: k("Rat.lt"),
            rat_ofnat: k("Rat.ofNat"),
            rat_ofnat_mul: k("Rat.ofNat_mul"),
            rat_mul_inv: k("Rat.mul_inv"),
            rat_inv_pos: k("Rat.inv_pos"),
            rat_ne_zero_of_pos: k("Rat.ne_zero_of_pos"),
            rat_zero_lt_one: k("Rat.zero_lt_one"),
            rat_one_le_ofnat_two_pow: k("Rat.one_le_ofNat_two_pow"),
            rat_lt_of_lt_of_le: k("Rat.lt_of_lt_of_le"),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn nat_lit(&self, n: u32) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..n {
            e = self.succ(e);
        }
        e
    }
    /// `Nat.pow 2 n`.
    fn npow2(&self, n: Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.nat_lit(2), n])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn ofnat(&self, n: Expr) -> Expr {
        Expr::app(self.rat_ofnat.clone(), n)
    }
    fn eq_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_rat.clone(), [self.rat.clone(), a, b])
    }
    fn eq_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.rat.clone(), a, b, cc, hab, hbc],
        )
    }
    fn congr_arg(&self, a: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, a2, f, h],
        )
    }
    /// `Rat.ofNat_mul m n : ofNat (Nat.mul m n) = ofNat m · ofNat n`.
    fn ofnat_mul(&self, m: Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_ofnat_mul.clone(), [m, n])
    }
    /// `Rat.mul_inv a b ha hb : inv (a·b) = inv a · inv b`.
    fn mul_inv(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.rat_mul_inv.clone(), [a, b, ha, hb])
    }
    /// `0 < x → x ≠ 0`  via `Rat.ne_zero_of_pos`.
    fn ne_zero_of_pos(&self, x: Expr, hpos: Expr) -> Expr {
        Expr::apps(self.rat_ne_zero_of_pos.clone(), [x, hpos])
    }
    /// `0 < ofNat (Nat.pow 2 n)`  := `lt_of_lt_of_le 0 1 (ofNat 2^n) zero_lt_one
    /// (one_le_ofNat_two_pow n)`.
    fn zero_lt_pow(&self, n: Expr) -> Expr {
        let d = self.ofnat(self.npow2(n.clone()));
        let one_le = Expr::app(self.rat_one_le_ofnat_two_pow.clone(), n);
        Expr::apps(
            self.rat_lt_of_lt_of_le.clone(),
            [
                self.rat_zero.clone(),
                self.rat_one.clone(),
                d,
                self.rat_zero_lt_one.clone(),
                one_le,
            ],
        )
    }
}

impl Environment {
    /// Register the dyadic inv step layer. Idempotent.
    pub fn init_algebra_rat_inv_dyadic_step(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_nat()?;
        // Rat.inv_pos / Rat.ne_zero_of_pos / Rat.zero_lt_one / lt_iff.
        self.init_algebra_rat_inv_dyadic()?;
        // Rat.inv_unique / Rat.mul_inv.
        self.init_algebra_rat_inv_mul()?;
        // Rat.ofNat, Rat.one_le_ofNat_two_pow (the Archimedean positivity).
        self.init_algebra_rat_archimedean()?;
        // Rat.ofNat_mul (cast multiplicativity).
        self.register_rat_ofnat_mul()?;
        // Rat.lt_of_lt_of_le.
        self.init_boolean_analysis_kkl_strictadd2()?;

        let c = InvStepConsts::new();
        self.register_rat_zero_lt_ofnat_two_pow(&c)?;
        self.register_rat_zero_lt_inv_two_pow(&c)?;
        self.register_rat_inv_two_pow_succ(&c)?;
        Ok(())
    }

    /// `Rat.zero_lt_ofNat_two_pow : ∀ n, Rat.lt 0 (ofNat (Nat.pow 2 n))`.
    fn register_rat_zero_lt_ofnat_two_pow(&mut self, c: &InvStepConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.zero_lt_ofNat_two_pow");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let d = c.ofnat(c.npow2(n.clone()));
            let concl = c.lt(c.rat_zero.clone(), d);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let body = c.zero_lt_pow(n);
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.zero_lt_inv_two_pow : ∀ n, Rat.lt 0 (inv (ofNat (Nat.pow 2 n)))`.
    fn register_rat_zero_lt_inv_two_pow(&mut self, c: &InvStepConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.zero_lt_inv_two_pow");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let d = c.ofnat(c.npow2(n.clone()));
            let concl = c.lt(c.rat_zero.clone(), c.inv(d));
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let d = c.ofnat(c.npow2(n.clone()));
            // inv_pos D (zero_lt_pow n) : 0 < inv D.
            let body = Expr::apps(c.rat_inv_pos.clone(), [d, c.zero_lt_pow(n)]);
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.inv_two_pow_succ : ∀ n,
    ///     inv (ofNat (Nat.pow 2 (succ n)))
    ///       = inv (ofNat (Nat.pow 2 n)) · inv (ofNat 2)`.
    fn register_rat_inv_two_pow_succ(&mut self, c: &InvStepConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.inv_two_pow_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let two = c.nat_lit(2);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let d_succ = c.ofnat(c.npow2(c.succ(n.clone())));
            let d_n = c.ofnat(c.npow2(n.clone()));
            let of2 = c.ofnat(two.clone());
            let rhs = c.mul(c.inv(d_n), c.inv(of2));
            let concl = c.eq_ty(c.inv(d_succ), rhs);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());

            // pow_n := Nat.pow 2 n ; D_n := ofNat pow_n ; of2 := ofNat 2.
            let pow_n = c.npow2(n.clone());
            let d_n = c.ofnat(pow_n.clone());
            let of2 = c.ofnat(two.clone());
            // ofNat (Nat.mul pow_n 2) — defeq to ofNat (Nat.pow 2 (succ n)).
            let pow_mul = Expr::apps(
                Expr::const_(Name::from_string("Nat.mul"), vec![]),
                [pow_n.clone(), two.clone()],
            );
            let d_succ_red = c.ofnat(pow_mul.clone());
            // d_succ as written in the goal (ofNat (Nat.pow 2 (succ n))) — defeq d_succ_red.
            let d_succ = c.ofnat(c.npow2(c.succ(n.clone())));

            // e1 : ofNat (Nat.mul pow_n 2) = ofNat pow_n · ofNat 2  (ofNat_mul).
            let e1 = c.ofnat_mul(pow_n.clone(), two.clone());
            let dn_of2 = c.mul(d_n.clone(), of2.clone());
            // step1 : inv (ofNat (Nat.mul pow_n 2)) = inv (ofNat pow_n · ofNat 2)
            //   via congrArg Rat.inv e1.
            let step1 = c.congr_arg(d_succ_red.clone(), dn_of2.clone(), c.rat_inv.clone(), e1);

            // ne-zero of the two factors (from positivity).
            let dn_pos = c.zero_lt_pow(n.clone());
            let dn_ne = c.ne_zero_of_pos(d_n.clone(), dn_pos);
            // 0 < ofNat 2: ofNat 2 ≡ ofNat (Nat.pow 2 1) defeq, so reuse zero_lt_pow 1.
            let of2_pos = c.zero_lt_pow(c.nat_lit(1));
            let of2_ne = c.ne_zero_of_pos(of2.clone(), of2_pos);

            // step2 : inv (ofNat pow_n · ofNat 2) = inv (ofNat pow_n) · inv (ofNat 2)
            //   via Rat.mul_inv.
            let inv_dn = c.inv(d_n.clone());
            let inv_of2 = c.inv(of2.clone());
            let rhs = c.mul(inv_dn.clone(), inv_of2.clone());
            let step2 = c.mul_inv(d_n.clone(), of2.clone(), dn_ne, of2_ne);

            // chain: inv d_succ (≡ inv d_succ_red) → inv (dn·of2) → inv dn · inv of2.
            // Eq.trans is stated with the SYNTACTIC d_succ from the goal; since
            // d_succ ≡ d_succ_red definitionally, step1 (over d_succ_red) is
            // accepted where inv d_succ is expected.
            let inv_dn_of2 = c.inv(dn_of2.clone());
            let body = c.eq_trans(c.inv(d_succ), inv_dn_of2, rhs, step1, step2);

            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
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

    const THEOREMS: &[&str] = &[
        "Rat.zero_lt_ofNat_two_pow",
        "Rat.zero_lt_inv_two_pow",
        "Rat.inv_two_pow_succ",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_inv_dyadic_step()
            .expect("init_algebra_rat_inv_dyadic_step");
        env.init_algebra_rat_inv_dyadic_step().expect("idempotent");
        env
    }

    #[test]
    fn test_rat_inv_dyadic_step_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_rat_inv_dyadic_step_theorems_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
