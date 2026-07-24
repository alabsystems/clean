// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the scaled dyadic approximation sequence
//! (Stage B3, sqrt run #3).
//!
//! # Why this module exists
//!
//! The keystone `NNReal.sqrt x · NNReal.sqrt x = ofRat x` (plan
//! `designs/2026-06-18-kkl-real-sqrt-layer-plan.md` §8.4 items 4–6) is built
//! from the scaled dyadic approximation
//!
//! ```text
//!   a_n := ofNat (dyadicNum x n) · inv (ofNat (Nat.pow 2 n))    ( ≈ ⌊√x·2^n⌋ / 2^n )
//! ```
//!
//! This module introduces that sequence as a `Rat`-valued map and proves its
//! per-term NONNEGATIVITY — the property the `NNRat`-lift of the sequence needs
//! (every term must carry a `0 ≤ a_n` proof to be an `NNRat`).
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.dyadicApprox : Rat → Nat → Rat`
//!   `:= fun x n => Rat.mul (Rat.ofNat (Rat.dyadicNum x n))
//!                          (Rat.inv (Rat.ofNat (Nat.pow 2 n)))`.
//!   Reducible `Definition`.
//! - `Rat.zero_le_dyadicApprox : ∀ x n, Rat.le Rat.zero (Rat.dyadicApprox x n)`.
//!   `Declaration::Theorem`, `ProofQuality::Constructive`, empty closure.
//!
//! NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.
//!
//! # Proof of nonnegativity
//!
//! `Rat.mul_nonneg (ofNat k_n) (inv (ofNat 2^n)) h1 h2`, where
//! - `h1 : 0 ≤ ofNat k_n` is `Rat.ofNat_le_ofNat_of_le 0 k_n (Nat.zero_le k_n)`
//!   (with `ofNat 0 ≡ Rat.zero` defeq), and
//! - `h2 : 0 ≤ inv (ofNat 2^n)` is `le_of_lt (Rat.zero_lt_inv_two_pow n)`
//!   (`And.left (Iff.mp (lt_iff_le_not_le 0 _) ·)`).
//!
//! # Frontier note (the telescoping `IsCauchy`, NOT built here)
//!
//! The remaining keystone work — `IsCauchy (dyadicApprox x)` and the squared
//! `Equiv (const x)` — needs the telescoping bound `a_m ≤ a_n + inv(2^n)` for
//! `m ≥ n`, an induction over the gap `m − n` that iterates the digit-step
//! bounds (`Rat.dyadicNum_two_mul_le_succ` / `_succ_le_two_mul_succ`) and the
//! step factorization `Rat.inv_two_pow_succ`. That induction is the documented
//! analytic frontier (plan §8.4 item 4b/5). All the inv-arithmetic gears it
//! consumes are now landed axiom-free (rungs 4a/4a-bis/4a-ter/4c).

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles for the scaled dyadic approximation.
pub(crate) struct SeqConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    nat_zero_le: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_mul: Expr,
    rat_inv: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_ofnat: Expr,
    rat_dyadic_num: Expr,
    rat_mul_nonneg: Expr,
    rat_ofnat_le_ofnat_of_le: Expr,
    rat_zero_lt_inv_two_pow: Expr,
    rat_lt_iff_le_not_le: Expr,
    and_c: Expr,
    and_left: Expr,
    not_c: Expr,
    iff_mp: Expr,
}

impl SeqConsts {
    pub(crate) fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            nat_zero_le: k("Nat.zero_le"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_mul: k("Rat.mul"),
            rat_inv: k("Rat.inv"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_ofnat: k("Rat.ofNat"),
            rat_dyadic_num: k("Rat.dyadicNum"),
            rat_mul_nonneg: k("Rat.mul_nonneg"),
            rat_ofnat_le_ofnat_of_le: k("Rat.ofNat_le_ofNat_of_le"),
            rat_zero_lt_inv_two_pow: k("Rat.zero_lt_inv_two_pow"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            and_c: k("And"),
            and_left: k("And.left"),
            not_c: k("Not"),
            iff_mp: k("Iff.mp"),
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
    fn npow2(&self, n: Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.nat_lit(2), n])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn not_(&self, p: Expr) -> Expr {
        Expr::app(self.not_c.clone(), p)
    }
    fn and(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_c.clone(), [p, q])
    }
    fn ofnat(&self, n: Expr) -> Expr {
        Expr::app(self.rat_ofnat.clone(), n)
    }
    /// `Rat.dyadicNum x n : Nat`.
    fn dyadic_num(&self, x: Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_dyadic_num.clone(), [x, n])
    }
    /// `Rat.dyadicApprox x n` (= `ofNat (dyadicNum x n) · inv (ofNat 2^n)`).
    fn approx(&self, x: Expr, n: Expr) -> Expr {
        let kn = self.ofnat(self.dyadic_num(x, n.clone()));
        let den = self.inv(self.ofnat(self.npow2(n)));
        self.mul(kn, den)
    }
    /// `0 ≤ x` from `0 < x`:  `And.left (Iff.mp (lt_iff_le_not_le 0 x) h)`.
    fn le_of_lt0(&self, x: Expr, h_pos: Expr) -> Expr {
        let le0x = self.le(self.rat_zero.clone(), x.clone());
        let not_le_x0 = self.not_(self.le(x.clone(), self.rat_zero.clone()));
        let and_ty = self.and(le0x.clone(), not_le_x0.clone());
        let lt0x = self.lt(self.rat_zero.clone(), x.clone());
        let iff = Expr::apps(
            self.rat_lt_iff_le_not_le.clone(),
            [self.rat_zero.clone(), x],
        );
        let mp = Expr::apps(self.iff_mp.clone(), [lt0x, and_ty, iff, h_pos]);
        Expr::apps(self.and_left.clone(), [le0x, not_le_x0, mp])
    }
}

impl Environment {
    /// Register the scaled dyadic approximation sequence. Idempotent.
    pub fn init_algebra_nnreal_sqrt_seq(&mut self) -> Result<(), EnvError> {
        self.init_nat()?;
        self.init_and()?;
        self.init_iff()?;
        // Rat.dyadicNum, Rat.ofNat, Rat.dyadicPow4.
        self.init_algebra_nnreal_sqrt_dyadic()?;
        // Rat.inv positivity (Rat.zero_lt_inv_two_pow), inv_pos, etc.
        self.init_algebra_rat_inv_dyadic_step()?;
        // Rat.mul_nonneg, Rat.lt_iff_le_not_le.
        self.register_rat_order_proofs()?;
        self.init_rat_linear_order()?;
        // Rat.ofNat_le_ofNat_of_le.
        self.register_rat_ofnat_le_ofnat_of_le()?;
        // Nat.zero_le.
        self.init_nat_succ_base()?;

        let c = SeqConsts::new();
        self.register_rat_dyadic_approx(&c)?;
        self.register_rat_zero_le_dyadic_approx(&c)?;
        Ok(())
    }

    /// `Rat.dyadicApprox : Rat → Nat → Rat`.
    fn register_rat_dyadic_approx(&mut self, c: &SeqConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.dyadicApprox");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(
            BinderInfo::Default,
            c.rat.clone(),
            Expr::pi(BinderInfo::Default, c.nat.clone(), c.rat.clone()),
        );
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let body = c.approx(x.clone(), n);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `Rat.zero_le_dyadicApprox : ∀ x n, Rat.le 0 (Rat.dyadicApprox x n)`.
    fn register_rat_zero_le_dyadic_approx(&mut self, c: &SeqConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.zero_le_dyadicApprox");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let approx_c = Expr::const_(Name::from_string("Rat.dyadicApprox"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let ap = Expr::apps(approx_c.clone(), [x.clone(), n.clone()]);
            let concl = c.le(c.rat_zero.clone(), ap);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());

            let kn_nat = c.dyadic_num(x.clone(), n.clone());
            let kn = c.ofnat(kn_nat.clone());
            let den = c.inv(c.ofnat(c.npow2(n.clone())));

            // h1 : 0 ≤ ofNat k_n
            //   ofNat_le_ofNat_of_le 0 k_n (Nat.zero_le k_n) : ofNat 0 ≤ ofNat k_n
            //   ofNat 0 ≡ Rat.zero defeq, so this is 0 ≤ ofNat k_n.
            let zero_le_kn_nat = Expr::app(c.nat_zero_le.clone(), kn_nat.clone());
            let h1 = Expr::apps(
                c.rat_ofnat_le_ofnat_of_le.clone(),
                [c.nat_zero.clone(), kn_nat.clone(), zero_le_kn_nat],
            );

            // h2 : 0 ≤ inv (ofNat 2^n)  := le_of_lt (zero_lt_inv_two_pow n).
            let inv_pos = Expr::app(c.rat_zero_lt_inv_two_pow.clone(), n.clone());
            let h2 = c.le_of_lt0(den.clone(), inv_pos);

            // mul_nonneg (ofNat k_n) (inv 2^n) h1 h2 : 0 ≤ (ofNat k_n)·(inv 2^n).
            let body = Expr::apps(c.rat_mul_nonneg.clone(), [kn, den, h1, h2]);

            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
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

    const DEFS: &[&str] = &["Rat.dyadicApprox"];
    const THEOREMS: &[&str] = &["Rat.zero_le_dyadicApprox"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_sqrt_seq()
            .expect("init_algebra_nnreal_sqrt_seq");
        env.init_algebra_nnreal_sqrt_seq().expect("idempotent");
        env
    }

    #[test]
    fn test_rat_sqrt_seq_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in DEFS.iter().chain(THEOREMS.iter()) {
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
    fn test_rat_sqrt_seq_theorems_constructive_empty_closure() {
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
