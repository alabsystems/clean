// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — the scaled cube dyadic approximation sequence.
//!
//! # Why this module exists
//!
//! The cube keystone `NNReal.cbrt x ^ 3 = ofRat x` is built from the scaled
//! cube dyadic approximation
//!
//! ```text
//!   a_n := ofNat (cbrtDyadicNum x n) · inv (ofNat (Nat.pow 2 n))    ( ≈ ⌊cbrt x·2^n⌋ / 2^n )
//! ```
//!
//! This is IDENTICAL in FORM to the sqrt layer's `Rat.dyadicApprox`
//! (`algebra_nnreal_sqrt_seq.rs`) — only the numerator `cbrtDyadicNum` (cube
//! floor) differs from `dyadicNum` (square floor). So the telescoping/Cauchy
//! machinery built over this sequence transfers from the sqrt layer (it depends
//! only on the digit-step bounds `Rat.cbrtDyadicNum_two_mul_le_succ` /
//! `_succ_le_two_mul_succ` + the generic dyadic-inv lemmas, all landed).
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.cbrtDyadicApprox : Rat → Nat → Rat`
//!   `:= fun x n => Rat.mul (Rat.ofNat (Rat.cbrtDyadicNum x n))
//!                          (Rat.inv (Rat.ofNat (Nat.pow 2 n)))`. Reducible Def.
//! - `Rat.zero_le_cbrtDyadicApprox : ∀ x n, Rat.le 0 (cbrtDyadicApprox x n)`.
//!   `Declaration::Theorem`, `ProofQuality::Constructive`, empty closure.
//!
//! NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.
//!
//! # Proof of nonnegativity (mirrors the sqrt seq)
//!
//! `Rat.mul_nonneg (ofNat k_n) (inv (ofNat 2^n)) h1 h2`, where
//! - `h1 : 0 ≤ ofNat k_n` is `Rat.ofNat_le_ofNat_of_le 0 k_n (Nat.zero_le k_n)`,
//! - `h2 : 0 ≤ inv (ofNat 2^n)` is `le_of_lt (Rat.zero_lt_inv_two_pow n)`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Pre-resolved handles for the scaled cube dyadic approximation.
pub(crate) struct CbrtSeqConsts {
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
    rat_cbrt_num: Expr,
    rat_mul_nonneg: Expr,
    rat_ofnat_le_ofnat_of_le: Expr,
    rat_zero_lt_inv_two_pow: Expr,
    rat_lt_iff_le_not_le: Expr,
    and_c: Expr,
    and_left: Expr,
    not_c: Expr,
    iff_mp: Expr,
}

impl CbrtSeqConsts {
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
            rat_cbrt_num: k("Rat.cbrtDyadicNum"),
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
    fn cbrt_num(&self, x: Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_cbrt_num.clone(), [x, n])
    }
    fn approx(&self, x: Expr, n: Expr) -> Expr {
        let kn = self.ofnat(self.cbrt_num(x, n.clone()));
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
    /// Register the scaled cube dyadic approximation sequence. Idempotent.
    pub fn init_algebra_nnreal_cbrt_seq(&mut self) -> Result<(), EnvError> {
        self.init_nat()?;
        self.init_and()?;
        self.init_iff()?;
        self.init_algebra_nnreal_cbrt_dyadic()?; // cbrtDyadicNum, ofNat
        self.init_algebra_rat_inv_dyadic_step()?; // zero_lt_inv_two_pow, inv_pos
        self.register_rat_order_proofs()?; // mul_nonneg, lt_iff_le_not_le
        self.init_rat_linear_order()?;
        self.register_rat_ofnat_le_ofnat_of_le()?; // ofNat_le_ofNat_of_le
        self.init_nat_succ_base()?; // Nat.zero_le

        let c = CbrtSeqConsts::new();
        self.register_rat_cbrt_dyadic_approx(&c)?;
        self.register_rat_zero_le_cbrt_dyadic_approx(&c)?;
        Ok(())
    }

    /// `Rat.cbrtDyadicApprox : Rat → Nat → Rat`.
    fn register_rat_cbrt_dyadic_approx(&mut self, c: &CbrtSeqConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.cbrtDyadicApprox");
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

    /// `Rat.zero_le_cbrtDyadicApprox : ∀ x n, Rat.le 0 (Rat.cbrtDyadicApprox x n)`.
    fn register_rat_zero_le_cbrt_dyadic_approx(
        &mut self,
        c: &CbrtSeqConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.zero_le_cbrtDyadicApprox");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let approx_c = Expr::const_(Name::from_string("Rat.cbrtDyadicApprox"), vec![]);
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

            let kn_nat = c.cbrt_num(x.clone(), n.clone());
            let kn = c.ofnat(kn_nat.clone());
            let den = c.inv(c.ofnat(c.npow2(n.clone())));

            let zero_le_kn_nat = Expr::app(c.nat_zero_le.clone(), kn_nat.clone());
            let h1 = Expr::apps(
                c.rat_ofnat_le_ofnat_of_le.clone(),
                [c.nat_zero.clone(), kn_nat.clone(), zero_le_kn_nat],
            );

            let inv_pos = Expr::app(c.rat_zero_lt_inv_two_pow.clone(), n.clone());
            let h2 = c.le_of_lt0(den.clone(), inv_pos);

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

    const DEFS: &[&str] = &["Rat.cbrtDyadicApprox"];
    const THEOREMS: &[&str] = &["Rat.zero_le_cbrtDyadicApprox"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_cbrt_seq()
            .expect("init_algebra_nnreal_cbrt_seq");
        env.init_algebra_nnreal_cbrt_seq().expect("idempotent");
        env
    }

    #[test]
    fn test_rat_cbrt_seq_present_and_kernel_check() {
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
    fn test_rat_cbrt_seq_theorems_constructive_empty_closure() {
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
