// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC connect — STEP 2 (sub-lemma 2b): the `Rat.powNat`↔`ofNat(2^n)`
//! spelling bridge.
//!
//! `dualhc_final_le`'s hypothesis carries the measure scale as
//! `Rat.powNat (Rat.mk (Int.ofNat 2) 1) n` (the `Rat.powNat` spelling of `2^n`),
//! while `Influence`/`Expect`/`cube` carry it as
//! `Rat.mk (Int.ofNat (Nat.pow 2 n)) 1 ≡ Rat.ofNat (Nat.pow 2 n)` (the `Nat.pow`
//! cast spelling). This module proves they coincide:
//!
//! ```text
//! BoolAnalysis.powNat_two_eq_ofNat_pow :
//!   ∀ (n : Nat),
//!     @Eq Rat
//!       (Rat.powNat (Rat.mk (Int.ofNat 2) 1) n)
//!       (Rat.mk (Int.ofNat (Nat.pow 2 n)) 1)
//! ```
//!
//! ## Proof (`Nat.rec` on `n`, constructive, EMPTY admitted-axiom closure)
//!
//! Write `two := Rat.mk (Int.ofNat 2) 1 ≡ Rat.ofNat 2`, `P n := powNat two n`,
//! `Q n := ofNat (Nat.pow 2 n)`.
//!
//!   * BASE `n = 0`: `P 0 ι→ Rat.one` (`powNat _ 0`), and
//!     `Q 0 ≡ ofNat (Nat.pow 2 0) ι→ ofNat 1 ≡ Rat.one` (`Nat.pow _ 0 ι→ 1`,
//!     `ofNat 1 ≡ Rat.one` defeq). So `Eq.refl Rat.one` closes it.
//!   * STEP `n = k+1`, ih `P k = Q k`:
//!     - `P (k+1) ι→ two · P k` (`powNat_succ`, recurses on the exponent,
//!       multiplies on the LEFT);
//!     - `Q (k+1) ≡ ofNat (Nat.pow 2 (k+1)) ι→ ofNat (Nat.mul (Nat.pow 2 k) 2)`
//!       (`Nat.pow _ (succ k) ι→ Nat.mul (Nat.pow _ k) _`).
//!       Chain:
//!       two·P k  =[congr (two·) ih]  two·Q k
//!               =[mul_comm]          Q k · two
//!               =[symm ofNat_mul]    ofNat (Nat.mul (Nat.pow 2 k) 2) ≡ Q (k+1).
//!       (`ofNat_mul (Nat.pow 2 k) 2 : ofNat(Nat.mul (2^k) 2) = ofNat(2^k)·ofNat 2`;
//!       `two ≡ ofNat 2` defeq, `Q k ≡ ofNat (2^k)` defeq, so the endpoints land
//!       by def-eq with no extra rewrite.)
//!
//! Every leaf (`Rat.mul_comm`, `Rat.ofNat_mul`, `Eq.refl/symm/trans/congrArg`,
//! `Nat.rec`) is `Constructive` with empty closure, so the bridge is too. NO
//! axiom is added or removed.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the `powNat`↔`ofNat(2^n)` bridge.
struct Pow2BridgeConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    int_of_nat: Expr,
    rat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    pow_nat: Expr,
    pow_nat_succ: Expr,
    ofnat_mul: Expr,
    mul_comm: Expr,
    eq1: Expr,
    eq_refl: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
    nat_rec: Expr,
}

impl Pow2BridgeConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            int_of_nat: k("Int.ofNat"),
            rat: k("Rat"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            pow_nat: k("Rat.powNat"),
            pow_nat_succ: k("Rat.powNat_succ"),
            ofnat_mul: k("Rat.ofNat_mul"),
            mul_comm: k("Rat.mul_comm"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            nat_rec: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
        }
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
    fn nat_pow_of(&self, m: Expr, n: Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [m, n])
    }
    fn nat_mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Nat.mul"), vec![]), [a, b])
    }
    /// `Rat.mk (Int.ofNat m) 1` ≡ `Rat.ofNat m`.
    fn rat_of_nat(&self, m: Expr) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), m), self.nat_lit(1)],
        )
    }
    /// `two := Rat.mk (Int.ofNat 2) 1`.
    fn two(&self) -> Expr {
        self.rat_of_nat(self.nat_lit(2))
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    /// `Rat.powNat two n`.
    fn pow(&self, n: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [self.two(), n.clone()])
    }
    /// `Q n := Rat.mk (Int.ofNat (Nat.pow 2 n)) 1`.
    fn qpow(&self, n: &Expr) -> Expr {
        self.rat_of_nat(self.nat_pow_of(self.nat_lit(2), n.clone()))
    }
    fn eq(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), a, b])
    }
    fn refl(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.rat.clone(), a])
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    fn congr(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, g, h],
        )
    }
    /// `Rat.powNat_succ two k : two^(k+1) = two·two^k`.
    fn pownat_succ(&self, k: Expr) -> Expr {
        Expr::apps(self.pow_nat_succ.clone(), [self.two(), k])
    }
    /// `Rat.ofNat_mul m n : ofNat(Nat.mul m n) = ofNat m · ofNat n`.
    fn ofnat_mul(&self, m: Expr, n: Expr) -> Expr {
        Expr::apps(self.ofnat_mul.clone(), [m, n])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm_e(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `fun (z : Rat) => two·z`.
    fn lam_two_mul(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat.clone());
        let body = self.mul(self.two(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }
}

fn build_pow2_bridge(c: &Pow2BridgeConsts, for_value: bool) -> Expr {
    // goal n : powNat two n = ofNat(2^n).
    let goal = |n: &Expr| c.eq(c.pow(n), c.qpow(n));
    if !for_value {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        return b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), goal(&n)));
    }

    let mut b = EnvDeclBuilder::new();

    // motive := fun n => goal n.
    let motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = m.fresh_local(c.nat.clone());
        m.finish_child(m.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), goal(&n)))
    };

    // BASE n=0: powNat two 0 ι→ ... = ofNat(2^0). Both reduce to ofNat 1; refl
    // on the RHS `ofNat(Nat.pow 2 0)` closes by def-eq (LHS ι→ Rat.one ≡ ofNat 1).
    let base = c.refl(c.qpow(&c.nat_lit(0)));

    // STEP: fun (n)(ih : goal n) => goal (n+1).
    let step = {
        let mut s = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = s.fresh_local(c.nat.clone());
        let ih_ty = goal(&n);
        let (ih_id, ih) = s.fresh_local(ih_ty.clone());

        let two = c.two();
        let p_k = c.pow(&n); // powNat two k
        let q_k = c.qpow(&n); // ofNat(2^k)
        let two_pk = c.mul(two.clone(), p_k.clone()); // two·P k
        let two_qk = c.mul(two.clone(), q_k.clone()); // two·Q k
        let qk_two = c.mul(q_k.clone(), two.clone()); // Q k · two

        // s1 : powNat two (k+1) = two·P k   [powNat_succ two k].
        let p_succ = c.pow(&c.succ(n.clone())); // powNat two (k+1)
        let s1 = c.pownat_succ(n.clone());

        // s2 : two·P k = two·Q k   [congr (two·) ih].
        let s2 = c.congr(p_k.clone(), q_k.clone(), c.lam_two_mul(&s), ih.clone());

        // s3 : two·Q k = Q k · two   [mul_comm two (Q k)].
        let s3 = c.mul_comm_e(two.clone(), q_k.clone());

        // s4 : Q k · two = ofNat(Nat.mul (2^k) 2)   [symm (ofNat_mul (2^k) 2)].
        //   ofNat_mul (2^k) 2 : ofNat(Nat.mul (2^k) 2) = ofNat(2^k)·ofNat 2.
        //   Q k ≡ ofNat(2^k) defeq, two ≡ ofNat 2 defeq, so RHS ≡ Q k · two.
        let two_pow_k = c.nat_pow_of(c.nat_lit(2), n.clone()); // Nat.pow 2 k
        let nat_mul_pk_2 = c.nat_mul(two_pow_k.clone(), c.nat_lit(2)); // Nat.mul (2^k) 2
        let ofnat_mul_pk_2 = c.rat_of_nat(nat_mul_pk_2.clone()); // ofNat(Nat.mul (2^k) 2)
        let ofnm = c.ofnat_mul(two_pow_k.clone(), c.nat_lit(2)); // = Q k · two (defeq RHS)
        let s4 = c.symm(ofnat_mul_pk_2.clone(), qk_two.clone(), ofnm);

        // q_succ := ofNat(2^(k+1)) ≡ ofNat(Nat.mul (2^k) 2) defeq.
        let q_succ = c.qpow(&c.succ(n.clone()));

        // chain: powNat two (k+1) = two·P k = two·Q k = Q k·two = ofNat(Nat.mul(2^k) 2)
        //   ≡ Q (k+1).  State the final endpoint as `q_succ` (def-eq to ofnat_mul_pk_2).
        let t1 = c.trans(p_succ.clone(), two_pk.clone(), two_qk.clone(), s1, s2);
        let t2 = c.trans(p_succ.clone(), two_qk.clone(), qk_two.clone(), t1, s3);
        let goal_succ = c.trans(p_succ.clone(), qk_two.clone(), q_succ.clone(), t2, s4);

        let e = s.mk_lam(ih_id, BinderInfo::Default, ih_ty, goal_succ);
        s.finish_child(s.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
    };

    let (n_id, n) = b.fresh_local(c.nat.clone());
    let rec = Expr::apps(c.nat_rec.clone(), [motive, base, step, n.clone()]);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec))
}

impl Environment {
    /// Register `BoolAnalysis.powNat_two_eq_ofNat_pow` — STEP 2 sub-lemma (2b):
    /// `Rat.powNat (Rat.mk (Int.ofNat 2) 1) n = Rat.mk (Int.ofNat (Nat.pow 2 n)) 1`.
    /// Kernel-checked, `Constructive`, EMPTY admitted-axiom closure. Idempotent.
    pub fn register_pownat_two_eq_ofnat_pow(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.powNat_two_eq_ofNat_pow");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_rat_pow_nat()?;
        self.register_rat_pow_nat_succ_theorem()?;
        self.init_rat_field_inst()?;
        self.register_rat_mul_comm_proof()?; // Rat.mul_comm
        self.register_rat_ofnat_mul()?; // Rat.ofNat_mul
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Pow2BridgeConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_pow2_bridge(&c, false),
            value: build_pow2_bridge(&c, true),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_pownat_two_eq_ofnat_pow_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_pownat_two_eq_ofnat_pow()
            .expect("register_pownat_two_eq_ofnat_pow");
        env.register_pownat_two_eq_ofnat_pow().expect("idempotent");
        let nm = Name::from_string("BoolAnalysis.powNat_two_eq_ofNat_pow");
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
