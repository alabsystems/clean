// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Friedgut SIZE/LOW spelling bridge — the `Rat.powNat (Rat.ofNat 9) d`↔`natCast(9^d)`
//! identity (BLOCKER 1 of the `friedgut_boolean` co-land).
//!
//! The LOW band (`friedgut_restricted_mass_le`) and `friedgut_l2_core` carry the
//! `9^d` factor as `Rat.powNat (Rat.ofNat 9) d` (the `Rat.powNat` spelling), while
//! `friedgut_low_budget_cancel` and `friedgut_size_poly_bound` carry it as
//! `natCast (Nat.pow 9 d) ≡ Rat.mk (Int.ofNat (Nat.pow 9 d)) 1` (the `Nat.pow` cast
//! spelling). This brick proves they coincide so the LOW-budget cancellation
//! (`9^d·(dr·I) ≤ eps/2`) feeds `friedgut_l2_core`'s `hlow` hypothesis directly:
//!
//! ```text
//! BoolAnalysis.powNat_nine_eq_ofNat_pow :
//!   ∀ (d : Nat),
//!     @Eq Rat
//!       (Rat.powNat (Rat.ofNat 9) d)
//!       (Rat.mk (Int.ofNat (Nat.pow 9 d)) 1)
//! ```
//!
//! ## Proof (`Nat.rec` on `d`, constructive, EMPTY admitted-axiom closure)
//!
//! Write `nine := Rat.ofNat 9` (the const-app spelling the LOW band uses),
//! `P d := powNat nine d`, `Q d := ofNat (Nat.pow 9 d)`. This is the base-9
//! analogue of `BoolAnalysis.powNat_two_eq_ofNat_pow`
//! (`boolean_analysis_kkl_pow2_bridge.rs`):
//!
//!   * BASE `d = 0`: `P 0 ι→ Rat.one` (`powNat _ 0`), and
//!     `Q 0 ≡ ofNat (Nat.pow 9 0) ι→ ofNat 1 ≡ Rat.one` (`Nat.pow _ 0 ι→ 1`,
//!     `ofNat 1 ≡ Rat.one` defeq). `Eq.refl` on the RHS `ofNat(Nat.pow 9 0)`
//!     closes it (LHS ι→ Rat.one is def-eq).
//!   * STEP `d = k+1`, ih `P k = Q k`:
//!     - `P (k+1) ι→ nine · P k` (`powNat_succ`);
//!     - `Q (k+1) ≡ ofNat (Nat.pow 9 (k+1)) ι→ ofNat (Nat.mul (Nat.pow 9 k) 9)`.
//!       Chain:
//!       nine·P k  =[congr (nine·) ih]  nine·Q k
//!                =[mul_comm]           Q k · nine
//!                =[symm ofNat_mul]     ofNat (Nat.mul (Nat.pow 9 k) 9) ≡ Q (k+1).
//!       (`ofNat_mul (Nat.pow 9 k) 9 : ofNat(Nat.mul (9^k) 9) = ofNat(9^k)·ofNat 9`;
//!       `nine ≡ ofNat 9`, `Q k ≡ ofNat (9^k)`, so the endpoints land by def-eq.)
//!
//! Every leaf (`Rat.mul_comm`, `Rat.ofNat_mul`, `Eq.refl/symm/trans/congrArg`,
//! `Nat.rec`, `Rat.powNat_succ`) is `Constructive` with empty closure, so the
//! bridge is too. NO axiom is added or removed. NO `sorry` /
//! `add_decl_unchecked` / `add_decl_structural` / `native_decide` / `unsafe` /
//! `Real`. Idempotent. Gated behind `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the `powNat (ofNat 9)`↔`ofNat(9^d)` bridge.
struct Pow9BridgeConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    int_of_nat: Expr,
    rat: Expr,
    rat_mk: Expr,
    rat_of_nat: Expr,
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

impl Pow9BridgeConsts {
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
            rat_of_nat: k("Rat.ofNat"),
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
    /// `nine := Rat.ofNat 9` (the const-app spelling the LOW band's `pow9` uses).
    fn nine(&self) -> Expr {
        Expr::app(self.rat_of_nat.clone(), self.nat_lit(9))
    }
    /// `Rat.mk (Int.ofNat m) 1` — the `natCast m` spelling.
    fn natcast(&self, m: Expr) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), m), self.nat_lit(1)],
        )
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    /// `Rat.powNat nine d`.
    fn pow(&self, d: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [self.nine(), d.clone()])
    }
    /// `Q d := Rat.mk (Int.ofNat (Nat.pow 9 d)) 1` (= `natCast (9^d)`).
    fn qpow(&self, d: &Expr) -> Expr {
        self.natcast(self.nat_pow_of(self.nat_lit(9), d.clone()))
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
    /// `Rat.powNat_succ nine k : nine^(k+1) = nine·nine^k`.
    fn pownat_succ(&self, k: Expr) -> Expr {
        Expr::apps(self.pow_nat_succ.clone(), [self.nine(), k])
    }
    /// `Rat.ofNat_mul m n : ofNat(Nat.mul m n) = ofNat m · ofNat n`.
    fn ofnat_mul(&self, m: Expr, n: Expr) -> Expr {
        Expr::apps(self.ofnat_mul.clone(), [m, n])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm_e(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `fun (z : Rat) => nine·z`.
    fn lam_nine_mul(&self, parent: &EnvDeclBuilder) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (z_id, z) = d.fresh_local(self.rat.clone());
        let body = self.mul(self.nine(), z);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
    }
}

fn build_pow9_bridge(c: &Pow9BridgeConsts, for_value: bool) -> Expr {
    // goal d : powNat nine d = natCast(9^d).
    let goal = |d: &Expr| c.eq(c.pow(d), c.qpow(d));
    if !for_value {
        let mut b = EnvDeclBuilder::new();
        let (d_id, d) = b.fresh_local(c.nat.clone());
        return b.finish(b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), goal(&d)));
    }

    let mut b = EnvDeclBuilder::new();

    // motive := fun d => goal d.
    let motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (d_id, d) = m.fresh_local(c.nat.clone());
        m.finish_child(m.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), goal(&d)))
    };

    // BASE d=0: powNat nine 0 ι→ Rat.one = natCast(9^0). Both reduce to ofNat 1;
    // refl on the RHS `natCast(Nat.pow 9 0)` closes by def-eq (LHS ι→ Rat.one).
    let base = c.refl(c.qpow(&c.nat_lit(0)));

    // STEP: fun (k)(ih : goal k) => goal (k+1).
    let step = {
        let mut s = EnvDeclBuilder::child_of(&b);
        let (k_id, k) = s.fresh_local(c.nat.clone());
        let ih_ty = goal(&k);
        let (ih_id, ih) = s.fresh_local(ih_ty.clone());

        let nine = c.nine();
        let p_k = c.pow(&k); // powNat nine k
        let q_k = c.qpow(&k); // natCast(9^k)
        let nine_pk = c.mul(nine.clone(), p_k.clone()); // nine·P k
        let nine_qk = c.mul(nine.clone(), q_k.clone()); // nine·Q k
        let qk_nine = c.mul(q_k.clone(), nine.clone()); // Q k · nine

        // s1 : powNat nine (k+1) = nine·P k   [powNat_succ nine k].
        let p_succ = c.pow(&c.succ(k.clone())); // powNat nine (k+1)
        let s1 = c.pownat_succ(k.clone());

        // s2 : nine·P k = nine·Q k   [congr (nine·) ih].
        let s2 = c.congr(p_k.clone(), q_k.clone(), c.lam_nine_mul(&s), ih.clone());

        // s3 : nine·Q k = Q k · nine   [mul_comm nine (Q k)].
        let s3 = c.mul_comm_e(nine.clone(), q_k.clone());

        // s4 : Q k · nine = natCast(Nat.mul (9^k) 9)   [symm (ofNat_mul (9^k) 9)].
        //   ofNat_mul (9^k) 9 : ofNat(Nat.mul (9^k) 9) = ofNat(9^k)·ofNat 9.
        //   Q k ≡ ofNat(9^k), nine ≡ ofNat 9, so RHS ≡ Q k · nine (def-eq).
        let nat_pow_k = c.nat_pow_of(c.nat_lit(9), k.clone()); // Nat.pow 9 k
        let nat_mul_pk_9 = c.nat_mul(nat_pow_k.clone(), c.nat_lit(9)); // Nat.mul (9^k) 9
        let ofnat_mul_pk_9 = c.natcast(nat_mul_pk_9.clone()); // natCast(Nat.mul (9^k) 9)
        let ofnm = c.ofnat_mul(nat_pow_k.clone(), c.nat_lit(9)); // = Q k · nine (defeq RHS)
        let s4 = c.symm(ofnat_mul_pk_9.clone(), qk_nine.clone(), ofnm);

        // q_succ := natCast(9^(k+1)) ≡ natCast(Nat.mul (9^k) 9) defeq.
        let q_succ = c.qpow(&c.succ(k.clone()));

        // chain: powNat nine (k+1) = nine·P k = nine·Q k = Q k·nine
        //   = natCast(Nat.mul (9^k) 9) ≡ Q (k+1).
        let t1 = c.trans(p_succ.clone(), nine_pk.clone(), nine_qk.clone(), s1, s2);
        let t2 = c.trans(p_succ.clone(), nine_qk.clone(), qk_nine.clone(), t1, s3);
        let goal_succ = c.trans(p_succ.clone(), qk_nine.clone(), q_succ.clone(), t2, s4);

        let e = s.mk_lam(ih_id, BinderInfo::Default, ih_ty, goal_succ);
        s.finish_child(s.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e))
    };

    let (d_id, d) = b.fresh_local(c.nat.clone());
    let rec = Expr::apps(c.nat_rec.clone(), [motive, base, step, d.clone()]);
    b.finish(b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), rec))
}

impl Environment {
    /// Register `BoolAnalysis.powNat_nine_eq_ofNat_pow`:
    /// `∀ d, Rat.powNat (Rat.ofNat 9) d = natCast (Nat.pow 9 d)`.
    /// Kernel-checked, `Constructive`, EMPTY admitted-axiom closure. Idempotent.
    pub fn register_pownat_nine_eq_ofnat_pow(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.powNat_nine_eq_ofNat_pow");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_rat_ofnat()?; // Rat.ofNat (reducible base)
        self.register_rat_pow_nat()?; // Rat.powNat
        self.register_rat_pow_nat_succ_theorem()?; // Rat.powNat_succ
        self.init_rat_field_inst()?;
        self.register_rat_mul_comm_proof()?; // Rat.mul_comm
        self.register_rat_ofnat_mul()?; // Rat.ofNat_mul
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = Pow9BridgeConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_pow9_bridge(&c, false),
            value: build_pow9_bridge(&c, true),
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
    fn test_pownat_nine_eq_ofnat_pow_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_pownat_nine_eq_ofnat_pow()
            .expect("register_pownat_nine_eq_ofnat_pow");
        env.register_pownat_nine_eq_ofnat_pow().expect("idempotent");
        let nm = Name::from_string("BoolAnalysis.powNat_nine_eq_ofNat_pow");
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
