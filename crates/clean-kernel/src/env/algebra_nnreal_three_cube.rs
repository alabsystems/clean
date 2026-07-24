// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — the additive `(3X)³ = 27·X³` identity on arbitrary
//! `NNReal`, in the SUBTRACTION-FREE additive forms (`3X := (X+X)+X`,
//! `27·Y := Y+Y+…+Y` 27-fold left-nested). This is the design's pinned
//! "additive-27 / (3X)³ identity" (`2026-06-20-hc43-dual-tensorization-cross-term.md`,
//! §11 rung 3-4) that the cube-Minkowski MERGE's split bound needs to reach the
//! `NNReal.cubed_amgm` lower bound `add27(P²Q)`.
//!
//! # Why a `CauSeq` equality lift (not an NNReal-native ring expansion)
//!
//! `(3X)³ = 27X³` at `NNReal` IS a ring identity, but expanding `((X+X)+X)³` to a
//! 27-fold additive normal form by `NNReal.add_cube` + `mul_assoc`/`add_comm` is a
//! many-hundred-term reassociation. At the `Rat` representative level it is a
//! ONE-LINE polynomial identity the landed `RatPolyProver` discharges
//! automatically (both sides normalise to `27·y³`). So we LIFT the `Rat` identity:
//! `Quot.ind` on `X`, then `Quot.sound` on `NNReal.CauSeq.Equiv`, whose
//! per-`ε`/per-`n` `bound_pair` obligation collapses because the two sides are
//! POINTWISE-EQUAL rationals (`val(seq … n) ≡` the same `Rat` value by the
//! `val_mul`/`val_add` `Eq.refl` reductions) — the `Equiv` is then the cheap
//! `vL n = vR n ⊢ vL n < vR n + ε ∧ vR n < vL n + ε` (the `Equiv.refl` shape with
//! one `Eq.subst`).
//!
//! # The identity (axiom-free, kernel-checked)
//!
//! ```text
//!   NNReal.three_cube_eq_add27 : ∀ X : NNReal,
//!     @Eq NNReal (((3X)·(3X))·(3X)) (add27 ((X·X)·X))
//! ```
//! with `3X := (X+X)+X`, `add27 Y := (((…((Y+Y)+Y)…)+Y)` (27 copies, left-nested).
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, admitted-axiom closure
//! `⊆ {propext, Quot.sound, Classical.choice, Eq}` (foundational only — `Quot.sound`
//! is the carrier's setoid quotient axiom, already in the `NNReal` TCB floor). NO
//! `sorry` / `add_decl_unchecked` / `add_decl_structural`. NO new axiom.

use super::algebra_rat_poly_prover::RatPolyProver;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// The additive multiplier in `27·Y`.
const AMGM_COEFF: u32 = 27;

/// Pre-resolved handles + smart-constructors for the `(3X)³ = 27X³` lift.
struct ThreeCubeConsts {
    nat: Expr,
    nat_zero: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_lt: Expr,
    rat_add_zero: Expr,
    rat_add_lt_add_left: Expr,
    nnrat_val: Expr,
    nnreal: Expr,
    nnreal_add: Expr,
    nnreal_mul: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    causeq_add: Expr,
    causeq_mul: Expr,
    and_c: Expr,
    and_intro: Expr,
    exists_c: Expr,
    exists_intro: Expr,
    nat_le: Expr,
    eq_rat: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
    quot_mk: Expr,
    quot_ind: Expr,
    quot_sound: Expr,
}

impl ThreeCubeConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_lt: k("Rat.lt"),
            rat_add_zero: k("Rat.add_zero"),
            rat_add_lt_add_left: k("Rat.add_lt_add_left"),
            nnrat_val: k("NNRat.val"),
            nnreal: k("NNReal"),
            nnreal_add: k("NNReal.add"),
            nnreal_mul: k("NNReal.mul"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_add: k("NNReal.CauSeq.add"),
            causeq_mul: k("NNReal.CauSeq.mul"),
            and_c: k("And"),
            and_intro: k("And.intro"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![l1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            nat_le: k("Nat.le"),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![l1.clone()]),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![l1.clone()]),
            quot_sound: Expr::const_(Name::from_string("Quot.sound"), vec![l1]),
        }
    }

    // ── Rat ──
    fn radd(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a.clone(), b.clone()])
    }
    fn rmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a.clone(), b.clone()])
    }
    fn rlt(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a.clone(), b.clone()])
    }
    fn rthree(&self, x: &Expr) -> Expr {
        self.radd(&self.radd(x, x), x)
    }
    fn rcube(&self, x: &Expr) -> Expr {
        self.rmul(&self.rmul(x, x), x)
    }
    fn radd_n(&self, y: &Expr, n: u32) -> Expr {
        debug_assert!(n >= 1);
        let mut acc = y.clone();
        for _ in 1..n {
            acc = self.radd(&acc, y);
        }
        acc
    }
    fn add_zero(&self, a: &Expr) -> Expr {
        Expr::app(self.rat_add_zero.clone(), a.clone())
    }
    fn add_lt_add_left(&self, a: &Expr, b: &Expr, cc: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.rat_add_lt_add_left.clone(),
            [a.clone(), b.clone(), cc.clone(), h],
        )
    }
    fn eq_symm(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_symm.clone(),
            [self.rat.clone(), a.clone(), b.clone(), h],
        )
    }
    fn subst(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }

    // ── NNReal carrier ──
    fn nn_add(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a.clone(), b.clone()])
    }
    fn nn_mul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn nn_three(&self, x: &Expr) -> Expr {
        self.nn_add(&self.nn_add(x, x), x)
    }
    fn nn_cube(&self, x: &Expr) -> Expr {
        self.nn_mul(&self.nn_mul(x, x), x)
    }
    fn nn_add_n(&self, y: &Expr, n: u32) -> Expr {
        debug_assert!(n >= 1);
        let mut acc = y.clone();
        for _ in 1..n {
            acc = self.nn_add(&acc, y);
        }
        acc
    }
    fn eq_nnreal(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.eq_rat.clone(),
            [self.nnreal.clone(), a.clone(), b.clone()],
        )
    }

    // ── CauSeq ──
    fn cau_add(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.causeq_add.clone(), [a.clone(), b.clone()])
    }
    fn cau_mul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.causeq_mul.clone(), [a.clone(), b.clone()])
    }
    fn cau_three(&self, x: &Expr) -> Expr {
        self.cau_add(&self.cau_add(x, x), x)
    }
    fn cau_cube(&self, x: &Expr) -> Expr {
        self.cau_mul(&self.cau_mul(x, x), x)
    }
    fn cau_add_n(&self, y: &Expr, n: u32) -> Expr {
        debug_assert!(n >= 1);
        let mut acc = y.clone();
        for _ in 1..n {
            acc = self.cau_add(&acc, y);
        }
        acc
    }
    /// `val (seq x n)`.
    fn vseq(&self, x: &Expr, n: &Expr) -> Expr {
        let seq = Expr::app(Expr::app(self.causeq_seq.clone(), x.clone()), n.clone());
        Expr::app(self.nnrat_val.clone(), seq)
    }
    fn nat_le(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a.clone(), b.clone()])
    }
    /// `bound_pair x y ε := And (x < y+ε)(y < x+ε)`.
    fn bound_pair(&self, x: &Expr, y: &Expr, eps: &Expr) -> Expr {
        let left = self.rlt(x, &self.radd(y, eps));
        let right = self.rlt(y, &self.radd(x, eps));
        Expr::apps(self.and_c.clone(), [left, right])
    }
    fn and_intro(&self, p: &Expr, q: &Expr, hp: Expr, hq: Expr) -> Expr {
        Expr::apps(self.and_intro.clone(), [p.clone(), q.clone(), hp, hq])
    }
    fn equiv(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.causeq_equiv.clone(), [a.clone(), b.clone()])
    }
    fn quot_mk(&self, l: &Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), l.clone()],
        )
    }
    /// `@Quot.sound CauSeq Equiv a b h : Eq NNReal (mk a)(mk b)`.
    fn quot_sound(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.quot_sound.clone(),
            [
                self.causeq.clone(),
                self.causeq_equiv.clone(),
                a.clone(),
                b.clone(),
                h,
            ],
        )
    }
}

impl Environment {
    /// Register `NNReal.three_cube_eq_add27`. Idempotent; foundational-only.
    pub fn init_algebra_nnreal_three_cube(&mut self) -> Result<(), EnvError> {
        self.init_algebra_rat_poly_prover()?; // RatPolyProver ring surface + Eq
        self.init_rat_quotient_poc()?; // Rat.add_zero
        self.register_rat_add_lt_add_left()?; // Rat.add_lt_add_left
        self.init_algebra_nnreal_mul_lift()?; // NNReal.mul, CauSeq.mul, NNRat.val
        self.init_algebra_nnreal_add()?; // NNReal.add, CauSeq.add
        self.init_algebra_nnreal_le()?; // NNReal carrier, Quot.sound, Equiv
        self.init_and()?;
        self.init_exists()?;
        self.init_eq()?;

        let c = ThreeCubeConsts::new();
        self.register_three_cube(&c)?;
        Ok(())
    }

    fn register_three_cube(&mut self, c: &ThreeCubeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.three_cube_eq_add27");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.nnreal.clone());
            let lhs = c.nn_cube(&c.nn_three(&x));
            let rhs = c.nn_add_n(&c.nn_cube(&x), AMGM_COEFF);
            let concl = c.eq_nnreal(&lhs, &rhs);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.nnreal.clone(), concl);
            b.finish(e)
        };
        let value = build_three_cube_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

include!("algebra_nnreal_three_cube_proof.rs");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_three_cube()
            .expect("init_algebra_nnreal_three_cube");
        env.init_algebra_nnreal_three_cube().expect("idempotent");
        env
    }

    #[test]
    fn test_three_cube_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("NNReal.three_cube_eq_add27");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("NNReal.three_cube_eq_add27 must kernel-check: {e:?}"));
    }

    #[test]
    fn test_three_cube_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("NNReal.three_cube_eq_add27");
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
