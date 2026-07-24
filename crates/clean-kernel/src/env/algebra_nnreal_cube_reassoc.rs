// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — the two monomial-reassociation identities that bridge
//! `NNReal.holder3_cross_mono`'s value/bound shapes to the
//! `NNReal.three_cube_eq_add27` / `NNReal.cubed_amgm` cube shapes, plus the
//! additive-27 monotonicity, all axiom-free.
//!
//! For the cube-Minkowski split `3U₁²U₂ ≤ 2P+Q` (design
//! `2026-06-20-hc43-dual-tensorization-cross-term.md`, §11), with `P:=S₁S₂T₁`,
//! `Q:=S₁²T₂`, the cubed chain is
//! ```text
//!   (3U₁²U₂)³ =[three_cube] add27((U₁²U₂)³)
//!             =[I_B]        add27((U₁³·U₁³)·U₂³)
//!             ≤[add27_mono(holder3)] add27(((S₁²T₁)·(S₁²T₁))·(S₂²T₂))
//!             =[I_C]        add27((P·P)·Q)
//!             ≤[cubed_amgm] (2P+Q)³.
//! ```
//! This module lands the three middle bricks (`I_B`, `I_C`, `add27_mono`); the
//! `cube_split.rs` module chains them with `le_of_cube_le_cube`.
//!
//! - `NNReal.cube_reassoc_lhs : ∀ a b, @Eq NNReal (((a·a)·b)³) ((a³·a³)·b³)`  (I_B)
//! - `NNReal.cube_reassoc_rhs : ∀ s1 s2 t1 t2, @Eq NNReal
//!       (((s1²t1)·(s1²t1))·(s2²t2)) (((s1s2t1)·(s1s2t1))·(s1²t2))`            (I_C)
//! - `NNReal.add27_mono : ∀ a b, NNReal.le a b → NNReal.le (add27 a) (add27 b)`
//!
//! The two equalities are pure `Rat` polynomial identities (`RatPolyProver`)
//! lifted via `Quot.sound` on a POINTWISE-EQUAL `CauSeq.Equiv` (the
//! `three_cube` recipe, generalised to 2 / 4 carrier variables). `add27_mono`
//! is 26 `NNReal.add_le_add`s over the left-nested sum.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, foundational-only
//! closure. NO `sorry` / `add_decl_unchecked` / `add_decl_structural` / new axiom.

use super::algebra_rat_poly_prover::RatPolyProver;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

const AMGM_COEFF: u32 = 27;

/// Shared handles for the reassociation lifts + additive monotonicity.
struct ReassocConsts {
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
    nnreal_le: Expr,
    nnreal_add_le_add: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    causeq_mul: Expr,
    and_c: Expr,
    and_intro: Expr,
    exists_c: Expr,
    exists_intro: Expr,
    nat_le: Expr,
    eq_rat: Expr,
    eq_symm: Expr,
    eq_subst: Expr,
    quot_equiv_sound: (Expr, Expr),
}

impl ReassocConsts {
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
            nnreal_le: k("NNReal.le"),
            nnreal_add_le_add: k("NNReal.add_le_add"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            causeq_mul: k("NNReal.CauSeq.mul"),
            and_c: k("And"),
            and_intro: k("And.intro"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![l1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            nat_le: k("Nat.le"),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            quot_equiv_sound: (
                Expr::const_(Name::from_string("Quot.ind"), vec![l1.clone()]),
                Expr::const_(Name::from_string("Quot.sound"), vec![l1]),
            ),
        }
    }

    fn quot_ind(&self) -> &Expr {
        &self.quot_equiv_sound.0
    }
    fn quot_sound_c(&self) -> &Expr {
        &self.quot_equiv_sound.1
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

    // ── NNReal ──
    fn nn_mul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn nn_add(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a.clone(), b.clone()])
    }
    fn nn_le(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a.clone(), b.clone()])
    }
    fn nn_add_le_add(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.nnreal_add_le_add.clone(),
            [a.clone(), b.clone(), cc.clone(), d.clone(), h1, h2],
        )
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
    fn cau_mul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.causeq_mul.clone(), [a.clone(), b.clone()])
    }
    fn vseq(&self, x: &Expr, n: &Expr) -> Expr {
        let seq = Expr::app(Expr::app(self.causeq_seq.clone(), x.clone()), n.clone());
        Expr::app(self.nnrat_val.clone(), seq)
    }
    fn nat_le(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a.clone(), b.clone()])
    }
    fn bound_pair(&self, x: &Expr, y: &Expr, eps: &Expr) -> Expr {
        let left = self.rlt(x, &self.radd(y, eps));
        let right = self.rlt(y, &self.radd(x, eps));
        Expr::apps(self.and_c.clone(), [left, right])
    }
    fn and_intro(&self, p: &Expr, q: &Expr, hp: Expr, hq: Expr) -> Expr {
        Expr::apps(self.and_intro.clone(), [p.clone(), q.clone(), hp, hq])
    }
    fn quot_sound(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.quot_sound_c().clone(),
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
    /// Register `NNReal.cube_reassoc_lhs`, `NNReal.cube_reassoc_rhs`,
    /// `NNReal.add27_mono`. Idempotent; foundational-only.
    pub fn init_algebra_nnreal_cube_reassoc(&mut self) -> Result<(), EnvError> {
        self.init_algebra_rat_poly_prover()?;
        self.init_rat_quotient_poc()?; // Rat.add_zero
        self.register_rat_add_lt_add_left()?;
        self.init_algebra_nnreal_mul_lift()?; // NNReal.mul, CauSeq.mul, NNRat.val
        self.init_algebra_nnreal_add()?; // NNReal.add
        self.init_algebra_nnreal_le()?; // NNReal carrier, Quot.sound, Equiv
        self.init_algebra_nnreal_le_add()?; // NNReal.add_le_add
        self.init_and()?;
        self.init_exists()?;
        self.init_eq()?;

        let c = ReassocConsts::new();
        self.register_reassoc_lhs(&c)?;
        self.register_reassoc_rhs(&c)?;
        self.register_reassoc_lhs_b(&c)?;
        self.register_reassoc_rhs_b(&c)?;
        self.register_add27_mono(&c)?;
        Ok(())
    }
}

include!("algebra_nnreal_cube_reassoc_proof.rs");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "NNReal.cube_reassoc_lhs",
        "NNReal.cube_reassoc_rhs",
        "NNReal.cube_reassoc_lhs_b",
        "NNReal.cube_reassoc_rhs_b",
        "NNReal.add27_mono",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_cube_reassoc()
            .expect("init_algebra_nnreal_cube_reassoc");
        env.init_algebra_nnreal_cube_reassoc().expect("idempotent");
        env
    }

    #[test]
    fn test_cube_reassoc_kernel_check() {
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
    fn test_cube_reassoc_constructive_empty_closure() {
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
