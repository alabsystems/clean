// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — L6 CLOSED: the UNCONDITIONAL cube-Minkowski merge
//! `NNReal.cube_minkowski` (`U₁³≤S₁²T₁ → U₂³≤S₂²T₂ → (U₁+U₂)³ ≤ (S₁+S₂)²(T₁+T₂)`),
//! obtained by DISCHARGING the two split hypotheses of the landed
//! `NNReal.cube_minkowski_merge` with the lifted cubed AM-GM
//! (`NNReal.cubed_amgm`) + the cube-order toolkit.
//!
//! # The two splits, derived (design `…hc43…`, §11)
//!
//! With `P:=S₁S₂T₁`, `Q:=S₁²T₂`, `P':=S₁S₂T₂`, `Q':=S₂²T₁`, each split closes
//! ROOT-FREELY by `NNReal.le_of_cube_le_cube` reducing to the cubed chain
//! ```text
//!   (3U₁²U₂)³ =[three_cube] add27((U₁²U₂)³) =[reassoc_lhs] add27((U₁³U₁³)U₂³)
//!             ≤[add27_mono(holder3_cross_mono)] add27(((S₁²T₁)²)S₂²T₂)
//!             =[reassoc_rhs] add27((P·P)·Q) ≤[cubed_amgm] (2P+Q)³,
//! ```
//! whence `3U₁²U₂ ≤ 2P+Q` (`cube_split_A`); `cube_split_B` is the mirror via the
//! `_b` reassoc bricks and `holder3_cross_mono` with swapped corners. Both feed
//! `cube_minkowski_merge` directly.
//!
//! ```text
//!   NNReal.cube_split_A : ∀ U₁ S₁ T₁ U₂ S₂ T₂, U₁³≤S₁²T₁ → U₂³≤S₂²T₂ →
//!     NNReal.le (((U₁²U₂)+(U₁²U₂))+(U₁²U₂)) (((P+P)+Q))
//!   NNReal.cube_split_B : … (the mirror)
//!   NNReal.cube_minkowski : ∀ U₁ S₁ T₁ U₂ S₂ T₂, U₁³≤S₁²T₁ → U₂³≤S₂²T₂ →
//!     NNReal.le (((U₁+U₂)·(U₁+U₂))·(U₁+U₂)) (((S₁+S₂)·(S₁+S₂))·(T₁+T₂))
//! ```
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, foundational-only
//! closure. NO `sorry` / `add_decl_unchecked` / `add_decl_structural` / new axiom.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

const AMGM_COEFF: u32 = 27;

/// Pre-resolved handles + smart-constructors for the L6 assembly.
struct MinkowskiConsts {
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_add: Expr,
    nnreal_le: Expr,
    nnreal_le_trans: Expr,
    le_of_cube_le_cube: Expr,
    holder3_cross_mono: Expr,
    add27_mono: Expr,
    three_cube: Expr,
    reassoc_lhs: Expr,
    reassoc_rhs: Expr,
    reassoc_lhs_b: Expr,
    reassoc_rhs_b: Expr,
    cubed_amgm: Expr,
    merge: Expr,
    eq_symm1: Expr,
    eq_subst1: Expr,
    congr_arg11: Expr,
}

impl MinkowskiConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_add: k("NNReal.add"),
            nnreal_le: k("NNReal.le"),
            nnreal_le_trans: k("NNReal.le.trans"),
            le_of_cube_le_cube: k("NNReal.le_of_cube_le_cube"),
            holder3_cross_mono: k("NNReal.holder3_cross_mono"),
            add27_mono: k("NNReal.add27_mono"),
            three_cube: k("NNReal.three_cube_eq_add27"),
            reassoc_lhs: k("NNReal.cube_reassoc_lhs"),
            reassoc_rhs: k("NNReal.cube_reassoc_rhs"),
            reassoc_lhs_b: k("NNReal.cube_reassoc_lhs_b"),
            reassoc_rhs_b: k("NNReal.cube_reassoc_rhs_b"),
            cubed_amgm: k("NNReal.cubed_amgm"),
            merge: k("NNReal.cube_minkowski_merge"),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg11: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn mul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn add(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a.clone(), b.clone()])
    }
    fn nnle(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a.clone(), b.clone()])
    }
    fn cube(&self, a: &Expr) -> Expr {
        self.mul(&self.mul(a, a), a)
    }
    fn sq_t(&self, s: &Expr, t: &Expr) -> Expr {
        self.mul(&self.mul(s, s), t)
    }
    fn prod3(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        self.mul(&self.mul(a, b), cc)
    }
    fn three(&self, x: &Expr) -> Expr {
        self.add(&self.add(x, x), x)
    }
    fn two_plus(&self, p: &Expr, q: &Expr) -> Expr {
        self.add(&self.add(p, p), q)
    }
    fn add_n(&self, y: &Expr, n: u32) -> Expr {
        debug_assert!(n >= 1);
        let mut acc = y.clone();
        for _ in 1..n {
            acc = self.add(&acc, y);
        }
        acc
    }

    fn le_trans(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.nnreal_le_trans.clone(),
            [a.clone(), b.clone(), cc.clone(), h1, h2],
        )
    }
    fn le_of_cube(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(self.le_of_cube_le_cube.clone(), [a.clone(), b.clone(), h])
    }
    fn symm(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_symm1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone(), h],
        )
    }
    fn subst(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.nnreal.clone(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }
    /// `congrArg (fun w => add27 w) (h : a=b) : add27 a = add27 b`.
    fn congr_add27(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr, h: Expr) -> Expr {
        let f = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = mb.fresh_local(self.nnreal.clone());
            let body = self.add_n(&w, AMGM_COEFF);
            mb.finish_child(mb.mk_lam(w_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        Expr::apps(
            self.congr_arg11.clone(),
            [
                self.nnreal.clone(),
                self.nnreal.clone(),
                a.clone(),
                b.clone(),
                f,
                h,
            ],
        )
    }
    /// `fun t => NNReal.le lhs t` motive.
    fn motive_le_right(&self, parent: &EnvDeclBuilder, lhs: &Expr) -> Expr {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(self.nnreal.clone());
        let body = self.nnle(lhs, &t);
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, self.nnreal.clone(), body))
    }
    /// `fun t => NNReal.le t rhs` motive.
    fn motive_le_left(&self, parent: &EnvDeclBuilder, rhs: &Expr) -> Expr {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = mb.fresh_local(self.nnreal.clone());
        let body = self.nnle(&t, rhs);
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, self.nnreal.clone(), body))
    }
}

impl Environment {
    /// Register `NNReal.cube_split_A`, `NNReal.cube_split_B`,
    /// `NNReal.cube_minkowski`. Idempotent; foundational-only.
    pub fn init_algebra_nnreal_cube_minkowski(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_reverse_cube()?; // NNReal.le_of_cube_le_cube
        self.init_algebra_nnreal_holder3_cross_mono()?; // holder3_cross_mono
        self.init_algebra_nnreal_three_cube()?; // NNReal.three_cube_eq_add27
        self.init_algebra_nnreal_cube_reassoc()?; // reassoc + add27_mono
        self.init_algebra_nnreal_cubed_amgm()?; // NNReal.cubed_amgm
        self.init_algebra_nnreal_cube_minkowski_merge()?; // the MERGE
        self.init_algebra_nnreal_le()?; // NNReal.le.trans
        self.init_eq()?;

        let c = MinkowskiConsts::new();
        self.register_cube_split_a(&c)?;
        self.register_cube_split_b(&c)?;
        self.register_cube_minkowski(&c)?;
        Ok(())
    }
}

include!("algebra_nnreal_cube_minkowski_proof.rs");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "NNReal.cube_split_A",
        "NNReal.cube_split_B",
        "NNReal.cube_minkowski",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_cube_minkowski()
            .expect("init_algebra_nnreal_cube_minkowski");
        env.init_algebra_nnreal_cube_minkowski()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_cube_minkowski_kernel_check() {
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
    fn test_cube_minkowski_constructive_empty_closure() {
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
