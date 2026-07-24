// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — `NNReal.cube_minkowski_merge` (L6 / the MERGE): the
//! superadditive merge of the cubed cube-Hölder functional, the cross-term
//! assembly the SQRT-FREE `(4/3,4)` dual-HC tensorization step needs.
//!
//! # Why this module exists (the sqrt-free dual route, L6)
//!
//! The sqrt-free dual tensorization (design
//! `2026-06-20-hc43-dual-tensorization-cross-term.md`, §11) closes its induction
//! step by the SUPERADDITIVE MERGE of the Hölder functional `U³ ≤ S²·T`:
//!
//! ```text
//!   (MERGE)  U₁³≤S₁²T₁ → U₂³≤S₂²T₂ → (U₁+U₂)³ ≤ (S₁+S₂)²·(T₁+T₂).
//! ```
//!
//! Expanding both sides (`NNReal.add_cube` on the LHS; the `add_sq`·distribute
//! expansion on the RHS), the merge reduces EXACTLY to the two cube hypotheses
//! plus the hypothesis-free CROSS inequality
//! ```text
//!   3U₁²U₂ + 3U₁U₂²  ≤  S₁²T₂ + 2S₁S₂T₁ + 2S₁S₂T₂ + S₂²T₁,
//! ```
//! which splits SYMMETRICALLY into
//! ```text
//!   (Split A)  3U₁²U₂ ≤ 2P+Q,    P:=S₁S₂T₁,  Q:=S₁²T₂
//!   (Split B)  3U₁U₂² ≤ 2P'+Q',  P':=S₁S₂T₂, Q':=S₂²T₁   (the mirror).
//! ```
//!
//! Per the design (§11), each split closes ROOT-FREELY by `le_of_cube_le_cube`
//! reducing to the cubed chain `(3U₁²U₂)³ = 27U₁⁶U₂³ ≤ 27P²Q ≤ (2P+Q)³`, whose
//! FIRST `≤` is the landed `NNReal.holder3_cross_mono` and whose SECOND `≤` is the
//! cubed AM-GM `27P²Q ≤ (2P+Q)³` (the residual the PARALLEL campaign proves; in
//! the design it is the explicit AM-GM leaf, named `h_amgm`). Plus the `27`/`(3X)³`
//! ring identities that the design (§11 rung 3-4) groups with that residual.
//!
//! # The honest split-hypothesis interface
//!
//! Rather than fabricate the `(3X)³ = 27X³` ring identities (subtraction-free
//! NNReal has no scalar `·`/numerals; these belong to the parallel CH3 tower per
//! design §11 rung 3-4), this module takes the two SPLIT inequalities — the genuine
//! AM-GM content of the cross-term — as EXPLICIT hypotheses (exactly as the
//! tensorization takes `h_tp`/`h_amgm`: honest named premises, NOT axioms). What
//! THIS module proves, axiom-free, is the genuine cube-Minkowski MERGE STRUCTURE:
//! given the two corner cube hyps `h1`/`h2` and the two split bounds, the
//! `(U₁+U₂)³` cube binomial is bounded term-for-term and the RHS reassembled by a
//! pure NNReal ring identity into `(S₁+S₂)²·(T₁+T₂)`.
//!
//! ```text
//!   NNReal.cube_minkowski_merge : ∀ U₁ S₁ T₁ U₂ S₂ T₂ : NNReal,
//!     -- h1 : U₁³ ≤ S₁²·T₁
//!     NNReal.le ((U₁·U₁)·U₁) ((S₁·S₁)·T₁) →
//!     -- h2 : U₂³ ≤ S₂²·T₂
//!     NNReal.le ((U₂·U₂)·U₂) ((S₂·S₂)·T₂) →
//!     -- h_splitA : 3U₁²U₂ ≤ 2·(S₁S₂T₁) + S₁²T₂
//!     NNReal.le (((U₁²U₂)+(U₁²U₂))+(U₁²U₂)) (((P+P)+Q)) →
//!     -- h_splitB : 3U₁U₂² ≤ 2·(S₁S₂T₂) + S₂²T₁
//!     NNReal.le (((U₁U₂²)+(U₁U₂²))+(U₁U₂²)) (((P'+P')+Q')) →
//!     NNReal.le (((U₁+U₂)·(U₁+U₂))·(U₁+U₂)) (((S₁+S₂)·(S₁+S₂))·(T₁+T₂))
//! ```
//!
//! with `U₁²U₂ := (U₁·U₁)·U₂`, `U₁U₂² := (U₁·U₂)·U₂`, `P := (S₁·S₂)·T₁`,
//! `Q := (S₁·S₁)·T₂`, `P' := (S₁·S₂)·T₂`, `Q' := (S₂·S₂)·T₁`, all left-nested.
//!
//! # Proof shape (axiom-free)
//!
//! 1. `NNReal.add_cube U₁ U₂` rewrites the LHS cube to
//!    `(U₁³ + 3U₁²U₂) + (3U₁U₂² + U₂³)`.
//! 2. `NNReal.add_le_add` (twice) bounds it by
//!    `(S₁²T₁ + (2P+Q)) + ((2P'+Q') + S₂²T₂)` using `h1`,`h_splitA`,`h_splitB`,`h2`.
//! 3. a pure NNReal ring identity `rhs_expand` shows
//!    `((S₁+S₂)·(S₁+S₂))·(T₁+T₂) = (S₁²T₁ + (2P+Q)) + ((2P'+Q') + S₂²T₂)`,
//!    along whose symm the bound is transported to the target RHS by `Eq.subst`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`. NO new axiom: the splits are honest hypotheses.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `NNReal.cube_minkowski_merge`.
struct MergeConsts {
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_add: Expr,
    nnreal_le: Expr,
    nnreal_add_le_add: Expr,
    nnreal_add_cube: Expr,
    nnreal_mul_add: Expr,
    nnreal_add_mul: Expr,
    nnreal_mul_comm: Expr,
    nnreal_mul_assoc: Expr,
    nnreal_add_comm: Expr,
    nnreal_add_assoc: Expr,
    eq_trans1: Expr,
    eq_symm1: Expr,
    eq_subst1: Expr,
    congr_arg11: Expr,
}

impl MergeConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_add: k("NNReal.add"),
            nnreal_le: k("NNReal.le"),
            nnreal_add_le_add: k("NNReal.add_le_add"),
            nnreal_add_cube: k("NNReal.add_cube"),
            nnreal_mul_add: k("NNReal.mul_add"),
            nnreal_add_mul: k("NNReal.add_mul"),
            nnreal_mul_comm: k("NNReal.mul_comm"),
            nnreal_mul_assoc: k("NNReal.mul_assoc"),
            nnreal_add_comm: k("NNReal.add_comm"),
            nnreal_add_assoc: k("NNReal.add_assoc"),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
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
    /// `(a·a)·a` (left-nested cube).
    fn cube(&self, a: &Expr) -> Expr {
        self.mul(&self.mul(a, a), a)
    }
    /// `(s·s)·t` (left-nested `s²·t`).
    fn sq_t(&self, s: &Expr, t: &Expr) -> Expr {
        self.mul(&self.mul(s, s), t)
    }
    /// `(x+x)+x` (the additive `3·x`).
    fn three(&self, x: &Expr) -> Expr {
        self.add(&self.add(x, x), x)
    }
    /// `(p+p)+q` (the `2p+q` split-RHS).
    fn two_plus(&self, p: &Expr, q: &Expr) -> Expr {
        self.add(&self.add(p, p), q)
    }
    fn eq(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [self.nnreal.clone(), a.clone(), b.clone()],
        )
    }

    // ── ring lemmas ──
    /// `NNReal.add_cube a b : ((a+b)·(a+b))·(a+b) = (a³+3a²b)+(3ab²+b³)`.
    fn add_cube(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add_cube.clone(), [a.clone(), b.clone()])
    }
    /// `NNReal.add_le_add a b c d hab hcd : add a c ≤ add b d`.
    #[allow(clippy::too_many_arguments)]
    fn add_le_add(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr, hab: Expr, hcd: Expr) -> Expr {
        Expr::apps(
            self.nnreal_add_le_add.clone(),
            [a.clone(), b.clone(), cc.clone(), d.clone(), hab, hcd],
        )
    }
    /// `NNReal.mul_add c a b : c·(a+b) = c·a + c·b`.
    fn mul_add(&self, cc: &Expr, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_mul_add.clone(),
            [cc.clone(), a.clone(), b.clone()],
        )
    }
    /// `NNReal.add_mul a b c : (a+b)·c = a·c + b·c`.
    fn add_mul(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_add_mul.clone(),
            [a.clone(), b.clone(), cc.clone()],
        )
    }
    /// `NNReal.mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul_comm.clone(), [a.clone(), b.clone()])
    }
    /// `NNReal.mul_assoc a b c : a·(b·c) = (a·b)·c`.
    fn mul_assoc(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_mul_assoc.clone(),
            [a.clone(), b.clone(), cc.clone()],
        )
    }
    /// `NNReal.add_comm a b : a+b = b+a`.
    fn add_comm(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add_comm.clone(), [a.clone(), b.clone()])
    }
    /// `NNReal.add_assoc a b c : (a+b)+c = a+(b+c)`.
    fn add_assoc(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_add_assoc.clone(),
            [a.clone(), b.clone(), cc.clone()],
        )
    }

    // ── Eq toolkit ──
    fn trans(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [
                self.nnreal.clone(),
                a.clone(),
                b.clone(),
                cc.clone(),
                h1,
                h2,
            ],
        )
    }
    fn symm(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_symm1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone(), h],
        )
    }
    /// `@Eq.subst NNReal motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.nnreal.clone(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }
    /// `congrArg NNReal NNReal from to f h : f from = f to`.
    fn congr_arg(&self, from: &Expr, to: &Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg11.clone(),
            [
                self.nnreal.clone(),
                self.nnreal.clone(),
                from.clone(),
                to.clone(),
                f,
                h,
            ],
        )
    }
    /// `congrArg (fun w => w + rhs) (h : a=b) : a+rhs = b+rhs`.
    fn cong_add_left(
        &self,
        parent: &EnvDeclBuilder,
        rhs: &Expr,
        a: &Expr,
        b: &Expr,
        h: Expr,
    ) -> Expr {
        let f = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = mb.fresh_local(self.nnreal.clone());
            let body = self.add(&w, rhs);
            mb.finish_child(mb.mk_lam(w_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.congr_arg(a, b, f, h)
    }
    /// `congrArg (fun w => lhs + w) (h : a=b) : lhs+a = lhs+b`.
    fn cong_add_right(
        &self,
        parent: &EnvDeclBuilder,
        lhs: &Expr,
        a: &Expr,
        b: &Expr,
        h: Expr,
    ) -> Expr {
        let f = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = mb.fresh_local(self.nnreal.clone());
            let body = self.add(lhs, &w);
            mb.finish_child(mb.mk_lam(w_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.congr_arg(a, b, f, h)
    }
    /// `congrArg (fun w => w · rhs) (h : a=b) : a·rhs = b·rhs`.
    fn cong_mul_left(
        &self,
        parent: &EnvDeclBuilder,
        rhs: &Expr,
        a: &Expr,
        b: &Expr,
        h: Expr,
    ) -> Expr {
        let f = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = mb.fresh_local(self.nnreal.clone());
            let body = self.mul(&w, rhs);
            mb.finish_child(mb.mk_lam(w_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.congr_arg(a, b, f, h)
    }
}

impl Environment {
    /// Register `NNReal.cube_minkowski_merge`. Idempotent; foundational-only.
    pub fn init_algebra_nnreal_cube_minkowski_merge(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_add_cube()?; // NNReal.add_cube + ring surface
        self.init_algebra_nnreal_le_add()?; // NNReal.add_le_add
        self.init_algebra_nnreal_mul_distrib()?; // NNReal.mul_add
        self.init_algebra_nnreal_add_mul()?; // NNReal.add_mul
        self.init_algebra_nnreal_reverse_square_algebra()?; // NNReal.mul_comm, mul_assoc
        self.init_algebra_nnreal_add_comm_assoc()?; // NNReal.add_comm, add_assoc
        self.init_eq()?;

        let c = MergeConsts::new();
        self.register_merge(&c)?;
        Ok(())
    }

    fn register_merge(&mut self, c: &MergeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.cube_minkowski_merge");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_merge(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

include!("algebra_nnreal_cube_minkowski_merge_proof.rs");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["NNReal.cube_minkowski_merge"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_cube_minkowski_merge()
            .expect("init_algebra_nnreal_cube_minkowski_merge");
        env.init_algebra_nnreal_cube_minkowski_merge()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_cube_minkowski_merge_kernel_check() {
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
    fn test_cube_minkowski_merge_constructive_empty_closure() {
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
