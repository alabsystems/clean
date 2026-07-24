// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — `NNReal.cube_holder3_base`, the `m=1` base case of the
//! cubed cube-Hölder inequality `(Σ A²B)³ ≤ (Σ A³)²·(Σ B³)` (CH3).
//!
//! # Why this module exists (the sqrt-free dual tensorization's hard rung)
//!
//! The design `2026-06-20-hc43-dual-tensorization-cross-term.md` (and the
//! `NNReal.add_sq` note) pin the SQRT-FREE dual `(4/3,4)` HC route: it closes the
//! cube-Minkowski finSum step via the cubed cube-Hölder
//! ```text
//!   CH3 :  (Σ_i (A i · A i)·(B i))³  ≤  (Σ_i (A i)³)²·(Σ_i (B i)³)
//! ```
//! plus the LANDED `NNReal.le_of_cube_le_cube` — never taking a root of a finSum.
//! CH3 is proven by INDUCTION on the number of terms `m`, with the superadditive
//! merge `U₁³≤S₁²T₁ ∧ U₂³≤S₂²T₂ → (U₁+U₂)³ ≤ (S₁+S₂)²(T₁+T₂)`. The base case of
//! that induction is the `m=1` (single-term) statement, which is an EQUALITY:
//! ```text
//!   ((A·A)·B)³  =  ((A·A)·A)²·((B·B)·B)         (both sides are A⁶·B³).
//! ```
//! With `U := (A·A)·B`, `S := (A·A)·A`, `T := (B·B)·B`: `U³ = A⁶B³ = S²·T`. The
//! base case of CH3 (`U³ ≤ S²T` at `m=1`) follows from this equality by
//! `NNReal.le.refl` + transport.
//!
//! # The brick (axiom-free, kernel-checked, EQUALITY — no AM-GM, no root)
//!
//! ```text
//!   NNReal.cube_holder3_base : ∀ A B : NNReal,
//!     NNReal.mul (NNReal.mul (NNReal.mul (NNReal.mul A A) B)
//!                            (NNReal.mul (NNReal.mul A A) B))
//!                (NNReal.mul (NNReal.mul A A) B)
//!       = NNReal.mul (NNReal.mul (NNReal.mul (NNReal.mul A A) A)
//!                                (NNReal.mul (NNReal.mul A A) A))
//!                    (NNReal.mul (NNReal.mul B B) B)
//! ```
//!
//! i.e. `((A·A)·B)³ = ((A·A)·A)²·((B·B)·B)`, cubes/squares left-nested as `(a·a)·a`
//! to match `NNReal.le_of_cube_le_cube` / `NNReal.cube_superadd`.
//!
//! # Proof shape (axiom-free, identity-only — pure `mul_mul_mul_comm` interchange)
//!
//! Both sides reduce to the common normal form
//! `NF := (((A·A)·(A·A))·(A·A))·((B·B)·B)` (= `A⁶·B³`) using ONLY the landed
//! interchange `NNReal.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`:
//!
//! - LHS `((A·A)·B)³` → `NF` (two interchanges):
//!   `((A·A)·B)·((A·A)·B) = ((A·A)·(A·A))·(B·B)` [`mmc (A·A) B (A·A) B`], then
//!   `(((A·A)·(A·A))·(B·B))·((A·A)·B) = (((A·A)·(A·A))·(A·A))·((B·B)·B)`
//!   [`mmc ((A·A)·(A·A)) (B·B) (A·A) B`].
//! - RHS `((A·A)·A)²·((B·B)·B)` → `NF` (one interchange):
//!   `((A·A)·A)·((A·A)·A) = ((A·A)·(A·A))·(A·A)` [`mmc (A·A) A (A·A) A`], so
//!   `S² = ((A·A)·(A·A))·(A·A)` and `S²·((B·B)·B) = NF`.
//!
//! Chain `LHS = NF = RHS` via `Eq.trans` + `Eq.symm`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `NNReal.cube_holder3_base`.
struct CubeHolder3BaseConsts {
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_mmm_comm: Expr,
    eq1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
}

impl CubeHolder3BaseConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_mmm_comm: k("NNReal.mul_mul_mul_comm"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1]),
        }
    }

    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn eq(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.eq1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone()],
        )
    }
    /// `NNReal.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmc(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_mmm_comm.clone(),
            [a.clone(), b.clone(), cc.clone(), d.clone()],
        )
    }
    /// `@Eq.symm NNReal a b h : Eq NNReal b a`.
    fn symm(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_symm1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone(), h],
        )
    }
    /// `@Eq.trans NNReal a b c hab hbc : Eq NNReal a c`.
    fn trans(&self, a: &Expr, b: &Expr, cc: &Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [
                self.nnreal.clone(),
                a.clone(),
                b.clone(),
                cc.clone(),
                hab,
                hbc,
            ],
        )
    }
    /// `congrArg (fun t => mul t fixed) h : mul a fixed = mul b fixed` for `h:a=b`.
    fn cong_left(
        &self,
        parent: &EnvDeclBuilder,
        fixed: &Expr,
        a: &Expr,
        b: &Expr,
        h: Expr,
    ) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(self.nnreal.clone());
            let body = self.nnmul(&w, fixed);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        let l1 = Level::succ(Level::zero());
        Expr::apps(
            Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
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
}

impl Environment {
    /// Register `NNReal.cube_holder3_base`. Idempotent; foundational-only closure.
    ///
    /// Depends only on the landed interchange `NNReal.mul_mul_mul_comm`
    /// (`pow43_cubed`) plus the `Eq` surface. No axiom is added or removed.
    pub fn init_algebra_nnreal_cube_holder3_base(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_pow43_cubed()?; // NNReal.mul_mul_mul_comm
        self.init_eq()?;

        let c = CubeHolder3BaseConsts::new();
        self.register_cube_holder3_base(&c)?;
        Ok(())
    }

    fn register_cube_holder3_base(&mut self, c: &CubeHolder3BaseConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.cube_holder3_base");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.nnreal.clone());
            let (bv_id, bv) = b.fresh_local(c.nnreal.clone());
            let (lhs, rhs) = base_lhs_rhs(c, &a, &bv);
            let concl = c.eq(&lhs, &rhs);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.nnreal.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nnreal.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.nnreal.clone());
            let (bv_id, bv) = b.fresh_local(c.nnreal.clone());
            let body = build_base_body(c, &b, &a, &bv);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.nnreal.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.nnreal.clone(), e);
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

/// The LHS `((A·A)·B)³` and RHS `((A·A)·A)²·((B·B)·B)` (left-nested).
fn base_lhs_rhs(c: &CubeHolder3BaseConsts, a: &Expr, bv: &Expr) -> (Expr, Expr) {
    let a2 = c.nnmul(a, a); // A·A
    let w = c.nnmul(&a2, bv); // (A·A)·B           = U
    let lhs = c.nnmul(&c.nnmul(&w, &w), &w); // ((A·A)·B)³

    let s = c.nnmul(&a2, a); // (A·A)·A           = S
    let s2 = c.nnmul(&s, &s); // S²
    let b3 = c.nnmul(&c.nnmul(bv, bv), bv); // (B·B)·B = T
    let rhs = c.nnmul(&s2, &b3); // S²·T
    (lhs, rhs)
}

/// Proof body `((A·A)·B)³ = ((A·A)·A)²·((B·B)·B)`.
///
/// Both sides reduce to `NF := (((A·A)·(A·A))·(A·A))·((B·B)·B)` via
/// `NNReal.mul_mul_mul_comm`. Then `LHS = NF = RHS`.
fn build_base_body(c: &CubeHolder3BaseConsts, b: &EnvDeclBuilder, a: &Expr, bv: &Expr) -> Expr {
    let a2 = c.nnmul(a, a); // A·A
    let a4 = c.nnmul(&a2, &a2); // (A·A)·(A·A)
    let a6 = c.nnmul(&a4, &a2); // ((A·A)·(A·A))·(A·A)
    let b2 = c.nnmul(bv, bv); // B·B
    let b3 = c.nnmul(&b2, bv); // (B·B)·B
    let nf = c.nnmul(&a6, &b3); // common normal form A⁶·B³

    // ── LHS = ((A·A)·B)³ → NF.
    let w = c.nnmul(&a2, bv); // (A·A)·B
    let ww = c.nnmul(&w, &w); // W·W
    let www = c.nnmul(&ww, &w); // (W·W)·W   = LHS

    // l1 : W·W = (A·A)·B · (A·A)·B = ((A·A)·(A·A))·(B·B)   [mmc (A·A) B (A·A) B].
    let a4_b2 = c.nnmul(&a4, &b2); // ((A·A)·(A·A))·(B·B)
    let l1 = c.mmc(&a2, bv, &a2, bv);
    // lift under (· · W): (W·W)·W = (((A·A)·(A·A))·(B·B))·W   [cong_left W].
    let a4b2_w = c.nnmul(&a4_b2, &w);
    let l1_lift = c.cong_left(b, &w, &ww, &a4_b2, l1);
    // l2 : (((A·A)·(A·A))·(B·B))·((A·A)·B)
    //        = (((A·A)·(A·A))·(A·A))·((B·B)·B)   [mmc ((A·A)·(A·A)) (B·B) (A·A) B].
    let l2 = c.mmc(&a4, &b2, &a2, bv);
    // chain: www = a4b2_w = nf.
    let lhs_chain = c.trans(&www, &a4b2_w, &nf, l1_lift, l2);

    // ── RHS = ((A·A)·A)²·((B·B)·B) → NF.
    let s = c.nnmul(&a2, a); // (A·A)·A
    let s2 = c.nnmul(&s, &s); // S²
    let rhs = c.nnmul(&s2, &b3); // S²·((B·B)·B) = RHS

    // r1 : S·S = ((A·A)·A)·((A·A)·A) = ((A·A)·(A·A))·(A·A)   [mmc (A·A) A (A·A) A] = a6.
    let r1 = c.mmc(&a2, a, &a2, a);
    // lift under (· · ((B·B)·B)): S²·((B·B)·B) = a6·((B·B)·B) = NF   [cong_left ((B·B)·B)].
    let rhs_chain = c.cong_left(b, &b3, &s2, &a6, r1);
    // rhs_chain : RHS = NF.

    // LHS = NF, RHS = NF  ⟹  LHS = RHS via trans (lhs_chain) (symm rhs_chain).
    let nf_eq_rhs = c.symm(&rhs, &nf, rhs_chain);
    c.trans(&www, &nf, &rhs, lhs_chain, nf_eq_rhs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_cube_holder3_base()
            .expect("init_algebra_nnreal_cube_holder3_base");
        env.init_algebra_nnreal_cube_holder3_base()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_cube_holder3_base_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("NNReal.cube_holder3_base");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("NNReal.cube_holder3_base must kernel-check: {e:?}"));
    }

    #[test]
    fn test_cube_holder3_base_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("NNReal.cube_holder3_base");
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
