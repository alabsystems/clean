// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — FORWARD cube monotonicity on `NNReal`
//! (`a ≤ b → a³ ≤ b³`), built at the `NNReal` level from the landed
//! left-multiplication monotonicity `NNReal.mul_le_mul_left`, commutativity
//! `NNReal.mul_comm`, and transitivity `NNReal.le.trans`.
//!
//! # Why this module exists (the forward partner of the reflection)
//!
//! `algebra_nnreal_reverse_cube.rs` lands the REFLECTION `a³ ≤ b³ → a ≤ b`. The
//! `(4/3,4)` two-point base also needs the FORWARD direction: a lower bound
//! `S ≤ R` on the `pow43`-mean is raised to a lower bound `S³ ≤ R³` on the cube.
//! Since `NNReal` already has left-mul monotonicity and commutativity, the
//! forward two-sided product monotonicity and the cube follow by chaining — no
//! Cauchy-sequence core needed.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNReal.mul_le_mul : ∀ a b c d, NNReal.le a b → NNReal.le c d →
//!     NNReal.le (NNReal.mul a c) (NNReal.mul b d)`
//!   (two-sided product monotonicity: `a·c ≤ a·d ≤ b·d` via `mul_le_mul_left`
//!   on the right factor, then on the left factor through `mul_comm`).
//! - `NNReal.cube_le_cube_of_le : ∀ a b, NNReal.le a b →
//!     NNReal.le (NNReal.mul (NNReal.mul a a) a) (NNReal.mul (NNReal.mul b b) b)`
//!   (two `mul_le_mul`s: `a·a ≤ b·b`, then `(a·a)·a ≤ (b·b)·b`).
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles for forward cube monotonicity.
struct CubeMonoConsts {
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_le: Expr,
    nnreal_mul_comm: Expr,
    nnreal_mul_le_mul_left: Expr,
    nnreal_le_trans: Expr,
    eq1: Expr,
    eq_subst1: Expr,
}

impl CubeMonoConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_le: k("NNReal.le"),
            nnreal_mul_comm: k("NNReal.mul_comm"),
            nnreal_mul_le_mul_left: k("NNReal.mul_le_mul_left"),
            nnreal_le_trans: k("NNReal.le.trans"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1]),
        }
    }

    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn nncube(&self, a: &Expr) -> Expr {
        self.nnmul(&self.nnmul(a, a), a)
    }
    fn nnle(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a.clone(), b.clone()])
    }
    /// `NNReal.mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul_comm.clone(), [a.clone(), b.clone()])
    }
    /// `NNReal.mul_le_mul_left a c d (c≤d) : a·c ≤ a·d`.
    fn mul_le_mul_left(&self, a: &Expr, cc: &Expr, d: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.nnreal_mul_le_mul_left.clone(),
            [a.clone(), cc.clone(), d.clone(), h],
        )
    }
    /// `NNReal.le.trans a b c (a≤b)(b≤c) : a ≤ c`.
    fn le_trans(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.nnreal_le_trans.clone(),
            [a.clone(), b.clone(), cc.clone(), h1, h2],
        )
    }
    /// `@Eq.subst.{1} NNReal motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.nnreal.clone(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }
    /// `a·c ≤ b·c` (right-factor monotone) from `h : a ≤ b`, via `mul_comm` +
    /// `mul_le_mul_left` (fix the right factor `cc`, vary the left):
    ///   `c·a ≤ c·b` (mul_le_mul_left c a b h); transport `c·a → a·c` and
    ///   `c·b → b·c` along `mul_comm`.
    fn mul_le_mul_right(
        &self,
        parent: &EnvDeclBuilder,
        a: &Expr,
        b: &Expr,
        cc: &Expr,
        h: Expr,
    ) -> Expr {
        // base : c·a ≤ c·b.
        let base = self.mul_le_mul_left(cc, a, b, h);
        let ca = self.nnmul(cc, a);
        let cb = self.nnmul(cc, b);
        let ac = self.nnmul(a, cc);
        let bc = self.nnmul(b, cc);
        // step1 : a·c ≤ c·b  (transport c·a → a·c in the LHS along mul_comm c a).
        let comm_ca = self.mul_comm(cc, a); // c·a = a·c
        let motive1 = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = m.fresh_local(self.nnreal.clone());
            let body = self.nnle(&t, &cb);
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        let step1 = self.subst(motive1, &ca, &ac, comm_ca, base); // a·c ≤ c·b
                                                                  // step2 : a·c ≤ b·c  (transport c·b → b·c in the RHS along mul_comm c b).
        let comm_cb = self.mul_comm(cc, b); // c·b = b·c
        let motive2 = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = m.fresh_local(self.nnreal.clone());
            let body = self.nnle(&ac, &t);
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.subst(motive2, &cb, &bc, comm_cb, step1) // a·c ≤ b·c
    }
    /// `a·c ≤ b·d` (two-sided) from `hab : a≤b`, `hcd : c≤d`:
    ///   `a·c ≤ a·d` (mul_le_mul_left a c d hcd), `a·d ≤ b·d` (mul_le_mul_right
    ///   a b d hab); chain via `le.trans`.
    fn mul_le_mul(
        &self,
        parent: &EnvDeclBuilder,
        a: &Expr,
        b: &Expr,
        cc: &Expr,
        d: &Expr,
        hab: Expr,
        hcd: Expr,
    ) -> Expr {
        let ac = self.nnmul(a, cc);
        let ad = self.nnmul(a, d);
        let bd = self.nnmul(b, d);
        let s1 = self.mul_le_mul_left(a, cc, d, hcd); // a·c ≤ a·d
        let s2 = self.mul_le_mul_right(parent, a, b, d, hab); // a·d ≤ b·d
        self.le_trans(&ac, &ad, &bd, s1, s2)
    }
}

impl Environment {
    /// Register `NNReal.mul_le_mul` and `NNReal.cube_le_cube_of_le`. Idempotent.
    pub fn init_algebra_nnreal_cube_mono(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_le()?; // NNReal.le, NNReal.le.trans
        self.init_algebra_nnreal_reverse_square_mono()?; // NNReal.mul_le_mul_left
        self.init_algebra_nnreal_reverse_square_algebra()?; // NNReal.mul_comm
        self.init_eq()?;

        let c = CubeMonoConsts::new();
        self.register_nnreal_mul_le_mul(&c)?;
        self.register_nnreal_cube_le_cube_of_le(&c)?;
        Ok(())
    }

    /// `NNReal.mul_le_mul : ∀ a b c d, a≤b → c≤d → a·c ≤ b·d`.
    fn register_nnreal_mul_le_mul(&mut self, c: &CubeMonoConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.mul_le_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.nnreal.clone());
            let (bv_id, bv) = b.fresh_local(c.nnreal.clone());
            let (cv_id, cv) = b.fresh_local(c.nnreal.clone());
            let (dv_id, dv) = b.fresh_local(c.nnreal.clone());
            let hab_ty = c.nnle(&a, &bv);
            let (hab_id, _) = b.fresh_local(hab_ty.clone());
            let hcd_ty = c.nnle(&cv, &dv);
            let (hcd_id, _) = b.fresh_local(hcd_ty.clone());
            let concl = c.nnle(&c.nnmul(&a, &cv), &c.nnmul(&bv, &dv));
            let e = b.mk_pi(hcd_id, BinderInfo::Default, hcd_ty, concl);
            let e = b.mk_pi(hab_id, BinderInfo::Default, hab_ty, e);
            let e = b.mk_pi(dv_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(cv_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nnreal.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.nnreal.clone());
            let (bv_id, bv) = b.fresh_local(c.nnreal.clone());
            let (cv_id, cv) = b.fresh_local(c.nnreal.clone());
            let (dv_id, dv) = b.fresh_local(c.nnreal.clone());
            let hab_ty = c.nnle(&a, &bv);
            let (hab_id, hab) = b.fresh_local(hab_ty.clone());
            let hcd_ty = c.nnle(&cv, &dv);
            let (hcd_id, hcd) = b.fresh_local(hcd_ty.clone());
            let body = c.mul_le_mul(&b, &a, &bv, &cv, &dv, hab, hcd);
            let e = b.mk_lam(hcd_id, BinderInfo::Default, hcd_ty, body);
            let e = b.mk_lam(hab_id, BinderInfo::Default, hab_ty, e);
            let e = b.mk_lam(dv_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_lam(cv_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.nnreal.clone(), e);
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

    /// `NNReal.cube_le_cube_of_le : ∀ a b, a≤b → (a·a)·a ≤ (b·b)·b`.
    fn register_nnreal_cube_le_cube_of_le(&mut self, c: &CubeMonoConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.cube_le_cube_of_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let mul_le_mul = Expr::const_(Name::from_string("NNReal.mul_le_mul"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.nnreal.clone());
            let (bv_id, bv) = b.fresh_local(c.nnreal.clone());
            let hab_ty = c.nnle(&a, &bv);
            let (hab_id, _) = b.fresh_local(hab_ty.clone());
            let concl = c.nnle(&c.nncube(&a), &c.nncube(&bv));
            let e = b.mk_pi(hab_id, BinderInfo::Default, hab_ty, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nnreal.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.nnreal.clone());
            let (bv_id, bv) = b.fresh_local(c.nnreal.clone());
            let hab_ty = c.nnle(&a, &bv);
            let (hab_id, hab) = b.fresh_local(hab_ty.clone());
            // sq_le : a·a ≤ b·b := mul_le_mul a b a b hab hab.
            let sq_le = Expr::apps(
                mul_le_mul.clone(),
                [
                    a.clone(),
                    bv.clone(),
                    a.clone(),
                    bv.clone(),
                    hab.clone(),
                    hab.clone(),
                ],
            );
            // cube_le : (a·a)·a ≤ (b·b)·b := mul_le_mul (a·a)(b·b) a b sq_le hab.
            let aa = c.nnmul(&a, &a);
            let bb = c.nnmul(&bv, &bv);
            let body = Expr::apps(mul_le_mul, [aa, bb, a.clone(), bv.clone(), sq_le, hab]);
            let e = b.mk_lam(hab_id, BinderInfo::Default, hab_ty, body);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.nnreal.clone(), e);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["NNReal.mul_le_mul", "NNReal.cube_le_cube_of_le"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_cube_mono()
            .expect("init_algebra_nnreal_cube_mono");
        env.init_algebra_nnreal_cube_mono().expect("idempotent");
        env
    }

    #[test]
    fn test_cube_mono_kernel_check() {
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
    fn test_cube_mono_constructive_empty_closure() {
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
