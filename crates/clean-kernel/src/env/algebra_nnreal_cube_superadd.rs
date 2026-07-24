// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — `NNReal.cube_superadd` (`u³ + v³ ≤ (u+v)³`): the CUBE
//! super-additivity, the rational dual of the `(2,4)` `hc24Assemble` for the
//! `(4/3,4)` dual-HC tensorization's two IH cube-RHS corners.
//!
//! # Why this module exists (the dual cross-term assembly)
//!
//! The `(4/3,4)` dual-HC tensorization step (design
//! `2026-06-20-hc43-dual-tensorization-cross-term.md`) must fold the two IH
//! cube-RHS objects `NG³ := (norm43_n gPart)³` and `NH³ := (norm43_n hPart)³`
//! into the single `(NG+NH)³` shape. The RATIONAL part of that assembly is the
//! cube super-additivity `u³+v³ ≤ (u+v)³` (the dual of the `(2,4)` SQUARE
//! assembly `hc24Assemble`, where the IH RHS was a square). It does NOT discharge
//! the cross-term `R`-bound (which needs an irrational `^{3/2}` of an NNReal — the
//! named wall), but it is the clean rational scaffolding the dual chain needs.
//!
//! # The brick (axiom-free, kernel-checked)
//!
//! ```text
//!   NNReal.cube_superadd : ∀ u v : NNReal,
//!     NNReal.le (NNReal.add (NNReal.mul (NNReal.mul u u) u)
//!                           (NNReal.mul (NNReal.mul v v) v))
//!               (NNReal.mul (NNReal.mul (NNReal.add u v) (NNReal.add u v))
//!                           (NNReal.add u v))
//! ```
//!
//! i.e. `u³ + v³ ≤ (u+v)³` (cubes left-nested as `(a·a)·a`, matching
//! `NNReal.cube_le_cube_of_le`).
//!
//! # Proof shape (axiom-free, identity-free — the clean monotone route)
//!
//! Let `s := u+v`, `s² := s·s`. The cube `s³ = (s²)·s = (s²)·(u+v)` splits by
//! left-distributivity (`NNReal.mul_add s² u v`) into `(s²·u) + (s²·v)`. Each
//! corner dominates the matching cube:
//!   * `u ≤ s` (`NNReal.le_self_add u v`), so `u·u ≤ s·s`
//!     (`NNReal.mul_le_mul u s u s …`), so `(u·u)·u ≤ (s²)·u`
//!     (`NNReal.mul_le_mul (u·u) s² u u …`).
//!   * `v ≤ s` (`NNReal.le_self_add v u : v ≤ v+u` transported along
//!     `NNReal.add_comm v u : v+u = u+v`), so `(v·v)·v ≤ (s²)·v`.
//!
//! Then `NNReal.add_le_add` gives `u³+v³ ≤ (s²·u)+(s²·v)`, and a final `Eq.subst`
//! along `NNReal.mul_add s² u v` rewrites the RHS to `(s²)·s = s³`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `NNReal.cube_superadd`.
struct CubeSuperaddConsts {
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_add: Expr,
    nnreal_le: Expr,
    nnreal_le_refl: Expr,
    nnreal_mul_le_mul: Expr,
    nnreal_add_le_add: Expr,
    nnreal_le_self_add: Expr,
    nnreal_mul_add: Expr,
    nnreal_add_comm: Expr,
    eq_symm1: Expr,
    eq_subst1: Expr,
}

impl CubeSuperaddConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_add: k("NNReal.add"),
            nnreal_le: k("NNReal.le"),
            nnreal_le_refl: k("NNReal.le.refl"),
            nnreal_mul_le_mul: k("NNReal.mul_le_mul"),
            nnreal_add_le_add: k("NNReal.add_le_add"),
            nnreal_le_self_add: k("NNReal.le_self_add"),
            nnreal_mul_add: k("NNReal.mul_add"),
            nnreal_add_comm: k("NNReal.add_comm"),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1]),
        }
    }

    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn nnadd(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a.clone(), b.clone()])
    }
    /// `mul (mul a a) a` (left-nested cube).
    fn nncube(&self, a: &Expr) -> Expr {
        self.nnmul(&self.nnmul(a, a), a)
    }
    fn nnle(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a.clone(), b.clone()])
    }
    /// `NNReal.le.refl a : NNReal.le a a`.
    fn le_refl(&self, a: &Expr) -> Expr {
        Expr::app(self.nnreal_le_refl.clone(), a.clone())
    }
    /// `NNReal.mul_le_mul a b c d hab hcd : mul a c ≤ mul b d`.
    #[allow(clippy::too_many_arguments)]
    fn mul_le_mul(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr, hab: Expr, hcd: Expr) -> Expr {
        Expr::apps(
            self.nnreal_mul_le_mul.clone(),
            [a.clone(), b.clone(), cc.clone(), d.clone(), hab, hcd],
        )
    }
    /// `NNReal.add_le_add a b c d hab hcd : add a c ≤ add b d`.
    #[allow(clippy::too_many_arguments)]
    fn add_le_add(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr, hab: Expr, hcd: Expr) -> Expr {
        Expr::apps(
            self.nnreal_add_le_add.clone(),
            [a.clone(), b.clone(), cc.clone(), d.clone(), hab, hcd],
        )
    }
    /// `NNReal.le_self_add a b : NNReal.le a (add a b)`.
    fn le_self_add(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_le_self_add.clone(), [a.clone(), b.clone()])
    }
    /// `NNReal.mul_add c a b : mul c (add a b) = add (mul c a)(mul c b)`.
    fn mul_add(&self, cc: &Expr, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_mul_add.clone(),
            [cc.clone(), a.clone(), b.clone()],
        )
    }
    /// `NNReal.add_comm a b : add a b = add b a`.
    fn add_comm(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add_comm.clone(), [a.clone(), b.clone()])
    }
    /// `@Eq.symm NNReal a b h : Eq NNReal b a`.
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
}

impl Environment {
    /// Register `NNReal.cube_superadd`. Idempotent; foundational-only closure.
    pub fn init_algebra_nnreal_cube_superadd(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_le_self_add()?; // NNReal.le_self_add
        self.init_algebra_nnreal_cube_mono()?; // NNReal.mul_le_mul
        self.init_algebra_nnreal_le_add()?; // NNReal.add_le_add
        self.init_algebra_nnreal_le()?; // NNReal.le.refl
        self.init_algebra_nnreal_mul_distrib()?; // NNReal.mul_add
        self.init_algebra_nnreal_add_comm_assoc()?; // NNReal.add_comm
        self.init_eq()?;

        let c = CubeSuperaddConsts::new();
        self.register_cube_superadd(&c)?;
        Ok(())
    }

    fn register_cube_superadd(&mut self, c: &CubeSuperaddConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.cube_superadd");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (u_id, u) = b.fresh_local(c.nnreal.clone());
            let (v_id, v) = b.fresh_local(c.nnreal.clone());
            let lhs = c.nnadd(&c.nncube(&u), &c.nncube(&v));
            let s = c.nnadd(&u, &v);
            let rhs = c.nncube(&s);
            let concl = c.nnle(&lhs, &rhs);
            let e = b.mk_pi(v_id, BinderInfo::Default, c.nnreal.clone(), concl);
            let e = b.mk_pi(u_id, BinderInfo::Default, c.nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_cube_superadd_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// The `NNReal.cube_superadd` proof term.
fn build_cube_superadd_value(c: &CubeSuperaddConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (u_id, u) = b.fresh_local(c.nnreal.clone());
    let (v_id, v) = b.fresh_local(c.nnreal.clone());

    let s = c.nnadd(&u, &v); // s = u+v
    let s2 = c.nnmul(&s, &s); // s² = s·s

    // hus : u ≤ s = u+v   (le_self_add u v).
    let hus = c.le_self_add(&u, &v);
    // hvs : v ≤ s = u+v   (le_self_add v u : v ≤ v+u, transported v+u → u+v via add_comm).
    let v_u = c.nnadd(&v, &u); // v+u
    let hvs_raw = c.le_self_add(&v, &u); // v ≤ v+u
    let motive_vs = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.nnreal.clone());
        let body = c.nnle(&v, &t);
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let hvs = c.subst(motive_vs, &v_u, &s, c.add_comm(&v, &u), hvs_raw); // v ≤ u+v

    // huu_ss : u·u ≤ s·s   (mul_le_mul u s u s hus hus).
    let huu_ss = c.mul_le_mul(&u, &s, &u, &s, hus.clone(), hus.clone());
    // cube_u_le : (u·u)·u ≤ (s·s)·u   (mul_le_mul (u·u) (s·s) u u huu_ss (le.refl u)).
    let uu = c.nnmul(&u, &u);
    let cube_u_le = c.mul_le_mul(&uu, &s2, &u, &u, huu_ss, c.le_refl(&u));
    let s2_u = c.nnmul(&s2, &u); // (s·s)·u

    // hvv_ss : v·v ≤ s·s   (mul_le_mul v s v s hvs hvs).
    let hvv_ss = c.mul_le_mul(&v, &s, &v, &s, hvs.clone(), hvs);
    // cube_v_le : (v·v)·v ≤ (s·s)·v.
    let vv = c.nnmul(&v, &v);
    let cube_v_le = c.mul_le_mul(&vv, &s2, &v, &v, hvv_ss, c.le_refl(&v));
    let s2_v = c.nnmul(&s2, &v); // (s·s)·v

    // sum_le : (u³ + v³) ≤ ((s²·u) + (s²·v))   (add_le_add … cube_u_le cube_v_le).
    let cube_u = c.nncube(&u);
    let cube_v = c.nncube(&v);
    let sum_le = c.add_le_add(&cube_u, &s2_u, &cube_v, &s2_v, cube_u_le, cube_v_le);
    let rhs_split = c.nnadd(&s2_u, &s2_v); // (s²·u)+(s²·v)

    // split : (s²)·(u+v) = (s²·u)+(s²·v)   (mul_add s² u v).  Note (s²)·(u+v) = (s²)·s = s³.
    let split = c.mul_add(&s2, &u, &v);
    let cube_s = c.nnmul(&s2, &s); // (s·s)·s = (s²)·(u+v) defeq

    // FINAL : (u³+v³) ≤ s³, transporting the RHS (s²·u)+(s²·v) → (s²)·s along symm split.
    let lhs = c.nnadd(&cube_u, &cube_v);
    let motive_fin = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = mb.fresh_local(c.nnreal.clone());
        let body = c.nnle(&lhs, &t);
        mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let proof = c.subst(
        motive_fin,
        &rhs_split,
        &cube_s,
        c.symm(&cube_s, &rhs_split, split),
        sum_le,
    );

    let e = b.mk_lam(v_id, BinderInfo::Default, c.nnreal.clone(), proof);
    let e = b.mk_lam(u_id, BinderInfo::Default, c.nnreal.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["NNReal.cube_superadd"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_cube_superadd()
            .expect("init_algebra_nnreal_cube_superadd");
        env.init_algebra_nnreal_cube_superadd().expect("idempotent");
        env
    }

    #[test]
    fn test_cube_superadd_kernel_check() {
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
    fn test_cube_superadd_constructive_empty_closure() {
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
