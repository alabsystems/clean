// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — RIGHT-distributivity `NNReal.add_mul`, derived (NO new
//! `Quot.sound`) from the landed `NNReal.mul_add` + `NNReal.mul_comm`.
//!
//! # Why this module exists (Step A1 of the dual `(4/3,4)` two-point base)
//!
//! The two-point-base RHS cube `(½·(α+β))³` expands through a binomial cube
//! identity `(u+v)³ = u³ + 3u²v + 3uv² + v³` over `NNReal`. The forward
//! (left-)distributivity `NNReal.mul_add` is landed; the cube also needs the
//! RIGHT distributivity `(a+b)·c = a·c + b·c`. That is a PURE DERIVATION from
//! `mul_add` and `mul_comm` — no carrier `Quot.sound` is required:
//!
//! ```text
//!   (a+b)·c = c·(a+b)            [mul_comm (a+b) c]
//!           = c·a + c·b          [mul_add c a b]
//!           = a·c + c·b          [cong_left  (mul_comm c a)]
//!           = a·c + b·c          [cong_right (mul_comm c b)]
//! ```
//!
//! - `NNReal.add_mul : ∀ a b c : NNReal,
//!     NNReal.mul (NNReal.add a b) c = NNReal.add (NNReal.mul a c)(NNReal.mul b c)`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only — its leaves `mul_add`/`mul_comm` are themselves
//! constructive `Quot.sound`s). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.
//!
//! # Scaffolding status of the full `NNReal.cube_of_sum` (HONEST)
//!
//! `add_mul` is the part of A1 that closes axiom-free with the CURRENT carrier.
//! The COLLECTED cube `(u+v)³ = u³ + 3u²v + 3uv² + v³` additionally needs
//! `NNReal.add_comm` and `NNReal.add_assoc` (to gather the three `u²v` and three
//! `uv²` cross-monomials into the `3·` coefficients). Those are NOT yet on the
//! carrier and — like `mul_add` — each is a triple `Quot.ind` + `Quot.sound` on a
//! pointwise-equal `CauSeq.Equiv` (over `NNRat.add_comm`/`add_assoc`, which are
//! themselves unbuilt). That is the remaining A1 sub-build; it is reported, NOT
//! admitted.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached carrier atoms + congruence smart-constructors for `add_mul`.
struct AddMulConsts {
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_add: Expr,
    nnreal_mul_add: Expr,
    nnreal_mul_comm: Expr,
    eq1: Expr,
    eq_trans1: Expr,
    congr_arg: Expr,
}

impl AddMulConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let kl = |s: &str| Expr::const_(Name::from_string(s), vec![l1.clone()]);
        Self {
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_add: k("NNReal.add"),
            nnreal_mul_add: k("NNReal.mul_add"),
            nnreal_mul_comm: k("NNReal.mul_comm"),
            eq1: kl("Eq"),
            eq_trans1: kl("Eq.trans"),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn mul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn add(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a.clone(), b.clone()])
    }
    fn eq_nn(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.eq1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone()],
        )
    }
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
    /// `NNReal.mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul_comm.clone(), [a.clone(), b.clone()])
    }
    /// `NNReal.mul_add c a b : c·(a+b) = c·a + c·b`.
    fn mul_add(&self, c: &Expr, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_mul_add.clone(),
            [c.clone(), a.clone(), b.clone()],
        )
    }
    /// `congrArg (fun w => w + fixed) h : x + fixed = y + fixed`.
    fn cong_add_left(
        &self,
        parent: &EnvDeclBuilder,
        fixed: &Expr,
        x: &Expr,
        y: &Expr,
        h: Expr,
    ) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(self.nnreal.clone());
            let body = self.add(&w, fixed);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        Expr::apps(
            self.congr_arg.clone(),
            [
                self.nnreal.clone(),
                self.nnreal.clone(),
                x.clone(),
                y.clone(),
                f,
                h,
            ],
        )
    }
    /// `congrArg (fun w => fixed + w) h : fixed + x = fixed + y`.
    fn cong_add_right(
        &self,
        parent: &EnvDeclBuilder,
        fixed: &Expr,
        x: &Expr,
        y: &Expr,
        h: Expr,
    ) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(self.nnreal.clone());
            let body = self.add(fixed, &w);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        Expr::apps(
            self.congr_arg.clone(),
            [
                self.nnreal.clone(),
                self.nnreal.clone(),
                x.clone(),
                y.clone(),
                f,
                h,
            ],
        )
    }
}

impl Environment {
    /// Register `NNReal.add_mul` (right-distributivity). Reuses the landed
    /// `NNReal.mul_add` and `NNReal.mul_comm`. Idempotent; foundational-only
    /// closure.
    pub fn init_algebra_nnreal_add_mul(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_mul_distrib()?; // NNReal.mul_add (+ NNReal.add/mul)
        self.init_algebra_nnreal_reverse_square_algebra()?; // NNReal.mul_comm
        self.init_eq()?;

        let c = AddMulConsts::new();
        self.register_nnreal_add_mul(&c)?;
        Ok(())
    }

    /// `NNReal.add_mul : ∀ a b c, (a+b)·c = a·c + b·c`.
    fn register_nnreal_add_mul(&mut self, c: &AddMulConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.add_mul");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.nnreal.clone());
            let (bv_id, bv) = b.fresh_local(c.nnreal.clone());
            let (cv_id, cv) = b.fresh_local(c.nnreal.clone());
            let lhs = c.mul(&c.add(&a, &bv), &cv);
            let rhs = c.add(&c.mul(&a, &cv), &c.mul(&bv, &cv));
            let concl = c.eq_nn(&lhs, &rhs);
            let e = b.mk_pi(cv_id, BinderInfo::Default, c.nnreal.clone(), concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_add_mul_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `(a+b)·c = a·c + b·c`:
///   `(a+b)·c =[mul_comm] c·(a+b) =[mul_add] c·a + c·b
///           =[cong_left (mul_comm c a)] a·c + c·b
///           =[cong_right (mul_comm c b)] a·c + b·c`.
fn build_add_mul_value(c: &AddMulConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nnreal.clone());
    let (bv_id, bv) = b.fresh_local(c.nnreal.clone());
    let (cv_id, cv) = b.fresh_local(c.nnreal.clone());

    let apb = c.add(&a, &bv);
    let lhs = c.mul(&apb, &cv); // (a+b)·c
    let c_apb = c.mul(&cv, &apb); // c·(a+b)
    let ca = c.mul(&cv, &a); // c·a
    let cb = c.mul(&cv, &bv); // c·b
    let ca_cb = c.add(&ca, &cb); // c·a + c·b
    let ac = c.mul(&a, &cv); // a·c
    let bc = c.mul(&bv, &cv); // b·c
    let ac_cb = c.add(&ac, &cb); // a·c + c·b
    let ac_bc = c.add(&ac, &bc); // a·c + b·c

    // step1 : (a+b)·c = c·(a+b)   [mul_comm (a+b) c]
    let s1 = c.mul_comm(&apb, &cv);
    // step2 : c·(a+b) = c·a + c·b   [mul_add c a b]
    let s2 = c.mul_add(&cv, &a, &bv);
    // step3 : c·a + c·b = a·c + c·b   [cong_left (mul_comm c a)]
    let comm_ca = c.mul_comm(&cv, &a); // c·a = a·c
    let s3 = c.cong_add_left(&b, &cb, &ca, &ac, comm_ca);
    // step4 : a·c + c·b = a·c + b·c   [cong_right (mul_comm c b)]
    let comm_cb = c.mul_comm(&cv, &bv); // c·b = b·c
    let s4 = c.cong_add_right(&b, &ac, &cb, &bc, comm_cb);

    // chain.
    let t = c.trans(&lhs, &c_apb, &ca_cb, s1, s2);
    let t = c.trans(&lhs, &ca_cb, &ac_cb, t, s3);
    let body = c.trans(&lhs, &ac_cb, &ac_bc, t, s4);

    let e = b.mk_lam(cv_id, BinderInfo::Default, c.nnreal.clone(), body);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.nnreal.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.nnreal.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_add_mul()
            .expect("init_algebra_nnreal_add_mul");
        env.init_algebra_nnreal_add_mul().expect("idempotent");
        env
    }

    #[test]
    fn test_add_mul_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("NNReal.add_mul");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("NNReal.add_mul must kernel-check: {e:?}"));
    }

    #[test]
    fn test_add_mul_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("NNReal.add_mul");
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
