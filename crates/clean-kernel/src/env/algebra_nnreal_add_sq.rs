// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — `NNReal.add_sq` (`(x+y)² = (x² + (xy + xy)) + y²`): the
//! NNReal-level square binomial expansion, the degree-2 predecessor of the cube
//! binomial the **sqrt-free** `(4/3,4)` dual-HC tensorization needs.
//!
//! # Why this module exists (the sqrt-free dual route)
//!
//! The design `2026-06-20-hc43-dual-tensorization-cross-term.md` pinned a C-S
//! route whose cross-term forces an irrational `^{3/2}`-of-an-NNReal (the
//! `NNReal.sqrt` wall). A SQRT-FREE alternative dual tensorization exists (the
//! pointwise-two-point + Minkowski-3 route, verified refute-clean): split the
//! last coordinate via `fL`/`fH` (not `gPart`/`hPart`), apply the LANDED two-point
//! base POINTWISE, and close the cube-Minkowski step `Σ(A+B)³ ≤ (s+t)³` by the
//! cubed cube-Hölder `(ΣA²B)³ ≤ (ΣA³)²(ΣB³)` + the LANDED
//! `NNReal.le_of_cube_le_cube` (the exact dual of the `(2,4)` chain's
//! `le_of_sq_le_sq`). That route NEVER takes a root of a finSum.
//!
//! The cube-Minkowski finSum split expands `(A+B)³` and `(s+t)³` via the cube
//! binomial `(a+b)³ = a³ + (a²b + a²b + a²b) + (ab² + ab² + ab²) + b³`, whose
//! degree-2 base case is this `add_sq`. We deliberately write the cross term
//! `x·y + x·y` (NOT `2·(x·y)`) so the expansion needs ONLY the ring surface
//! (`mul_add`, `add_mul`, `mul_comm`, `add_assoc`) and NO scalar-`2` lemma.
//!
//! # The brick (axiom-free, kernel-checked)
//!
//! ```text
//!   NNReal.add_sq : ∀ x y : NNReal,
//!     NNReal.mul (NNReal.add x y) (NNReal.add x y)
//!       = NNReal.add
//!           (NNReal.add (NNReal.mul x x)
//!                       (NNReal.add (NNReal.mul x y) (NNReal.mul x y)))
//!           (NNReal.mul y y)
//! ```
//!
//! i.e. `(x+y)·(x+y) = (x·x + (x·y + x·y)) + y·y`.
//!
//! # Proof shape (axiom-free, identity-only — mirrors `Rat.add_sq` one carrier up)
//!
//! `(x+y)·(x+y)`
//! → [`mul_add`]     `(x+y)·x + (x+y)·y`
//! → [`add_mul` ×2]  `(x·x + y·x) + (x·y + y·y)`
//! → [`mul_comm` on `y·x`]  `(x·x + x·y) + (x·y + y·y)`
//! → [`add_assoc` re-bracketing]  `(x·x + (x·y + x·y)) + y·y`.
//!
//! Each step is an `Eq` lifted by `congrArg`/`Eq.trans` over the `NNReal.add`
//! structure. `Declaration::Theorem`, `ProofQuality::Constructive`, empty
//! admitted-axiom closure (foundational only). NO `sorry` /
//! `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + congruence smart-constructors for `NNReal.add_sq`.
struct AddSqConsts {
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_add: Expr,
    nnreal_mul_add: Expr,
    nnreal_add_mul: Expr,
    nnreal_mul_comm: Expr,
    nnreal_add_assoc: Expr,
    eq_trans1: Expr,
    eq_symm1: Expr,
    congr_arg11: Expr,
}

impl AddSqConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_add: k("NNReal.add"),
            nnreal_mul_add: k("NNReal.mul_add"),
            nnreal_add_mul: k("NNReal.add_mul"),
            nnreal_mul_comm: k("NNReal.mul_comm"),
            nnreal_add_assoc: k("NNReal.add_assoc"),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg11: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn nnadd(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a.clone(), b.clone()])
    }
    fn eq(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [self.nnreal.clone(), a.clone(), b.clone()],
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
    /// `NNReal.add_assoc a b c : (a+b)+c = a+(b+c)`.
    fn add_assoc(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_add_assoc.clone(),
            [a.clone(), b.clone(), cc.clone()],
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
    fn symm(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_symm1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone(), h],
        )
    }
    /// `congrArg (fun t => add fixed t) h : add fixed a = add fixed b` for `h:a=b`.
    fn cong_right(
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
            let body = self.nnadd(fixed, &w);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.nnreal.clone(), body))
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
    /// `congrArg (fun t => add t fixed) h : add a fixed = add b fixed` for `h:a=b`.
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
            let body = self.nnadd(&w, fixed);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.nnreal.clone(), body))
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
}

impl Environment {
    /// Register `NNReal.add_sq`. Idempotent; foundational-only closure.
    ///
    /// Depends on the NNReal ring surface: `NNReal.mul_add` (`mul_distrib`),
    /// `NNReal.add_mul`, `NNReal.mul_comm` (`reverse_square_algebra`),
    /// `NNReal.add_assoc` (`add_comm_assoc`), plus the `Eq` surface. No axiom is
    /// added or removed.
    pub fn init_algebra_nnreal_add_sq(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_mul_distrib()?; // NNReal.mul_add
        self.init_algebra_nnreal_add_mul()?; // NNReal.add_mul
        self.init_algebra_nnreal_reverse_square_algebra()?; // NNReal.mul_comm
        self.init_algebra_nnreal_add_comm_assoc()?; // NNReal.add_assoc
        self.init_eq()?;

        let c = AddSqConsts::new();
        self.register_add_sq(&c)?;
        Ok(())
    }

    fn register_add_sq(&mut self, c: &AddSqConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.add_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.nnreal.clone());
            let (y_id, y) = b.fresh_local(c.nnreal.clone());
            let s = c.nnadd(&x, &y);
            let lhs = c.nnmul(&s, &s);
            let rhs = add_sq_rhs(c, &x, &y);
            let concl = c.eq(&lhs, &rhs);
            let e = b.mk_pi(y_id, BinderInfo::Default, c.nnreal.clone(), concl);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.nnreal.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.nnreal.clone());
            let (y_id, y) = b.fresh_local(c.nnreal.clone());
            let body = build_add_sq_body(c, &b, &x, &y);
            let e = b.mk_lam(y_id, BinderInfo::Default, c.nnreal.clone(), body);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.nnreal.clone(), e);
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

/// The canonical RHS `(x·x + (x·y + x·y)) + y·y`.
fn add_sq_rhs(c: &AddSqConsts, x: &Expr, y: &Expr) -> Expr {
    let xx = c.nnmul(x, x);
    let xy = c.nnmul(x, y);
    let yy = c.nnmul(y, y);
    let xy_xy = c.nnadd(&xy, &xy);
    c.nnadd(&c.nnadd(&xx, &xy_xy), &yy)
}

/// Proof body `(x+y)·(x+y) = (x·x + (x·y + x·y)) + y·y` for FREE `x`, `y`.
fn build_add_sq_body(c: &AddSqConsts, b: &EnvDeclBuilder, x: &Expr, y: &Expr) -> Expr {
    let xpy = c.nnadd(x, y);
    let e0 = c.nnmul(&xpy, &xpy); // (x+y)·(x+y)

    // STEP 1: mul_add (x+y) x y : (x+y)·(x+y) = (x+y)·x + (x+y)·y
    let xpy_x = c.nnmul(&xpy, x);
    let xpy_y = c.nnmul(&xpy, y);
    let e1 = c.nnadd(&xpy_x, &xpy_y);
    let t1 = c.mul_add(&xpy, x, y);

    // STEP 2a: add_mul x y x : (x+y)·x = x·x + y·x   (lift over fixed right (x+y)·y)
    let xx = c.nnmul(x, x);
    let yx = c.nnmul(y, x);
    let xx_yx = c.nnadd(&xx, &yx);
    let t2a = c.add_mul(x, y, x);
    let mid1 = c.nnadd(&xx_yx, &xpy_y);
    let c1 = c.cong_left(b, &xpy_y, &xpy_x, &xx_yx, t2a);

    // STEP 2b: add_mul x y y : (x+y)·y = x·y + y·y   (lift over fixed left x·x+y·x)
    let xy = c.nnmul(x, y);
    let yy = c.nnmul(y, y);
    let xy_yy = c.nnadd(&xy, &yy);
    let t2b = c.add_mul(x, y, y);
    let e2 = c.nnadd(&xx_yx, &xy_yy);
    let c2 = c.cong_right(b, &xx_yx, &xpy_y, &xy_yy, t2b);

    // STEP 3: mul_comm y x : y·x = x·y   (rewrite inside x·x+y·x → x·x+x·y)
    let xx_xy = c.nnadd(&xx, &xy);
    let h_yx = c.mul_comm(y, x); // y·x = x·y
    let c3 = c.cong_right(b, &xx, &yx, &xy, h_yx); // (x·x + y·x) = (x·x + x·y)
    let e3 = c.nnadd(&xx_xy, &xy_yy);
    let c3p = c.cong_left(b, &xy_yy, &xx_yx, &xx_xy, c3);

    // STEP 4: re-bracket (x·x+x·y) + (x·y+y·y) into (x·x+(x·y+x·y)) + y·y.
    //   a := add_assoc (x·x) (x·y) (x·y+y·y) :
    //        (x·x+x·y) + (x·y+y·y) = x·x + (x·y + (x·y+y·y))
    let inner_r = c.nnadd(&xy, &xy_yy); // x·y + (x·y+y·y)
    let e4 = c.nnadd(&xx, &inner_r);
    let a1 = c.add_assoc(&xx, &xy, &xy_yy);

    //   inner regroup: symm (add_assoc (x·y) (x·y) (y·y)) :
    //        x·y + (x·y+y·y) = (x·y+x·y) + y·y
    let xy_xy = c.nnadd(&xy, &xy);
    let xy_xy_yy = c.nnadd(&xy_xy, &yy);
    let a_inner = c.add_assoc(&xy, &xy, &yy); // (x·y+x·y)+y·y = x·y+(x·y+y·y)
    let a_inner_sym = c.symm(&xy_xy_yy, &inner_r, a_inner);
    let e5 = c.nnadd(&xx, &xy_xy_yy);
    let c5 = c.cong_right(b, &xx, &inner_r, &xy_xy_yy, a_inner_sym);

    //   outer regroup: symm (add_assoc (x·x) (x·y+x·y) (y·y)) :
    //        x·x + ((x·y+x·y)+y·y) = (x·x+(x·y+x·y)) + y·y
    let xx_xy_xy = c.nnadd(&xx, &xy_xy);
    let rhs = c.nnadd(&xx_xy_xy, &yy);
    let a_outer = c.add_assoc(&xx, &xy_xy, &yy); // (x·x+(x·y+x·y))+y·y = x·x+((x·y+x·y)+y·y)
    let a_outer_sym = c.symm(&rhs, &e5, a_outer);

    // trans-chain: e0 → e1 → mid1 → e2 → e3 → e4 → e5 → rhs
    let s = c.trans(&e0, &e1, &mid1, t1, c1);
    let s = c.trans(&e0, &mid1, &e2, s, c2);
    let s = c.trans(&e0, &e2, &e3, s, c3p);
    let s = c.trans(&e0, &e3, &e4, s, a1);
    let s = c.trans(&e0, &e4, &e5, s, c5);
    c.trans(&e0, &e5, &rhs, s, a_outer_sym)
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_add_sq()
            .expect("init_algebra_nnreal_add_sq");
        env.init_algebra_nnreal_add_sq().expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_add_sq_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("NNReal.add_sq");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("NNReal.add_sq must kernel-check: {e:?}"));
    }

    #[test]
    fn test_nnreal_add_sq_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("NNReal.add_sq");
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
