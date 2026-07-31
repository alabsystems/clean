// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — `NNReal.add_cube` (`(a+b)³ = (a³ + 3a²b) + (3ab² + b³)`):
//! the NNReal-level cube binomial, the degree-3 successor of `NNReal.add_sq` the
//! **sqrt-free** `(4/3,4)` dual-HC tensorization's cube-Minkowski step needs.
//!
//! # Why this module exists (the sqrt-free dual route, L2)
//!
//! The sqrt-free dual tensorization (design
//! `2026-06-20-hc43-dual-tensorization-cross-term.md`) closes the cube-Minkowski
//! finSum split `Σ(A+B)³ ≤ (s+t)³` by expanding `(A+B)³` and `(s+t)³` through the
//! cube binomial. The `Rat`-level binomial is the landed `Rat.add_cube`; this is
//! its NNReal carrier-up analog (L2 of the L0–L8 list). It is a pure NNReal ring
//! identity built from the landed `NNReal.add_sq`, `NNReal.mul_add`/`add_mul`,
//! `NNReal.mul_comm`/`mul_assoc`, `NNReal.add_comm`/`add_assoc`.
//!
//! # The `3·t` form (NNReal-native)
//!
//! NNReal has NO `one`/`one_mul` on branch (the `(1+1+1)·t` form that `Rat.add_cube`
//! uses is unavailable). The cube-Minkowski consumer needs the three cross-monomials
//! ANYWAY, so we write the coefficient `3·t` as the purely-additive `(t+t)+t` — no
//! scalar-`·`, no `one`. This is the cleanest NNReal cube form and needs ONLY the
//! ring surface already landed.
//!
//! # The brick (axiom-free, kernel-checked)
//!
//! ```text
//!   NNReal.add_cube : ∀ a b : NNReal,
//!     ((a+b)·(a+b))·(a+b)
//!       = (a³ + ((a²b + a²b) + a²b)) + (((ab² + ab²) + ab²) + b³)
//! ```
//!
//! with `a³ = (a·a)·a`, `a²b = (a·a)·b`, `ab² = (a·b)·b`, `b³ = (b·b)·b`
//! (cubes/monomials left-nested, matching `NNReal.cube_superadd`'s
//! `NNReal.cube_le_cube_of_le` convention), and the `3·` coefficient `(t+t)+t`.
//!
//! # Proof shape (axiom-free, identity-only)
//!
//! Let `SQ := NNReal.add_sq a b = (a·a + (a·b + a·b)) + b·b`.
//!   1. `cube(a+b) = SQ·(a+b)`              (congr `(·(a+b))` of `add_sq`)
//!   2. `SQ·(a+b) = SQ·a + SQ·b`            (`mul_add SQ a b`)
//!   3. expand `SQ·a`, `SQ·b` by `add_mul` (right-distrib), turning each into a
//!      sum of left-nested monomials.
//!   4. reshape every cross monomial to the canonical `a²b = (a·a)·b` /
//!      `ab² = (a·b)·b` via `mul_assoc`/`mul_comm`, then reassociate/reorder the
//!      whole nine-term sum into the canonical `(a³+3a²b)+(3ab²+b³)` bracketing
//!      via `add_assoc`/`add_comm`.
//!
//! Each step is an `Eq` lifted by `congrArg`/`Eq.trans`/`Eq.symm` over the
//! `NNReal.add`/`NNReal.mul` structure. `Declaration::Theorem`,
//! `ProofQuality::Constructive`, empty admitted-axiom closure (foundational only).
//! NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + congruence smart-constructors for `NNReal.add_cube`.
pub(crate) struct AddCubeConsts {
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_add: Expr,
    nnreal_mul_add: Expr,
    nnreal_add_mul: Expr,
    nnreal_mul_comm: Expr,
    nnreal_mul_assoc: Expr,
    nnreal_add_comm: Expr,
    nnreal_add_assoc: Expr,
    nnreal_add_sq: Expr,
    eq_trans1: Expr,
    eq_symm1: Expr,
    congr_arg11: Expr,
}

impl AddCubeConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_add: k("NNReal.add"),
            nnreal_mul_add: k("NNReal.mul_add"),
            nnreal_add_mul: k("NNReal.add_mul"),
            nnreal_mul_comm: k("NNReal.mul_comm"),
            nnreal_mul_assoc: k("NNReal.mul_assoc"),
            nnreal_add_comm: k("NNReal.add_comm"),
            nnreal_add_assoc: k("NNReal.add_assoc"),
            nnreal_add_sq: k("NNReal.add_sq"),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            congr_arg11: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    // ── carrier constructors ──
    fn mul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn add(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a.clone(), b.clone()])
    }
    /// `(a·a)·a` (left-nested cube).
    fn cube(&self, a: &Expr) -> Expr {
        self.mul(&self.mul(a, a), a)
    }
    fn eq(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [self.nnreal.clone(), a.clone(), b.clone()],
        )
    }

    // ── ring lemmas ──
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
    /// `NNReal.add_sq a b : (a+b)·(a+b) = (a·a + (a·b + a·b)) + b·b`.
    fn add_sq(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add_sq.clone(), [a.clone(), b.clone()])
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
    fn congr(&self, a: &Expr, b: &Expr, f: Expr, h: Expr) -> Expr {
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

    // ── congrArg closures ──
    /// `congrArg (fun w => w + fixed) h : x+fixed = y+fixed`.
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
        self.congr(x, y, f, h)
    }
    /// `congrArg (fun w => fixed + w) h : fixed+x = fixed+y`.
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
        self.congr(x, y, f, h)
    }
    /// `congrArg (fun w => w · fixed) h : x·fixed = y·fixed`.
    fn cong_mul_left(
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
            let body = self.mul(&w, fixed);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.congr(x, y, f, h)
    }
    /// `congrArg (fun w => fixed · w) h : fixed·x = fixed·y`.
    #[cfg(test)]
    fn cong_mul_right(
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
            let body = self.mul(fixed, &w);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        self.congr(x, y, f, h)
    }

    /// `3·t` as `(t+t)+t` (NNReal-native, no `one`).
    fn three(&self, t: &Expr) -> Expr {
        self.add(&self.add(t, t), t)
    }

    /// The canonical RHS `(a³ + 3a²b) + (3ab² + b³)`.
    fn rhs(&self, a: &Expr, b: &Expr) -> Expr {
        let a3 = self.cube(a);
        let b3 = self.cube(b);
        let a2b = self.mul(&self.mul(a, a), b); // (a·a)·b
        let ab2 = self.mul(&self.mul(a, b), b); // (a·b)·b
        let left = self.add(&a3, &self.three(&a2b));
        let right = self.add(&self.three(&ab2), &b3);
        self.add(&left, &right)
    }
}

impl Environment {
    /// Register `NNReal.add_cube`. Idempotent; foundational-only closure.
    pub fn init_algebra_nnreal_add_cube(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_add_sq()?; // NNReal.add_sq (+ mul_add/add_mul/mul_comm/add_assoc)
        self.init_algebra_nnreal_add_mul()?; // NNReal.add_mul
        self.init_algebra_nnreal_reverse_square_algebra()?; // NNReal.mul_comm, NNReal.mul_assoc
        self.init_algebra_nnreal_add_comm_assoc()?; // NNReal.add_comm, NNReal.add_assoc
        self.init_eq()?;

        let c = AddCubeConsts::new();
        self.register_add_cube(&c)?;
        Ok(())
    }

    fn register_add_cube(&mut self, c: &AddCubeConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.add_cube");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.nnreal.clone());
            let (bv_id, bv) = b.fresh_local(c.nnreal.clone());
            let s = c.add(&a, &bv);
            let lhs = c.mul(&c.mul(&s, &s), &s);
            let concl = c.eq(&lhs, &c.rhs(&a, &bv));
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.nnreal.clone(), concl);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nnreal.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.nnreal.clone());
            let (bv_id, bv) = b.fresh_local(c.nnreal.clone());
            let body = build_add_cube_body(c, &b, &a, &bv);
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

/// Proof body of `NNReal.add_cube` for free `a`, `b`.
fn build_add_cube_body(c: &AddCubeConsts, b: &EnvDeclBuilder, a: &Expr, bv: &Expr) -> Expr {
    let s = c.add(a, bv); // a+b
    let aa = c.mul(a, a); // a·a
    let ab = c.mul(a, bv); // a·b
    let bb = c.mul(bv, bv); // b·b
    let ab_ab = c.add(&ab, &ab); // a·b + a·b
                                 // SQ := (a·a + (a·b + a·b)) + b·b  (the canonical NNReal.add_sq RHS)
    let aa_plus = c.add(&aa, &ab_ab);
    let sq = c.add(&aa_plus, &bb);

    let ss = c.mul(&s, &s); // (a+b)·(a+b)
    let cube_s = c.mul(&ss, &s); // ((a+b)·(a+b))·(a+b)

    // step1 : cube_s = SQ·(a+b)   [congr (·(a+b)) (add_sq a b)]
    let h_addsq = c.add_sq(a, bv);
    let step1 = c.cong_mul_left(b, &s, &ss, &sq, h_addsq);
    let sq_s = c.mul(&sq, &s);

    // step2 : SQ·(a+b) = SQ·a + SQ·b   [mul_add SQ a b]
    let step2 = c.mul_add(&sq, a, bv);
    let sq_a = c.mul(&sq, a);
    let sq_b = c.mul(&sq, bv);
    let sqa_plus_sqb = c.add(&sq_a, &sq_b);

    // ── expand SQ·a = ((a·a + (a·b+a·b)) + b·b)·a ──
    // add_mul (a·a+(a·b+a·b)) (b·b) a : SQ·a = (a·a+(a·b+a·b))·a + (b·b)·a
    let e_sqa_1 = c.add_mul(&aa_plus, &bb, a);
    let lead_a = c.mul(&aa_plus, a); // (a·a+(a·b+a·b))·a
    let bba = c.mul(&bb, a); // (b·b)·a
    let lead_a_plus_bba = c.add(&lead_a, &bba);
    // add_mul (a·a) (a·b+a·b) a : (a·a+(a·b+a·b))·a = (a·a)·a + (a·b+a·b)·a
    let e_lead_a = c.add_mul(&aa, &ab_ab, a);
    let a3 = c.mul(&aa, a); // (a·a)·a = a³
    let abab_a = c.mul(&ab_ab, a); // (a·b+a·b)·a
    let a3_plus_ababa = c.add(&a3, &abab_a);
    // congr (·+ (b·b)·a) e_lead_a
    let c_sqa_2 = c.cong_add_left(b, &bba, &lead_a, &a3_plus_ababa, e_lead_a);
    let inner_a = c.add(&a3_plus_ababa, &bba); // ((a³ + (a·b+a·b)·a) + (b·b)·a)
    let h_sqa = c.trans(&sq_a, &lead_a_plus_bba, &inner_a, e_sqa_1, c_sqa_2);

    // ── expand SQ·b similarly ──
    let e_sqb_1 = c.add_mul(&aa_plus, &bb, bv);
    let lead_b = c.mul(&aa_plus, bv);
    let bbb = c.mul(&bb, bv); // (b·b)·b = b³
    let lead_b_plus_bbb = c.add(&lead_b, &bbb);
    let e_lead_b = c.add_mul(&aa, &ab_ab, bv);
    let aab = c.mul(&aa, bv); // (a·a)·b = a²b
    let abab_b = c.mul(&ab_ab, bv); // (a·b+a·b)·b
    let aab_plus_ababb = c.add(&aab, &abab_b);
    let c_sqb_2 = c.cong_add_left(b, &bbb, &lead_b, &aab_plus_ababb, e_lead_b);
    let inner_b = c.add(&aab_plus_ababb, &bbb);
    let h_sqb = c.trans(&sq_b, &lead_b_plus_bbb, &inner_b, e_sqb_1, c_sqb_2);

    // step3 : SQ·a + SQ·b = inner_a + inner_b
    let c_left = c.cong_add_left(b, &sq_b, &sq_a, &inner_a, h_sqa);
    let inner_a_plus_sqb = c.add(&inner_a, &sq_b);
    let c_right = c.cong_add_right(b, &inner_a, &sq_b, &inner_b, h_sqb);
    let inner_sum = c.add(&inner_a, &inner_b);
    let step3 = c.trans(
        &sqa_plus_sqb,
        &inner_a_plus_sqb,
        &inner_sum,
        c_left,
        c_right,
    );

    // h_pre : cube_s = inner_a + inner_b
    let h_pre = {
        let t1 = c.trans(&cube_s, &sq_s, &sqa_plus_sqb, step1, step2);
        c.trans(&cube_s, &sqa_plus_sqb, &inner_sum, t1, step3)
    };

    // Now reshape monomials + collect into the canonical RHS.
    let h_reshape = reshape_and_collect(c, b, a, bv, &inner_a, &inner_b);
    // h_reshape : inner_a + inner_b = (a³ + 3a²b) + (3ab² + b³)
    let target = c.rhs(a, bv);
    c.trans(&cube_s, &inner_sum, &target, h_pre, h_reshape)
}

/// Reshape `(a·b+a·b)·a`, `(b·b)·a`, `(a·b+a·b)·b` into `a²b`/`ab²` monomials and
/// collect `inner_a + inner_b` into the canonical `(a³ + 3a²b) + (3ab² + b³)`.
///
/// `inner_a = (a³ + (a·b+a·b)·a) + (b·b)·a`
/// `inner_b = ((a·a)·b + (a·b+a·b)·b) + (b·b)·b`
#[allow(clippy::too_many_arguments)]
fn reshape_and_collect(
    c: &AddCubeConsts,
    b: &EnvDeclBuilder,
    a: &Expr,
    bv: &Expr,
    inner_a: &Expr,
    inner_b: &Expr,
) -> Expr {
    let aa = c.mul(a, a);
    let ab = c.mul(a, bv);
    let bb = c.mul(bv, bv);
    let ab_ab = c.add(&ab, &ab);
    let a3 = c.mul(&aa, a);
    let b3 = c.mul(&bb, bv);
    let a2b = c.mul(&aa, bv); // (a·a)·b
    let ab2 = c.mul(&ab, bv); // (a·b)·b
    let abab_a = c.mul(&ab_ab, a); // (a·b+a·b)·a
    let abab_b = c.mul(&ab_ab, bv); // (a·b+a·b)·b
    let bba = c.mul(&bb, a); // (b·b)·a

    // ── E1 : (a·b+a·b)·a = a²b + a²b ──
    // add_mul (a·b) (a·b) a : (a·b+a·b)·a = (a·b)·a + (a·b)·a
    let aba = c.mul(&ab, a); // (a·b)·a
    let e_abab_a_split = c.add_mul(&ab, &ab, a);
    let aba_plus_aba = c.add(&aba, &aba);
    // (a·b)·a = a²b :  (a·b)·a = a·(b·a)? No — use mul_comm + mul_assoc carefully.
    //   mul_comm (a·b) a : (a·b)·a = a·(a·b)            [comm with the scalar a]
    //   mul_assoc a a b  : a·(a·b) = (a·a)·b = a²b      [NNReal.mul_assoc dir]
    let e_aba_comm = c.mul_comm(&ab, a); // (a·b)·a = a·(a·b)
    let a_ab = c.mul(a, &ab); // a·(a·b)
    let e_aba_assoc = c.mul_assoc(a, a, bv); // a·(a·b) = (a·a)·b
    let e_aba = c.trans(&aba, &a_ab, &a2b, e_aba_comm, e_aba_assoc); // (a·b)·a = a²b
                                                                     // lift to the pair: (a·b)·a + (a·b)·a = a²b + a²b
    let c_aba_l = c.cong_add_left(b, &aba, &aba, &a2b, e_aba.clone()); // (aba+aba)=(a2b+aba)
    let a2b_plus_aba = c.add(&a2b, &aba);
    let c_aba_r = c.cong_add_right(b, &a2b, &aba, &a2b, e_aba); // (a2b+aba)=(a2b+a2b)
    let a2b_plus_a2b = c.add(&a2b, &a2b);
    let e_pair_a = c.trans(
        &aba_plus_aba,
        &a2b_plus_aba,
        &a2b_plus_a2b,
        c_aba_l,
        c_aba_r,
    );
    let e1 = c.trans(
        &abab_a,
        &aba_plus_aba,
        &a2b_plus_a2b,
        e_abab_a_split,
        e_pair_a,
    );
    // E1 : (a·b+a·b)·a = a²b + a²b

    // ── E2 : (b·b)·a = ab² ──
    //   mul_comm (b·b) a : (b·b)·a = a·(b·b)
    //   mul_assoc a b b  : a·(b·b) = (a·b)·b = ab²
    let e_bba_comm = c.mul_comm(&bb, a); // (b·b)·a = a·(b·b)
    let a_bb = c.mul(a, &bb);
    let e_bba_assoc = c.mul_assoc(a, bv, bv); // a·(b·b) = (a·b)·b
    let e2 = c.trans(&bba, &a_bb, &ab2, e_bba_comm, e_bba_assoc); // (b·b)·a = ab²

    // ── E3 : (a·b+a·b)·b = ab² + ab² ──
    // add_mul (a·b) (a·b) b : (a·b+a·b)·b = (a·b)·b + (a·b)·b = ab² + ab²
    let e3 = c.add_mul(&ab, &ab, bv); // (a·b+a·b)·b = (a·b)·b + (a·b)·b
    let ab2_plus_ab2 = c.add(&ab2, &ab2); // (ab² + ab²)  [= RHS of e3 defeq, ab2=(a·b)·b]

    // ── rewrite inner_a → ia := (a³ + (a²b+a²b)) + ab² ──
    // inner_a = (a³ + (a·b+a·b)·a) + (b·b)·a
    let f_ia_mid = {
        // congr on the middle summand (a·b+a·b)·a → a²b+a²b inside (a³ + ·)
        let e_left = c.cong_add_right(b, &a3, &abab_a, &a2b_plus_a2b, e1.clone());
        let a3_plus_ababa = c.add(&a3, &abab_a);
        let a3_plus_2a2b = c.add(&a3, &a2b_plus_a2b);
        // lift over (· + (b·b)·a)
        let c_outer = c.cong_add_left(b, &bba, &a3_plus_ababa, &a3_plus_2a2b, e_left);
        let ia_mid = c.add(&a3_plus_2a2b, &bba);
        let a3_plus_ababa_full = c.add(&a3_plus_ababa, &bba); // == inner_a
                                                              // then (b·b)·a → ab²
        let c_tail = c.cong_add_right(b, &a3_plus_2a2b, &bba, &ab2, e2.clone());
        let ia = c.add(&a3_plus_2a2b, &ab2);
        let h = c.trans(&a3_plus_ababa_full, &ia_mid, &ia, c_outer, c_tail);
        (ia, h) // h : inner_a = ia
    };
    let (ia, h_inner_a) = f_ia_mid;

    // ── rewrite inner_b → ib := (a²b + (ab²+ab²)) + b³ ──
    // inner_b = ((a·a)·b + (a·b+a·b)·b) + (b·b)·b  with (a·a)·b = a²b, (b·b)·b = b³
    let h_inner_b = {
        let e_mid = c.cong_add_right(b, &a2b, &abab_b, &ab2_plus_ab2, e3.clone());
        let a2b_plus_ababb = c.add(&a2b, &abab_b);
        let a2b_plus_2ab2 = c.add(&a2b, &ab2_plus_ab2);
        c.cong_add_left(b, &b3, &a2b_plus_ababb, &a2b_plus_2ab2, e_mid)
        // : inner_b = (a²b + (ab²+ab²)) + b³ = ib
    };
    let a2b_plus_2ab2 = c.add(&a2b, &ab2_plus_ab2);
    let ib = c.add(&a2b_plus_2ab2, &b3);

    // ── inner_a + inner_b = ia + ib ──
    let c_sum_l = c.cong_add_left(b, inner_b, inner_a, &ia, h_inner_a);
    let ia_plus_inner_b = c.add(&ia, inner_b);
    let c_sum_r = c.cong_add_right(b, &ia, inner_b, &ib, h_inner_b);
    let ia_plus_ib = c.add(&ia, &ib);
    let inner_sum = c.add(inner_a, inner_b);
    let h_sum = c.trans(&inner_sum, &ia_plus_inner_b, &ia_plus_ib, c_sum_l, c_sum_r);

    // ── ia + ib = canonical target, by pure additive reassociation ──
    // ia = (a³ + (a²b+a²b)) + ab²,  ib = (a²b + (ab²+ab²)) + b³.
    // target = (a³ + ((a²b+a²b)+a²b)) + (((ab²+ab²)+ab²) + b³).
    let h_reassoc = finish_reassoc(c, b, &a3, &a2b, &ab2, &b3);
    let target = c.rhs(a, bv);
    c.trans(&inner_sum, &ia_plus_ib, &target, h_sum, h_reassoc)
}

/// Prove `((a³+(a²b+a²b))+ab²) + ((a²b+(ab²+ab²))+b³)
///        = (a³ + ((a²b+a²b)+a²b)) + (((ab²+ab²)+ab²)+b³)`
/// from pure additive associativity/commutativity (monomials opaque).
fn finish_reassoc(
    c: &AddCubeConsts,
    parent: &EnvDeclBuilder,
    a3: &Expr,
    a2b: &Expr,
    ab2: &Expr,
    b3: &Expr,
) -> Expr {
    // Abbreviations.
    let two_a2b = c.add(a2b, a2b); // a²b+a²b
    let two_ab2 = c.add(ab2, ab2); // ab²+ab²
    let three_a2b = c.add(&two_a2b, a2b); // (a²b+a²b)+a²b
    let three_ab2 = c.add(&two_ab2, ab2); // (ab²+ab²)+ab²

    // L := (a³+2a²b)+ab² ; R := (a²b+2ab²)+b³.
    let a3_2a2b = c.add(a3, &two_a2b);
    let l = c.add(&a3_2a2b, ab2);
    let a2b_2ab2 = c.add(a2b, &two_ab2);
    let r = c.add(&a2b_2ab2, b3);
    let lhs = c.add(&l, &r);

    // Plan: bring both sides to the fully-right-associated 6-term canonical
    //   C := a³ + (2a²b + (ab² + (a²b + (2ab² + b³)))).
    // Step A: lhs = C  (pure add_assoc).
    let h_lhs_c = reassoc_lhs_to_canon(c, parent, a3, a2b, ab2, b3);
    // canon C explicit:
    let two_ab2_b3 = c.add(&two_ab2, b3);
    let a2b_rest = c.add(a2b, &two_ab2_b3);
    let ab2_rest = c.add(ab2, &a2b_rest);
    let twoa2b_rest = c.add(&two_a2b, &ab2_rest);
    let canon = c.add(a3, &twoa2b_rest);

    // Step B: C = `a³ + (3a²b + (3ab² + b³))`. Inner:
    //   I := 2a²b + (ab² + (a²b + (2ab²+b³)))  →  3a²b + (3ab² + b³).
    let h_inner = collect_inner(c, parent, a2b, ab2, b3);
    let three_ab2_b3 = c.add(&three_ab2, b3);
    let target_inner = c.add(&three_a2b, &three_ab2_b3);
    let h_c_mid = c.cong_add_right(parent, a3, &twoa2b_rest, &target_inner, h_inner);
    let mid = c.add(a3, &target_inner); // a³ + (3a²b + (3ab² + b³))

    // Step C: rebracket to the `rhs` shape `(a³ + 3a²b) + (3ab² + b³)`.
    //   symm add_assoc a³ 3a²b (3ab²+b³) : a³+(3a²b+X) = (a³+3a²b)+X.
    let a3_3a2b = c.add(a3, &three_a2b);
    let target = c.add(&a3_3a2b, &three_ab2_b3); // == c.rhs(a,b)
    let h_mid_target = c.symm(&target, &mid, c.add_assoc(a3, &three_a2b, &three_ab2_b3));

    let t1 = c.trans(&lhs, &canon, &mid, h_lhs_c, h_c_mid);
    c.trans(&lhs, &mid, &target, t1, h_mid_target)
}

/// Reassociate `((a³+2a²b)+ab²) + ((a²b+2ab²)+b³)` fully right to
/// `a³ + (2a²b + (ab² + (a²b + (2ab²+b³))))`.
fn reassoc_lhs_to_canon(
    c: &AddCubeConsts,
    parent: &EnvDeclBuilder,
    a3: &Expr,
    a2b: &Expr,
    ab2: &Expr,
    b3: &Expr,
) -> Expr {
    let two_a2b = c.add(a2b, a2b);
    let two_ab2 = c.add(ab2, ab2);
    let a3_2a2b = c.add(a3, &two_a2b);
    let l = c.add(&a3_2a2b, ab2);
    let a2b_2ab2 = c.add(a2b, &two_ab2);
    let r = c.add(&a2b_2ab2, b3);
    let lhs = c.add(&l, &r);

    // s1 : ((a3_2a2b)+ab²)+R = (a3_2a2b)+(ab²+R)   [add_assoc (a3_2a2b) ab² R]
    let ab2_plus_r = c.add(ab2, &r);
    let s1 = c.add_assoc(&a3_2a2b, ab2, &r);
    let mid1 = c.add(&a3_2a2b, &ab2_plus_r);
    // s2 : (a³+2a²b)+(ab²+R) = a³+(2a²b+(ab²+R))   [add_assoc a³ 2a²b (ab²+R)]
    let twoa2b_plus = c.add(&two_a2b, &ab2_plus_r);
    let s2 = c.add_assoc(a3, &two_a2b, &ab2_plus_r);
    let mid2 = c.add(a3, &twoa2b_plus);
    // expand R inside: R = a²b+(2ab²+b³)  [add_assoc a²b 2ab² b³]
    let two_ab2_b3 = c.add(&two_ab2, b3);
    let a2b_rest = c.add(a2b, &two_ab2_b3);
    let e_r = c.add_assoc(a2b, &two_ab2, b3); // R = a²b+(2ab²+b³)
    let e_ab2r = c.cong_add_right(parent, ab2, &r, &a2b_rest, e_r); // (ab²+R) = ab²+(a²b+(2ab²+b³))
    let ab2_rest = c.add(ab2, &a2b_rest);
    let e_2a2b = c.cong_add_right(parent, &two_a2b, &ab2_plus_r, &ab2_rest, e_ab2r);
    let twoa2b_plus2 = c.add(&two_a2b, &ab2_rest);
    let e_final = c.cong_add_right(parent, a3, &twoa2b_plus, &twoa2b_plus2, e_2a2b);
    let canon = c.add(a3, &twoa2b_plus2);

    let t1 = c.trans(&lhs, &mid1, &mid2, s1, s2);
    c.trans(&lhs, &mid2, &canon, t1, e_final)
}

/// Prove `2a²b + (ab² + (a²b + (2ab²+b³))) = 3a²b + (3ab² + b³)`,
/// with `3·t = (t+t)+t`. Pure additive assoc/comm.
fn collect_inner(
    c: &AddCubeConsts,
    parent: &EnvDeclBuilder,
    a2b: &Expr,
    ab2: &Expr,
    b3: &Expr,
) -> Expr {
    let two_a2b = c.add(a2b, a2b);
    let two_ab2 = c.add(ab2, ab2);
    let three_a2b = c.add(&two_a2b, a2b);
    let three_ab2 = c.add(&two_ab2, ab2);

    // I = 2a²b + (ab² + (a²b + Y)),  Y := 2ab²+b³.
    let y = c.add(&two_ab2, b3);
    let a2b_y = c.add(a2b, &y);
    let ab2_rest = c.add(ab2, &a2b_y);
    let i = c.add(&two_a2b, &ab2_rest);

    // Move a²b in front of ab²: ab²+(a²b+Y) = a²b+(ab²+Y).
    //   ab²+(a²b+Y) = (ab²+a²b)+Y  (symm add_assoc ab² a²b Y)
    //              = (a²b+ab²)+Y  (congr (·+Y) add_comm ab² a²b)
    //              = a²b+(ab²+Y)  (add_assoc a²b ab² Y)
    let ab2_a2b = c.add(ab2, a2b);
    let a2b_ab2 = c.add(a2b, ab2);
    let ab2_a2b_y = c.add(&ab2_a2b, &y);
    let e_s1 = c.symm(&ab2_a2b_y, &ab2_rest, c.add_assoc(ab2, a2b, &y));
    let e_s2 = c.cong_add_left(parent, &y, &ab2_a2b, &a2b_ab2, c.add_comm(ab2, a2b));
    let a2b_ab2_y = c.add(&a2b_ab2, &y);
    let e_s3 = c.add_assoc(a2b, ab2, &y); // (a²b+ab²)+Y = a²b+(ab²+Y)
    let ab2_y = c.add(ab2, &y);
    let a2b_plus_ab2y = c.add(a2b, &ab2_y);
    let e_move = {
        let t1 = c.trans(&ab2_rest, &ab2_a2b_y, &a2b_ab2_y, e_s1, e_s2);
        c.trans(&ab2_rest, &a2b_ab2_y, &a2b_plus_ab2y, t1, e_s3)
    };

    // congr (2a²b + ·) e_move : I = 2a²b + (a²b + (ab²+Y))
    let e_i1 = c.cong_add_right(parent, &two_a2b, &ab2_rest, &a2b_plus_ab2y, e_move);
    let i1 = c.add(&two_a2b, &a2b_plus_ab2y);

    // (2a²b) + (a²b + Z) = (2a²b + a²b) + Z   [symm add_assoc], Z := ab²+Y.
    // Note `(2a²b + a²b)` is LITERALLY `three_a2b = (a²b+a²b)+a²b`, so `i2` is
    // syntactically `three_a2b + Z` — no coefficient-fold lemma needed.
    let z = ab2_y.clone();
    let i2 = c.add(&three_a2b, &z);
    let e_i2 = c.symm(&i2, &i1, c.add_assoc(&two_a2b, a2b, &z));

    // Z = ab²+(2ab²+b³). Want 3ab²+b³.
    //   ab²+(2ab²+b³) = (ab²+2ab²)+b³  (symm add_assoc)
    //   (ab²+2ab²) = 3ab²? NO — 3ab² = (ab²+ab²)+ab² = 2ab²+ab² (left assoc),
    //   but here we have ab²+2ab² = ab²+(ab²+ab²). Use add_assoc/comm to reorder.
    let ab2_2ab2 = c.add(ab2, &two_ab2); // ab²+(ab²+ab²)
    let e_z1 = c.symm(&c.add(&ab2_2ab2, b3), &z, c.add_assoc(ab2, &two_ab2, b3));
    //   ab²+(ab²+ab²) = (ab²+ab²)+ab² = 3ab²   [symm add_assoc ab² ab² ab²]
    let e_coeff = c.symm(&three_ab2, &ab2_2ab2, c.add_assoc(ab2, ab2, ab2));
    let e_z2 = c.cong_add_left(parent, b3, &ab2_2ab2, &three_ab2, e_coeff);
    let three_ab2_b3 = c.add(&three_ab2, b3);
    let e_z = c.trans(&z, &c.add(&ab2_2ab2, b3), &three_ab2_b3, e_z1, e_z2);

    // congr (3a²b + ·) e_z : (3a²b + Z) = 3a²b + (3ab²+b³) = target.
    let e_i4 = c.cong_add_right(parent, &three_a2b, &z, &three_ab2_b3, e_z);
    let target = c.add(&three_a2b, &three_ab2_b3);

    // chain: I = i1 (e_i1) = i2 (e_i2) = target (e_i4).
    let t1 = c.trans(&i, &i1, &i2, e_i1, e_i2);
    c.trans(&i, &i2, &target, t1, e_i4)
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_add_cube()
            .expect("init_algebra_nnreal_add_cube");
        env.init_algebra_nnreal_add_cube().expect("idempotent");
        env
    }

    #[test]
    fn test_nnreal_add_cube_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("NNReal.add_cube");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("NNReal.add_cube must kernel-check: {e:?}"));
    }

    #[test]
    fn test_nnreal_add_cube_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("NNReal.add_cube");
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
