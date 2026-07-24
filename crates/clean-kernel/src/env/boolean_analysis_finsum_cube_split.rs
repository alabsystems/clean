// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — `BoolAnalysis.finSum_cube_split` (L3): the finSum cube
//! split of the sqrt-free `(4/3,4)` dual-HC tensorization.
//!
//! # Why this module exists (L3 of the sqrt-free dual route)
//!
//! The cube-Minkowski step of the `(4/3,4)` dual tensorization (design
//! `2026-06-20-hc43-dual-tensorization-cross-term.md`) expands the summed cube of
//! a pointwise sum `Σ_i (A i + B i)³` into the four collected monomial sums. This
//! is the finSum-level lift of the pointwise cube binomial `NNReal.add_cube` (L2):
//! apply `NNReal.add_cube` POINTWISE under the sum (via `NNReal.finSum_congr`),
//! then distribute the finSum over the four-way `+` (via `NNReal.finSum_add`).
//!
//! # The brick (axiom-free, kernel-checked)
//!
//! ```text
//!   BoolAnalysis.finSum_cube_split : ∀ (n : Nat)(A B : Fin n → NNReal),
//!     NNReal.finSum n (fun i => ((A i + B i)·(A i + B i))·(A i + B i))
//!       = ( NNReal.finSum n (fun i => (A i·A i)·A i)          -- Σ A³
//!         + NNReal.finSum n (fun i => 3·((A i·A i)·B i)) )    -- Σ 3A²B
//!       + ( NNReal.finSum n (fun i => 3·((A i·B i)·B i))      -- Σ 3AB²
//!         + NNReal.finSum n (fun i => (B i·B i)·B i) )        -- Σ B³
//! ```
//!
//! with the `3·t` coefficient written purely-additively as `(t+t)+t` (NNReal has
//! no `one`; this matches `NNReal.add_cube`'s RHS shape exactly).
//!
//! # Proof shape (axiom-free)
//!
//! Let `cube_uv i := ((A i+B i)·(A i+B i))·(A i+B i)` and `rhs_i := (A³ i + 3A²B
//! i) + (3AB² i + B³ i)` (the `NNReal.add_cube` RHS at `A i, B i`).
//!   1. `NNReal.finSum_congr n cube_uv rhs (fun i => NNReal.add_cube (A i)(B i))`
//!      : `finSum n cube_uv = finSum n rhs`.
//!   2. `NNReal.finSum_add n (fun i => A³ i + 3A²B i)(fun i => 3AB² i + B³ i)`
//!      : `finSum n rhs = finSum n L + finSum n R`  (L i = A³+3A²B, R i = 3AB²+B³).
//!   3. `NNReal.finSum_add` on each of `L`, `R`, lifted by `congr`, gives
//!      `finSum n L = ΣA³ + Σ3A²B` and `finSum n R = Σ3AB² + ΣB³`.
//!   4. `Eq.trans`/`congr` assembly into the canonical four-sum RHS.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only — `add_cube`/`finSum_congr`/`finSum_add` are all
//! constructive). NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for `finSum_cube_split`.
struct CubeSplitConsts {
    nat: Expr,
    fin: Expr,
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_add: Expr,
    nnreal_finsum: Expr,
    nnreal_add_cube: Expr,
    nnreal_finsum_congr: Expr,
    nnreal_finsum_add: Expr,
    eq_trans1: Expr,
    congr_arg11: Expr,
    congr11: Expr,
}

impl CubeSplitConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            fin: k("Fin"),
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_add: k("NNReal.add"),
            nnreal_finsum: k("NNReal.finSum"),
            nnreal_add_cube: k("NNReal.add_cube"),
            nnreal_finsum_congr: k("NNReal.finSum_congr"),
            nnreal_finsum_add: k("NNReal.finSum_add"),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg11: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            congr11: Expr::const_(Name::from_string("congr"), vec![l1.clone(), l1]),
        }
    }

    fn fin_n(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn fin_to_nn(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_n(n), self.nnreal.clone())
    }
    fn mul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn add(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a.clone(), b.clone()])
    }
    fn three(&self, t: &Expr) -> Expr {
        self.add(&self.add(t, t), t)
    }
    fn sum(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.nnreal_finsum.clone(), [n.clone(), f.clone()])
    }
    fn eq_nn(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [self.nnreal.clone(), a.clone(), b.clone()],
        )
    }
    fn trans(&self, a: &Expr, b: &Expr, c: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone(), c.clone(), h1, h2],
        )
    }
    /// `congr (congrArg add hL) hR : (xl+xr) = (yl+yr)` from `hL : xl=yl`,
    /// `hR : xr=yr`.
    fn cong_add_both(
        &self,
        xl: &Expr,
        yl: &Expr,
        xr: &Expr,
        yr: &Expr,
        hl: Expr,
        hr: Expr,
    ) -> Expr {
        let nn_to_nn = Expr::pi(
            BinderInfo::Default,
            self.nnreal.clone(),
            self.nnreal.clone(),
        );
        let congr_add = Expr::apps(
            self.congr_arg11.clone(),
            [
                self.nnreal.clone(),
                nn_to_nn,
                xl.clone(),
                yl.clone(),
                self.nnreal_add.clone(),
                hl,
            ],
        );
        let add_xl = Expr::app(self.nnreal_add.clone(), xl.clone());
        let add_yl = Expr::app(self.nnreal_add.clone(), yl.clone());
        Expr::apps(
            self.congr11.clone(),
            [
                self.nnreal.clone(),
                self.nnreal.clone(),
                add_xl,
                add_yl,
                xr.clone(),
                yr.clone(),
                congr_add,
                hr,
            ],
        )
    }

    // ── per-index monomial bodies (at a free `i`, given `A i`, `B i`) ──
    fn cube_uv_body(&self, ai: &Expr, bi: &Expr) -> Expr {
        let s = self.add(ai, bi);
        self.mul(&self.mul(&s, &s), &s)
    }
    fn a3_body(&self, ai: &Expr) -> Expr {
        self.mul(&self.mul(ai, ai), ai)
    }
    fn b3_body(&self, bi: &Expr) -> Expr {
        self.mul(&self.mul(bi, bi), bi)
    }
    fn a2b_body(&self, ai: &Expr, bi: &Expr) -> Expr {
        self.mul(&self.mul(ai, ai), bi)
    }
    fn ab2_body(&self, ai: &Expr, bi: &Expr) -> Expr {
        self.mul(&self.mul(ai, bi), bi)
    }
    /// The `NNReal.add_cube` RHS at `A i, B i`: `(A³ + 3A²B) + (3AB² + B³)`.
    fn add_cube_rhs_body(&self, ai: &Expr, bi: &Expr) -> Expr {
        let left = self.add(&self.a3_body(ai), &self.three(&self.a2b_body(ai, bi)));
        let right = self.add(&self.three(&self.ab2_body(ai, bi)), &self.b3_body(bi));
        self.add(&left, &right)
    }

    /// Build `fun i : Fin n => body(A i, B i)` for a body-builder.
    fn lam_ab<F>(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr, b: &Expr, body: F) -> Expr
    where
        F: Fn(&Self, &Expr, &Expr) -> Expr,
    {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (i_id, i) = d.fresh_local(self.fin_n(n));
        let ai = Expr::app(a.clone(), i.clone());
        let bi = Expr::app(b.clone(), i.clone());
        let bod = body(self, &ai, &bi);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, self.fin_n(n), bod))
    }
}

impl Environment {
    /// Register `BoolAnalysis.finSum_cube_split`. Idempotent; foundational-only.
    pub fn register_finsum_cube_split(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.finSum_cube_split");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_algebra_nnreal_add_cube()?; // NNReal.add_cube + ring surface
        self.init_algebra_nnreal_finsum_add()?; // NNReal.finSum_congr + finSum_add
        self.init_eq()?;

        let c = CubeSplitConsts::new();
        let (ty, value) = build_cube_split(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

fn build_cube_split(c: &CubeSplitConsts) -> (Expr, Expr) {
    // Body-builders for the four collected summands and the L/R halves.
    let l_body = |s: &CubeSplitConsts, ai: &Expr, bi: &Expr| {
        s.add(&s.a3_body(ai), &s.three(&s.a2b_body(ai, bi)))
    };
    let r_body = |s: &CubeSplitConsts, ai: &Expr, bi: &Expr| {
        s.add(&s.three(&s.ab2_body(ai, bi)), &s.b3_body(bi))
    };
    let three_a2b_body = |s: &CubeSplitConsts, ai: &Expr, bi: &Expr| s.three(&s.a2b_body(ai, bi));
    let three_ab2_body = |s: &CubeSplitConsts, ai: &Expr, bi: &Expr| s.three(&s.ab2_body(ai, bi));
    let a3_only = |s: &CubeSplitConsts, ai: &Expr, _bi: &Expr| s.a3_body(ai);
    let b3_only = |s: &CubeSplitConsts, _ai: &Expr, bi: &Expr| s.b3_body(bi);

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (a_id, a) = b.fresh_local(c.fin_to_nn(&n));
        let (bv_id, bv) = b.fresh_local(c.fin_to_nn(&n));

        let lhs = c.sum(
            &n,
            &c.lam_ab(&b, &n, &a, &bv, |s, ai, bi| s.cube_uv_body(ai, bi)),
        );
        let sum_a3 = c.sum(&n, &c.lam_ab(&b, &n, &a, &bv, a3_only));
        let sum_3a2b = c.sum(&n, &c.lam_ab(&b, &n, &a, &bv, three_a2b_body));
        let sum_3ab2 = c.sum(&n, &c.lam_ab(&b, &n, &a, &bv, three_ab2_body));
        let sum_b3 = c.sum(&n, &c.lam_ab(&b, &n, &a, &bv, b3_only));
        let rhs = c.add(&c.add(&sum_a3, &sum_3a2b), &c.add(&sum_3ab2, &sum_b3));
        let concl = c.eq_nn(&lhs, &rhs);

        let e = b.mk_pi(bv_id, BinderInfo::Default, c.fin_to_nn(&n), concl);
        let e = b.mk_pi(a_id, BinderInfo::Default, c.fin_to_nn(&n), e);
        let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (a_id, a) = b.fresh_local(c.fin_to_nn(&n));
        let (bv_id, bv) = b.fresh_local(c.fin_to_nn(&n));

        // summand functions
        let cube_uv = c.lam_ab(&b, &n, &a, &bv, |s, ai, bi| s.cube_uv_body(ai, bi));
        let rhs_fn = c.lam_ab(&b, &n, &a, &bv, |s, ai, bi| s.add_cube_rhs_body(ai, bi));
        let l_fn = c.lam_ab(&b, &n, &a, &bv, l_body);
        let r_fn = c.lam_ab(&b, &n, &a, &bv, r_body);
        let a3_fn = c.lam_ab(&b, &n, &a, &bv, a3_only);
        let three_a2b_fn = c.lam_ab(&b, &n, &a, &bv, three_a2b_body);
        let three_ab2_fn = c.lam_ab(&b, &n, &a, &bv, three_ab2_body);
        let b3_fn = c.lam_ab(&b, &n, &a, &bv, b3_only);

        // sums
        let sum_cube_uv = c.sum(&n, &cube_uv);
        let sum_rhs = c.sum(&n, &rhs_fn);
        let sum_l = c.sum(&n, &l_fn);
        let sum_r = c.sum(&n, &r_fn);
        let sum_a3 = c.sum(&n, &a3_fn);
        let sum_3a2b = c.sum(&n, &three_a2b_fn);
        let sum_3ab2 = c.sum(&n, &three_ab2_fn);
        let sum_b3 = c.sum(&n, &b3_fn);

        // step1 : sum_cube_uv = sum_rhs  (finSum_congr + pointwise add_cube)
        let h_pw = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (i_id, i) = d.fresh_local(c.fin_n(&n));
            let ai = Expr::app(a.clone(), i.clone());
            let bi = Expr::app(bv.clone(), i.clone());
            // NNReal.add_cube (A i)(B i) : cube_uv_body = add_cube_rhs_body.
            let body = Expr::apps(c.nnreal_add_cube.clone(), [ai, bi]);
            d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_n(&n), body))
        };
        let step1 = Expr::apps(
            c.nnreal_finsum_congr.clone(),
            [n.clone(), cube_uv.clone(), rhs_fn.clone(), h_pw],
        );

        // step2 : sum_rhs = sum_l + sum_r  (finSum_add n l_fn r_fn)
        // (rhs_fn i ≡ (l_fn i) + (r_fn i) definitionally.)
        let step2 = Expr::apps(
            c.nnreal_finsum_add.clone(),
            [n.clone(), l_fn.clone(), r_fn.clone()],
        );
        let sum_l_plus_r = c.add(&sum_l, &sum_r);

        // step3a : sum_l = sum_a3 + sum_3a2b  (finSum_add n a3_fn three_a2b_fn)
        let step3a = Expr::apps(
            c.nnreal_finsum_add.clone(),
            [n.clone(), a3_fn.clone(), three_a2b_fn.clone()],
        );
        let sum_a3_plus_3a2b = c.add(&sum_a3, &sum_3a2b);
        // step3b : sum_r = sum_3ab2 + sum_b3
        let step3b = Expr::apps(
            c.nnreal_finsum_add.clone(),
            [n.clone(), three_ab2_fn.clone(), b3_fn.clone()],
        );
        let sum_3ab2_plus_b3 = c.add(&sum_3ab2, &sum_b3);

        // step3 : (sum_l + sum_r) = ((ΣA³+Σ3A²B) + (Σ3AB²+ΣB³))  via congr both.
        let step3 = c.cong_add_both(
            &sum_l,
            &sum_a3_plus_3a2b,
            &sum_r,
            &sum_3ab2_plus_b3,
            step3a,
            step3b,
        );
        let target = c.add(&sum_a3_plus_3a2b, &sum_3ab2_plus_b3);

        // chain: sum_cube_uv = sum_rhs = (sum_l+sum_r) = target.
        let t1 = c.trans(&sum_cube_uv, &sum_rhs, &sum_l_plus_r, step1, step2);
        let proof = c.trans(&sum_cube_uv, &sum_l_plus_r, &target, t1, step3);

        let e = b.mk_lam(bv_id, BinderInfo::Default, c.fin_to_nn(&n), proof);
        let e = b.mk_lam(a_id, BinderInfo::Default, c.fin_to_nn(&n), e);
        let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    };

    (ty, value)
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_finsum_cube_split()
            .expect("register_finsum_cube_split");
        env.register_finsum_cube_split().expect("idempotent");
        env
    }

    #[test]
    fn test_finsum_cube_split_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nm = Name::from_string("BoolAnalysis.finSum_cube_split");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("BoolAnalysis.finSum_cube_split must kernel-check: {e:?}"));
    }

    #[test]
    fn test_finsum_cube_split_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.finSum_cube_split");
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
