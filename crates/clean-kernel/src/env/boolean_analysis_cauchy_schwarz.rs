// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — the finite Cauchy-Schwarz inequality, via the
//! constructive Lagrange identity.
//!
//! `Fin.sum_cauchy_schwarz : ∀ (n : Nat) (a b : Fin n → Rat),
//!     Rat.le (Rat.mul (Fin.sum n (fun i => Rat.mul (a i) (b i)))
//!                     (Fin.sum n (fun i => Rat.mul (a i) (b i))))
//!            (Rat.mul (Fin.sum n (fun i => Rat.mul (a i) (a i)))
//!                     (Fin.sum n (fun i => Rat.mul (b i) (b i))))`
//!
//! i.e. `(Σ aᵢbᵢ)² ≤ (Σ aᵢ²)·(Σ bᵢ²)`. Confirmed absent from the entire kernel.
//!
//! Route — the constructive LAGRANGE identity (no completeness / no analysis):
//!
//! 1. The doubled difference is a sum of squares:
//!    `X + X = Σᵢ Σⱼ (aᵢbⱼ − aⱼbᵢ)²`,  where
//!    `X := (Σaᵢ²)(Σbᵢ²) − (Σaᵢbᵢ)²`   (`Fin.sum_lagrange_identity`).
//! 2. The RHS is `≥ 0` — a `Fin.sum_nonneg` of a `Fin.sum_nonneg` of squares
//!    (`Rat.sq_nonneg`)  (`Fin.sum_cauchy_rhs_nonneg`).
//! 3. The doubling-sign helper `0 ≤ d + d → 0 ≤ d`
//!    (`Rat.nonneg_of_add_self_nonneg`) lifts `0 ≤ X + X` to `0 ≤ X`.
//! 4. `Rat.le_of_sub_nonneg` converts `0 ≤ (Σaᵢ²)(Σbᵢ²) − (Σaᵢbᵢ)²` into the
//!    stated `(Σaᵢbᵢ)² ≤ (Σaᵢ²)(Σbᵢ²)`.
//!
//! Every piece is a kernel-checked `Declaration::Theorem` built from the
//! genuinely-`Constructive` Rat ring/order surface and the constructive finite
//! sum engine (`Fin.sum_mul_sum`, `Fin.sum_swap`, `Fin.sum_congr`,
//! `Fin.sum_add`/`Fin.sum_sub`, `Fin.sum_nonneg`, `Rat.sub_sq`, `Rat.sq_nonneg`,
//! the `sub_nonneg`/`le_of_sub_nonneg` bridge). Empty domain-axiom closure ⇒
//! `ProofQuality::Constructive`.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared constants for the Cauchy-Schwarz / Lagrange build. Wraps an
/// `OrderConsts` (Rat, add, mul, sub, neg, le, eq, subst, …) and adds the
/// order lemmas the doubling helper and assembly consume.
pub(super) struct CauchyConsts {
    pub(super) o: OrderConsts,
    le_total: Expr,
    le_refl: Expr,
    le_trans: Expr,
    add_le_add: Expr,
    add_zero: Expr,
    or_c: Expr,
    or_rec: Expr,
    nat: Expr,
    fin: Expr,
    fin_sum: Expr,
    fin_sum_nonneg: Expr,
    sq_nonneg: Expr,
}

impl CauchyConsts {
    pub(super) fn new() -> Self {
        Self {
            o: OrderConsts::new(),
            le_total: Expr::const_(Name::from_string("Rat.le_total"), vec![]),
            le_refl: Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
            le_trans: Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
            add_le_add: Expr::const_(Name::from_string("Rat.add_le_add"), vec![]),
            add_zero: Expr::const_(Name::from_string("Rat.add_zero"), vec![]),
            or_c: Expr::const_(Name::from_string("Or"), vec![]),
            or_rec: Expr::const_(Name::from_string("Or.rec"), vec![]),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_sum_nonneg: Expr::const_(Name::from_string("Fin.sum_nonneg"), vec![]),
            sq_nonneg: Expr::const_(Name::from_string("Rat.sq_nonneg"), vec![]),
        }
    }

    pub(super) fn rat(&self) -> Expr {
        self.o.rat.clone()
    }
    pub(super) fn nat(&self) -> Expr {
        self.nat.clone()
    }
    pub(super) fn zero(&self) -> Expr {
        self.o.rat_zero.clone()
    }
    pub(super) fn add(&self, a: Expr, b: Expr) -> Expr {
        self.o.add(a, b)
    }
    pub(super) fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.o.mul(a, b)
    }
    pub(super) fn sub(&self, a: Expr, b: Expr) -> Expr {
        self.o.sub(a, b)
    }
    pub(super) fn le(&self, a: Expr, b: Expr) -> Expr {
        self.o.rat_le(a, b)
    }

    /// `Fin n`.
    pub(super) fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    /// `Fin.sum n f`.
    pub(super) fn sum(&self, n: Expr, f: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n, f])
    }
    /// `Rat.sq_nonneg t : 0 ≤ t·t`.
    fn sq_nonneg(&self, t: Expr) -> Expr {
        Expr::app(self.sq_nonneg.clone(), t)
    }
    /// `Fin.sum_nonneg n f h : 0 ≤ Fin.sum n f`, where `h : ∀ i, 0 ≤ f i`.
    fn sum_nonneg(&self, n: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(self.fin_sum_nonneg.clone(), [n, f, h])
    }

    /// The Lagrange cross term `aᵢ·bⱼ − aⱼ·bᵢ`.
    pub(super) fn cross(&self, a: &Expr, b: &Expr, i: &Expr, j: &Expr) -> Expr {
        let ai_bj = self.mul(
            Expr::app(a.clone(), i.clone()),
            Expr::app(b.clone(), j.clone()),
        );
        let aj_bi = self.mul(
            Expr::app(a.clone(), j.clone()),
            Expr::app(b.clone(), i.clone()),
        );
        self.sub(ai_bj, aj_bi)
    }
    /// `(aᵢbⱼ − aⱼbᵢ)²` as `cross·cross`.
    pub(super) fn cross_sq(&self, a: &Expr, b: &Expr, i: &Expr, j: &Expr) -> Expr {
        let c = self.cross(a, b, i, j);
        self.mul(c.clone(), c)
    }
    /// `fun (j : Fin n) => (aᵢbⱼ − aⱼbᵢ)²` — the inner-sum integrand at fixed `i`.
    pub(super) fn inner_cross_fn(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        a: &Expr,
        b: &Expr,
        i: &Expr,
    ) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (j_id, j) = d.fresh_local(fin_n.clone());
        let body = self.cross_sq(a, b, i, &j);
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_n, body))
    }
    /// `fun (i : Fin n) => Fin.sum n (inner_cross_fn i)` — the outer integrand.
    pub(super) fn outer_cross_fn(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        a: &Expr,
        b: &Expr,
    ) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let inner = self.inner_cross_fn(&d, n, a, b, &i);
        let body = self.sum(n.clone(), inner);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `fun (i : Fin n) => Rat.mul (f i) (g i)` — the pointwise product integrand
    /// (used for `Σ aᵢbᵢ`, `Σ aᵢ²`, `Σ bᵢ²` in the Lagrange identity / assembly).
    pub(super) fn prod_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, g: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let body = self.mul(Expr::app(f.clone(), i.clone()), Expr::app(g.clone(), i));
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    /// `Rat.le_total a b : Or (a ≤ b) (b ≤ a)`.
    fn le_total(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.le_total.clone(), [a, b])
    }
    /// `Rat.le_refl a : a ≤ a`.
    fn le_refl(&self, a: Expr) -> Expr {
        Expr::app(self.le_refl.clone(), a)
    }
    /// `Rat.le_trans a b c h_ab h_bc : a ≤ c`.
    fn le_trans(&self, a: Expr, b: Expr, cc: Expr, h_ab: Expr, h_bc: Expr) -> Expr {
        Expr::apps(self.le_trans.clone(), [a, b, cc, h_ab, h_bc])
    }
    /// `Rat.add_le_add a b c d h1 h2 : (a + c) ≤ (b + d)`.
    fn add_le_add(&self, a: Expr, b: Expr, cc: Expr, dd: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.add_le_add.clone(), [a, b, cc, dd, h1, h2])
    }
    /// `Rat.add_zero a : a + 0 = a`.
    fn add_zero(&self, a: Expr) -> Expr {
        Expr::app(self.add_zero.clone(), a)
    }

    /// `@Or.rec p q (fun _ => goal) h_left h_right h_or : goal` — non-dependent
    /// `Or` elimination into a Prop `goal`.
    fn or_elim(
        &self,
        parent: &EnvDeclBuilder,
        p: Expr,
        q: Expr,
        goal: Expr,
        h_or: Expr,
        h_left: Expr,
        h_right: Expr,
    ) -> Expr {
        let motive = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let or_ty = Expr::apps(self.or_c.clone(), [p.clone(), q.clone()]);
            let (h_id, _) = m.fresh_local(or_ty.clone());
            m.finish_child(m.mk_lam(h_id, BinderInfo::Default, or_ty, goal))
        };
        Expr::apps(self.or_rec.clone(), [p, q, motive, h_left, h_right, h_or])
    }
}

impl Environment {
    /// `Rat.nonneg_of_add_self_nonneg : ∀ d, Rat.le 0 (Rat.add d d) → Rat.le 0 d`.
    ///
    /// The doubling-sign helper. Case-split on `Rat.le_total d 0`:
    /// - `d ≤ 0`: from the hypothesis `0 ≤ d + d` and `d ≤ d` (`le_refl`) +
    ///   `d ≤ 0`, `Rat.add_le_add` gives `d + d ≤ d + 0`; `Rat.add_zero` rewrites
    ///   `d + 0 → d`, so `d + d ≤ d`; `Rat.le_trans` chains `0 ≤ d + d ≤ d`.
    /// - `0 ≤ d`: immediate.
    ///
    /// Kernel-checked, constructive (empty domain-axiom closure). Idempotent.
    pub(crate) fn register_rat_nonneg_of_add_self_nonneg(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.nonneg_of_add_self_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis_order_toolkit()?;

        let c = CauchyConsts::new();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.rat());
            let hyp = c.le(c.zero(), c.add(d.clone(), d.clone()));
            let concl = c.le(c.zero(), d.clone());
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(d_id, BinderInfo::Default, c.rat(), e);
            b.finish(e)
        };
        let value = build_nonneg_of_add_self_nonneg_proof(&c);

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Fin.sum_cauchy_rhs_nonneg : ∀ (n : Nat) (a b : Fin n → Rat),
    ///   Rat.le 0 (Fin.sum n (fun i => Fin.sum n (fun j => (aᵢbⱼ − aⱼbᵢ)²)))`.
    ///
    /// The RHS of the Lagrange identity is nonneg: a `Fin.sum_nonneg` of a
    /// `Fin.sum_nonneg` of squares. The outer integrand `Σⱼ (cross i j)²` is
    /// nonneg for each `i` (inner `Fin.sum_nonneg` with `Rat.sq_nonneg` on each
    /// `cross i j`), so the outer `Fin.sum_nonneg` applies. Kernel-checked,
    /// constructive. Idempotent.
    pub(crate) fn register_fin_sum_cauchy_rhs_nonneg(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sum_cauchy_rhs_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_fin_sum()?;
        self.init_boolean_analysis_order_toolkit()?; // Rat.sq_nonneg
        {
            use super::nn_verify_fin_sum::FinSumConsts;
            let fc = FinSumConsts::new();
            self.register_fin_sum_nonneg_theorem(&fc)?;
        }

        let c = CauchyConsts::new();
        let (ty, value) = build_rhs_nonneg(&c);
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the type + proof of `Fin.sum_cauchy_rhs_nonneg`.
fn build_rhs_nonneg(c: &CauchyConsts) -> (Expr, Expr) {
    let f_g_ty = |n: &Expr| Expr::pi(BinderInfo::Default, c.fin_of(n), c.rat());

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat());
        let (a_id, a) = b.fresh_local(f_g_ty(&n));
        let (bb_id, bv) = b.fresh_local(f_g_ty(&n));
        let outer = c.outer_cross_fn(&b, &n, &a, &bv);
        let rhs = c.sum(n.clone(), outer);
        let concl = c.le(c.zero(), rhs);
        let e = b.mk_pi(bb_id, BinderInfo::Default, f_g_ty(&n), concl);
        let e = b.mk_pi(a_id, BinderInfo::Default, f_g_ty(&n), e);
        let e = b.mk_pi(n_id, BinderInfo::Default, c.nat(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat());
        let (a_id, a) = b.fresh_local(f_g_ty(&n));
        let (bb_id, bv) = b.fresh_local(f_g_ty(&n));

        let outer = c.outer_cross_fn(&b, &n, &a, &bv);

        // h_outer : ∀ (i : Fin n), 0 ≤ Σⱼ (cross i j)²
        //   := fun i => Fin.sum_nonneg n (inner i) (fun j => sq_nonneg (cross i j))
        let h_outer = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (i_id, i) = d.fresh_local(c.fin_of(&n));
            let inner = c.inner_cross_fn(&d, &n, &a, &bv, &i);
            // h_inner : ∀ (j : Fin n), 0 ≤ (cross i j)²
            let h_inner = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (j_id, j) = e.fresh_local(c.fin_of(&n));
                let body = c.sq_nonneg(c.cross(&a, &bv, &i, &j));
                e.finish_child(e.mk_lam(j_id, BinderInfo::Default, c.fin_of(&n), body))
            };
            let body = c.sum_nonneg(n.clone(), inner, h_inner);
            d.finish_child(d.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), body))
        };
        // Fin.sum_nonneg n outer h_outer : 0 ≤ Σᵢ Σⱼ (cross i j)²
        let proof = c.sum_nonneg(n.clone(), outer, h_outer);

        let e = b.mk_lam(bb_id, BinderInfo::Default, f_g_ty(&n), proof);
        let e = b.mk_lam(a_id, BinderInfo::Default, f_g_ty(&n), e);
        let e = b.mk_lam(n_id, BinderInfo::Default, c.nat(), e);
        b.finish(e)
    };

    (ty, value)
}

/// Proof term for `Rat.nonneg_of_add_self_nonneg`.
fn build_nonneg_of_add_self_nonneg_proof(c: &CauchyConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.rat());
    let dd = c.add(d.clone(), d.clone());
    let hyp = c.le(c.zero(), dd.clone());
    let (h_id, h) = b.fresh_local(hyp.clone());

    let goal = c.le(c.zero(), d.clone());
    let le_d0 = c.le(d.clone(), c.zero());
    let le_0d = c.le(c.zero(), d.clone());

    // le_total d 0 : Or (d ≤ 0) (0 ≤ d)
    let h_total = c.le_total(d.clone(), c.zero());

    // Branch 1: d ≤ 0  ⇒  0 ≤ d
    let branch_neg = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (hd_id, hd) = ch.fresh_local(le_d0.clone());
        // add_le_add d d d 0 (le_refl d) hd : (d + d) ≤ (d + 0)
        let h_dd_le_d0 = c.add_le_add(
            d.clone(),
            d.clone(),
            d.clone(),
            c.zero(),
            c.le_refl(d.clone()),
            hd,
        );
        // add_zero d : d + 0 = d ; subst (fun x => (d + d) ≤ x) → (d + d) ≤ d
        let d_plus_zero = c.add(d.clone(), c.zero());
        let motive = {
            let mut m = EnvDeclBuilder::child_of(&ch);
            let (x_id, x) = m.fresh_local(c.rat());
            let body = c.le(dd.clone(), x);
            m.finish_child(m.mk_lam(x_id, BinderInfo::Default, c.rat(), body))
        };
        let h_dd_le_d = c.o.subst(
            motive,
            d_plus_zero,
            d.clone(),
            c.add_zero(d.clone()),
            h_dd_le_d0,
        );
        // le_trans 0 (d + d) d h h_dd_le_d : 0 ≤ d
        let body = c.le_trans(c.zero(), dd.clone(), d.clone(), h.clone(), h_dd_le_d);
        ch.finish_child(ch.mk_lam(hd_id, BinderInfo::Default, le_d0.clone(), body))
    };

    // Branch 2: 0 ≤ d  ⇒  0 ≤ d  (identity)
    let branch_pos = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (hp_id, hp) = ch.fresh_local(le_0d.clone());
        ch.finish_child(ch.mk_lam(hp_id, BinderInfo::Default, le_0d.clone(), hp))
    };

    let body = c.or_elim(&b, le_d0, le_0d, goal, h_total, branch_neg, branch_pos);
    let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::expr::Expr;
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_rat_nonneg_of_add_self_nonneg()
            .expect("register_rat_nonneg_of_add_self_nonneg should succeed");
        env
    }

    #[test]
    fn test_helper_registered_as_theorem() {
        let env = env();
        let info = env
            .get_const(&Name::from_string("Rat.nonneg_of_add_self_nonneg"))
            .expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
    }

    #[test]
    fn test_helper_type_checks() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("Rat.nonneg_of_add_self_nonneg"),
                vec![],
            ))
            .expect("Rat.nonneg_of_add_self_nonneg should type-check");
    }

    #[test]
    fn test_helper_constructive_axiom_free() {
        let env = env();
        let name = Name::from_string("Rat.nonneg_of_add_self_nonneg");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
    }

    fn rhs_env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_fin_sum_cauchy_rhs_nonneg()
            .expect("register_fin_sum_cauchy_rhs_nonneg should succeed");
        env
    }

    #[test]
    fn test_rhs_nonneg_type_checks() {
        let env = rhs_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("Fin.sum_cauchy_rhs_nonneg"),
                vec![],
            ))
            .expect("Fin.sum_cauchy_rhs_nonneg should type-check");
    }

    #[test]
    fn test_rhs_nonneg_constructive_axiom_free() {
        let env = rhs_env();
        let name = Name::from_string("Fin.sum_cauchy_rhs_nonneg");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
    }
}
