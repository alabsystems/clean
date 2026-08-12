// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type builders for C003 ECLipsE convergence rate declarations.
//!
//! NOTE: This file builds types for axiom-wrapping theorem declarations,
//! not genuine proofs. The theorem types defined here are used for both
//! the `_axiom` (Declaration::Axiom) and the wrapper (Declaration::Theorem)
//! entries. See nn_verify_eclipse_convergence.rs for the full axiom-dependent
//! status of C003.
//!
//! Contains the `ConvergenceConsts` shared constants and `build_*` functions
//! for definition types and theorem types. Split from
//! `nn_verify_eclipse_convergence.rs` for the 500-line file limit.
//!
//! Part of #3311, Part of #3150.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Constants for ECLipsE convergence formalization.
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(super) struct ConvergenceConsts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) type0: Expr,
    #[cfg(test)]
    pub(super) prop: Expr,
    pub(super) nn_vec: Expr,
    pub(super) rat_mul: Expr,
    pub(super) rat_one: Expr,
    pub(super) rat_zero: Expr,
    pub(super) le_le: Expr,
    pub(super) lt_lt: Expr,
    pub(super) inst_le_rat: Expr,
    pub(super) inst_lt_rat: Expr,
    pub(super) and: Expr,
    pub(super) lipschitz_constant: Expr,
    pub(super) rat_pow: Expr,
    pub(super) width: Expr,
    pub(super) refine_op: Expr,
    #[cfg(test)]
    pub(super) log_rat: Expr,
}

impl ConvergenceConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            #[cfg(test)]
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            lt_lt: Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            inst_lt_rat: Expr::const_(Name::from_string("instLTRat"), vec![]),
            and: Expr::const_(Name::from_string("And"), vec![]),
            lipschitz_constant: Expr::const_(
                Name::from_string("NNVerify.Lipschitz.constant"),
                vec![],
            ),
            rat_pow: Expr::const_(Name::from_string("NNVerify.ECLipsE.rat_pow"), vec![]),
            width: Expr::const_(Name::from_string("NNVerify.ECLipsE.width"), vec![]),
            refine_op: Expr::const_(Name::from_string("NNVerify.ECLipsE.refine_op"), vec![]),
            #[cfg(test)]
            log_rat: Expr::const_(Name::from_string("NNVerify.ECLipsE.log_rat"), vec![]),
        }
    }

    pub(super) fn vec_of(&self, n: &Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n.clone())
    }

    pub(super) fn endo_ty(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.vec_of(n), self.vec_of(n))
    }

    pub(super) fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.le_le.clone(), self.rat.clone()),
                    self.inst_le_rat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    pub(super) fn rat_lt(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.lt_lt.clone(), self.rat.clone()),
                    self.inst_lt_rat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    pub(super) fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_mul.clone(), a), b)
    }

    pub(super) fn pow(&self, base: Expr, exp: Expr) -> Expr {
        Expr::app(Expr::app(self.rat_pow.clone(), base), exp)
    }
}

// =============================================================================
// Type builders for definitions
// =============================================================================

/// `NNVerify.ECLipsE.rat_pow : Rat -> Nat -> Rat`
pub(super) fn build_rat_pow_type(c: &ConvergenceConsts) -> Expr {
    Expr::pi(
        BinderInfo::Default,
        c.rat.clone(),
        Expr::pi(BinderInfo::Default, c.nat.clone(), c.rat.clone()),
    )
}

/// `NNVerify.ECLipsE.width : Nat -> Nat -> (NNVec n -> NNVec n) -> Rat -> Rat`
pub(super) fn build_width_type(c: &ConvergenceConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, _) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (t_id, _) = b.fresh_local(endo.clone());
    let (w0_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(w0_id, BinderInfo::Default, c.rat.clone(), c.rat.clone());
    let e = b.mk_pi(t_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.ECLipsE.refine_op : Nat -> Type`
pub(super) fn build_refine_op_type(c: &ConvergenceConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.nat.clone(), c.type0.clone())
}

/// `NNVerify.ECLipsE.refine_apply : (n : Nat) -> refine_op n -> NNVec n -> NNVec n`
pub(super) fn build_refine_apply_type(c: &ConvergenceConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let op_n = Expr::app(c.refine_op.clone(), n.clone());
    let (op_id, _) = b.fresh_local(op_n.clone());
    let vec_n = c.vec_of(&n);
    let e = b.mk_pi(
        op_id,
        BinderInfo::Default,
        op_n,
        Expr::pi(BinderInfo::Default, vec_n.clone(), vec_n),
    );
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.ECLipsE.log_rat : Rat -> Rat`
pub(super) fn build_log_rat_type(c: &ConvergenceConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.rat.clone(), c.rat.clone())
}

/// `NNVerify.ECLipsE.ceil_nat : Rat -> Nat`
pub(super) fn build_ceil_nat_type(c: &ConvergenceConsts) -> Expr {
    Expr::pi(BinderInfo::Default, c.rat.clone(), c.nat.clone())
}

// =============================================================================
// Type builders for theorems
// =============================================================================

/// C003a: `eclipse_geometric_decay`
///
/// ```text
/// forall (n : Nat) (T : NNVec n -> NNVec n) (L : Rat) (w0 : Rat) (k : Nat),
///   Lipschitz.constant n T L ->
///   0 <= L -> L < 1 ->
///   0 <= w0 ->
///   width n k T w0 <= rat_pow L k * w0
/// ```
pub(super) fn build_geometric_decay_type(c: &ConvergenceConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (t_id, t) = b.fresh_local(endo.clone());
    let (l_id, l) = b.fresh_local(c.rat.clone());
    let (w0_id, w0) = b.fresh_local(c.rat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());

    let hyp_lip = Expr::apps(
        c.lipschitz_constant.clone(),
        [n.clone(), t.clone(), l.clone()],
    );
    let (h1_id, _) = b.fresh_local(hyp_lip.clone());
    let hyp_nonneg = c.rat_le(c.rat_zero.clone(), l.clone());
    let (h2_id, _) = b.fresh_local(hyp_nonneg.clone());
    let hyp_lt_one = c.rat_lt(l.clone(), c.rat_one.clone());
    let (h3_id, _) = b.fresh_local(hyp_lt_one.clone());
    let hyp_w0 = c.rat_le(c.rat_zero.clone(), w0.clone());
    let (h4_id, _) = b.fresh_local(hyp_w0.clone());

    let lhs = Expr::apps(c.width.clone(), [n.clone(), k.clone(), t, w0.clone()]);
    let rhs = c.mul(c.pow(l, k), w0);
    let concl = c.rat_le(lhs, rhs);

    let e = b.mk_pi(h4_id, BinderInfo::Default, hyp_w0, concl);
    let e = b.mk_pi(h3_id, BinderInfo::Default, hyp_lt_one, e);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_nonneg, e);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_lip, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(w0_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(l_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(t_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// C003b: `eclipse_termination_bound`
///
/// ```text
/// forall (n : Nat) (T : NNVec n -> NNVec n) (L w0 eps : Rat) (k : Nat),
///   Lipschitz.constant n T L ->
///   0 <= L -> L < 1 -> 0 < w0 -> 0 < eps ->
///   rat_pow L k * w0 <= eps ->
///   width n k T w0 <= eps
/// ```
pub(super) fn build_termination_bound_type(c: &ConvergenceConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (t_id, t) = b.fresh_local(endo.clone());
    let (l_id, l) = b.fresh_local(c.rat.clone());
    let (w0_id, w0) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let hyp_lip = Expr::apps(
        c.lipschitz_constant.clone(),
        [n.clone(), t.clone(), l.clone()],
    );
    let (h1_id, _) = b.fresh_local(hyp_lip.clone());
    let hyp_nonneg = c.rat_le(c.rat_zero.clone(), l.clone());
    let (h2_id, _) = b.fresh_local(hyp_nonneg.clone());
    let hyp_lt_one = c.rat_lt(l.clone(), c.rat_one.clone());
    let (h3_id, _) = b.fresh_local(hyp_lt_one.clone());
    let hyp_w0 = c.rat_lt(c.rat_zero.clone(), w0.clone());
    let (h4_id, _) = b.fresh_local(hyp_w0.clone());
    let hyp_eps = c.rat_lt(c.rat_zero.clone(), eps.clone());
    let (h5_id, _) = b.fresh_local(hyp_eps.clone());

    let (k_id, k) = b.fresh_local(c.nat.clone());
    let lk_w0 = c.mul(c.pow(l, k.clone()), w0.clone());
    let hyp_pow_bound = c.rat_le(lk_w0, eps.clone());
    let (h6_id, _) = b.fresh_local(hyp_pow_bound.clone());

    let width_k = Expr::apps(c.width.clone(), [n.clone(), k, t, w0]);
    let concl = c.rat_le(width_k, eps);

    let e = b.mk_pi(h6_id, BinderInfo::Default, hyp_pow_bound, concl);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(h5_id, BinderInfo::Default, hyp_eps, e);
    let e = b.mk_pi(h4_id, BinderInfo::Default, hyp_w0, e);
    let e = b.mk_pi(h3_id, BinderInfo::Default, hyp_lt_one, e);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_nonneg, e);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_lip, e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(w0_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(l_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(t_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// C003c: `eclipse_fixed_point` (Banach contraction mapping theorem)
///
/// ```text
/// forall (n : Nat) (T : NNVec n -> NNVec n) (L : Rat),
///   Lipschitz.constant n T L -> 0 <= L -> L < 1 ->
///   Exists (fun x : NNVec n => And (T x = x) (forall y, T y = y -> x = y))
/// ```
pub(super) fn build_fixed_point_type(c: &ConvergenceConsts) -> Expr {
    let eq_ = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let exists_ = Expr::const_(
        Name::from_string("Exists"),
        vec![Level::succ(Level::zero())],
    );

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (t_id, t) = b.fresh_local(endo.clone());
    let (l_id, l) = b.fresh_local(c.rat.clone());

    let hyp_lip = Expr::apps(
        c.lipschitz_constant.clone(),
        [n.clone(), t.clone(), l.clone()],
    );
    let (h1_id, _) = b.fresh_local(hyp_lip.clone());
    let hyp_nonneg = c.rat_le(c.rat_zero.clone(), l.clone());
    let (h2_id, _) = b.fresh_local(hyp_nonneg.clone());
    let hyp_lt_one = c.rat_lt(l.clone(), c.rat_one.clone());
    let (h3_id, _) = b.fresh_local(hyp_lt_one.clone());

    let vec_n = c.vec_of(&n);

    let body = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(vec_n.clone());
        let t_x = Expr::app(t.clone(), x.clone());
        let eq_tx_x = Expr::apps(eq_.clone(), [vec_n.clone(), t_x, x.clone()]);

        let uniq = {
            let mut ch2 = EnvDeclBuilder::child_of(&ch);
            let (y_id, y) = ch2.fresh_local(vec_n.clone());
            let t_y = Expr::app(t.clone(), y.clone());
            let eq_ty_y = Expr::apps(eq_.clone(), [vec_n.clone(), t_y, y.clone()]);
            let (hy_id, _) = ch2.fresh_local(eq_ty_y.clone());
            let eq_xy = Expr::apps(eq_.clone(), [vec_n.clone(), x.clone(), y]);
            let r = ch2.mk_pi(hy_id, BinderInfo::Default, eq_ty_y, eq_xy);
            let r = ch2.mk_pi(y_id, BinderInfo::Default, vec_n.clone(), r);
            ch2.finish_child(r)
        };

        let conj = Expr::app(Expr::app(c.and.clone(), eq_tx_x), uniq);
        let lam = ch.mk_lam(x_id, BinderInfo::Default, vec_n.clone(), conj);
        ch.finish_child(lam)
    };

    let concl = Expr::app(Expr::app(exists_.clone(), vec_n), body);

    let e = b.mk_pi(h3_id, BinderInfo::Default, hyp_lt_one, concl);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_nonneg, e);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_lip, e);
    let e = b.mk_pi(l_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(t_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// C003d: `eclipse_contraction_compose`
///
/// ```text
/// forall (n : Nat) (S T : NNVec n -> NNVec n) (Ls Lt : Rat),
///   Lipschitz.constant n S Ls -> Lipschitz.constant n T Lt ->
///   0 <= Ls -> Ls < 1 -> 0 <= Lt -> Lt < 1 ->
///   And (Lipschitz.constant n (fun x => S (T x)) (Ls * Lt)) (Ls * Lt < 1)
/// ```
pub(super) fn build_contraction_compose_type(c: &ConvergenceConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (s_id, s) = b.fresh_local(endo.clone());
    let (t_id, t) = b.fresh_local(endo.clone());
    let (ls_id, ls) = b.fresh_local(c.rat.clone());
    let (lt_id, lt) = b.fresh_local(c.rat.clone());

    let hyp_s = Expr::apps(
        c.lipschitz_constant.clone(),
        [n.clone(), s.clone(), ls.clone()],
    );
    let (h1_id, _) = b.fresh_local(hyp_s.clone());
    let hyp_t = Expr::apps(
        c.lipschitz_constant.clone(),
        [n.clone(), t.clone(), lt.clone()],
    );
    let (h2_id, _) = b.fresh_local(hyp_t.clone());
    let hyp_ls_nn = c.rat_le(c.rat_zero.clone(), ls.clone());
    let (h3_id, _) = b.fresh_local(hyp_ls_nn.clone());
    let hyp_ls_lt1 = c.rat_lt(ls.clone(), c.rat_one.clone());
    let (h4_id, _) = b.fresh_local(hyp_ls_lt1.clone());
    let hyp_lt_nn = c.rat_le(c.rat_zero.clone(), lt.clone());
    let (h5_id, _) = b.fresh_local(hyp_lt_nn.clone());
    let hyp_lt_lt1 = c.rat_lt(lt.clone(), c.rat_one.clone());
    let (h6_id, _) = b.fresh_local(hyp_lt_lt1.clone());

    let vec_n = c.vec_of(&n);
    let comp = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(vec_n.clone());
        let body = Expr::app(s, Expr::app(t, x));
        let r = ch.mk_lam(x_id, BinderInfo::Default, vec_n.clone(), body);
        ch.finish_child(r)
    };

    let prod = c.mul(ls.clone(), lt.clone());
    let lip_comp = Expr::apps(
        c.lipschitz_constant.clone(),
        [n.clone(), comp, prod.clone()],
    );
    let prod_lt1 = c.rat_lt(prod, c.rat_one.clone());
    let concl = Expr::app(Expr::app(c.and.clone(), lip_comp), prod_lt1);

    let e = b.mk_pi(h6_id, BinderInfo::Default, hyp_lt_lt1, concl);
    let e = b.mk_pi(h5_id, BinderInfo::Default, hyp_lt_nn, e);
    let e = b.mk_pi(h4_id, BinderInfo::Default, hyp_ls_lt1, e);
    let e = b.mk_pi(h3_id, BinderInfo::Default, hyp_ls_nn, e);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp_t, e);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp_s, e);
    let e = b.mk_pi(lt_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(ls_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(t_id, BinderInfo::Default, endo.clone(), e);
    let e = b.mk_pi(s_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
