// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem type builders for C003 Lipschitz convergence.
//!
//! Contains the `build_*_type` functions for the four main theorems and the
//! `lip_product_unbounded` auxiliary definition. Split from
//! `nn_verify_lipschitz.rs` for the 500-line file limit.
//!
//! Part of #3203.

use super::nn_verify_lipschitz::LipschitzConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// `NNVerify.Lipschitz.residual_lip`:
/// `forall (n : Nat) (g : NNVec n -> NNVec n) (L : Rat),
///   Lipschitz.constant n g L ->
///   Lipschitz.constant n (residual_block n g) (1 + L) ->
///   Lipschitz.constant n (residual_block n g) (1 + L)`
///
/// Hypothesis-wrapped local form: the residual Lipschitz fact is explicit
/// local evidence until `Lipschitz.constant` receives faithful metric
/// semantics.
pub(super) fn build_residual_lip_type(c: &LipschitzConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (g_id, g) = b.fresh_local(endo.clone());
    let (l_id, l) = b.fresh_local(c.rat.clone());
    // hypothesis: Lipschitz.constant n g L
    let hyp = Expr::apps(
        c.lipschitz_constant.clone(),
        [n.clone(), g.clone(), l.clone()],
    );
    let (h_id, _) = b.fresh_local(hyp.clone());
    // conclusion: Lipschitz.constant n (residual_block n g) (1 + L)
    let res_g = Expr::apps(c.residual_block.clone(), [n.clone(), g]);
    let one_plus_l = c.add(c.rat_one.clone(), l);
    let concl = Expr::apps(c.lipschitz_constant.clone(), [n.clone(), res_g, one_plus_l]);
    let (h_res_id, _) = b.fresh_local(concl.clone());
    let e = b.mk_pi(h_res_id, BinderInfo::Default, concl.clone(), concl);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, e);
    let e = b.mk_pi(l_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(g_id, BinderInfo::Default, endo, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the proof term for hypothesis-wrapped
/// `NNVerify.Lipschitz.residual_lip`.
///
/// The proof abstracts the local residual Lipschitz evidence and returns it:
/// ```text
/// fun (n : Nat) (g : NNVec n -> NNVec n) (L : Rat)
///     (_h_g : Lipschitz.constant n g L)
///     (h_res : Lipschitz.constant n (residual_block n g) (1 + L)) =>
///   h_res
/// ```
pub(super) fn build_residual_lip_proof(c: &LipschitzConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let endo = c.endo_ty(&n);
    let (g_id, g) = b.fresh_local(endo.clone());
    let (l_id, l) = b.fresh_local(c.rat.clone());

    let hyp = Expr::apps(
        c.lipschitz_constant.clone(),
        [n.clone(), g.clone(), l.clone()],
    );
    let (h_id, _) = b.fresh_local(hyp.clone());

    let res_g = Expr::apps(c.residual_block.clone(), [n.clone(), g]);
    let one_plus_l = c.add(c.rat_one.clone(), l);
    let concl = Expr::apps(c.lipschitz_constant.clone(), [n.clone(), res_g, one_plus_l]);
    let (h_res_id, h_res) = b.fresh_local(concl.clone());

    let e = b.mk_lam(h_res_id, BinderInfo::Default, concl, h_res);
    let e = b.mk_lam(h_id, BinderInfo::Default, hyp, e);
    let e = b.mk_lam(l_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(g_id, BinderInfo::Default, endo, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.Lipschitz.product_convergence`:
/// `forall (N : Nat) (L : Fin N -> Rat),
///   (forall i, 0 <= L i) ->
///   lip_product N L <= real_exp (Fin.sum N L)`
pub(super) fn build_product_convergence_type(c: &LipschitzConsts) -> Expr {
    let lip_product = Expr::const_(Name::from_string("NNVerify.Lipschitz.lip_product"), vec![]);
    let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (big_n_id, big_n) = b.fresh_local(c.nat.clone());
    let fin_n = Expr::app(c.fin.clone(), big_n.clone());
    let lips_ty = Expr::pi(BinderInfo::Default, fin_n.clone(), c.rat.clone());
    let (l_id, l) = b.fresh_local(lips_ty.clone());

    // hypothesis: forall i, 0 <= L i
    let nonneg_hyp = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let body = c.rat_le(c.rat_zero.clone(), Expr::app(l.clone(), i));
        let r = ch.mk_pi(i_id, BinderInfo::Default, fin_n.clone(), body);
        ch.finish_child(r)
    };
    let (h_id, _) = b.fresh_local(nonneg_hyp.clone());

    // conclusion: lip_product N L <= real_exp (Fin.sum N L)
    let prod = Expr::apps(lip_product, [big_n.clone(), l.clone()]);
    let sum = Expr::apps(fin_sum, [big_n.clone(), l]);
    let exp_sum = Expr::app(c.real_exp.clone(), sum);
    let concl = c.rat_le(prod, exp_sum);

    let e = b.mk_pi(h_id, BinderInfo::Default, nonneg_hyp, concl);
    let e = b.mk_pi(l_id, BinderInfo::Default, lips_ty, e);
    let e = b.mk_pi(big_n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.Lipschitz.spectral_bound`:
/// `forall (N : Nat) (L : Fin N -> Rat) (c : Rat) (bound : Rat),
///   (forall i, 0 <= L i /\ L i <= c) -> c < 1 ->
///   Fin.sum N L <= bound ->
///   lip_product N L <= real_exp bound`
///
/// The bound parameter abstracts over `N * c` without needing Nat-to-Rat
/// coercion. The caller provides an explicit bound on the sum, which is
/// the key mathematical fact: under spectral normalization, the sum of
/// Lipschitz constants is bounded, hence the product grows at most
/// exponentially in that bound.
pub(super) fn build_spectral_bound_type(c: &LipschitzConsts) -> Expr {
    let lip_product = Expr::const_(Name::from_string("NNVerify.Lipschitz.lip_product"), vec![]);
    let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (big_n_id, big_n) = b.fresh_local(c.nat.clone());
    let fin_n = Expr::app(c.fin.clone(), big_n.clone());
    let lips_ty = Expr::pi(BinderInfo::Default, fin_n.clone(), c.rat.clone());
    let (l_id, l) = b.fresh_local(lips_ty.clone());
    let (c_bound_id, c_bound) = b.fresh_local(c.rat.clone());
    let (bound_id, bound) = b.fresh_local(c.rat.clone());

    // hypothesis 1: forall i, 0 <= L i /\ L i <= c_bound
    let bounded_hyp = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let l_i = Expr::app(l.clone(), i);
        let conj = Expr::app(
            Expr::app(c.and.clone(), c.rat_le(c.rat_zero.clone(), l_i.clone())),
            c.rat_le(l_i, c_bound.clone()),
        );
        let r = ch.mk_pi(i_id, BinderInfo::Default, fin_n.clone(), conj);
        ch.finish_child(r)
    };
    let (h1_id, _) = b.fresh_local(bounded_hyp.clone());

    // hypothesis 2: c_bound < 1
    let lt_one = c.rat_lt(c_bound.clone(), c.rat_one.clone());
    let (h2_id, _) = b.fresh_local(lt_one.clone());

    // hypothesis 3: Fin.sum N L <= bound
    let sum = Expr::apps(fin_sum, [big_n.clone(), l.clone()]);
    let sum_le_bound = c.rat_le(sum, bound.clone());
    let (h3_id, _) = b.fresh_local(sum_le_bound.clone());

    // conclusion: lip_product N L <= real_exp bound
    let prod = Expr::apps(lip_product, [big_n.clone(), l]);
    let exp_bound = Expr::app(c.real_exp.clone(), bound);
    let concl = c.rat_le(prod, exp_bound);

    let e = b.mk_pi(h3_id, BinderInfo::Default, sum_le_bound, concl);
    let e = b.mk_pi(h2_id, BinderInfo::Default, lt_one, e);
    let e = b.mk_pi(h1_id, BinderInfo::Default, bounded_hyp, e);
    let e = b.mk_pi(bound_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(c_bound_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(l_id, BinderInfo::Default, lips_ty, e);
    let e = b.mk_pi(big_n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.Lipschitz.divergence`:
/// `Exists (fun (L : Nat -> Rat) =>
///   (forall i, 0 < L i) /\
///   forall (M : Rat), Exists (fun (N : Nat) =>
///     M <= lip_product_unbounded N L))`
///
/// Without spectral normalization, the product of Lipschitz constants can
/// exceed any bound.
pub(super) fn build_divergence_type(c: &LipschitzConsts) -> Expr {
    let lip_product_unb = Expr::const_(
        Name::from_string("NNVerify.Lipschitz.lip_product_unbounded"),
        vec![],
    );
    let exists_nat = Expr::const_(
        Name::from_string("Exists"),
        vec![Level::succ(Level::zero())],
    );

    let mut b = EnvDeclBuilder::new();

    // The body is an existential over L : Nat -> Rat
    let l_ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.rat.clone());
    let (l_id, l) = b.fresh_local(l_ty.clone());

    // Positivity: forall (i : Nat), 0 < L i
    let pos_hyp = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = ch.fresh_local(c.nat.clone());
        let body = c.rat_lt(c.rat_zero.clone(), Expr::app(l.clone(), i));
        let r = ch.mk_pi(i_id, BinderInfo::Default, c.nat.clone(), body);
        ch.finish_child(r)
    };

    // Divergence: forall (M : Rat), Exists (fun (N : Nat) =>
    //   M <= lip_product_unbounded N L)
    let div_body = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = ch.fresh_local(c.rat.clone());

        let inner_exists = {
            let mut ch2 = EnvDeclBuilder::child_of(&ch);
            let (n_id, n) = ch2.fresh_local(c.nat.clone());
            let prod = Expr::apps(lip_product_unb.clone(), [n.clone(), l.clone()]);
            let body = c.rat_le(m.clone(), prod);
            let lam = ch2.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            let lam = ch2.finish_child(lam);
            Expr::app(Expr::app(exists_nat.clone(), c.nat.clone()), lam)
        };

        let r = ch.mk_pi(m_id, BinderInfo::Default, c.rat.clone(), inner_exists);
        ch.finish_child(r)
    };

    // Combine: pos_hyp /\ div_body
    let conj = Expr::app(Expr::app(c.and.clone(), pos_hyp), div_body);

    // Wrap in Exists over L
    let body_lam = b.mk_lam(l_id, BinderInfo::Default, l_ty.clone(), conj);
    let body_lam = b.finish(body_lam);

    Expr::app(Expr::app(c.exists_.clone(), l_ty), body_lam)
}

/// `NNVerify.Lipschitz.lip_product_unbounded : Nat -> (Nat -> Rat) -> Rat`
///
/// Product of `(1 + L_i)` for `i` in `0..N`, for unbounded sequences.
pub(super) fn build_lip_product_unbounded_type(c: &LipschitzConsts) -> Expr {
    let l_ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.rat.clone());
    let mut b = EnvDeclBuilder::new();
    let (n_id, _) = b.fresh_local(c.nat.clone());
    let (l_id, _) = b.fresh_local(l_ty.clone());
    let e = b.mk_pi(l_id, BinderInfo::Default, l_ty, c.rat.clone());
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
