// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C012 Value Builders — Opaque/Definition placeholder values
//!
//! Separated from `nn_verify_relu_stability_defs` for file-size compliance.
//! These builders construct well-typed placeholder values for former
//! Declaration::Axiom entries that have been converted to Declaration::Opaque
//! or Declaration::Definition.
//!
//! All values are verified by the kernel's type checker (`tc.check_type`).
//! Opaque values are not reduced; Definition values are reduced only when
//! `is_reducible` is true.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

use super::nn_verify_relu_stability_defs::C012Consts;

/// Build the Opaque value for `NNVerify.C012.Network`:
/// ```text
/// Nat
/// ```
///
/// Well-typed placeholder: Nat inhabits Type (Sort 1), matching the declared
/// type. Opaque prevents reduction.
pub(super) fn build_network_value() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

/// Build the Opaque value for `NNVerify.C012.pre_activation`:
/// ```text
/// fun (n : Nat) (_ : Network) (x : NNVec n) => x
/// ```
///
/// Well-typed identity placeholder. Opaque prevents reduction.
pub(super) fn build_pre_activation_value(c: &C012Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let (net_id, _) = b.fresh_local(c.network.clone());
    let (x_id, x) = b.fresh_local(vec_n.clone());
    let e = b.mk_lam(x_id, BinderInfo::Default, vec_n, x);
    let e = b.mk_lam(net_id, BinderInfo::Default, c.network.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the Opaque value for `NNVerify.C012.activation_pattern`:
/// ```text
/// fun (n : Nat) (_ : NNVec n) (_ : Fin n) => Bool.false
/// ```
///
/// Well-typed constant-false placeholder. Opaque prevents reduction.
pub(super) fn build_activation_pattern_value(c: &C012Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let fin_n = c.fin_of(&n);
    let (z_id, _) = b.fresh_local(vec_n.clone());
    let (i_id, _) = b.fresh_local(fin_n.clone());
    let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
    let e = b.mk_lam(i_id, BinderInfo::Default, fin_n, bool_false);
    let e = b.mk_lam(z_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the Opaque value for `NNVerify.C012.stability_radius`:
/// ```text
/// fun (n : Nat) (_ : Network) (_ : NNVec n) => Rat.zero
/// ```
///
/// Well-typed Rat.zero placeholder. Opaque prevents reduction.
pub(super) fn build_stability_radius_value(c: &C012Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let (net_id, _) = b.fresh_local(c.network.clone());
    let (x0_id, _) = b.fresh_local(vec_n.clone());
    let e = b.mk_lam(x0_id, BinderInfo::Default, vec_n, c.rat_zero.clone());
    let e = b.mk_lam(net_id, BinderInfo::Default, c.network.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the Opaque value for `NNVerify.C012.perturbation_ball`:
/// ```text
/// fun (n : Nat) (_ : NNVec n) (_ : Rat) =>
///   IntervalBounds.mk @n (fun _ => Rat.zero) (fun _ => Rat.zero)
///                        (fun _ => Rat.le_refl Rat.zero)
/// ```
///
/// Well-typed zero-IntervalBounds placeholder. The validity proof is
/// `fun (_ : Fin n) => Rat.le_refl Rat.zero`, which proves
/// `forall i, Rat.zero <= Rat.zero`. Opaque prevents reduction.
pub(super) fn build_perturbation_ball_value(c: &C012Consts) -> Expr {
    let ib_mk = Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]);
    let le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let fin_n = c.fin_of(&n);
    let (x0_id, _) = b.fresh_local(vec_n.clone());
    let (eps_id, _) = b.fresh_local(c.rat.clone());

    // lower = fun (_ : Fin n) => Rat.zero
    let zero_vec = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (i_id, _) = ch.fresh_local(fin_n.clone());
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), c.rat_zero.clone());
        ch.finish_child(r)
    };
    // valid = fun (_ : Fin n) => Rat.le_refl Rat.zero
    let valid = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (i_id, _) = ch.fresh_local(fin_n.clone());
        let proof = Expr::app(le_refl, c.rat_zero.clone());
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_n, proof);
        ch.finish_child(r)
    };
    // IntervalBounds.mk @n zero_vec zero_vec valid
    let ib_val = Expr::apps(ib_mk, [n.clone(), zero_vec.clone(), zero_vec, valid]);

    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), ib_val);
    let e = b.mk_lam(x0_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the Opaque value for `NNVerify.C012.crown_relaxation_gap`:
/// ```text
/// fun (n : Nat) (_ : Network) (_ : IntervalBounds n) => Rat.zero
/// ```
///
/// Well-typed Rat.zero placeholder. Opaque prevents reduction.
pub(super) fn build_crown_relaxation_gap_value(c: &C012Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let ib_n = c.ib_of(&n);
    let (net_id, _) = b.fresh_local(c.network.clone());
    let (bnd_id, _) = b.fresh_local(ib_n.clone());
    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, c.rat_zero.clone());
    let e = b.mk_lam(net_id, BinderInfo::Default, c.network.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the Definition value for `NNVerify.C012.pattern_stable`:
/// ```text
/// fun (n : Nat) (_ : Network) (_ : NNVec n) (_ : Rat) => True
/// ```
///
/// Well-typed Prop body (True). The actual semantics would require forall-
/// quantification over the perturbation ball, which depends on NNVec
/// membership infrastructure not yet in the kernel.
pub(super) fn build_pattern_stable_value(c: &C012Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let (net_id, _) = b.fresh_local(c.network.clone());
    let (x0_id, _) = b.fresh_local(vec_n.clone());
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let true_const = Expr::const_(Name::from_string("True"), vec![]);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), true_const);
    let e = b.mk_lam(x0_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(net_id, BinderInfo::Default, c.network.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the Definition value for `NNVerify.C012.single_lp_form`:
/// ```text
/// fun (n : Nat) (_ : Network) (_ : NNVec n) (_ : Rat) => True
/// ```
///
/// Well-typed Prop body (True). The actual semantics would require LP
/// formalization not yet in the kernel.
pub(super) fn build_single_lp_form_value(c: &C012Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let (net_id, _) = b.fresh_local(c.network.clone());
    let (x0_id, _) = b.fresh_local(vec_n.clone());
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let true_const = Expr::const_(Name::from_string("True"), vec![]);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), true_const);
    let e = b.mk_lam(x0_id, BinderInfo::Default, vec_n, e);
    let e = b.mk_lam(net_id, BinderInfo::Default, c.network.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
