// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C009 Definition Types and Opaque Values
//!
//! Type builders and placeholder values for the 10 support-object declarations
//! that were formerly axioms. These are definitions and opaques — they describe
//! the *setup* of the CROWN-vs-IBP comparison (network family, depth parameter,
//! weight matrices, width functions), not the mathematical claims themselves.
//!
//! ## Classification
//!
//! | Declaration | Category | Reason |
//! |---|---|---|
//! | C009ReLUNetwork | Definition | Type constructor for depth-indexed network family |
//! | c009_depth | Definition | Configuration: network depth N |
//! | c009_contraction_factor | Definition | Configuration: per-layer contraction ratio r |
//! | c009_input_radius | Opaque | Input perturbation radius epsilon |
//! | c009_weight_matrices | Opaque | Weight matrix sequence W_1, ..., W_N |
//! | c009_relu_relaxation_slopes | Opaque | Diagonal ReLU relaxation slopes alpha_i |
//! | c009_effective_crown_matrix | Opaque | Combined CROWN backsubstitution matrix |
//! | c009_ibp_width | Opaque | IBP output width as function of depth |
//! | c009_crown_width | Opaque | CROWN output width as function of depth |
//! | c009_crown_ibp_ratio | Opaque | Ratio crown_width / ibp_width |
//!
//! Part of #3371.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for C009 type construction.
pub(super) struct C009Consts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) prop: Expr,
    pub(super) rat_zero: Expr,
    pub(super) nat_zero: Expr,
    pub(super) true_const: Expr,
    pub(super) type0: Expr,
}

impl C009Consts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            true_const: Expr::const_(Name::from_string("True"), vec![]),
            type0: Expr::sort(Level::succ(Level::zero())),
        }
    }
}

// =============================================================================
// Definition type builders (3 Definitions)
// =============================================================================

/// `NNVerification.C009ReLUNetwork : Nat -> Type`
///
/// A depth-indexed ReLU network family. Given depth N, produces the type of
/// networks with N layers.
pub(super) fn build_relu_network_type(c: &C009Consts) -> Expr {
    // Nat -> Type 0
    Expr::pi(BinderInfo::Default, c.nat.clone(), c.type0.clone())
}

/// `NNVerification.C009ReLUNetwork` value: `fun _ => True`
///
/// Placeholder: in a real formalization this would be a structure type
/// containing weight matrices, bias vectors, and activation functions.
pub(super) fn build_relu_network_value(c: &C009Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, _) = b.fresh_local(c.nat.clone());
    // Return Prop (a valid Type) as placeholder
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), c.prop.clone());
    b.finish(e)
}

/// `NNVerification.c009_depth : Nat`
pub(super) fn build_depth_type(c: &C009Consts) -> Expr {
    c.nat.clone()
}

/// `NNVerification.c009_depth` value: `Nat.zero`
pub(super) fn build_depth_value(c: &C009Consts) -> Expr {
    c.nat_zero.clone()
}

/// `NNVerification.c009_contraction_factor : Rat`
///
/// The per-layer contraction ratio 0 < r < 1.
pub(super) fn build_contraction_factor_type(c: &C009Consts) -> Expr {
    c.rat.clone()
}

/// `NNVerification.c009_contraction_factor` value: `Rat.zero`
pub(super) fn build_contraction_factor_value(c: &C009Consts) -> Expr {
    c.rat_zero.clone()
}

// =============================================================================
// Opaque type builders (7 Opaques)
// =============================================================================

/// `NNVerification.c009_input_radius : Rat`
pub(super) fn build_input_radius_type(c: &C009Consts) -> Expr {
    c.rat.clone()
}

/// `NNVerification.c009_input_radius` value: `Rat.zero`
pub(super) fn build_input_radius_value(c: &C009Consts) -> Expr {
    c.rat_zero.clone()
}

/// `NNVerification.c009_weight_matrices : Nat -> Nat -> Prop`
///
/// Sequence of weight matrices indexed by layer. In the full formalization
/// this would be `Nat -> Matrix m n Rat`, but we use `Nat -> Nat -> Prop`
/// as a stand-in (the exact matrix type is not needed for the theorem structure).
pub(super) fn build_weight_matrices_type(c: &C009Consts) -> Expr {
    // Nat -> Nat -> Prop
    Expr::pi(
        BinderInfo::Default,
        c.nat.clone(),
        Expr::pi(BinderInfo::Default, c.nat.clone(), c.prop.clone()),
    )
}

/// `NNVerification.c009_weight_matrices` value: `fun _ _ => True`
pub(super) fn build_weight_matrices_value(c: &C009Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (i_id, _) = b.fresh_local(c.nat.clone());
    let (j_id, _) = b.fresh_local(c.nat.clone());
    let e = b.mk_lam(
        j_id,
        BinderInfo::Default,
        c.nat.clone(),
        c.true_const.clone(),
    );
    let e = b.mk_lam(i_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerification.c009_relu_relaxation_slopes : Nat -> Prop`
///
/// Diagonal ReLU relaxation slopes alpha_i for each layer.
pub(super) fn build_relu_relaxation_slopes_type(c: &C009Consts) -> Expr {
    // Nat -> Prop
    Expr::pi(BinderInfo::Default, c.nat.clone(), c.prop.clone())
}

/// `NNVerification.c009_relu_relaxation_slopes` value: `fun _ => True`
pub(super) fn build_relu_relaxation_slopes_value(c: &C009Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (i_id, _) = b.fresh_local(c.nat.clone());
    let e = b.mk_lam(
        i_id,
        BinderInfo::Default,
        c.nat.clone(),
        c.true_const.clone(),
    );
    b.finish(e)
}

/// `NNVerification.c009_effective_crown_matrix : Prop`
///
/// The combined CROWN backsubstitution matrix product W_N * diag(alpha) * ... * W_1.
/// Typed as Prop since we don't have a concrete matrix type in scope.
pub(super) fn build_effective_crown_matrix_type(c: &C009Consts) -> Expr {
    c.prop.clone()
}

/// `NNVerification.c009_effective_crown_matrix` value: `True`
pub(super) fn build_effective_crown_matrix_value(c: &C009Consts) -> Expr {
    c.true_const.clone()
}

/// `NNVerification.c009_ibp_width : Nat -> Rat`
///
/// IBP output width as a function of network depth.
pub(super) fn build_ibp_width_type(c: &C009Consts) -> Expr {
    // Nat -> Rat
    Expr::pi(BinderInfo::Default, c.nat.clone(), c.rat.clone())
}

/// `NNVerification.c009_ibp_width` value: `fun _ => Rat.zero`
pub(super) fn build_ibp_width_value(c: &C009Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, _) = b.fresh_local(c.nat.clone());
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), c.rat_zero.clone());
    b.finish(e)
}

/// `NNVerification.c009_crown_width : Nat -> Rat`
///
/// CROWN output width as a function of network depth.
pub(super) fn build_crown_width_type(c: &C009Consts) -> Expr {
    // Nat -> Rat
    Expr::pi(BinderInfo::Default, c.nat.clone(), c.rat.clone())
}

/// `NNVerification.c009_crown_width` value: `fun _ => Rat.zero`
pub(super) fn build_crown_width_value(c: &C009Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, _) = b.fresh_local(c.nat.clone());
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), c.rat_zero.clone());
    b.finish(e)
}

/// `NNVerification.c009_crown_ibp_ratio : Nat -> Rat`
///
/// The ratio crown_width(N) / ibp_width(N) as a function of depth.
pub(super) fn build_crown_ibp_ratio_type(c: &C009Consts) -> Expr {
    // Nat -> Rat
    Expr::pi(BinderInfo::Default, c.nat.clone(), c.rat.clone())
}

/// `NNVerification.c009_crown_ibp_ratio` value: `fun _ => Rat.zero`
pub(super) fn build_crown_ibp_ratio_value(c: &C009Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, _) = b.fresh_local(c.nat.clone());
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), c.rat_zero.clone());
    b.finish(e)
}
