// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type builders for abstract interpretation framework: lattice operations,
//! Galois connection, interval domain instances, and core lattice/Galois
//! soundness theorems.
//!
//! Zonotope domain, transfer functions, and domain/transfer soundness theorems
//! are in `abstract_interpretation_framework_defs2.rs`.
//!
//! ## Definitions
//!
//! - `join` - lattice join operator
//! - `meet` - lattice meet operator
//! - `bot` - lattice bottom element
//! - `top` - lattice top element
//! - `GaloisConnection` - abstraction/concretization interface
//! - `interval_*` - interval-domain lattice operators
//!
//! ## Theorems
//!
//! 1. `galois_adjunction` - the Galois adjunction law
//! 2. `interval_zonotope_galois` - interval/zonotope refinement interface
//! 3. `join_upper_bound` - join is an upper bound
//! 4. `meet_lower_bound` - meet is a lower bound
//! 5. `bot_least` - bottom is least
//! 6. `top_greatest` - top is greatest
//! 7. `galois_connection_sound` - Galois connections preserve soundness
//!
//! Part of #3189.

use super::abstract_interpretation::AbstractInterpConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};

// =============================================================================
// Definition type builders
// =============================================================================

/// `AbstractInterp.Framework.join :
///    AbstractState -> AbstractState -> AbstractState`
///
/// Lattice join operation on abstract states. Given two abstract elements,
/// returns their least upper bound in the abstract domain ordering.
pub(super) fn build_join_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, _) = b.fresh_local(c.abstract_state.clone());
    let (bv_id, _) = b.fresh_local(c.abstract_state.clone());
    let e = b.mk_pi(
        bv_id,
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), e);
    b.finish(e)
}

/// `AbstractInterp.Framework.meet :
///    AbstractState -> AbstractState -> AbstractState`
///
/// Lattice meet operation on abstract states. Given two abstract elements,
/// returns their greatest lower bound in the abstract domain ordering.
pub(super) fn build_meet_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, _) = b.fresh_local(c.abstract_state.clone());
    let (bv_id, _) = b.fresh_local(c.abstract_state.clone());
    let e = b.mk_pi(
        bv_id,
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), e);
    b.finish(e)
}

/// `AbstractInterp.Framework.bot : AbstractState`
///
/// Bottom element of the abstract lattice. Represents the least abstract
/// state, typically the empty or unreachable state.
pub(super) fn build_bot_type(c: &AbstractInterpConsts) -> Expr {
    c.abstract_state.clone()
}

/// `AbstractInterp.Framework.top : AbstractState`
///
/// Top element of the abstract lattice. Represents the greatest abstract
/// state, typically complete uncertainty.
pub(super) fn build_top_type(c: &AbstractInterpConsts) -> Expr {
    c.abstract_state.clone()
}

/// `AbstractInterp.Framework.GaloisConnection :
///    (AbstractState -> AbstractState) ->
///    (AbstractState -> AbstractState) ->
///    Prop`
///
/// Simplified Galois connection predicate. Takes an abstraction map `alpha`
/// and a concretization map `gamma`, both modeled as endofunctions on the
/// shared `AbstractState` carrier, and returns the proposition that they form
/// a sound adjoint pair.
pub(super) fn build_galois_connection_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let map_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let (alpha_id, _) = b.fresh_local(map_ty.clone());
    let (gamma_id, _) = b.fresh_local(map_ty.clone());
    let e = b.mk_pi(
        gamma_id,
        BinderInfo::Default,
        map_ty.clone(),
        c.prop.clone(),
    );
    let e = b.mk_pi(alpha_id, BinderInfo::Default, map_ty, e);
    b.finish(e)
}

/// `AbstractInterp.Framework.interval_join :
///    AbstractState -> AbstractState -> AbstractState`
///
/// Interval-domain join operation. Computes the least upper bound of two
/// interval abstract states.
pub(super) fn build_interval_join_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, _) = b.fresh_local(c.abstract_state.clone());
    let (bv_id, _) = b.fresh_local(c.abstract_state.clone());
    let e = b.mk_pi(
        bv_id,
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), e);
    b.finish(e)
}

/// `AbstractInterp.Framework.interval_meet :
///    AbstractState -> AbstractState -> AbstractState`
///
/// Interval-domain meet operation. Computes the greatest lower bound of two
/// interval abstract states.
pub(super) fn build_interval_meet_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, _) = b.fresh_local(c.abstract_state.clone());
    let (bv_id, _) = b.fresh_local(c.abstract_state.clone());
    let e = b.mk_pi(
        bv_id,
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), e);
    b.finish(e)
}

/// `AbstractInterp.Framework.interval_bot : AbstractState`
///
/// Bottom element for the interval abstract domain.
pub(super) fn build_interval_bot_type(c: &AbstractInterpConsts) -> Expr {
    c.abstract_state.clone()
}

/// `AbstractInterp.Framework.interval_top : AbstractState`
///
/// Top element for the interval abstract domain.
pub(super) fn build_interval_top_type(c: &AbstractInterpConsts) -> Expr {
    c.abstract_state.clone()
}

/// `AbstractInterp.Framework.interval_widening :
///    AbstractState -> AbstractState -> AbstractState`
///
/// Interval-domain widening operator. Accelerates fixpoint computation by
/// extrapolating ascending chains in the interval lattice.
pub(super) fn build_interval_widening_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, _) = b.fresh_local(c.abstract_state.clone());
    let (bv_id, _) = b.fresh_local(c.abstract_state.clone());
    let e = b.mk_pi(
        bv_id,
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), e);
    b.finish(e)
}

// =============================================================================
// Theorem type builders
// =============================================================================

/// `AbstractInterp.Framework.galois_adjunction`:
/// ```text
/// forall (alpha gamma : AbstractState -> AbstractState)
///        (c a : AbstractState),
///   LE.le c (gamma a) ->
///   LE.le (alpha c) a
/// ```
///
/// The adjunction law for the simplified Galois connection interface. If a
/// concrete-side state `c` is below `gamma a`, then abstracting `c` with
/// `alpha` stays below `a`.
pub(super) fn build_galois_adjunction_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let map_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let (alpha_id, alpha) = b.fresh_local(map_ty.clone());
    let (gamma_id, gamma) = b.fresh_local(map_ty.clone());
    let (cv_id, cv) = b.fresh_local(c.abstract_state.clone());
    let (a_id, a) = b.fresh_local(c.abstract_state.clone());
    // hypothesis: LE.le c (gamma a)
    let gamma_a = Expr::app(gamma, a.clone());
    let hyp = c.state_le(cv.clone(), gamma_a);
    let (h_id, _) = b.fresh_local(hyp.clone());
    // conclusion: LE.le (alpha c) a
    let alpha_c = Expr::app(alpha, cv);
    let concl = c.state_le(alpha_c, a);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(cv_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(gamma_id, BinderInfo::Default, map_ty.clone(), e);
    let e = b.mk_pi(alpha_id, BinderInfo::Default, map_ty, e);
    b.finish(e)
}

/// `AbstractInterp.Framework.interval_zonotope_galois`:
/// ```text
/// forall (alpha_iz gamma_iz : AbstractState -> AbstractState)
///        (a : AbstractState),
///   LE.le (alpha_iz a) (gamma_iz a)
/// ```
///
/// Simplified interval-to-zonotope Galois interface. Encodes that the
/// zonotope view refines or over-approximates the interval view through
/// the abstraction/concretization maps `alpha_iz` and `gamma_iz`.
pub(super) fn build_interval_zonotope_galois_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let map_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let (alpha_id, alpha) = b.fresh_local(map_ty.clone());
    let (gamma_id, gamma) = b.fresh_local(map_ty.clone());
    let (a_id, a) = b.fresh_local(c.abstract_state.clone());
    // conclusion: LE.le (alpha_iz a) (gamma_iz a)
    let alpha_a = Expr::app(alpha, a.clone());
    let gamma_a = Expr::app(gamma, a);
    let concl = c.state_le(alpha_a, gamma_a);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), concl);
    let e = b.mk_pi(gamma_id, BinderInfo::Default, map_ty.clone(), e);
    let e = b.mk_pi(alpha_id, BinderInfo::Default, map_ty, e);
    b.finish(e)
}

/// `AbstractInterp.Framework.join_upper_bound`:
/// ```text
/// forall (join : AbstractState -> AbstractState -> AbstractState)
///        (a b : AbstractState),
///   LE.le a (join a b)
/// ```
///
/// Join is an upper bound for its left argument in the abstract lattice.
pub(super) fn build_join_upper_bound_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let join_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        Expr::pi(
            BinderInfo::Default,
            c.abstract_state.clone(),
            c.abstract_state.clone(),
        ),
    );
    let (join_id, join) = b.fresh_local(join_ty.clone());
    let (a_id, a) = b.fresh_local(c.abstract_state.clone());
    let (bv_id, bv) = b.fresh_local(c.abstract_state.clone());
    // conclusion: LE.le a (join a b)
    let join_a_b = Expr::app(Expr::app(join, a.clone()), bv);
    let concl = c.state_le(a, join_a_b);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.abstract_state.clone(), concl);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(join_id, BinderInfo::Default, join_ty, e);
    b.finish(e)
}

/// `AbstractInterp.Framework.meet_lower_bound`:
/// ```text
/// forall (meet : AbstractState -> AbstractState -> AbstractState)
///        (a b : AbstractState),
///   LE.le (meet a b) a
/// ```
///
/// Meet is a lower bound for its left argument in the abstract lattice.
pub(super) fn build_meet_lower_bound_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let meet_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        Expr::pi(
            BinderInfo::Default,
            c.abstract_state.clone(),
            c.abstract_state.clone(),
        ),
    );
    let (meet_id, meet) = b.fresh_local(meet_ty.clone());
    let (a_id, a) = b.fresh_local(c.abstract_state.clone());
    let (bv_id, bv) = b.fresh_local(c.abstract_state.clone());
    // conclusion: LE.le (meet a b) a
    let meet_a_b = Expr::app(Expr::app(meet, a.clone()), bv);
    let concl = c.state_le(meet_a_b, a);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.abstract_state.clone(), concl);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(meet_id, BinderInfo::Default, meet_ty, e);
    b.finish(e)
}

/// `AbstractInterp.Framework.bot_least`:
/// ```text
/// forall (bot : AbstractState) (a : AbstractState),
///   LE.le bot a
/// ```
///
/// Bottom is the least element of the abstract lattice.
pub(super) fn build_bot_least_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (bot_id, bot) = b.fresh_local(c.abstract_state.clone());
    let (a_id, a) = b.fresh_local(c.abstract_state.clone());
    // conclusion: LE.le bot a
    let concl = c.state_le(bot, a);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), concl);
    let e = b.mk_pi(bot_id, BinderInfo::Default, c.abstract_state.clone(), e);
    b.finish(e)
}

/// `AbstractInterp.Framework.top_greatest`:
/// ```text
/// forall (top : AbstractState) (a : AbstractState),
///   LE.le a top
/// ```
///
/// Top is the greatest element of the abstract lattice.
pub(super) fn build_top_greatest_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (top_id, top) = b.fresh_local(c.abstract_state.clone());
    let (a_id, a) = b.fresh_local(c.abstract_state.clone());
    // conclusion: LE.le a top
    let concl = c.state_le(a, top);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), concl);
    let e = b.mk_pi(top_id, BinderInfo::Default, c.abstract_state.clone(), e);
    b.finish(e)
}

/// `AbstractInterp.Framework.galois_connection_sound`:
/// ```text
/// forall (GaloisConnection :
///          (AbstractState -> AbstractState) ->
///          (AbstractState -> AbstractState) ->
///          Prop)
///        (alpha gamma : AbstractState -> AbstractState)
///        (c a : AbstractState),
///   GaloisConnection alpha gamma ->
///   LE.le c (gamma a) ->
///   LE.le (alpha c) a
/// ```
///
/// Soundness interface for Galois connections. If `alpha` and `gamma` satisfy
/// the Galois-connection predicate, the adjunction law holds.
pub(super) fn build_galois_connection_sound_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let map_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let gc_ty = Expr::pi(
        BinderInfo::Default,
        map_ty.clone(),
        Expr::pi(BinderInfo::Default, map_ty.clone(), c.prop.clone()),
    );
    let (gc_id, gc) = b.fresh_local(gc_ty.clone());
    let (alpha_id, alpha) = b.fresh_local(map_ty.clone());
    let (gamma_id, gamma) = b.fresh_local(map_ty.clone());
    let (cv_id, cv) = b.fresh_local(c.abstract_state.clone());
    let (a_id, a) = b.fresh_local(c.abstract_state.clone());
    // hypothesis 1: GaloisConnection alpha gamma
    let gc_alpha_gamma = Expr::app(Expr::app(gc, alpha.clone()), gamma.clone());
    let (hgc_id, _) = b.fresh_local(gc_alpha_gamma.clone());
    // hypothesis 2: LE.le c (gamma a)
    let gamma_a = Expr::app(gamma, a.clone());
    let hyp = c.state_le(cv.clone(), gamma_a);
    let (h_id, _) = b.fresh_local(hyp.clone());
    // conclusion: LE.le (alpha c) a
    let alpha_c = Expr::app(alpha, cv);
    let concl = c.state_le(alpha_c, a);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(hgc_id, BinderInfo::Default, gc_alpha_gamma, e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(cv_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(gamma_id, BinderInfo::Default, map_ty.clone(), e);
    let e = b.mk_pi(alpha_id, BinderInfo::Default, map_ty.clone(), e);
    let e = b.mk_pi(gc_id, BinderInfo::Default, gc_ty, e);
    b.finish(e)
}
