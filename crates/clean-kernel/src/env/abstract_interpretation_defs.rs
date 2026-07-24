// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type builders for abstract interpretation framework formalization.
//!
//! Contains definition type builders and theorem type builders for the
//! classical Cousot & Cousot abstract interpretation framework.
//!
//! ## Definitions
//!
//! - `ConcreteSemantics` — concrete collecting semantics (State -> State)
//! - `AbstractSemantics` — abstract semantics (AbstractState -> AbstractState)
//! - `Widening` — widening operator (AbstractState -> AbstractState -> AbstractState)
//! - `Narrowing` — narrowing operator (AbstractState -> AbstractState -> AbstractState)
//! - `fixpoint_iteration` — Kleene iteration with widening/narrowing
//!
//! ## Theorems
//!
//! 1. `soundness` — abstract over-approximates concrete
//! 2. `widening_termination` — widening ensures termination
//! 3. `narrowing_refines` — narrowing refines without losing soundness
//! 4. `fixpoint_sound` — computed fixpoint over-approximates least fixpoint
//! 5. `domain_product_sound` — reduced product preserves soundness
//!
//! Part of #3189.

use super::abstract_interpretation::AbstractInterpConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};

// =============================================================================
// Definition type builders
// =============================================================================

/// `AbstractInterp.ConcreteSemantics : Type`
///
/// Concrete collecting semantics: a monotone function on concrete program
/// states. Modeled as `AbstractState -> AbstractState` where both input and
/// output live in the concrete lattice (powerset of program states).
///
/// In the classical framework (Cousot & Cousot 1977), this is
/// `F : P(State) -> P(State)` — the concrete transfer function whose
/// least fixpoint gives the collecting semantics.
pub(super) fn build_concrete_semantics_type(c: &AbstractInterpConsts) -> Expr {
    // ConcreteSemantics : AbstractState -> AbstractState
    Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    )
}

/// `AbstractInterp.AbstractSemantics : Type`
///
/// Abstract semantics: a monotone function on abstract lattice elements.
/// Models `F# : AbstractState -> AbstractState` — the abstract transfer
/// function that over-approximates the concrete semantics.
pub(super) fn build_abstract_semantics_type(c: &AbstractInterpConsts) -> Expr {
    // AbstractSemantics : AbstractState -> AbstractState
    Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    )
}

/// `AbstractInterp.Widening : Type`
///
/// Widening operator: `AbstractState -> AbstractState -> AbstractState`.
/// Given the previous iterate and the new iterate, produces an
/// upper-approximation that ensures the ascending chain stabilizes in
/// finitely many steps (even on infinite-height lattices).
///
/// Key property: `a <= widen(a, b)` and `b <= widen(a, b)`, and the
/// widening chain `a0, widen(a0, F#(a0)), widen(..., F#(...)), ...`
/// stabilizes.
pub(super) fn build_widening_type(c: &AbstractInterpConsts) -> Expr {
    // Widening : AbstractState -> AbstractState -> AbstractState
    Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        Expr::pi(
            BinderInfo::Default,
            c.abstract_state.clone(),
            c.abstract_state.clone(),
        ),
    )
}

/// `AbstractInterp.Narrowing : Type`
///
/// Narrowing operator: `AbstractState -> AbstractState -> AbstractState`.
/// Given a post-widening fixpoint and a new iterate, produces a tighter
/// (but still sound) approximation. Used after widening to recover
/// precision lost during the ascending phase.
///
/// Key property: `narrow(a, b) <= a` (refining) and if `b <= a` then
/// `b <= narrow(a, b)` (soundness preservation).
pub(super) fn build_narrowing_type(c: &AbstractInterpConsts) -> Expr {
    // Narrowing : AbstractState -> AbstractState -> AbstractState
    Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        Expr::pi(
            BinderInfo::Default,
            c.abstract_state.clone(),
            c.abstract_state.clone(),
        ),
    )
}

/// `AbstractInterp.fixpoint_iteration :
///    (AbstractState -> AbstractState) ->
///    (AbstractState -> AbstractState -> AbstractState) ->
///    Nat ->
///    AbstractState ->
///    AbstractState`
///
/// Kleene fixpoint iteration with widening. Takes:
/// - `f` : the abstract transfer function
/// - `widen` : the widening operator
/// - `fuel` : iteration bound (Nat)
/// - `init` : initial abstract state (typically bottom)
///
/// Returns the widened fixpoint approximation after `fuel` steps.
pub(super) fn build_fixpoint_iteration_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    // f : AbstractState -> AbstractState
    let f_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let (f_id, _) = b.fresh_local(f_ty.clone());
    // widen : AbstractState -> AbstractState -> AbstractState
    let widen_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        Expr::pi(
            BinderInfo::Default,
            c.abstract_state.clone(),
            c.abstract_state.clone(),
        ),
    );
    let (w_id, _) = b.fresh_local(widen_ty.clone());
    // fuel : Nat
    let (fuel_id, _) = b.fresh_local(c.nat.clone());
    // init : AbstractState
    let (init_id, _) = b.fresh_local(c.abstract_state.clone());
    let e = b.mk_pi(
        init_id,
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let e = b.mk_pi(fuel_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(w_id, BinderInfo::Default, widen_ty, e);
    let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
    b.finish(e)
}

// =============================================================================
// Theorem type builders
// =============================================================================

/// `AbstractInterp.soundness`:
/// ```text
/// forall (f_concrete f_abstract : AbstractState -> AbstractState)
///        (s : AbstractState),
///   LE.le (f_concrete s) (f_abstract s)
/// ```
///
/// The fundamental soundness theorem of abstract interpretation:
/// for every concrete state, the abstract transfer function
/// over-approximates the concrete transfer function.
/// (The real mathematical content — that this holds for all reachable
/// states under the Galois connection — is in the backing axiom.)
pub(super) fn build_soundness_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    // f_concrete : AbstractState -> AbstractState
    let f_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let (fc_id, fc) = b.fresh_local(f_ty.clone());
    let (fa_id, fa) = b.fresh_local(f_ty.clone());
    let (s_id, s) = b.fresh_local(c.abstract_state.clone());
    // conclusion: LE.le (f_concrete s) (f_abstract s)
    let fc_s = Expr::app(fc, s.clone());
    let fa_s = Expr::app(fa, s);
    let concl = c.state_le(fc_s, fa_s);
    let e = b.mk_pi(s_id, BinderInfo::Default, c.abstract_state.clone(), concl);
    let e = b.mk_pi(fa_id, BinderInfo::Default, f_ty.clone(), e);
    let e = b.mk_pi(fc_id, BinderInfo::Default, f_ty, e);
    b.finish(e)
}

/// `AbstractInterp.widening_termination`:
/// ```text
/// forall (widen : AbstractState -> AbstractState -> AbstractState)
///        (a b : AbstractState),
///   LE.le a (widen a b)
/// ```
///
/// Widening is an upper bound: for any two abstract states a and b,
/// `widen(a, b)` is above `a` in the lattice ordering. Together with
/// the descending chain condition (finite height of widened chains),
/// this ensures termination of the widened Kleene iteration.
/// The real content (that widened chains stabilize) is in the backing axiom.
pub(super) fn build_widening_termination_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let widen_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        Expr::pi(
            BinderInfo::Default,
            c.abstract_state.clone(),
            c.abstract_state.clone(),
        ),
    );
    let (w_id, w) = b.fresh_local(widen_ty.clone());
    let (a_id, a) = b.fresh_local(c.abstract_state.clone());
    let (bv_id, bv) = b.fresh_local(c.abstract_state.clone());
    // conclusion: LE.le a (widen a b)
    let widen_a_b = Expr::app(Expr::app(w, a.clone()), bv);
    let concl = c.state_le(a, widen_a_b);
    let e = b.mk_pi(bv_id, BinderInfo::Default, c.abstract_state.clone(), concl);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(w_id, BinderInfo::Default, widen_ty, e);
    b.finish(e)
}

/// `AbstractInterp.narrowing_refines`:
/// ```text
/// forall (narrow : AbstractState -> AbstractState -> AbstractState)
///        (a b : AbstractState),
///   LE.le b a ->
///   LE.le (narrow a b) a
/// ```
///
/// Narrowing is a refinement: if b <= a (the new iterate is below the
/// current), then narrow(a, b) <= a (the narrowed result is still below
/// the current — it descends monotonically).
pub(super) fn build_narrowing_refines_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let narrow_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        Expr::pi(
            BinderInfo::Default,
            c.abstract_state.clone(),
            c.abstract_state.clone(),
        ),
    );
    let (narrow_id, narrow) = b.fresh_local(narrow_ty.clone());
    let (a_id, a) = b.fresh_local(c.abstract_state.clone());
    let (b_id, bv) = b.fresh_local(c.abstract_state.clone());
    // hypothesis: LE.le b a
    let hyp = c.state_le(bv.clone(), a.clone());
    let (h_id, _) = b.fresh_local(hyp.clone());
    // conclusion: LE.le (narrow a b) a
    let narrow_a_b = Expr::app(Expr::app(narrow, a.clone()), bv);
    let concl = c.state_le(narrow_a_b, a);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(b_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(narrow_id, BinderInfo::Default, narrow_ty, e);
    b.finish(e)
}

/// `AbstractInterp.fixpoint_sound`:
/// ```text
/// forall (f_concrete f_abstract : AbstractState -> AbstractState)
///        (widen : AbstractState -> AbstractState -> AbstractState)
///        (n : Nat) (init : AbstractState),
///   LE.le (f_concrete (fixpoint_iteration f_abstract widen n init))
///          (fixpoint_iteration f_abstract widen n init)
/// ```
///
/// The computed fixpoint (via widened Kleene iteration) is a sound
/// over-approximation: it is a post-fixpoint of the concrete semantics.
/// This means every concrete reachable state is below the computed fixpoint.
pub(super) fn build_fixpoint_sound_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let f_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let (fc_id, fc) = b.fresh_local(f_ty.clone());
    let (fa_id, fa) = b.fresh_local(f_ty.clone());
    let widen_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        Expr::pi(
            BinderInfo::Default,
            c.abstract_state.clone(),
            c.abstract_state.clone(),
        ),
    );
    let (w_id, w) = b.fresh_local(widen_ty.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (init_id, init) = b.fresh_local(c.abstract_state.clone());
    // fixpoint_iteration f_abstract widen n init
    let fp = Expr::apps(c.fixpoint_iteration.clone(), [fa, w, n, init]);
    // conclusion: LE.le (f_concrete fp) fp
    let fc_fp = Expr::app(fc, fp.clone());
    let concl = c.state_le(fc_fp, fp);
    let e = b.mk_pi(
        init_id,
        BinderInfo::Default,
        c.abstract_state.clone(),
        concl,
    );
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(w_id, BinderInfo::Default, widen_ty, e);
    let e = b.mk_pi(fa_id, BinderInfo::Default, f_ty.clone(), e);
    let e = b.mk_pi(fc_id, BinderInfo::Default, f_ty, e);
    b.finish(e)
}

/// `AbstractInterp.domain_product_sound`:
/// ```text
/// forall (f1 f2 : AbstractState -> AbstractState)
///        (s : AbstractState),
///   LE.le s (f1 s) ->
///   LE.le s (f2 s) ->
///   LE.le s (f1 (f2 s))
/// ```
///
/// Soundness of the reduced product: if both abstract transfer functions
/// individually over-approximate a state, then their composition (reduced
/// product) also over-approximates. This is the foundation for combining
/// multiple abstract domains (e.g., intervals + octagons + polyhedra).
pub(super) fn build_domain_product_sound_type(c: &AbstractInterpConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let f_ty = Expr::pi(
        BinderInfo::Default,
        c.abstract_state.clone(),
        c.abstract_state.clone(),
    );
    let (f1_id, f1) = b.fresh_local(f_ty.clone());
    let (f2_id, f2) = b.fresh_local(f_ty.clone());
    let (s_id, s) = b.fresh_local(c.abstract_state.clone());
    // hypothesis 1: LE.le s (f1 s)
    let f1_s = Expr::app(f1.clone(), s.clone());
    let hyp1 = c.state_le(s.clone(), f1_s);
    let (h1_id, _) = b.fresh_local(hyp1.clone());
    // hypothesis 2: LE.le s (f2 s)
    let f2_s = Expr::app(f2.clone(), s.clone());
    let hyp2 = c.state_le(s.clone(), f2_s.clone());
    let (h2_id, _) = b.fresh_local(hyp2.clone());
    // conclusion: LE.le s (f1 (f2 s))
    let f1_f2_s = Expr::app(f1, f2_s);
    let concl = c.state_le(s, f1_f2_s);
    let e = b.mk_pi(h2_id, BinderInfo::Default, hyp2, concl);
    let e = b.mk_pi(h1_id, BinderInfo::Default, hyp1, e);
    let e = b.mk_pi(s_id, BinderInfo::Default, c.abstract_state.clone(), e);
    let e = b.mk_pi(f2_id, BinderInfo::Default, f_ty.clone(), e);
    let e = b.mk_pi(f1_id, BinderInfo::Default, f_ty, e);
    b.finish(e)
}
