// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Metaprogram-time *computed control flow* for term-elaborator bodies.
//!
//! # The problem this solves
//!
//! A term-elaborator body written as an `if`-then-else
//!
//! ```text
//! elab "pick" : term => if true then Nat.zero else Nat.succ Nat.zero
//! ```
//!
//! is, in Lean's metaprogramming model, an *elaboration-time* decision: the
//! condition is evaluated *while the elaborator runs* to choose which branch's
//! syntax to elaborate and return. That is different from an ordinary object-level
//! `if` (`elab_if`), which builds a runtime `ite` term that keeps *both* branches.
//!
//! Before this module, a `SurfaceExpr::If` body fell through to `elab_if`, so the
//! result was always the `ite α cond inst then else` application — never the
//! selected branch. This module recognizes the `if`-body shape, *evaluates the
//! condition at metaprogram time*, and elaborates only the chosen branch.
//!
//! # What it does
//!
//! For a body `if <cond> then <a> else <b>`:
//!
//! 1. elaborate `<cond>` through the normal kernel-checked pipeline;
//! 2. weak-head-normalize it via the kernel reducer ([`ElabCtx::whnf`]);
//! 3. if the reduced form is the `Bool.true` constructor, elaborate `<a>`; if it
//!    is `Bool.false`, elaborate `<b>` — through the *normal* pipeline, so the
//!    chosen branch is kernel-checked exactly like any other term.
//!
//! # When it DECLINES (and why that matters for soundness)
//!
//! If `<cond>` does **not** whnf-reduce to a concrete `Bool.true`/`Bool.false`
//! constructor — it is stuck, symbolic, a runtime value, or a non-`Bool` type —
//! this module returns `None` and the caller falls through to the ordinary
//! `elab_if` path (which builds the honest `ite` term, or fails honestly if the
//! condition is ill-typed). It NEVER guesses a branch: picking arbitrarily when
//! the condition is not a decided metaprogram-time value would be unsound, so a
//! non-`Bool`-decided condition is declined rather than resolved.
//!
//! Elaborating `<cond>` is itself a normal, kernel-checked elaboration; if it
//! fails, the failure is reported honestly (the body is not silently accepted).
//!
//! # Soundness
//!
//! - The condition is elaborated and kernel-checked by the normal pipeline; its
//!   value is read by the kernel weak-head reducer, which is meaning-preserving.
//! - Branch selection is a *metaprogram-time* decision (which syntax to
//!   elaborate), exactly like Lean's elaboration-time `if`. It is **not** an
//!   object-level/proof-level case split: nothing here asserts `cond = true` or
//!   closes a goal.
//! - The selected branch is elaborated + kernel-checked by the normal
//!   `ElabCtx::elaborate` pipeline, so a wrong-typed chosen branch fails honestly
//!   with the ordinary type-mismatch error. No term is accepted without the kernel
//!   check; no goal is closed; no axiom is introduced.

use super::ElabCtx;
use crate::error::ElabError;
use clean_kernel::{Expr, ExprKind, Name};
use clean_parser::SurfaceExpr;

/// The `Bool.true` constructor name a decided-true condition reduces to.
const BOOL_TRUE: &str = "Bool.true";
/// The `Bool.false` constructor name a decided-false condition reduces to.
const BOOL_FALSE: &str = "Bool.false";

/// Whether `body` is a term-level `if`-then-else (the shape this module's
/// computed control flow handles). A nullary `if` body has no other surface
/// representation, so recognizing the variant is sufficient.
#[must_use]
pub(super) fn is_meta_if_body(body: &SurfaceExpr) -> bool {
    matches!(body, SurfaceExpr::If(..))
}

/// The metaprogram-time decision a `Bool`-valued condition reduces to.
enum CondDecision {
    /// The condition whnf-reduced to the `Bool.true` constructor: take `then`.
    Then,
    /// The condition whnf-reduced to the `Bool.false` constructor: take `else`.
    Else,
}

/// Classify the whnf-reduced condition term as a concrete `Bool` constructor.
///
/// Returns `None` for any term that is not the bare `Bool.true`/`Bool.false`
/// constructor (stuck application, metavariable, symbolic value, non-`Bool`
/// constant, ...), which signals the caller to DECLINE rather than guess a
/// branch.
fn classify_bool(reduced: &Expr) -> Option<CondDecision> {
    let ExprKind::Const(name, _) = reduced.kind() else {
        return None;
    };
    if *name == Name::from_string(BOOL_TRUE) {
        Some(CondDecision::Then)
    } else if *name == Name::from_string(BOOL_FALSE) {
        Some(CondDecision::Else)
    } else {
        None
    }
}

impl<'a> ElabCtx<'a> {
    /// Evaluate a term-elaborator body of the shape `if <cond> then <a> else <b>`
    /// as metaprogram-time computed control flow, returning the elaborated chosen
    /// branch.
    ///
    /// Returns:
    /// - `None` if `body` is not an `if`-then-else, **or** if `<cond>` does not
    ///   whnf-reduce to a concrete `Bool.true`/`Bool.false` constructor (stuck /
    ///   symbolic / non-`Bool`) — in both cases the caller falls through to the
    ///   ordinary `elab_if` path so the body fails honestly or builds the runtime
    ///   `ite`, never picking a branch arbitrarily;
    /// - `Some(Ok(expr))` with the kernel-checkable elaboration of the selected
    ///   branch when the condition is decided;
    /// - `Some(Err(..))` if the (recognized) condition fails to elaborate — an
    ///   honest error, never a fabricated branch.
    ///
    /// # Soundness
    ///
    /// The condition is elaborated and kernel-checked by the normal pipeline and
    /// reduced by the kernel weak-head reducer (meaning-preserving). Only a
    /// concrete `Bool` constructor decides a branch; anything else declines. The
    /// selected branch is elaborated + kernel-checked by the normal pipeline, so a
    /// wrong-typed branch fails honestly. This is a metaprogram-time choice of
    /// which syntax to elaborate, not an object-level case split: no goal is
    /// closed and no term is accepted without the normal kernel check.
    pub(super) fn eval_meta_if_body(
        &mut self,
        body: &SurfaceExpr,
    ) -> Option<Result<Expr, ElabError>> {
        let SurfaceExpr::If(_, cond, then_br, else_br) = body else {
            return None;
        };
        // Elaborate the condition through the normal kernel-checked pipeline. A
        // failure here is honest (the condition is ill-typed / unresolvable); we
        // surface it so the body is not silently accepted.
        let cond_expr = match self.elaborate(cond) {
            Ok(e) => e,
            Err(e) => return Some(Err(e)),
        };
        // Weak-head reduce and require a concrete Bool constructor. A stuck /
        // symbolic / non-Bool condition is NOT a decided metaprogram-time value:
        // decline so the caller falls through to the ordinary `elab_if` path
        // rather than guessing a branch.
        let reduced = self.whnf(&cond_expr);
        let chosen = match classify_bool(&reduced)? {
            CondDecision::Then => then_br,
            CondDecision::Else => else_br,
        };
        // A supported `throwError "msg"` in the chosen branch raises the user's
        // custom error as a typed diagnostic: it produces no term and fabricates
        // nothing — it only makes elaboration FAIL with exactly the user's
        // message. (The headline use case: `if <cond> then throwError "bad" else
        // <ok>` — when `<cond>` is decided-true the error fires.)
        if let Some(message) = super::user_tactic::as_throw_error_message(chosen) {
            return Some(Err(ElabError::UserThrowError { message }));
        }
        // Elaborate the selected branch against the current expected type, exactly
        // like `elab_if` elaborates its branches. This kernel-checks the branch
        // *and* enforces the elaborator's expected type, so a wrong-typed chosen
        // branch (e.g. `Bool.true` where a `Nat` is expected) fails honestly with
        // the ordinary type-mismatch error — no kernel bypass.
        let expected = self.current_expected_type.clone();
        Some(self.elaborate_with_expected_type(chosen, expected))
    }
}

#[cfg(test)]
#[path = "meta_control_flow_tests.rs"]
mod tests;
