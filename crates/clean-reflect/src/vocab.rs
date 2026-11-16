// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The reflector's kernel vocabulary.
//!
//! ## The overflow arm emits over REAL Lean declaration Names
//!
//! Increment 1 (the arithmetic-overflow arm) emits the obligation over the
//! ACTUAL declaration Names the elaborated `proofs/trust-soundness/
//! overflow_trust_boundary.lean` environment contains:
//!
//! - [`OVERFLOW_OBLIGATION`] — `overflowObligation : Bool -> Bool`
//!   (`:= bnot (ayNoOverflow tp)`), the proven, panic-flag-parameterized
//!   obligation.
//! - [`AY_ADD_OVERFLOWS`] — `ayAddOverflows : Nat -> Nat -> Bool`, the NAMED
//!   trust-boundary primitive (an `opaque` declaration): ay's BV add-overflow
//!   decision over the two raw operands. Its real semantics are ay's job; clean
//!   does NOT prove `ayAddOverflows a b = decide (a + b >= 256)`.
//!
//! The emitted obligation is therefore `overflowObligation (ayAddOverflows a b)`,
//! a term built entirely from the real kernel Names. Verification is INTRINSIC:
//! the Clean kernel proves the OBJECT'S OWN obligation via `check_type` under
//! `Environment::with_prelude()` (see `tests/fused_overflow.rs`), NOT by
//! `is_def_eq`-comparing this term against a hand-written
//! `overflow_trust_boundary.lean` loaded as a per-obligation reference model.
//! That outside-model side-check has been retired; the `.lean` survives only as
//! the once-proven meta-soundness theorem `PROVED => safe`.
//!
//! The operands `a, b` are `Nat` terms (a literal for a `bvConst`, a fresh
//! per-operand constant for a `bvVar`); they enter the soundness story ONLY
//! through `ayAddOverflows`.
//!
//! ## Increment-2 helpers still use a private comparison vocabulary
//!
//! The (dead-code, not-yet-emitted) Increment-2 comparison helpers — bvUlt /
//! bvEq / bvNot — remain on a private [`comparison`] vocabulary because their
//! real Lean Names live in `expr_obligation_semantics.lean` and their
//! env-resolved correspondence is a later increment. They are NOT part of the
//! Increment-1 emission contract and never reach `reflect_module`'s output.

use clean_kernel::{Declaration, Environment, Expr, Name};

// --- REAL Lean Names the overflow arm emits over -----------------------------

/// `overflowObligation : Bool -> Bool` — the proven, panic-flag-parameterized
/// overflow obligation `bnot (ayNoOverflow tp)` (overflow_trust_boundary.lean).
pub(crate) const OVERFLOW_OBLIGATION: &str = "overflowObligation";

/// `ayAddOverflows : Nat -> Nat -> Bool` — the NAMED trust-boundary primitive:
/// ay's BV add-overflow decision over the two raw operands
/// (overflow_trust_boundary.lean). Opaque; ay owns its semantics.
pub(crate) const AY_ADD_OVERFLOWS: &str = "ayAddOverflows";

// NOTE: `overflowObligation` unfolds (in the trust-soundness `.lean`) to
// `bnot (ayNoOverflow tp)`, but the reflector emits the folded
// `overflowObligation (ayAddOverflows a b)` form and the kernel discharge in
// `tests/fused_overflow.rs` works over the object's own derived obligation —
// neither `ayNoOverflow` nor `bnot` is opened per obligation, so they are not
// declared as reflector vocabulary here.

/// The carrier sort for bit-vector-valued operand terms (modeled by `Nat`,
/// matching `ayAddOverflows`' `Nat -> Nat -> Bool` signature).
pub(crate) const NAT: &str = "Nat";

/// The carrier sort of an obligation *condition* (`Bool`), used as the type
/// argument when wrapping it as an `@Eq.{1} Bool _ _` `not_fires` goal.
pub(crate) const NAT_BOOL_CARRIER: &str = "Bool";

/// Propositional equality, used to wrap an obligation as a `not_fires` goal.
const EQ: &str = "Eq";
/// `Bool.false`, the value an obligation evaluates to when it does not fire.
const BOOL_FALSE: &str = "Bool.false";

/// Kernel constant name for propositional equality (used by `not_fires`).
#[must_use]
pub fn eq_const() -> &'static str {
    EQ
}

/// Kernel constant name for `Bool.false` (used by `not_fires`).
#[must_use]
pub fn bool_false_const() -> &'static str {
    BOOL_FALSE
}

/// Register an SSA operand symbol (e.g. `%0`) into `env` with carrier sort
/// `Nat`, so an obligation referencing it as an `ayAddOverflows` argument
/// type-checks against that environment.
///
/// # Errors
///
/// Returns the kernel `EnvError` if `symbol` is already declared.
pub fn register_operand(
    env: &mut Environment,
    symbol: &str,
) -> Result<(), clean_kernel::KernelEnvError> {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(symbol),
        level_params: vec![],
        type_: Expr::const_str(NAT),
    })
}

// --- Private Increment-2 comparison vocabulary (NOT yet emitted) --------------

/// Private kernel constants for the Increment-2 comparison fragment (bvUlt /
/// bvEq / bvNot). These are NOT real Lean Names yet and are NOT part of the
/// Increment-1 emission contract; the helpers that use them are dead code until
/// Increment 2 wires their env-resolved correspondence.
pub(crate) mod comparison {
    /// Boolean negation node (Lean `bnot`, comparison-fragment private name).
    pub(crate) const BV_NOT: &str = "Reflect.bvNot";
    /// Unsigned-less-than comparison (Lean `bvUlt`).
    pub(crate) const BV_ULT: &str = "Reflect.bvUlt";
    /// Equality comparison (Lean `bvEq`).
    pub(crate) const BV_EQ: &str = "Reflect.bvEq";

    pub(crate) const fn bv_not() -> &'static str {
        BV_NOT
    }
    pub(crate) const fn bv_ult() -> &'static str {
        BV_ULT
    }
    pub(crate) const fn bv_eq() -> &'static str {
        BV_EQ
    }
}
