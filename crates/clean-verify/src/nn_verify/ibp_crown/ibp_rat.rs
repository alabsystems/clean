// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! IBP linear layer soundness over **rationals** (gamma-crown#4515, clean#3524).
//!
//! This module is the `clean-verify` spec-layer wrapper around the kernel
//! theorem `NNVerify.ibp_linear_sound`, which is already registered with a
//! real proof term that type-checks via `tc.infer_type()` + `tc.is_def_eq()`
//! in `clean-kernel::env::nn_verify_ibp_linear_proof`.
//!
//! ## Theorem (mail from gamma-crown#4515)
//!
//! For a linear layer `y = W·x + b` with input `x ∈ [l, u]` (element-wise
//! over `Rat`), the IBP output bounds contain the true output:
//!
//! ```text
//! theorem ibp_linear_sound (W : Matrix m n Rat) (b : Fin m -> Rat)
//!     (l u : Fin n -> Rat) (x : Fin n -> Rat)
//!     (hx : ∀ i, l i ≤ x i ∧ x i ≤ u i) :
//!   ∀ j, ibp_lower W b l u j ≤ (W·x + b) j
//!       ∧ (W·x + b) j ≤ ibp_upper W b l u j
//! ```
//!
//! where `ibp_lower`/`ibp_upper` are the W+/W- decomposition bounds:
//! ```text
//! l'_j = Σ_i min(W_ji · l_i, W_ji · u_i) + b_j
//! u'_j = Σ_i max(W_ji · l_i, W_ji · u_i) + b_j
//! ```
//!
//! ## Kernel encoding
//!
//! The kernel registers this as the single theorem
//!
//! ```text
//! NNVerify.ibp_linear_sound :
//!   ∀ (m n : Nat) (W : NNMat m n) (b : NNVec m) (B : IntervalBounds n)
//!     (x : NNVec n),
//!     IntervalBounds.contains n B x
//!       -> IntervalBounds.contains m
//!            (ibp_linear_bounds m n W b B)
//!            (linear_output m n W b x)
//! ```
//!
//! over `Rat` (via `NNMat = Fin m -> Fin n -> Rat`, `NNVec = Fin n -> Rat`,
//! and the `Rat` `LE.le` instance). The mail-level `(l, u)` pair is the
//! `IntervalBounds` structure (fields `lower, upper : Fin n -> Rat`), and
//! `ibp_lower = ibp_linear_bounds.lower` / `ibp_upper = ibp_linear_bounds.upper`.
//!
//! ## Proof provenance
//!
//! The kernel proof factors through:
//!
//! - `NNVerify.mul_nonneg_le_left` — constructive Theorem (#3490 T3)
//! - `NNVerify.mul_nonpos_le_left` — Opaque, sorry-inhabited (#3366)
//! - `NNVerify.add_le_add` — constructive Theorem (#3490 Batch 0)
//! - `NNVerify.le_of_eq_of_le` / `le_of_le_of_eq` — constructive via `Eq.subst`
//! - `NNVerify.ibp_linear_per_component` — Opaque, sorry-inhabited (#3366)
//!
//! The top-level theorem term is a `Declaration::Theorem` (not an Axiom or
//! Opaque wrapper), so the kernel's `add_decl` runs a full `infer_type` /
//! `is_def_eq` check when the environment is constructed. See
//! `verify_kernel_ibp_linear_sound()` for the behavioral gate that re-runs
//! this check directly from `clean-verify`. See
//! [`super::ibp_rat_helper_audit::audit_ibp_linear_sound_helpers`] for the
//! machine-readable transitive-sorry audit that gamma-crown consumes.
//!
//! ## Status
//!
//! `DerivedPending` — kernel proof term still depends on sorry-inhabited
//! Opaque helpers (`mul_nonpos_le_left`, `ibp_linear_per_component`) plus
//! the structural `ibp_linear_bounds` axiom. Discharging the Opaques to
//! constructive theorems and giving `ibp_linear_bounds` a Definition body
//! will flip this to `DerivedProved`. Tracked in #3366.

use crate::nn_verify::ibp_crown::{Phase, TheoremEntry};
use crate::spec::ProofStatus;

use clean_kernel::{ConstantKind, EnvError, Environment, Expr, Name, TypeChecker};

/// Fully qualified kernel name of the top-level theorem.
pub const IBP_LINEAR_SOUND_NAME: &str = "NNVerify.ibp_linear_sound";

/// Fully qualified kernel name of the IBP bound computation.
pub const IBP_LINEAR_BOUNDS_NAME: &str = "NNVerify.ibp_linear_bounds";

/// Fully qualified kernel name of the linear output definition.
pub const LINEAR_OUTPUT_NAME: &str = "NNVerify.linear_output";

/// Kernel helper lemmas on the `ibp_linear_sound` transitive dependency tree
/// that gamma-crown tracks for cross-validation readiness.
///
/// Current state (as of #3524 / #3490 Batch 0):
/// - `mul_nonpos_le_left` — sorry-inhabited `Opaque` (discharge tracked in #3366)
/// - `add_le_add` — constructive `Theorem` (promoted in #3490)
/// - `ibp_linear_per_component` — sorry-inhabited `Opaque` (#3366)
/// - `ibp_linear_bounds` — structural `Axiom` (computation function, awaits
///   a concrete `Definition` body; #3366)
///
/// Additional honest Rat ordered-field axioms (`Rat.mul_nonneg`,
/// `Rat.add_le_add_left`, etc.) are intentionally excluded — they are
/// foundational axioms, not on the "needs discharge" list.
pub const IBP_SOUND_HELPER_NAMES: &[&str] = &[
    "NNVerify.mul_nonpos_le_left",
    "NNVerify.add_le_add",
    "NNVerify.ibp_linear_per_component",
    "NNVerify.ibp_linear_bounds",
];

/// Proof status for the Rat-valued IBP linear soundness theorem.
///
/// `DerivedPending` while any of the helper Opaques (`mul_nonpos_le_left`,
/// `ibp_linear_per_component`) remain sorry-inhabited. See
/// `nn_verify_ibp_linear.rs` in clean-kernel for the Opaque list.
pub const IBP_LINEAR_SOUND_RAT_STATUS: ProofStatus = ProofStatus::DerivedPending;

/// Kernel-backed soundness spec for the rational IBP linear layer.
///
/// Thin spec marker type mirroring `IbpLinearSpec` (f64) but pointed at the
/// Rat-typed kernel theorem. The `verify_kernel` method re-runs the kernel's
/// `add_decl` checks by constructing a fresh `Environment` and asking the
/// type checker to agree on the theorem's inferred type.
#[derive(Debug, Clone, Copy)]
pub struct IbpLinearRatSpec;

impl IbpLinearRatSpec {
    /// Construct the spec marker.
    #[must_use]
    pub const fn new() -> Self {
        Self
    }

    /// Current proof status.
    #[must_use]
    pub const fn status(self) -> ProofStatus {
        IBP_LINEAR_SOUND_RAT_STATUS
    }

    /// Kernel theorem name this spec is backed by.
    #[must_use]
    pub const fn theorem_name(self) -> &'static str {
        IBP_LINEAR_SOUND_NAME
    }
}

impl Default for IbpLinearRatSpec {
    fn default() -> Self {
        Self::new()
    }
}

/// Outcome of running the kernel soundness gate.
///
/// Carries the inferred type expression so callers (e.g. the cross-validation
/// harness requested by gamma-crown) can inspect the Pi spine if they want
/// structural assertions beyond the scalar `is_def_eq` result.
#[derive(Debug, Clone)]
pub struct KernelCheckReport {
    /// Declared theorem type (as registered via `add_decl`).
    pub declared_type: Expr,
    /// Type inferred from the proof term.
    pub inferred_type: Expr,
    /// `tc.is_def_eq(declared, inferred)` outcome — `true` when the
    /// kernel accepts the proof term.
    pub def_eq: bool,
    /// Whether the proof term is sorry-free (sorry-derived terms should
    /// never appear at the top level of a `Declaration::Theorem`).
    pub sorry_free: bool,
    /// Proof term (clone of the value stored on the `Declaration::Theorem`).
    ///
    /// Exposed so callers (and the proof-quality test in this module) can
    /// assert that the term is not a trivial axiom-wrapper. A bare
    /// `Const(axiom_name, _)` head would indicate that the theorem is
    /// merely restating an existing `Declaration::Axiom` — the design doc
    /// "Proof Soundness Rules" forbid counting such wrappers as proofs.
    pub proof_term: Expr,
}

/// Errors from `verify_kernel_ibp_linear_sound`.
#[derive(Debug, thiserror::Error)]
pub enum IbpRatVerifyError {
    /// Initializing the kernel environment for the IBP linear theorems failed.
    #[error("kernel environment init failed: {0:?}")]
    Init(EnvError),
    /// The kernel did not register the expected theorem name.
    #[error("kernel is missing declaration `{0}`")]
    MissingConst(&'static str),
    /// The kernel registered the name but not as a theorem with a proof term.
    #[error("`{0}` is present but not a Theorem with a proof value")]
    NotATheorem(&'static str),
    /// The kernel proof term failed to type-check.
    #[error("proof term of `{name}` failed to type-check: {err}")]
    InferFailed {
        /// Theorem name whose proof failed to type-check.
        name: &'static str,
        /// Stringified kernel error.
        err: String,
    },
}

/// Behavioral gate: load `NNVerify.ibp_linear_sound` into a fresh kernel
/// environment and re-run `tc.infer_type() + tc.is_def_eq()` on the proof
/// term.
///
/// This is the clean-verify-level witness that the kernel theorem is real
/// (not a `Declaration::Axiom` wrapped in a `Theorem` façade). It exercises:
///
/// 1. `Environment::init_nn_verify_ibp_linear` — constructs every definition
///    and lemma in the IBP linear dependency tree via `add_decl`, each of
///    which individually passes `add_decl`'s typechecking gate.
/// 2. Re-typechecking the theorem's proof term against its declared type.
/// 3. Asserting the proof term is sorry-free (a stronger condition than
///    `DerivedPending`: helper lemmas may still be Opaques, but the top
///    theorem must have a real lambda term).
///
/// Part of #3524 and gamma-crown#4515.
pub fn verify_kernel_ibp_linear_sound() -> Result<KernelCheckReport, IbpRatVerifyError> {
    let mut env = Environment::new();
    env.init_nn_verify_ibp_linear()
        .map_err(IbpRatVerifyError::Init)?;

    let info = env
        .get_const(&Name::from_string(IBP_LINEAR_SOUND_NAME))
        .ok_or(IbpRatVerifyError::MissingConst(IBP_LINEAR_SOUND_NAME))?;

    if info.kind != ConstantKind::Theorem {
        return Err(IbpRatVerifyError::NotATheorem(IBP_LINEAR_SOUND_NAME));
    }
    let proof = info
        .value
        .as_ref()
        .ok_or(IbpRatVerifyError::NotATheorem(IBP_LINEAR_SOUND_NAME))?;

    let declared_type = info.type_.clone();
    let sorry_free = !info.sorry_summary().has_sorry;

    let tc = TypeChecker::with_mode(&env, env.mode());
    let inferred_type = tc
        .infer_type(proof)
        .map_err(|err| IbpRatVerifyError::InferFailed {
            name: IBP_LINEAR_SOUND_NAME,
            err: format!("{err:?}"),
        })?;
    let def_eq = tc.is_def_eq(&inferred_type, &declared_type);

    Ok(KernelCheckReport {
        declared_type,
        inferred_type,
        def_eq,
        sorry_free,
        proof_term: proof.clone(),
    })
}

/// Return the (single) theorem registry entry for the Rat IBP soundness
/// spec, suitable for inclusion in the IBP/CROWN theorem registry.
///
/// We deliberately do not splice this into `ibp_theorems()` — that list
/// already contains `T80` for IBP linear soundness. This entry is the
/// Rat-typed mirror requested by gamma-crown#4515 and is tracked
/// separately under the `C4515` id.
#[must_use]
pub fn c4515_theorem_entries() -> Vec<TheoremEntry> {
    vec![TheoremEntry {
        id: "C4515",
        description: "IBP linear layer soundness over Rat (pre-TorchLean)",
        status: IBP_LINEAR_SOUND_RAT_STATUS,
        phase: Phase::Phase1,
    }]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ibp_linear_rat_spec_status() {
        let spec = IbpLinearRatSpec::new();
        assert_eq!(spec.status(), ProofStatus::DerivedPending);
        assert_eq!(spec.theorem_name(), "NNVerify.ibp_linear_sound");
    }

    #[test]
    fn test_c4515_theorem_entry() {
        let entries = c4515_theorem_entries();
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].id, "C4515");
        assert_eq!(entries[0].status, ProofStatus::DerivedPending);
        assert_eq!(entries[0].phase, Phase::Phase1);
    }

    /// Behavioral gate: kernel theorem loads and type-checks. This is the
    /// primary evidence that the Rat IBP linear soundness theorem is real.
    #[test]
    fn test_verify_kernel_ibp_linear_sound_type_checks() {
        let report = verify_kernel_ibp_linear_sound()
            .expect("kernel env should accept NNVerify.ibp_linear_sound");
        assert!(
            report.def_eq,
            "inferred proof type must match declared theorem type"
        );
        assert!(
            report.sorry_free,
            "top-level `ibp_linear_sound` must not use sorry directly"
        );
    }

    /// Extra structural check: the declared theorem type is a Pi-chain
    /// (forall m n W b B x, contains B x -> contains (ibp_linear_bounds ..)
    /// (linear_output ..)). Keeps downstream cross-validation fixtures
    /// honest about shape.
    #[test]
    fn test_kernel_ibp_linear_sound_is_pi() {
        use clean_kernel::ExprKind;
        let report = verify_kernel_ibp_linear_sound().expect("kernel env should load");
        assert!(
            matches!(report.declared_type.kind(), ExprKind::Pi(..)),
            "declared type must be a Pi chain, got {:?}",
            report.declared_type.kind()
        );
    }

    /// Proof-quality gate: the theorem's proof term must be a real Lambda
    /// abstraction, not a bare `Const` reference to some existing axiom.
    ///
    /// design doc "Proof Soundness Rules" forbid counting a `Declaration::Theorem`
    /// that merely wraps a `Declaration::Axiom` as a genuine proof. The kernel
    /// theorem's declared type is a Pi-chain, so the corresponding proof term
    /// must be a Lambda (or at minimum an App headed by something other than
    /// a single axiom Const). A lone `Const(name, _)` head would be the classic
    /// axiom-wrapper pattern we are guarding against.
    #[test]
    fn test_ibp_linear_sound_proof_is_not_axiom_wrapper() {
        use clean_kernel::ExprKind;
        let report = verify_kernel_ibp_linear_sound()
            .expect("kernel env should accept NNVerify.ibp_linear_sound");
        match report.proof_term.kind() {
            ExprKind::Lam(..) => { /* expected shape for a Pi-typed theorem */ }
            ExprKind::App(..) => { /* allowable — still contentful, not a bare Const */ }
            ExprKind::Const(name, _) => {
                panic!(
                    "proof term is a bare Const({name:?}) — axiom-wrapper pattern forbidden \
                     by design doc Proof Soundness Rules"
                );
            }
            other => panic!("proof term has unexpected shape for a Pi-typed theorem: {other:?}"),
        }
    }
}
