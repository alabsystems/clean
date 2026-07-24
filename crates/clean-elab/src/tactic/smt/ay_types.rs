// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ay SMT solver types and configuration.
//!
//! Solver driver logic lives in `ay_solver.rs`. Part of #2518.

#[cfg(any(feature = "ay-smt", test))]
use crate::tactic::smt_translate::SmtSort;
#[cfg(feature = "ay-smt")]
use clean_auto::bridge::ay_contract::{AyBackendConfig, TriggerPolicy};
use clean_auto::bridge::ay_contract::{AyLogic, ProofProfile};
#[cfg(any(feature = "ay-smt", test))]
use clean_kernel::{name::Name, Expr};

/// SMT verification policy for ay tactics
///
/// Controls how ay UNSAT results are verified and selected at the tactic
/// boundary. This allows balancing performance vs trust level depending on the
/// use case.
///
/// # Trust Levels
///
/// | Policy | Performance | Trust Level | Use Case |
/// |--------|-------------|-------------|----------|
/// | TrustSolver | Fastest | Tier 0 | Interactive development |
/// | ExtractOnly | Slow | Tier 0 | Paranoid logging, debugging |
/// | VerifyCarcara | Slowest | Tier 1 | Production proofs, CI |
/// | VerifyStrict | Slowest | Tier 1 | Self-verification, soundness-critical |
///
/// # Example
///
/// ```text
/// // Default: fast solving, no external proof check
/// let config = AyConfig::default();
///
/// // Production: verify with Carcara
/// let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::VerifyCarcara);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SmtVerifyPolicy {
    /// Fast path - no external proof check at the ay tactic boundary
    ///
    /// Uses `AyBackend` for solving. The tactic still runs selected-proof
    /// acceptance, but it skips independent external verification. Accepted
    /// direct proofs can therefore retain embedded `trustedAy` sub-terms. This
    /// is the default for interactive use.
    #[default]
    TrustSolver,

    /// Extract Alethe proof but don't verify (paranoid logging)
    ///
    /// Uses `AyProofBackend` with proof production enabled so the tactic can
    /// extract Alethe proofs, run kernel reconstruction/selection, and keep
    /// residual trust accounting. Useful for debugging or when you want proof
    /// artifacts without an external checker.
    ExtractOnly,

    /// Verify with Carcara (requires carcara-verify feature)
    ///
    /// Uses `AyProofBackend` with Carcara verification. Supported UNSAT proofs
    /// are independently checked before acceptance, which catches ay
    /// soundness bugs for `QF_LIA`/`QF_LRA`/`QF_UF` theories.
    VerifyCarcara,

    /// Strictest: only accept fully-verifiable theories
    ///
    /// Uses `AyProofBackend` with a strict theory whitelist. The current
    /// strict contract has two explicit outcomes:
    ///
    /// 1. supported strict fragments (`QF_UF`, `QF_LIA`, `QF_LRA`) must
    ///    produce zero-trust acceptance
    /// 2. unsupported strict logics (for example `QF_BV`, `QF_AUFLIA`, and
    ///    combined or quantified lanes) are rejected at the ay proof boundary
    ///    so the caller can fail closed or fall back
    ///
    /// Use for self-verification and soundness-critical proofs.
    VerifyStrict,
}

/// Error returned when parsing a textual SMT-LIB logic override.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("invalid Ay logic name: {0}")]
pub struct InvalidAyLogicName(String);

impl InvalidAyLogicName {
    #[must_use]
    pub fn name(&self) -> &str {
        &self.0
    }
}

/// Configuration options for Ay tactics
///
/// This wraps `AyBackendConfig` from clean-auto and adds tactic-specific options.
/// The backend config handles timeout, verbose output, and proof production.
#[derive(Debug, Clone)]
#[must_use]
pub struct AyConfig {
    /// Timeout in milliseconds (default: 5000, None = no timeout)
    timeout_ms: Option<u64>,
    /// Verbose output (print SMT-LIB2 and result)
    verbose: bool,
    /// Override logic detection (e.g., `QF_LIA`, `QF_BV`)
    /// If None, the tactic will use its default logic.
    logic: Option<AyLogic>,
    /// Whether to request proof production from Ay
    produce_proofs: bool,
    /// Verification policy for UNSAT results (default: TrustSolver)
    ///
    /// Controls whether and how ay UNSAT results are independently verified.
    /// See [`SmtVerifyPolicy`] for details on each option.
    verify_policy: SmtVerifyPolicy,
    /// Policy for quantifier trigger selection (default: Auto)
    ///
    /// Controls how user-provided triggers interact with solver-inferred triggers.
    /// See `TriggerPolicy` for available options.
    #[cfg(feature = "ay-smt")]
    trigger_policy: TriggerPolicy,
}

impl Default for AyConfig {
    fn default() -> Self {
        Self {
            timeout_ms: Some(5000),
            verbose: false,
            logic: None,
            produce_proofs: false,
            verify_policy: SmtVerifyPolicy::default(),
            #[cfg(feature = "ay-smt")]
            trigger_policy: TriggerPolicy::default(),
        }
    }
}

impl AyConfig {
    /// Create a AyConfig with verify policy from the `CLEAN_SMT_VERIFY` env var.
    ///
    /// | Env value | Policy | Effect |
    /// |-----------|--------|--------|
    /// | `"trust"` | `TrustSolver` | Fast path, no external proof check |
    /// | (unset) / `"extract"` | `ExtractOnly` | Extract Alethe proof + selected-proof reconstruction |
    /// | `"carcara"` | `VerifyCarcara` | Independent Carcara proof check before accepting supported proofs |
    /// | `"strict"` | `VerifyStrict` | Zero-trust acceptance for supported strict fragments |
    ///
    /// Default is `ExtractOnly` to activate the proof extraction and
    /// selected-proof pipeline. Use `CLEAN_SMT_VERIFY=trust` to opt out of
    /// external verification for performance-sensitive use. When a
    /// non-`TrustSolver` policy is selected, `produce_proofs` is set to `true`
    /// so `AyProofBackend` enables proof extraction from the solver. The
    /// tactic wrappers may still fail closed or fall back to native `decide`
    /// after selection rejects a proof. Part of #302, #2427.
    ///
    /// # Contract
    ///
    /// ENSURES: `produce_proofs` == true iff `verify_policy` != `TrustSolver`
    /// ENSURES: Unrecognized env values default to `ExtractOnly`
    pub fn from_env() -> Self {
        let policy = match std::env::var("CLEAN_SMT_VERIFY").ok().as_deref() {
            Some("trust") => SmtVerifyPolicy::TrustSolver,
            Some("extract") => SmtVerifyPolicy::ExtractOnly,
            Some("carcara") => SmtVerifyPolicy::VerifyCarcara,
            Some("strict") => SmtVerifyPolicy::VerifyStrict,
            _ => SmtVerifyPolicy::ExtractOnly,
        };
        let produce_proofs = policy != SmtVerifyPolicy::TrustSolver;
        Self {
            verify_policy: policy,
            produce_proofs,
            ..Default::default()
        }
    }

    #[must_use]
    pub fn timeout_ms(&self) -> Option<u64> {
        self.timeout_ms
    }

    pub fn with_timeout_ms(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = Some(timeout_ms);
        self
    }

    #[must_use]
    pub fn is_verbose(&self) -> bool {
        self.verbose
    }

    pub fn verbose(mut self) -> Self {
        self.verbose = true;
        self
    }

    #[must_use]
    pub fn logic_override(&self) -> Option<AyLogic> {
        self.logic
    }

    pub fn with_logic(mut self, logic: AyLogic) -> Self {
        self.logic = Some(logic);
        self
    }

    pub fn try_with_logic_name(self, logic: &str) -> Result<Self, InvalidAyLogicName> {
        Ok(self.with_logic(Self::parse_logic_name(logic)?))
    }

    pub fn parse_logic_name(logic: &str) -> Result<AyLogic, InvalidAyLogicName> {
        match logic {
            "ALL" => Ok(AyLogic::All),
            "QF_LIA" => Ok(AyLogic::QfLia),
            "QF_LRA" => Ok(AyLogic::QfLra),
            "QF_UF" => Ok(AyLogic::QfUf),
            "QF_UFLIA" => Ok(AyLogic::QfUflia),
            "QF_BV" => Ok(AyLogic::QfBv),
            "QF_AUFLIA" => Ok(AyLogic::QfAuflia),
            "UF" => Ok(AyLogic::Uf),
            "UFLIA" => Ok(AyLogic::Uflia),
            _ => Err(InvalidAyLogicName(logic.to_string())),
        }
    }

    #[must_use]
    pub fn produces_proofs(&self) -> bool {
        self.produce_proofs
    }

    #[cfg(test)]
    pub(crate) fn enable_proofs(mut self) -> Self {
        self.produce_proofs = true;
        self
    }

    #[must_use]
    pub fn verify_policy(&self) -> SmtVerifyPolicy {
        self.verify_policy
    }

    pub fn with_verify_policy(mut self, verify_policy: SmtVerifyPolicy) -> Self {
        self.verify_policy = verify_policy;
        // Maintain the `from_env` invariant: produce_proofs ↔ non-TrustSolver.
        self.produce_proofs = verify_policy != SmtVerifyPolicy::TrustSolver;
        self
    }

    /// Parse the configured SMT-LIB logic, defaulting to `QF_UF`.
    #[cfg_attr(not(any(feature = "ay-smt", test)), allow(dead_code))]
    pub(super) fn effective_logic(&self) -> AyLogic {
        self.logic_override().unwrap_or(AyLogic::QfUf)
    }

    /// Convert to backend configuration for the given logic
    ///
    /// REQUIRES: `logic` is the solver logic the backend should enforce
    /// ENSURES: Returned config preserves this struct's timeout/verbose/proof settings
    /// ENSURES: Returned config targets the requested `logic`
    #[cfg(feature = "ay-smt")]
    pub(super) fn to_backend_config(&self, logic: AyLogic) -> AyBackendConfig {
        let mut config = AyBackendConfig::new(logic);
        if let Some(ms) = self.timeout_ms {
            config = config.timeout(ms);
        }
        if self.verbose {
            config = config.verbose();
        }
        if self.produce_proofs {
            config = config.enable_proofs();
        }
        config = config.trigger_policy(self.trigger_policy);
        config
    }
}

#[cfg_attr(not(feature = "ay-smt"), allow(dead_code))]
const KNOWN_AY_LOGICS: [AyLogic; 10] = [
    AyLogic::All,
    AyLogic::QfLia,
    AyLogic::QfLra,
    AyLogic::QfUf,
    AyLogic::QfUflia,
    AyLogic::QfBv,
    AyLogic::QfAuflia,
    AyLogic::QfFp,
    AyLogic::Uf,
    AyLogic::Uflia,
];

/// Explicit `VerifyStrict` behavior for a given solver logic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum StrictLogicBehavior {
    /// The logic is currently in the zero-trust strict rollout.
    SupportedZeroTrust,
    /// The strict ay proof lane must reject this logic and let the caller
    /// fail closed or fall back.
    UnsupportedRejectAndFallback,
}

/// Classify the current strict-policy behavior for a solver logic.
pub(super) fn verify_strict_logic_behavior(logic: AyLogic) -> StrictLogicBehavior {
    match logic {
        AyLogic::QfUf | AyLogic::QfLia | AyLogic::QfLra => StrictLogicBehavior::SupportedZeroTrust,
        AyLogic::All
        | AyLogic::QfUflia
        | AyLogic::QfBv
        | AyLogic::QfAuflia
        | AyLogic::QfFp
        | AyLogic::Uf
        | AyLogic::Uflia
        | _ => StrictLogicBehavior::UnsupportedRejectAndFallback,
    }
}

/// Proof profile used by `VerifyStrict`.
///
/// This keeps the proof-profile gate aligned with the same supported strict
/// fragment set as the zero-trust reconstruction helpers.
#[cfg_attr(not(feature = "ay-smt"), allow(dead_code))]
pub(super) fn verify_strict_proof_profile() -> ProofProfile {
    let theory_names: Vec<String> = KNOWN_AY_LOGICS
        .iter()
        .copied()
        .filter(|logic| {
            verify_strict_logic_behavior(*logic) == StrictLogicBehavior::SupportedZeroTrust
        })
        .map(|logic| logic.to_string())
        .collect();
    let theory_refs: Vec<&str> = theory_names.iter().map(String::as_str).collect();
    ProofProfile::carcara_verified_with_theories(&theory_refs)
}

/// Returns true when the policy+logic pair requires a zero-trust direct proof.
///
/// This derives from [`verify_strict_logic_behavior`] so the runtime strict
/// policy, reconstruction budget, and proof-profile gate stay aligned.
pub(super) fn requires_zero_trust_reconstruction(policy: SmtVerifyPolicy, logic: AyLogic) -> bool {
    policy == SmtVerifyPolicy::VerifyStrict
        && verify_strict_logic_behavior(logic) == StrictLogicBehavior::SupportedZeroTrust
}

/// Map an SMT sort to the corresponding Lean kernel type expression.
///
/// `SmtSort::Bool` → `Prop`, `SmtSort::Int` → `Int`, `SmtSort::Real` → `Real`.
/// Used by `SmtSolver::Verifiable` to populate `VariableMapping` types.
///
/// # Contract
///
/// ENSURES: `SmtSort::Bool` maps to `Expr::prop()` (Sort 0)
/// ENSURES: `SmtSort::Int` maps to `Const("Int", [])` expression
/// ENSURES: `SmtSort::Real` maps to `Const("Real", [])` expression
#[cfg(any(feature = "ay-smt", test))]
pub(super) fn smt_sort_to_lean_type(sort: SmtSort) -> Expr {
    match sort {
        SmtSort::Bool => Expr::prop(),
        SmtSort::Int => Expr::const_(Name::from_string("Int"), vec![]),
        SmtSort::Real => Expr::const_(Name::from_string("Real"), vec![]),
    }
}

#[cfg(feature = "ay-smt")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum SupportedLocalDeclKind {
    Scalar(SmtSort),
    Callable { result_sort: SmtSort },
}

#[cfg(feature = "ay-smt")]
fn supported_smt_sort_from_const_name(name: &str) -> Option<SmtSort> {
    match name {
        "Bool" => Some(SmtSort::Bool),
        "Nat" | "Int" => Some(SmtSort::Int),
        "Real" | "Rat" => Some(SmtSort::Real),
        _ => None,
    }
}

#[cfg(feature = "ay-smt")]
pub(super) fn supported_local_decl_kind(lean_type: &Expr) -> Option<SupportedLocalDeclKind> {
    let lean_type = lean_type.strip_mdata();
    if lean_type.is_prop() {
        return Some(SupportedLocalDeclKind::Scalar(SmtSort::Bool));
    }
    if lean_type.is_sort() {
        return None;
    }

    match lean_type.kind() {
        clean_kernel::ExprKind::Const(name, _) => {
            supported_smt_sort_from_const_name(&name.to_string())
                .map(SupportedLocalDeclKind::Scalar)
        }
        clean_kernel::ExprKind::Pi(_, _, _) => supported_callable_result_sort(lean_type)
            .map(|result_sort| SupportedLocalDeclKind::Callable { result_sort }),
        _ => None,
    }
}

#[cfg(feature = "ay-smt")]
fn supported_callable_result_sort(lean_type: &Expr) -> Option<SmtSort> {
    let mut current = lean_type.strip_mdata();
    while let clean_kernel::ExprKind::Pi(_, _, body) = current.kind() {
        current = body.strip_mdata();
    }

    if current.is_prop() {
        return Some(SmtSort::Bool);
    }

    match current.kind() {
        clean_kernel::ExprKind::Const(name, _) => {
            supported_smt_sort_from_const_name(&name.to_string())
        }
        _ => None,
    }
}
