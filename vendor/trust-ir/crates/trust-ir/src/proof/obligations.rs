// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof obligations and their machine-readable payloads: [`ProofObligation`],
//! [`ObligationKind`], [`ProofStatus`], [`ProofFormula`], the module-level
//! [`ProofSummary`], the embedded [`ProofObligationSourceIdentity`], and the
//! per-call-site [`ProofContext`].

use super::evidence::ProofDigest;
use crate::value::{BlockId, FuncId, ProofId, SourceSpan};

/// Maximum UTF-8 byte length of a source, assertion, or public obligation id.
pub const PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES: usize = 1024;

/// Source/assertion ids preserve frontend text, including internal Unicode and
/// spaces, but must be nonempty, bounded, trimmed, and control-free.
pub fn is_valid_proof_obligation_source_text_id(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES
        && value.trim() == value
        && !value.chars().any(char::is_control)
}

/// Public obligation ids use a stricter canonical transport spelling: visible
/// ASCII only, excluding URI query/fragment delimiters.
pub fn is_canonical_public_obligation_id(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= PROOF_OBLIGATION_SOURCE_TEXT_ID_MAX_BYTES
        && value
            .bytes()
            .all(|byte| byte.is_ascii_graphic() && !matches!(byte, b'?' | b'#'))
}

/// Summary of proof obligation statuses within a module.
///
/// Used by TrustIr to quickly determine the overall proof health of a module
/// before attempting cross-target synthesis.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofSummary {
    pub pending: usize,
    /// Rows carrying the public `Discharged` status. This count does not imply
    /// that any certificate was replayed.
    pub discharged: usize,
    pub failed: usize,
    pub trusted: usize,
    /// Rows carrying the public `Certified` status. Counted separately for
    /// reporting only; the summary has no evidence table or validator
    /// capability and therefore cannot confirm a kernel replay.
    #[cfg_attr(feature = "serde", serde(default))]
    pub certified: usize,
}

impl ProofSummary {
    /// Total number of proof obligations.
    pub fn total(&self) -> usize {
        self.pending + self.discharged + self.failed + self.trusted + self.certified
    }

    /// Returns true if no obligation is pending or failed.
    ///
    /// NOTE: this is a *status-level* check, not an evidence-level one. It treats
    /// `Trusted` (a manual audit taken on faith) as satisfied, so an all-`Trusted`
    /// or empty summary reports `true`.
    /// [`statuses_claim_strong_completion`](Self::statuses_claim_strong_completion)
    /// is a stricter status-only report. Neither method validates evidence; an
    /// admission path must use a replay capability.
    pub fn is_fully_verified(&self) -> bool {
        self.pending == 0 && self.failed == 0
    }

    /// Status-only report: at least one row exists and every row *claims* a
    /// strong status (no pending, failed, or trusted rows). This does not
    /// validate evidence and must never authorize optimization or proof reuse.
    pub fn statuses_claim_strong_completion(&self) -> bool {
        self.pending == 0 && self.failed == 0 && self.trusted == 0 && self.total() > 0
    }

    /// Backward-compatible name for [`Self::statuses_claim_strong_completion`].
    ///
    /// This method is deprecated because “verified” was routinely read as an
    /// evidence judgment even though `ProofSummary` contains status counts
    /// only. Use the explicitly status-only name for reporting, and
    /// `obligation_has_replayed_authority` (with a real replay capability) for
    /// admission decisions.
    #[deprecated(
        note = "status counts do not validate evidence; use statuses_claim_strong_completion only for reporting"
    )]
    pub fn is_fully_verified_strict(&self) -> bool {
        self.statuses_claim_strong_completion()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
// Trust (trust-ir-spine Phase 2, item T1): `#[non_exhaustive]` so the spine can
// grow routing-grade panic-class kinds (`ArithmeticSafety`, `BoundsCheck`, …)
// matching `trust_verifier_api::ObligationKind` without a lockstep break of
// every downstream exhaustive match. Adding the wildcard arm downstream is the
// one-time cost; future variants are then additive.
#[non_exhaustive]
pub enum ObligationKind {
    Precondition,
    Postcondition,
    LoopInvariant,
    TypeInvariant,
    RefinementType,
    TranslationValidation,
    MemorySafety,
    PanicFreedom,
    TemporalSafety,
    Liveness,
    /// Panic-class arithmetic safety: overflow (add/sub/mul/neg), shift-amount
    /// range, division/remainder-by-zero. Routes identically to `PanicFreedom`
    /// today (it *is* a panic-freedom obligation) but preserves the
    /// arithmetic-vs-bounds distinction the trust-types/router path makes,
    /// matching `trust_verifier_api::ObligationKind::ArithmeticSafety`.
    ArithmeticSafety,
    /// Panic-class bounds safety: array/slice index-in-bounds checks. Routes
    /// identically to `PanicFreedom` today, but preserves the distinction
    /// matching `trust_verifier_api::ObligationKind::BoundsCheck`. NOTE: this is
    /// a panic-freedom obligation, NOT `MemorySafety` — `MemorySafety` routes to
    /// borrow-check, which would mis-categorize a bounds panic.
    BoundsCheck,
    /// `(f_fwd, f_back_*)` refine the value-at-address semantics of a `&mut`
    /// function (Aeneas-style give-back view); status `Pending` until a Clean
    /// refinement certificate discharges it.
    GiveBackRefinement,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ProofStatus {
    Pending,
    Discharged,
    Failed,
    Trusted,
    /// Discharged by a kernel-checkable CIC proof term (the de Bruijn
    /// "Certified" tier). Strictly stronger than `Trusted`: where `Trusted`
    /// is a manual audit justification taken on faith, `Certified` is backed
    /// by a `ProofEvidence::CleanCic` payload a kernel can re-check.
    Certified,
}

/// Machine-readable formula carried by a proof obligation.
///
/// `description` remains the human-facing explanation. `ProofFormula` is
/// the verifier-facing payload: a stable schema name plus an opaque payload
/// that producers and consumers agree on. Optional SMT-LIB and sort strings
/// let routers index and dispatch obligations without reparsing
/// producer-specific JSON first.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofFormula {
    /// Schema identifier for `payload`, for example `trust-types.Formula@1`.
    pub schema: String,
    /// Opaque formula payload in the named schema.
    pub payload: String,
    /// Optional SMT-LIB2 rendering of the same formula.
    // R3 #5: the canonical Module MessagePack codec (`rmp_serde::to_vec`) serializes
    // structs POSITIONALLY (as arrays) and may only skip a TRAILING field — a
    // skipped non-last field shifts every later field into the wrong slot
    // (smtlib=None/sort=Some silently round-tripped back as smtlib=Some/sort=None,
    // corrupting this live `FunctionSummary` contract-clause carrier). `smtlib` is
    // NOT the last field, so it must ALWAYS be emitted; only the trailing `sort` may
    // skip. `default` preserves backward-compatible decode of shorter legacy arrays.
    #[cfg_attr(feature = "serde", serde(default))]
    pub smtlib: Option<String>,
    /// Optional SMT-LIB2 sort of the formula.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub sort: Option<String>,
}

impl ProofFormula {
    pub fn new(schema: impl Into<String>, payload: impl Into<String>) -> Self {
        Self {
            schema: schema.into(),
            payload: payload.into(),
            smtlib: None,
            sort: None,
        }
    }

    pub fn smtlib2(text: impl Into<String>, sort: impl Into<String>) -> Self {
        let text = text.into();
        Self {
            schema: "smtlib2".to_string(),
            payload: text.clone(),
            smtlib: Some(text),
            sort: Some(sort.into()),
        }
    }

    pub fn trust_types_json(
        json: impl Into<String>,
        smtlib: impl Into<String>,
        sort: impl Into<String>,
    ) -> Self {
        Self {
            schema: "trust-types.Formula@1".to_string(),
            payload: json.into(),
            smtlib: Some(smtlib.into()),
            sort: Some(sort.into()),
        }
    }
}

impl core::fmt::Display for ObligationKind {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            ObligationKind::Precondition => "precondition",
            ObligationKind::Postcondition => "postcondition",
            ObligationKind::LoopInvariant => "loop_invariant",
            ObligationKind::TypeInvariant => "type_invariant",
            ObligationKind::RefinementType => "refinement_type",
            ObligationKind::TranslationValidation => "translation_validation",
            ObligationKind::MemorySafety => "memory_safety",
            ObligationKind::PanicFreedom => "panic_freedom",
            ObligationKind::TemporalSafety => "temporal_safety",
            ObligationKind::Liveness => "liveness",
            ObligationKind::ArithmeticSafety => "arithmetic_safety",
            ObligationKind::BoundsCheck => "bounds_check",
            ObligationKind::GiveBackRefinement => "give_back_refinement",
        })
    }
}

impl core::fmt::Display for ProofStatus {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            ProofStatus::Pending => "pending",
            ProofStatus::Discharged => "discharged",
            ProofStatus::Failed => "failed",
            ProofStatus::Trusted => "trusted",
            ProofStatus::Certified => "certified",
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofObligation {
    pub id: ProofId,
    pub kind: ObligationKind,
    pub status: ProofStatus,
    pub description: String,
    // R3 #5 (same rule as `ProofFormula::smtlib`): the canonical MessagePack
    // codec (`rmp_serde::to_vec`) serializes structs POSITIONALLY and may only
    // skip a TRAILING field. `formula` is NOT the last field — skipping it when
    // `function` is `Some` shifted the `FuncId` into the formula slot and made
    // the obligation undecodable ("invalid type: integer, expected struct
    // ProofFormula"). So `formula` must ALWAYS be emitted; only the trailing
    // `source` follows this field in v28, so `function` must ALWAYS be emitted:
    // skipping None when source is Some would shift the source record into the
    // function slot. `default` preserves old JSON/short positional arrays.
    #[cfg_attr(feature = "serde", serde(default))]
    pub formula: Option<ProofFormula>,
    /// The function this obligation is a pre/postcondition OF, if known.
    /// Turns `InheritedFromCallee` from "discharged somewhere in the module"
    /// into "this exact callee discharged this exact obligation" (B4). `None`
    /// for legacy/unscoped obligations (back-compat).
    #[cfg_attr(feature = "serde", serde(default))]
    pub function: Option<FuncId>,
    /// Exact frontend/public identity for this obligation. Generic or legacy
    /// obligations may omit it. Appended in v28 so legacy serde/binary payloads
    /// decode to `None` without shifting any earlier field.
    ///
    /// MUST ALWAYS BE EMITTED. It carried `skip_serializing_if` while it was the
    /// trailing field, which was correct then — but `site` was appended after it,
    /// and positional MessagePack may only skip a TRAILING field. Skipping a
    /// `None` `source` when `site` is `Some` shifted the site record into the
    /// source slot and made the obligation undecodable. This is the same trap
    /// `formula` and `function` above are annotated for; `source` simply joined
    /// them the moment it stopped being last.
    #[cfg_attr(feature = "serde", serde(default))]
    pub source: Option<ProofObligationSourceIdentity>,
    /// The exact IR position this obligation is ABOUT.
    ///
    /// `function` (B4) scopes an obligation to a whole function; that is enough
    /// for a pre/postcondition but NOT for a per-check obligation. A function
    /// carrying twelve bounds checks has twelve obligations that `function`
    /// alone cannot tell apart, so any verifier trying to back one of them with
    /// a solver verdict has to guess — and the only available guess ("every
    /// condition in the body was proved, so every obligation in the function is
    /// backed") is unsound the moment the body's conditions do not correspond
    /// one-to-one with its obligations.
    ///
    /// `site` is the fix: it names the `(block, inst_index)` of the instruction
    /// whose check this obligation states. A verifier may back the obligation
    /// only with the condition generated AT that position. `None` means "no
    /// position recorded", which every fail-closed consumer must treat as
    /// unbindable rather than as a wildcard.
    ///
    /// Appended AFTER `source` (v34): positional MessagePack may only skip a
    /// trailing field, so this must stay last — and appending it is precisely
    /// what forced `source` above to drop its own `skip_serializing_if`.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub site: Option<ObligationSite>,
}

/// The IR position an obligation is about: a specific instruction node inside
/// a specific block of the obligation's owning function.
///
/// Deliberately NOT a `ValueId`: the checks these bind to (a lowered `Assert`
/// arriving as a `CondBr`, a `Store`, a `Dealloc`) are terminators or
/// effectful nodes that produce no result value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ObligationSite {
    /// Function containing the site. Must agree with `ProofObligation::function`
    /// when that is also set — the validator enforces it.
    pub function: FuncId,
    /// Block containing the instruction.
    pub block: BlockId,
    /// Index of the instruction within `block.body`.
    pub inst_index: u32,
}

impl ObligationSite {
    pub fn new(function: FuncId, block: BlockId, inst_index: u32) -> Self {
        Self {
            function,
            block,
            inst_index,
        }
    }
}

/// Exact source range for an obligation, retaining both endpoints.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofObligationSourceRange {
    /// Index into [`crate::Module::files`].
    pub file: u32,
    pub start_line: u32,
    pub start_col: u32,
    pub end_line: u32,
    pub end_col: u32,
}

/// Atomic public proof-unit identity. The textual id and semantic digest must
/// never be inferred or updated independently.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PublicObligationIdentity {
    pub obligation_id: String,
    pub semantic_digest: ProofDigest,
}

/// Exact frontend source identity embedded in one [`ProofObligation`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofObligationSourceIdentity {
    pub source_id: String,
    pub assertion_id: String,
    // Positional serde: `range` is not trailing when `public` is present, so it
    // must always serialize (including explicit None).
    #[cfg_attr(feature = "serde", serde(default))]
    pub range: Option<ProofObligationSourceRange>,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub public: Option<PublicObligationIdentity>,
}

impl ProofObligationSourceIdentity {
    pub fn new(source_id: impl Into<String>, assertion_id: impl Into<String>) -> Self {
        Self {
            source_id: source_id.into(),
            assertion_id: assertion_id.into(),
            range: None,
            public: None,
        }
    }

    pub fn with_range(mut self, range: ProofObligationSourceRange) -> Self {
        self.range = Some(range);
        self
    }

    pub fn with_public(mut self, public: PublicObligationIdentity) -> Self {
        self.public = Some(public);
        self
    }
}

/// Per-call-site proof transfer (B5). Attached to a `Call`/`CallIndirect`
/// node, it declares which callee postconditions the caller may ASSUME after
/// the call and which callee preconditions the caller must ESTABLISH before
/// it — the contract that lets per-function proofs compose into a
/// whole-program proof. Both reference module `ProofObligation` ids.
#[derive(Debug, Clone, PartialEq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofContext {
    /// Callee postconditions the caller may rely on after the call returns.
    pub assumes: Vec<ProofId>,
    /// Callee preconditions the caller must establish before the call.
    pub establishes: Vec<ProofId>,
}

impl ProofObligation {
    pub fn new(
        id: ProofId,
        kind: ObligationKind,
        status: ProofStatus,
        description: impl Into<String>,
    ) -> Self {
        Self {
            id,
            kind,
            status,
            description: description.into(),
            formula: None,
            function: None,
            source: None,
            site: None,
        }
    }

    /// Scope this obligation to the function it is a pre/postcondition OF (B4).
    pub fn with_function(mut self, function: FuncId) -> Self {
        self.function = Some(function);
        self
    }

    pub fn with_formula(mut self, formula: ProofFormula) -> Self {
        self.formula = Some(formula);
        self
    }

    pub fn with_source(mut self, source: ProofObligationSourceIdentity) -> Self {
        self.source = Some(source);
        self
    }

    /// Bind this obligation to the exact IR instruction whose check it states.
    pub fn with_site(mut self, site: ObligationSite) -> Self {
        self.site = Some(site);
        self
    }

    pub fn has_formula(&self) -> bool {
        self.formula.is_some()
    }
}

/// A diagnostic attached to a proof obligation — the actionable payload a
/// verifier (ay/ty/Lean) emits when it cannot discharge (or wants to annotate)
/// an obligation. Carried as a module-level sidecar (`Module.obligation_
/// diagnostics`) keyed by `obligation`, so adding diagnostics does not change
/// the `ProofObligation` shape or its wire layout. Verifier-agnostic: the
/// `message` is human-readable, `location` points into the debug-info source
/// table when known, and `detail` carries an optional machine-readable blob
/// (e.g. a counterexample model) the producing verifier defines.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ObligationDiagnostic {
    /// The obligation this diagnostic is about.
    pub obligation: ProofId,
    /// Severity / kind of the diagnostic.
    pub severity: DiagnosticSeverity,
    /// Human-readable message.
    pub message: String,
    // R3 #5 (same rule as `ProofObligation::formula`): the canonical MessagePack
    // codec (`rmp_serde::to_vec`) serializes structs POSITIONALLY and may only
    // skip a TRAILING field. `location` is NOT the last field — skipping it when
    // `detail` is `Some` shifted the detail string into the location slot and
    // made the diagnostic undecodable ("invalid type: string, expected struct
    // SourceSpan"). So `location` must ALWAYS be emitted; only the trailing
    // `detail` may skip. `default` preserves backward-compatible decode of
    // shorter legacy arrays / older JSON without the field.
    /// Source location, if known (`SourceSpan::file` indexes `Module.files`).
    #[cfg_attr(feature = "serde", serde(default))]
    pub location: Option<SourceSpan>,
    /// Optional verifier-defined machine-readable detail (e.g. a counterexample).
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub detail: Option<String>,
}

/// Severity of an [`ObligationDiagnostic`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum DiagnosticSeverity {
    /// The obligation could not be discharged (a real failure).
    #[default]
    Error,
    /// Advisory (e.g. discharged only via a `Trusted` rung).
    Warning,
    /// Informational note.
    Note,
}

impl core::fmt::Display for DiagnosticSeverity {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            DiagnosticSeverity::Error => "error",
            DiagnosticSeverity::Warning => "warning",
            DiagnosticSeverity::Note => "note",
        })
    }
}

impl ObligationDiagnostic {
    /// A new error-severity diagnostic for `obligation`.
    pub fn error(obligation: ProofId, message: impl Into<String>) -> Self {
        Self {
            obligation,
            severity: DiagnosticSeverity::Error,
            message: message.into(),
            location: None,
            detail: None,
        }
    }

    /// A new note-severity diagnostic for `obligation`.
    ///
    /// The severity that lets a verifier RECORD evidence without CLAIMING a
    /// status. A solver verdict that is real but not yet replayable-and-bound
    /// belongs here: visible, machine-readable, and carrying no authority.
    pub fn note(obligation: ProofId, message: impl Into<String>) -> Self {
        Self {
            obligation,
            severity: DiagnosticSeverity::Note,
            message: message.into(),
            location: None,
            detail: None,
        }
    }

    /// Builder: attach a source location.
    pub fn with_location(mut self, span: SourceSpan) -> Self {
        self.location = Some(span);
        self
    }

    /// Builder: attach a machine-readable detail blob.
    pub fn with_detail(mut self, detail: impl Into<String>) -> Self {
        self.detail = Some(detail.into());
        self
    }
}
