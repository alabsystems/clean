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
    /// Well-founded termination: the `decreases` measure strictly descends on
    /// every back edge and is bounded below (v41).
    ///
    /// The shipping Trust compiler parses, elaborates and discharges
    /// `decreases` today, but had no kind to file it under — so it landed as
    /// `Liveness`, which the validator itself classes CATEGORY-AMBIGUOUS and
    /// therefore lets back ANY substantive claim. Mirrors
    /// `trust_verifier_api::ObligationKind::Termination`.
    Termination,
    /// Ownership / aliasing discipline: Send/Sync violations, data races,
    /// lifetime violations (v41).
    ///
    /// Deliberately NOT `MemorySafety`: that kind routes to borrow-check, and
    /// collapsing the two loses precisely the distinction a concurrency
    /// obligation needs. Mirrors `trust_verifier_api::ObligationKind::Ownership`.
    Ownership,
    /// Producer-namespaced kind (v41).
    ///
    /// `namespace` is AUTHORITY-BEARING — a consumer should admit it from a
    /// pinned list rather than trusting an arbitrary string — while `name` is
    /// a label within that namespace and is deliberately not sealed.
    /// `validate_module` admits exactly `ADMITTED_OBLIGATION_NAMESPACES`;
    /// must-refuse corpus row `refuse/custom_obligation_unpinned_namespace`.
    ///
    /// This is the ONLY payload-carrying variant, which is why
    /// [`ObligationKind`] does not derive `Copy` and why its binary codec had
    /// to leave the tag-only `tag_enum!` macro.
    Custom {
        /// Authority-bearing namespace, e.g. `trust.concurrency`.
        namespace: String,
        /// Label within `namespace`.
        name: String,
    },
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

impl ProofStatus {
    /// The DISCHARGED tier: `Discharged` or `Certified` — the statuses that
    /// claim the obligation holds on evidence (a `Trusted` row is a manual
    /// audit taken on faith, and is outside the tier).
    ///
    /// The one statement of the tier import authentication (R7's
    /// `ObligationNotDischarged`), the linked walk's restatement check, the
    /// per-clause `proved` rule, lineage closure, the proof-table transform,
    /// the authority predicates, bundle replay and the bundle digest read.
    /// Exhaustive on purpose: a status added later must be placed here.
    ///
    /// PROVED, every cell: `trust_ir_laws::laws::discharged_tier_*` (gate 13).
    #[inline]
    #[must_use]
    pub const fn is_discharged_tier(self) -> bool {
        match self {
            ProofStatus::Discharged | ProofStatus::Certified => true,
            ProofStatus::Pending | ProofStatus::Failed | ProofStatus::Trusted => false,
        }
    }

    /// The KERNEL tier: `Certified` alone — discharged by a kernel-checkable
    /// CIC proof term. The one statement of the tier trust-ir-build's
    /// validator reads wherever it re-checks or trusts a `CleanCic`
    /// certificate: the certified-evidence re-check, the unbound and
    /// source-unbound certificate rules, the `clean-kernel-tv` license
    /// evidence, the kernel-tier `ProofRef` authority set and the
    /// source-to-silicon composition.
    ///
    /// Strictly inside [`ProofStatus::is_discharged_tier`]: that inclusion
    /// is a hand step over the two tables' proved cells (five each), not a
    /// proved row — an implication between two tables is not a law form this
    /// lane proves (the `trust-ir-laws` crate docs).
    ///
    /// PROVED, every cell: `trust_ir_laws::laws::kernel_tier_*` (gate 13).
    #[inline]
    #[must_use]
    pub const fn is_kernel_tier(self) -> bool {
        match self {
            ProofStatus::Certified => true,
            ProofStatus::Pending
            | ProofStatus::Discharged
            | ProofStatus::Failed
            | ProofStatus::Trusted => false,
        }
    }
}

variant_shape! {
    /// The payload-free shape of an [`ObligationKind`]: its variant, with
    /// `Custom`'s namespace and name projected away, as a `Copy` value.
    ///
    /// The obligation-kind decision tables (import admission, the Clean-expr
    /// grounder's contract classification, the assert-class routing, the
    /// validator's category rules) are stated over this type, because a
    /// table over `&ObligationKind` is not provable in the verified lane
    /// (`variant_shape!`). `ObligationKind` is `#[non_exhaustive]` for
    /// DOWNSTREAM crates only: [`ObligationKind::shape`] is exhaustive here,
    /// so a new kind is a compile error until it has a shape, and then every
    /// whitelist table refuses it until it is placed.
    pub enum ObligationKindShape for ObligationKind {
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
        ArithmeticSafety,
        BoundsCheck,
        GiveBackRefinement,
        Termination,
        Ownership,
        Custom,
    }
}

impl ObligationKindShape {
    /// The L1 CONTRACT kinds whose predicate formula the Clean-expr grounder
    /// (`clean_expr_lowering::contract`) grounds: `Precondition`,
    /// `Postcondition`, `LoopInvariant`, `RefinementType`. Every other kind is
    /// not a contract predicate there and fails closed.
    ///
    /// `Termination` and `Ownership` (v41) are outside it BY DECISION, not by
    /// omission (roadmap WS1.9 DECIDE A, `docs/SPEC_RATIFICATIONS.md` §11): a
    /// `decreases` measure is a term, not a Bool predicate the grounder could
    /// decide, and no well-founded-measure kernel anchor is built. Both are
    /// discharged through a consumer capability as `Discharged`, never
    /// `Certified`; the two-language row
    /// `b2.gap.termination_not_kernel_certifiable` holds that shape.
    ///
    /// PROVED, every cell: `trust_ir_laws::laws::grounded_contract_kind_*`
    /// (gate 13).
    #[inline]
    #[must_use]
    pub const fn is_grounded_contract_kind(self) -> bool {
        matches!(
            self,
            ObligationKindShape::Precondition
                | ObligationKindShape::Postcondition
                | ObligationKindShape::LoopInvariant
                | ObligationKindShape::RefinementType
        )
    }

    /// Whether a free-variable-tautology goal of this kind is PROVED (needs a
    /// real proof term) rather than ASSUMED (a hypothesis with no proof term).
    ///
    /// SOUNDNESS — the single most important classification of the Clean-expr
    /// contract slice. A `Precondition` (and a `LoopInvariant` at entry) is
    /// ASSUMED: the body reasons under it, and the caller is on the hook to
    /// establish it. A `Postcondition` / `RefinementType` is PROVED: it is a
    /// claim to the caller, and assuming it would let an UNPROVEN
    /// postcondition mint `Certified`. Getting this backwards is the
    /// catastrophic failure mode. Every non-contract kind is `false` (it
    /// never reaches the free-variable path).
    ///
    /// PROVED, every cell: `trust_ir_laws::laws::free_var_proved_*` (gate 13).
    #[inline]
    #[must_use]
    pub const fn free_var_is_proved(self) -> bool {
        matches!(
            self,
            ObligationKindShape::Postcondition | ObligationKindShape::RefinementType
        )
    }

    /// The ASSERT-CLASS kinds: `BoundsCheck` and `ArithmeticSafety`, the only
    /// kinds a proof that a sited assert condition always holds may discharge
    /// ([`crate::proof::ASSERT_CLASS_OBLIGATION_KINDS`] is the same set as
    /// data, and is tested against this table).
    ///
    /// Deliberately narrow: such a proof is a panic-freedom fact about THAT
    /// check. `MemorySafety` is excluded (alignment and non-nullness are
    /// provenance facts a bit-vector condition does not establish), and
    /// `PanicFreedom` (a whole-function claim one site does not establish).
    ///
    /// PROVED, every cell: `trust_ir_laws::laws::assert_class_*` (gate 13).
    #[inline]
    #[must_use]
    pub const fn is_assert_class(self) -> bool {
        matches!(
            self,
            ObligationKindShape::BoundsCheck | ObligationKindShape::ArithmeticSafety
        )
    }
}

/// SMT sort of a clause-bound name (v41).
///
/// A STRUCTURAL MIRROR of `trust_ir_contract::Sort`, never an import: pulling
/// the contract crate into this one would break `trust-ir`'s
/// zero-required-dependency guarantee, which [`crate::FunctionSummary`]'s own
/// doc states is load-bearing. Variant order and wire tags are the mirrored
/// type's, so a `trust-ir-bridge` translation is a tag-preserving identity.
///
/// NOT `#[non_exhaustive]`, deliberately, even though `Sort` is: this is a
/// wire vocabulary with frozen tags. A `Sort` variant added upstream is a
/// version bump here, which is exactly the coupling we want — a silently
/// widened sort would let a clause claim a domain no reader can check.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ClauseSort {
    Bool,
    Int,
    BitVec(u32),
    Array(Box<ClauseSort>, Box<ClauseSort>),
    /// IEEE-754 binary FP: `eb` exponent bits, `sb` significand bits INCLUDING
    /// the hidden bit. `f32 = { eb: 8, sb: 24 }`, `f64 = { eb: 11, sb: 53 }`.
    Float {
        eb: u32,
        sb: u32,
    },
    RoundingMode,
    /// An algebraic datatype. An EMPTY `constructors` is a BY-NAME reference to
    /// a datatype defined elsewhere, NOT a zero-constructor datatype — the same
    /// convention `trust_ir_contract::Sort::Datatype` documents.
    Datatype {
        name: String,
        constructors: Vec<(String, Vec<(String, ClauseSort)>)>,
    },
}

/// The IR place a clause free name denotes (v41).
///
/// Vocabulary deliberately aligned with [`crate::SourcePlace`]: `Param { index }`
/// is the SAME index space as `SourcePlace::FunctionParameter { index }` and
/// `FuncTy::params`. It is a separate type because `SourcePlace` is a v35
/// authenticated-provenance vocabulary that cannot grow spec-only places
/// without changing what its binding digest attests.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ClausePlace {
    /// Formal parameter `index` of the owning function's `FuncTy::params`.
    Param { index: u32 },
    /// Return slot `index` of `FuncTy::returns` — the `result` symbol.
    ResultSlot { index: u32 },
    /// The value-at-EXIT of `&mut`/`*mut` parameter `index`: the Aeneas
    /// give-back place, and the only way to state a primed (`x'`)
    /// postcondition — the clause names it through a binding under a plain
    /// SMT-LIB2 symbol (`x_exit`); `x'` itself is no SMT-LIB2 token, and
    /// trust-ir's reader refuses it. Legal only on an `ensures` clause.
    MutParamExit { index: u32 },
    /// The ambient heap/world state, with NO epoch (v41).
    ///
    /// The legacy spelling: it cannot say whether it denotes the world
    /// before the call or after it, so a clause that binds it states nothing
    /// a caller can check. Since v59 it is UNBINDABLE on a `proved` summary
    /// (`trust_ir_build` refuses it by name); bind [`ClausePlace::WorldPre`]
    /// or [`ClausePlace::WorldPost`] instead. Kept, and still decoded, for
    /// every pre-v59 artifact.
    World,
    /// The in-flight unwind state. Illegal on a `requires` clause.
    Unwind,
    /// A named SSA value in the owning function's body. Never resolvable on a
    /// body-less contract-only declaration.
    Value(crate::value::ValueId),
    /// State variable `index` of the owning [`SpecModule`](crate::SpecModule)'s
    /// `vars` — the CURRENT-state value (v46).
    ///
    /// Meaningful ONLY inside a `SpecModule` (a typed invariant, or a leaf of
    /// a [`SpecTemporal`](crate::spec::SpecTemporal)). A function summary
    /// clause and a module proof obligation have no spec-variable index space,
    /// so both validators REFUSE it by name rather than resolving it to
    /// whatever parameter happens to share the number.
    SpecVar { index: u32 },
    /// The PRIMED, successor-state value of state variable `index` (v46).
    ///
    /// Legal only in an ACTION RELATION — the `relation` of a
    /// [`TemporalForm::WeakFair`](crate::spec::TemporalForm::WeakFair) or
    /// [`StrongFair`](crate::spec::TemporalForm::StrongFair) — because a
    /// successor value exists only where a transition does. A state predicate
    /// (an invariant, an `Always`/`Eventually`/`LeadsTo` leaf) that binds it
    /// is refused, as is any use outside a `SpecModule`.
    SpecVarNext { index: u32 },
    /// The ambient heap/world state at function ENTRY — the pre-state epoch
    /// (v59, roadmap WS1.14). Legal on every clause role.
    ///
    /// Together with [`ClausePlace::WorldPost`] this is what lets an `ensures`
    /// clause relate the world after a call to the world before it (`old(*g)`),
    /// which a single un-epoched [`ClausePlace::World`] cannot. What a call may
    /// change between the two epochs is bounded by the summary's
    /// [`crate::FunctionSummary::effects`] frame.
    WorldPre,
    /// The ambient heap/world state at function EXIT — the post-state epoch
    /// (v59). Legal only on an `ensures` clause: a precondition is evaluated
    /// before the call, and a termination measure on entry.
    WorldPost,
    /// The value at function ENTRY behind reference parameter `index`: the
    /// entry-state pointee `*x` of a `&T` / `&mut T` parameter (v62, roadmap
    /// DG-63 for WS5.5).
    ///
    /// The place a `requires *x > 0` or an `ensures result == old(*x)` binds.
    /// [`ClausePlace::Param`] is the reference itself, an IR pointer no clause
    /// sort reads, and [`ClausePlace::MutParamExit`] is the value at EXIT, so
    /// before v62 such a clause had no place and a producer carried it opaque
    /// (`trust.contract-opaque@1`). The binding is typed against `T`, never
    /// against the reference: binding `*x` as `Param { index }` at
    /// `BitVec(64)` is the width/type lie the binding check refuses.
    ///
    /// Legal on every clause role and on every obligation kind that may bind
    /// a parameter: the entry state exists before the call, so a precondition
    /// and a termination measure may read it, and with
    /// [`ClausePlace::MutParamExit`] an `ensures` clause can relate the exit
    /// value of a `&mut` to its entry value. Parameter `index` must be `&T` or
    /// `&mut T` (`Ty::Ref` / `Ty::RefMut`). A raw pointer, an untyped `Ptr`, a
    /// fat pointer, an `Rc` and a by-value parameter are refused by name: a
    /// reference is valid and aligned at entry by the type alone, and none of
    /// the others carries the premise that its pointee exists. A consumer
    /// MUST refuse a binding of this place on a parameter that is not a
    /// reference (`refuse/summary_clause_param_pointee_of_by_value_param`),
    /// and a reader MUST refuse its tag under a header older than its version
    /// (`refuse/blob_param_pointee_place_below_its_version`).
    ParamPointeeEntry { index: u32 },
}

/// One clause free name's sort and IR place (v41).
///
/// This is what makes a carried contract clause CHECKABLE rather than
/// decorative: without it a root verifier holding only the sealed module
/// cannot decide whether a clause's variables denote that function's
/// parameters, nor what arithmetic domain they range over — so it must
/// re-derive every verification condition from the body, and the carried
/// clause states nothing.
///
/// The `sort` is the axis on which a width-strip yields a wrong POSITIVE
/// rather than a refusal: `result + 1 > result` is true over `Int` and false
/// at `u64::MAX`, so a clause that fails to say `BitVec(64)` can be
/// "discharged" against a domain the program never had.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ClauseBinding {
    pub sort: ClauseSort,
    pub place: ClausePlace,
}

/// The [`ProofFormula::schema`] whose `payload` IS SMT-LIB2 text
/// ([`ProofFormula::smtlib2`]).
pub const SMTLIB2_FORMULA_SCHEMA: &str = "smtlib2";

/// Machine-readable formula carried by a proof obligation.
///
/// `description` remains the human-facing explanation. `ProofFormula` is
/// the verifier-facing payload: a stable schema name plus an opaque payload
/// that producers and consumers agree on. Optional SMT-LIB and sort strings
/// let routers index and dispatch obligations without reparsing
/// producer-specific JSON first.
///
/// # One formula
///
/// The formula IS `payload`, read in `schema`; `smtlib` is a rendering of it,
/// never a second formula. Which text a payload states is decided by its
/// schema, for every schema trust-ir owns
/// ([`super::OwnedFormulaSchema`], matched exhaustively; the table is in
/// [`super::formula_schema`]): an `smtlib2` payload IS its text, a
/// `trust-ir.Pred@1` citation states the cited predicate's rendering, and a
/// claim schema (bit-blast goal, SAT refutation, lineage binding) states no
/// SMT-LIB text. A formula whose rendering is not that one text states two
/// ([`Self::states_two_texts`]), and both validators refuse it WHEREVER a
/// module states it ([`crate::Module::stated_formulas`]: an obligation, a
/// summary clause, a spec carrier; and a bundle's replay atoms; must-refuse
/// corpus rows `refuse/formula_smtlib_rendering_disagrees`,
/// `refuse/summary_clause_smtlib_rendering_disagrees`,
/// `refuse/spec_carrier_smtlib_rendering_disagrees` and
/// `refuse/pred_citation_rendering_disagrees`): a consumer MUST NOT read
/// either text of such a formula. Any other schema is opaque: trust-ir never
/// compares its rendering and never reads either text as the formula.
///
/// Anything that READS the formula as SMT-LIB — to ground it (the kernel's
/// contract replay), to prove it (the bit-blast route's goal match) or to
/// compare it (the spec linker's typed carriers) — reads exactly
/// [`Self::smtlib_text`], through trust-ir's one SMT-LIB2 reader
/// ([`super::read_smtlib_term`]). (Before this rule the contract grounder
/// preferred `smtlib` whatever the schema, so a kernel replay of a true
/// rendering was admitted for an obligation whose payload was false; the spec
/// linker compared a typed carrier's rendering and never its payload; the
/// bit-blast route discharged an opaque payload on its rendering; and a
/// `pred.N` citation beside another predicate's rendering validated.)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofFormula {
    /// Schema identifier for `payload`, for example `trust-types.Formula@1`.
    pub schema: String,
    /// Opaque formula payload in the named schema.
    pub payload: String,
    /// Optional SMT-LIB2 rendering of the same formula. Under
    /// [`SMTLIB2_FORMULA_SCHEMA`] it must equal `payload` byte for byte.
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
    ///
    /// MUST ALWAYS BE EMITTED. It carried `skip_serializing_if` while it was
    /// the trailing field, which was correct then — but `bindings` was
    /// appended after it (v41), and positional MessagePack may only skip a
    /// TRAILING field. See the R3 #5 note on `smtlib` above.
    #[cfg_attr(feature = "serde", serde(default))]
    pub sort: Option<String>,
    /// Typed bindings for this clause's free names (v41): name -> (sort, IR place).
    ///
    /// An EMPTY `bindings` reads as UNBINDABLE, never as a wildcard — the v34
    /// `ObligationSite::site` precedent. A consumer that cannot resolve a
    /// clause's names must refuse to use the clause, not assume the names mean
    /// whatever is convenient. The must-refuse corpus cannot express this
    /// (`refuse/obligation_site_none_is_unbindable`): a module with empty
    /// bindings is well-formed and must be ACCEPTED; the obligation is on
    /// the consumer's binder, whose rung is its own test.
    ///
    /// Declared LAST and conditionally skipped so all pre-v41 positional serde
    /// arrays continue to decode empty.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub bindings: Vec<(String, ClauseBinding)>,
}

impl ProofFormula {
    pub fn new(schema: impl Into<String>, payload: impl Into<String>) -> Self {
        Self {
            schema: schema.into(),
            payload: payload.into(),
            smtlib: None,
            sort: None,
            bindings: Vec::new(),
        }
    }

    pub fn smtlib2(text: impl Into<String>, sort: impl Into<String>) -> Self {
        let text = text.into();
        Self {
            schema: SMTLIB2_FORMULA_SCHEMA.to_string(),
            payload: text.clone(),
            smtlib: Some(text),
            sort: Some(sort.into()),
            bindings: Vec::new(),
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
            bindings: Vec::new(),
        }
    }

    /// The ONE SMT-LIB2 text this formula states as its payload, or `None`:
    /// the payload of an [`SMTLIB2_FORMULA_SCHEMA`] formula whose `smtlib`
    /// rendering is absent or equal to it. `None` for an `smtlib2` formula
    /// whose rendering differs (two formulas), and for every other schema — a
    /// claim schema states no SMT-LIB text, a `pred.N` citation is a
    /// predicate over `self` that nothing grounds, and an opaque schema's
    /// payload is unreadable here. What a kernel replay grounds, and the only
    /// text it may; a reader then reads it with [`super::read_smtlib_term`],
    /// which refuses a text that is not SMT-LIB2 source.
    #[must_use]
    pub fn smtlib_text(&self) -> Option<&str> {
        match self.owned_schema() {
            Some(super::OwnedFormulaSchema::Smtlib2) => self
                .smtlib
                .as_deref()
                .is_none_or(|rendering| rendering == self.payload)
                .then_some(self.payload.as_str()),
            Some(
                super::OwnedFormulaSchema::Pred
                | super::OwnedFormulaSchema::BvBlastGoal
                | super::OwnedFormulaSchema::SatRes
                | super::OwnedFormulaSchema::LineageTransformBinding,
            )
            | None => None,
        }
    }
}

/// Where a [`crate::Module`] states a [`ProofFormula`]
/// ([`crate::Module::stated_formulas`]). The validators name it when the
/// formula there states two texts ([`ProofFormula::states_two_texts`]).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FormulaSite {
    /// `formula` of the obligation with this id.
    Obligation(ProofId),
    /// Clause `index` of the `clause` list (`requires`, `ensures` or
    /// `decreases`) of `function`'s summary.
    SummaryClause {
        function: FuncId,
        clause: &'static str,
        index: usize,
    },
    /// The typed carrier of invariant `invariant` of spec machine `machine`.
    SpecInvariant { machine: String, invariant: String },
    /// A formula of temporal property `property` of spec machine `machine`.
    SpecTemporal { machine: String, property: String },
}

/// Borrowed location of a stated formula. Traversal does not clone labels;
/// consumers retaining diagnostics can explicitly materialize [`FormulaSite`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FormulaSiteRef<'a> {
    /// Formula attached to this obligation id.
    Obligation(ProofId),
    /// A clause of this actual function's summary.
    SummaryClause {
        function: FuncId,
        clause: &'static str,
        index: usize,
    },
    /// Typed invariant carrier; labels borrow their spec record.
    SpecInvariant {
        machine: &'a str,
        invariant: &'a str,
    },
    /// Temporal formula leaf; both leads-to leaves share this site.
    SpecTemporal { machine: &'a str, property: &'a str },
}

impl FormulaSiteRef<'_> {
    /// Own the labels only when this site must outlive its source module.
    #[must_use]
    pub fn into_owned(self) -> FormulaSite {
        match self {
            Self::Obligation(id) => FormulaSite::Obligation(id),
            Self::SummaryClause {
                function,
                clause,
                index,
            } => FormulaSite::SummaryClause {
                function,
                clause,
                index,
            },
            Self::SpecInvariant { machine, invariant } => FormulaSite::SpecInvariant {
                machine: machine.to_owned(),
                invariant: invariant.to_owned(),
            },
            Self::SpecTemporal { machine, property } => FormulaSite::SpecTemporal {
                machine: machine.to_owned(),
                property: property.to_owned(),
            },
        }
    }
}

impl FormulaSite {
    /// Borrow this diagnostic's labels without allocating.
    #[must_use]
    pub fn as_ref(&self) -> FormulaSiteRef<'_> {
        match self {
            Self::Obligation(id) => FormulaSiteRef::Obligation(*id),
            Self::SummaryClause {
                function,
                clause,
                index,
            } => FormulaSiteRef::SummaryClause {
                function: *function,
                clause,
                index: *index,
            },
            Self::SpecInvariant { machine, invariant } => {
                FormulaSiteRef::SpecInvariant { machine, invariant }
            }
            Self::SpecTemporal { machine, property } => {
                FormulaSiteRef::SpecTemporal { machine, property }
            }
        }
    }
}

impl core::fmt::Display for FormulaSiteRef<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Obligation(id) => write!(f, "obligation #{}", id.index()),
            Self::SummaryClause {
                function,
                clause,
                index,
            } => write!(
                f,
                "function f{} summary {clause} clause {index}",
                function.index()
            ),
            Self::SpecInvariant { machine, invariant } => write!(
                f,
                "spec machine {machine:?} invariant {invariant:?} typed carrier"
            ),
            Self::SpecTemporal { machine, property } => {
                write!(f, "spec machine {machine:?} temporal property {property:?}")
            }
        }
    }
}

impl core::fmt::Display for FormulaSite {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Display::fmt(&self.as_ref(), f)
    }
}

fn disagreeing_formula_sites<'a>(
    formulas: impl Iterator<Item = (FormulaSiteRef<'a>, &'a ProofFormula)>,
    predicates: crate::pred::PredTable<'a>,
) -> impl Iterator<Item = FormulaSiteRef<'a>> {
    formulas
        .filter_map(move |(site, formula)| formula.states_two_texts(&predicates).then_some(site))
}

impl crate::Function {
    /// Borrow this actual function's summary formulas, in requires / ensures /
    /// decreases order and clause order within each list. No body/module clone
    /// is needed when a consumer is checking a detached function.
    pub fn stated_formulas_iter(
        &self,
    ) -> impl Iterator<Item = (FormulaSiteRef<'_>, &ProofFormula)> {
        self.summary.iter().flat_map(move |summary| {
            [
                ("requires", summary.requires.as_slice()),
                ("ensures", summary.ensures.as_slice()),
                ("decreases", summary.decreases.as_slice()),
            ]
            .into_iter()
            .flat_map(move |(clause, formulas)| {
                formulas.iter().enumerate().map(move |(index, formula)| {
                    (
                        FormulaSiteRef::SummaryClause {
                            function: self.id,
                            clause,
                            index,
                        },
                        formula,
                    )
                })
            })
        })
    }

    /// Borrow every inconsistent site without collecting or owning labels.
    ///
    /// A DETACHED function has no module predicate table, so a
    /// `trust-ir.Pred@1` clause citation resolves to nothing here and any
    /// rendering beside it is a second text; check a function its module
    /// owns through [`crate::Module::formulas_stating_two_texts_iter`].
    pub fn formulas_stating_two_texts_iter(&self) -> impl Iterator<Item = FormulaSiteRef<'_>> {
        disagreeing_formula_sites(
            self.stated_formulas_iter(),
            crate::pred::PredTable::new(&[], &[]),
        )
    }

    /// Stop at this actual function's first inconsistent formula, if any.
    #[must_use]
    pub fn first_formula_stating_two_texts(&self) -> Option<FormulaSiteRef<'_>> {
        self.formulas_stating_two_texts_iter().next()
    }
}

impl crate::Module {
    /// Every [`ProofFormula`] this module STATES, with where it states it:
    /// each obligation's formula, each summary clause, each spec machine's
    /// typed invariant carriers and temporal formulas. The one-formula rule
    /// ([`ProofFormula::smtlib_text`]) is checked over exactly this walk by
    /// both validators, so a new place that stores a `ProofFormula` in a
    /// module belongs here.
    #[must_use]
    pub fn stated_formulas(&self) -> Vec<(FormulaSite, &ProofFormula)> {
        self.stated_formulas_iter()
            .map(|(site, formula)| (site.into_owned(), formula))
            .collect()
    }

    /// Allocation-free canonical inventory. Order is obligations, functions,
    /// then each spec's invariants and temporal leaves, all in source order.
    /// A new module formula carrier belongs in this walk.
    pub fn stated_formulas_iter(
        &self,
    ) -> impl Iterator<Item = (FormulaSiteRef<'_>, &ProofFormula)> {
        let obligations = self.proof_obligations.iter().filter_map(|obligation| {
            obligation
                .formula
                .as_ref()
                .map(|formula| (FormulaSiteRef::Obligation(obligation.id), formula))
        });
        let functions = self
            .functions
            .iter()
            .flat_map(crate::Function::stated_formulas_iter);
        let specs = self.spec_modules.iter().flat_map(|spec| {
            let invariants = spec.invariants.iter().filter_map(move |invariant| {
                invariant.typed.as_ref().map(|formula| {
                    (
                        FormulaSiteRef::SpecInvariant {
                            machine: &spec.name,
                            invariant: &invariant.name,
                        },
                        formula,
                    )
                })
            });
            let temporal = spec.temporal.iter().flat_map(move |property| {
                property.form.formulas_iter().map(move |(formula, _)| {
                    (
                        FormulaSiteRef::SpecTemporal {
                            machine: &spec.name,
                            property: &property.name,
                        },
                        formula,
                    )
                })
            });
            invariants.chain(temporal)
        });
        obligations.chain(functions).chain(specs)
    }

    /// The sites of [`Self::stated_formulas`] whose formula states two texts
    /// ([`ProofFormula::states_two_texts`], a `pred.N` citation resolved
    /// against this module's predicate table) — what both validators
    /// refuse.
    #[must_use]
    pub fn formulas_stating_two_texts(&self) -> Vec<FormulaSite> {
        self.formulas_stating_two_texts_iter()
            .map(FormulaSiteRef::into_owned)
            .collect()
    }

    /// Borrow inconsistent sites in canonical order, owning no labels and
    /// visiting only as much of the inventory as the consumer requests.
    pub fn formulas_stating_two_texts_iter(&self) -> impl Iterator<Item = FormulaSiteRef<'_>> {
        disagreeing_formula_sites(self.stated_formulas_iter(), self.pred_table())
    }

    /// Stop at the first inconsistent formula without collecting the rest.
    #[must_use]
    pub fn first_formula_stating_two_texts(&self) -> Option<FormulaSiteRef<'_>> {
        self.formulas_stating_two_texts_iter().next()
    }
}

impl core::fmt::Display for ObligationKind {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        // `Custom` carries a payload, so this cannot stay a bare
        // `f.write_str(match ..)` — it is rendered as `custom:<ns>/<name>`.
        if let ObligationKind::Custom { namespace, name } = self {
            return write!(f, "custom:{namespace}/{name}");
        }
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
            ObligationKind::Termination => "termination",
            ObligationKind::Ownership => "ownership",
            ObligationKind::Custom { .. } => unreachable!("handled above"),
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
    /// unbindable rather than as a wildcard. The must-refuse corpus cannot
    /// express this (`refuse/obligation_site_none_is_unbindable`): a module
    /// with `site = None` is well-formed and must be accepted; the rule binds
    /// the consumer's binder, not the module.
    ///
    /// Appended AFTER `source` (v34): positional MessagePack may only skip a
    /// trailing field, so this must stay last — and appending it is precisely
    /// what forced `source` above to drop its own `skip_serializing_if`.
    /// MUST ALWAYS BE EMITTED since v46. It carried `skip_serializing_if`
    /// while it was the trailing field; `spec` was appended after it, and
    /// positional MessagePack may only skip a TRAILING field.
    #[cfg_attr(feature = "serde", serde(default))]
    pub site: Option<ObligationSite>,
    /// The named temporal property this obligation DISCHARGES (v46).
    ///
    /// `site` says which instruction a per-check obligation is about;
    /// `function` says which function it is scoped to. Neither can say which
    /// TEMPORAL PROPERTY a `Liveness` / `TemporalSafety` obligation states, so
    /// before this a consumer holding a sealed module could not tell twelve
    /// liveness obligations apart, and "every temporal property in the machine
    /// was proved" was the only available attribution — which is unsound for
    /// the same reason the v34 `site` argument gives.
    ///
    /// `None` = NOT RECORDED, which every fail-closed consumer treats as
    /// UNBINDABLE, never as a wildcard. Legal only on the two temporal kinds;
    /// the validator refuses it elsewhere, and refuses a reference that does
    /// not resolve to a declared machine and temporal property.
    ///
    /// Sole trailing skipped field, so positional MessagePack is satisfied.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub spec: Option<SpecObligationRef>,
}

/// The temporal property a [`ProofObligation`] discharges (v46).
///
/// Both halves are NAMES, resolved against `Module.spec_modules`: a machine
/// name and one of that machine's [`SpecTemporal`](crate::spec::SpecTemporal)
/// labels. Names rather than indices because a `SpecModule`'s identity is its
/// name everywhere else in this surface (anchors, waivers, proofs all bind by
/// name), and an index would silently re-target under a reorder.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SpecObligationRef {
    /// Name of the `SpecModule` that declares the property.
    pub machine: String,
    /// Name of the `SpecTemporal` property within that machine.
    pub temporal: String,
}

impl SpecObligationRef {
    /// Construct a reference to `machine`'s temporal property `temporal`.
    pub fn new(machine: impl Into<String>, temporal: impl Into<String>) -> Self {
        Self {
            machine: machine.into(),
            temporal: temporal.into(),
        }
    }
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
            spec: None,
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

#[cfg(test)]
mod formula_inventory_tests {
    use super::*;

    #[test]
    fn first_disagreement_does_not_visit_the_tail() {
        let good = ProofFormula::smtlib2("true", "Bool");
        let mut bad = ProofFormula::smtlib2("false", "Bool");
        bad.smtlib = Some("true".into());
        let site = FormulaSiteRef::Obligation(ProofId::new(9));
        let prefix = [
            (FormulaSiteRef::Obligation(ProofId::new(3)), &good),
            (site, &bad),
        ];
        let tail = core::iter::from_fn(|| panic!("inventory advanced past first disagreement"));
        assert_eq!(
            disagreeing_formula_sites(
                prefix.into_iter().chain(tail),
                crate::pred::PredTable::new(&[], &[])
            )
            .next(),
            Some(site)
        );
    }
}
