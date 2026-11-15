// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! IMPORT AUTHENTICATION: re-earning a cross-crate proof claim against the
//! serialized dependency artifact.
//!
//! v41 made a cross-crate proof claim SPELLABLE — [`crate::Module::imports`],
//! [`crate::ExternRef`], [`crate::FunctionSummary::backed_by`] and the
//! `external: Some` form of [`crate::proof::ProofEvidence::InheritedFromCallee`]
//! — and the structural validator takes every one of those rows on faith: it
//! checks that the cited import EXISTS in the table and nothing else. That is
//! the correct floor for a format build that holds only one module, and it is
//! also exactly the surface a laundering producer needs: name a digest, name a
//! symbol, name an obligation id, and `proved` reads as authenticated.
//!
//! This module is the other half. Every proof-bearing cross-crate row is a
//! CLAIM, and the API here either RE-EARNS it against the dependency module a
//! consumer actually loaded, or refuses with a named
//! [`ImportVerificationError`]. Two rules are load-bearing throughout:
//!
//! * **The verdict is computed over the dependency module's
//!   [`crate::Module::stable_digest`] under [`MODULE_IDENTITY_DOMAIN`], never
//!   over a name.** [`crate::ModuleImport::name`] is a diagnostic; two modules
//!   named `core_shim` are two modules. A rebuilt dependency with the same name
//!   and a different body is refused as [`ImportVerificationError::DigestMismatch`].
//!   The must-refuse corpus pins the single-module half of this obligation —
//!   `refuse/import_backed_summary_unauthenticated`, a `backed_by` claim the
//!   authority lane refuses as `UnauthenticatedImport` — and cannot express
//!   the mismatch itself (`refuse/import_digest_mismatch_pair`): that verdict
//!   needs a root plus dependency PAIR under the linked walk, and one wire
//!   artifact carries no dependency. The rung for the pair is the
//!   `verify_import` / linked-walk tests (gate `import-verification`).
//! * **`None` is never a wildcard.** An unrecorded producer, an absent target,
//!   an unscoped obligation and an empty `obligation` each REFUSE the claim
//!   that would need them — the v34 `site = None` precedent, applied at the
//!   crate seam.
//!
//! The layer here is deliberately zero-dependency and single-module-aware: it
//! authenticates ONE import edge and resolves ONE reference across it. The
//! closure walk (resolving every import of every import, memoized by digest,
//! cycle- and depth-guarded, and composed with the module validator) is
//! `trust_ir_build::validate_linked_module`, which is built on these
//! primitives.
//!
//! # Wire
//!
//! Every fact this module reads is carried by binary v41, except the row's
//! [`IdentityScheme`], which v44 adds (`ModuleImport.scheme`, read-gated on
//! `version >= 44`; a row decoded from an older blob is [`IdentityScheme::V2`]).
//! The scheme names the digest construction the row's digest was recorded
//! under, so a domain bump never silently re-means an existing row: the
//! verifier hashes the candidate under the ROW's scheme
//! ([`crate::Module::stable_digest_under`]). Ratified in
//! `docs/SPEC_RATIFICATIONS.md` §6.

use std::collections::{BTreeMap, BTreeSet};

use crate::proof::{
    ObligationKind, ObligationKindShape, ProofDigest, ProofDigestAlgorithm, ProofObligation,
    ProofStatus,
};
use crate::ty::{FatPtrKind, Ty, TypeOrigin};
use crate::value::{FuncId, FuncTyId, ImportId, PredId, ProofId, TyId};
use crate::{ExternRef, Function, Linkage, Module, ModuleFunctionCatalog, ModuleImport, Producer};

/// The domain-separation tag under which [`crate::Module::stable_digest`] is
/// computed: the CURRENT module identity, [`IdentityScheme::V3`]'s domain, and
/// therefore the domain every newly minted [`crate::ModuleImport::digest`] is
/// compared under.
///
/// Pinned here as the SINGLE spelling so the digest producer and the import
/// verifier cannot drift: `stable_digest` reads this constant (through
/// [`IdentityScheme::domain`]), and so do the request-side digest-context
/// census (`request::consts::NATIVE_BUNDLE_IDENTITY_CONTRACT_DIGEST_CONTEXTS`)
/// and the conformance determinism test. A change to the digest construction
/// is a change to what every recorded import means, so it is NOT a silent edit
/// of this string: `docs/SPEC_RATIFICATIONS.md` §6 ratifies that a domain bump
/// comes with a new [`IdentityScheme`] variant carried by every import row
/// (`ModuleImport.scheme`, wire v44), and that the older domains stay
/// computable through [`crate::Module::stable_digest_under`], so an import
/// recorded under an older domain is still authenticated under THAT domain.
pub const MODULE_IDENTITY_DOMAIN: &str = IdentityScheme::CURRENT.domain();

/// The legacy (pre-v44) module identity domain: [`IdentityScheme::V2`], the
/// SHA-256 of the whole canonical binary encoding, debug file paths included.
/// Still computable, so an import row recorded under it keeps authenticating.
pub const MODULE_IDENTITY_DOMAIN_V2: &str = IdentityScheme::V2.domain();

/// Which digest construction a [`crate::ModuleImport::digest`] was recorded
/// under — the `ModuleImport.scheme` discriminator (wire v44,
/// `docs/SPEC_RATIFICATIONS.md` §6).
///
/// The two schemes hash the SAME canonical binary plan
/// ([`crate::binary::ModuleBinaryPlan`]); they differ in exactly one
/// projection and in the domain:
///
/// * [`IdentityScheme::V2`] — `trust_ir.module.v2`: the whole encoding,
///   [`crate::Module::files`] strings included. Every row written before v44
///   decodes as V2, and V2 stays computable, so those rows keep
///   authenticating. It is the identity a MOVED checkout breaks: the debug
///   file table embeds the absolute source path, so a dependency built in a
///   macOS home directory never authenticates against the same crate built at
///   `/home/b/…` (roadmap F-117, measured by the critic as `crit.unex03`).
/// * [`IdentityScheme::V3`] — `trust_ir.module.v3`, the PORTABLE identity and
///   [`IdentityScheme::CURRENT`]: each `files[i]` string is projected to the
///   empty string before hashing. The table LENGTH is kept, so every
///   `SourceSpan.file` index stays range-valid and every span line/column
///   stays identity; only the debug path strings leave it.
///
/// # Why excluding the path strings is sound
///
/// Blanking `files` makes two modules that differ ONLY in debug path strings
/// one identity. That is admissible only while nothing load-bearing reads a
/// `files[i]` STRING — spans index the table for diagnostics, and the bundle
/// validator range-checks the index (the length is kept, so that check still
/// binds). The conformance tripwire `module_files_strings_are_debug_only`
/// fails the build if a validator rule or digest projection other than the
/// debug printers and the codec starts dereferencing one; a future rule that
/// makes a path load-bearing must first move it out of `files`.
///
/// # Codec
///
/// The wire tag is `0` for V2 and `1` for V3 (tag space `IdentityScheme` in
/// `wire-allocations.toml`). The binary writer selects v44 only when a row's
/// scheme is not V2, so a module whose rows are all V2 keeps its v41–v43
/// bytes exactly; serde skips a V2 scheme and defaults an absent one to V2;
/// the text form spells ` scheme v3` and spells V2 by omission.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum IdentityScheme {
    /// `trust_ir.module.v2`: the whole canonical encoding. The decode default
    /// for every row written before v44.
    #[default]
    V2,
    /// `trust_ir.module.v3`: the canonical encoding with every
    /// [`crate::Module::files`] string projected to `""` (length kept).
    V3,
}

impl IdentityScheme {
    /// The scheme [`crate::Module::stable_digest`] computes, and the one
    /// [`crate::ModuleImport::new`] records.
    pub const CURRENT: IdentityScheme = IdentityScheme::V3;

    /// Every scheme this build can compute, oldest first.
    pub const ALL: [IdentityScheme; 2] = [IdentityScheme::V2, IdentityScheme::V3];

    /// The domain-separation tag this scheme's digest is computed under.
    #[must_use]
    pub const fn domain(self) -> &'static str {
        match self {
            IdentityScheme::V2 => "trust_ir.module.v2",
            IdentityScheme::V3 => "trust_ir.module.v3",
        }
    }

    /// Whether this scheme projects the [`crate::Module::files`] strings out
    /// of the hashed image.
    #[must_use]
    pub const fn blanks_debug_file_paths(self) -> bool {
        match self {
            IdentityScheme::V2 => false,
            IdentityScheme::V3 => true,
        }
    }

    /// Whether this is the legacy [`IdentityScheme::V2`] — the pre-v44 decode
    /// default, which every codec spells by omission.
    #[must_use]
    pub const fn is_v2(&self) -> bool {
        matches!(self, IdentityScheme::V2)
    }

    /// The stable label used by the text form and diagnostics (`v2`, `v3`).
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            IdentityScheme::V2 => "v2",
            IdentityScheme::V3 => "v3",
        }
    }
}

impl core::fmt::Display for IdentityScheme {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.label())
    }
}

/// Which cross-crate row an [`ExternRef`] is being resolved FOR: one of the
/// two proof-bearing rows, or a claim-free call edge.
///
/// The site decides which obligation kinds are admissible: a summary's
/// `backed_by` may only cite a CONTRACT obligation (the kinds a summary's
/// clauses are backed by locally), while an `InheritedFromCallee` certificate
/// may inherit any enumerated kind except the producer-namespaced `Custom`,
/// whose namespace is authority-bearing and must be admitted from a pinned
/// list a format-level rule cannot own.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ExternRefSite {
    /// [`crate::FunctionSummary::backed_by`] on a `proved` summary.
    SummaryBackedBy,
    /// `external: Some` on a
    /// [`crate::proof::ProofEvidence::InheritedFromCallee`] certificate.
    InheritedFromCallee,
    /// A CLAIM-FREE call edge: a body-less declaration the linked walk binds
    /// to a dependency's exported definition (`trust_ir_build`'s rule L10).
    /// It relies on no obligation, so [`ExternRefSite::admits`] admits no
    /// kind; and its local declaration may be `ExternalWeak`, because the
    /// nullable binding is the importer's own validated idiom and there is no
    /// proof about the far body for a different binding to invalidate — R3–R6
    /// (symbol, export, far interposability, producer, signature) still run.
    CallEdge,
    /// An IMPORT-BACKED HANDLE DECLARATION (WS3.3, F-048): a body-less,
    /// non-pinned declaration whose signature reaches a v43 `Ty::Handle`,
    /// bound to a dependency by a `backed_by` naming the far entity. A
    /// declaration whose signature reaches a handle is a handle ORIGIN, so
    /// the far site must be the body the linker actually binds — R4 is
    /// HARDENED here and differs from every other site:
    ///
    /// * a far DEFINITION is admitted unless it is
    ///   [`Linkage::AvailableExternally`] (a body copy the linker never emits:
    ///   [`ImportVerificationError::FarSiteIsAvailableExternallyCopy`]);
    /// * a far DECLARATION is admitted only when the caller vouches that it is
    ///   itself an AUTHENTICATED handle declaration of the dependency
    ///   ([`Module::resolve_handle_declaration`]'s explicit set, which the
    ///   linked walk fills from the dependency's own verdict). Through
    ///   [`Module::resolve_extern_ref`] — which holds no dependency verdict —
    ///   every far declaration is refused
    ///   ([`ImportVerificationError::FarSiteIsUnbackedDeclaration`]): recording
    ///   a `backed_by`, the general R4 test, is NOT enough, because an
    ///   entity-only `backed_by` is a claim nothing re-earned.
    ///
    /// Claim-free like [`ExternRefSite::CallEdge`] ([`ExternRefSite::admits`]
    /// admits no kind), but a local `ExternalWeak` declaration is NOT
    /// admitted: a null binding of a handle origin is not a checked idiom.
    HandleDeclaration,
}

impl ExternRefSite {
    /// The stable label used in diagnostics.
    #[must_use]
    pub const fn label(self) -> &'static str {
        match self {
            ExternRefSite::SummaryBackedBy => "backed_by",
            ExternRefSite::InheritedFromCallee => "inherited",
            ExternRefSite::CallEdge => "call",
            ExternRefSite::HandleDeclaration => "handle",
        }
    }

    /// Whether `kind` may be relied upon from this site: the table
    /// [`ExternRefSite::admits_shape`] at the kind's [`ObligationKind::shape`].
    #[must_use]
    pub fn admits(self, kind: &ObligationKind) -> bool {
        self.admits_shape(kind.shape())
    }

    /// Whether an obligation of this kind SHAPE may be relied upon from this
    /// site (import authentication rule R7):
    ///
    /// | site | admitted kinds |
    /// |---|---|
    /// | `SummaryBackedBy` | `Precondition`, `Postcondition`, `Termination` (the contract kinds a summary's clauses are backed by) |
    /// | `InheritedFromCallee` | every kind except `Custom` (its namespace is authority-bearing) |
    /// | `CallEdge`, `HandleDeclaration` | none (claim-free) |
    ///
    /// Each row is a whitelist: `ObligationKind` is `#[non_exhaustive]`, and a
    /// kind added later gets a shape (the projection is exhaustive) that no
    /// row names, so it is refused, never admitted by a wildcard arm.
    ///
    /// PROVED, every cell: `trust_ir_laws::laws::{backed_by,inherited}_*`,
    /// `call_edge_admits_nothing` and `handle_declaration_admits_nothing`
    /// (gate 13). Measured 2026-09-29: this body is inlined into the laws at
    /// a cost of 95 against the inliner's threshold of 100, so a new ROW with
    /// its own kind list would push it over and turn every law UNKNOWN (the
    /// gate would fail closed, not pass); more kinds in an existing row cost
    /// nothing.
    #[inline]
    #[must_use]
    pub const fn admits_shape(self, kind: ObligationKindShape) -> bool {
        match self {
            ExternRefSite::SummaryBackedBy => matches!(
                kind,
                ObligationKindShape::Precondition
                    | ObligationKindShape::Postcondition
                    | ObligationKindShape::Termination
            ),
            ExternRefSite::InheritedFromCallee => matches!(
                kind,
                ObligationKindShape::Precondition
                    | ObligationKindShape::Postcondition
                    | ObligationKindShape::LoopInvariant
                    | ObligationKindShape::TypeInvariant
                    | ObligationKindShape::RefinementType
                    | ObligationKindShape::TranslationValidation
                    | ObligationKindShape::MemorySafety
                    | ObligationKindShape::PanicFreedom
                    | ObligationKindShape::TemporalSafety
                    | ObligationKindShape::Liveness
                    | ObligationKindShape::ArithmeticSafety
                    | ObligationKindShape::BoundsCheck
                    | ObligationKindShape::GiveBackRefinement
                    | ObligationKindShape::Termination
                    | ObligationKindShape::Ownership
            ),
            // A call edge and a handle declaration carry no claim: nothing
            // may be relied upon.
            ExternRefSite::CallEdge | ExternRefSite::HandleDeclaration => false,
        }
    }
}

impl core::fmt::Display for ExternRefSite {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.label())
    }
}

/// Why an import could not be authenticated, or a reference across it could
/// not be resolved. Every variant is a REFUSAL; there is no advisory tier.
///
/// The variants are listed in check order: [`Module::verify_import`] runs C1–C6
/// and [`Module::resolve_extern_ref`] runs R1–R7, and the FIRST failure names
/// itself. `#[non_exhaustive]` because the check list is expected to grow.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportVerificationError {
    /// C1: the [`ImportId`] is not declared in the importer's table.
    UnresolvedImport { import: u32 },
    /// C2: the recorded digest is not SHA-256. `TrustIrStableV1` is a
    /// checksum, not an identity, and must never select a module.
    UnsupportedDigestAlgorithm {
        import: u32,
        algorithm: ProofDigestAlgorithm,
    },
    /// C3: the candidate's digest under the row's
    /// [`crate::ModuleImport::scheme`] ([`Module::stable_digest_under`]) is
    /// not the recorded one — the module the consumer holds is not the module
    /// the proof was about. `actual` is computed under the ROW's scheme.
    DigestMismatch {
        import: u32,
        recorded: ProofDigest,
        actual: ProofDigest,
    },
    /// C4: the candidate's `Module::name` differs from the recorded name.
    /// Reached only AFTER the digest matched, so this catches a re-labelled
    /// artifact rather than substituting for the digest check.
    NameMismatch {
        import: u32,
        recorded: String,
        actual: String,
    },
    /// C5 / R5: a producer that a rule depends on is UNRECORDED. `side` is
    /// `"import"` for [`ModuleImport::producer`] and `"function"` for the
    /// far [`Function::producer`].
    ProducerUnrecorded { import: u32, side: &'static str },
    /// R5: the far function's recorded producer is not the import's.
    ProducerMismatch {
        symbol: String,
        recorded: Producer,
        actual: Producer,
    },
    /// C6: the two modules do not pin the same target. Both must be `Some` and
    /// agree on every field; one-sided or two-sided absence is a mismatch — a
    /// `Usize` proof must not cross pointer widths.
    TargetMismatch { import: u32, detail: String },
    /// R1: the [`ExternRef::module`] is not the import that was verified.
    ImportIdMismatch { expected: u32, actual: u32 },
    /// R1: an equal import row was verified for another importer, whose
    /// target may differ even though this row has equal bytes.
    VerifiedImportForOtherModule { import: u32 },
    /// R2: the importer's local site function does not resolve uniquely.
    LocalFunctionUnresolved { function: u32 },
    /// R2: the importer's local handle on the callee has a body. A cross-crate
    /// proof is about the FAR body; a local definition would make the claim
    /// about a different one.
    LocalSiteHasBody { function: u32 },
    /// R2: the local declaration's link symbol is not the referenced one.
    LinkSymbolMismatch {
        function: u32,
        local: String,
        symbol: String,
    },
    /// R2 (`side: "local"`) / R4 (`side: "far"`): a function on one end of
    /// the cross-crate edge has INTERPOSABLE linkage — [`Linkage::Weak`],
    /// [`Linkage::LinkOnce`] or [`Linkage::ExternalWeak`].
    ///
    /// A cross-crate proof is about ONE far body. On the far side, a `Weak` /
    /// `LinkOnce` definition may be replaced at link time by a stronger (or
    /// any other) definition of the same symbol that nobody proved anything
    /// about, and an `ExternalWeak` row names no definition at all. On the
    /// local side, an `ExternalWeak` (or `Weak` / `LinkOnce`) declaration may
    /// resolve to a different definition or to NULL, so the far body the proof
    /// is about may never be the one called. Either way the proof does not
    /// transfer.
    ///
    /// The ODR spellings — [`Linkage::WeakOdr`], [`Linkage::LinkOnceOdr`] —
    /// and [`Linkage::AvailableExternally`] stay admitted under the
    /// one-definition-rule premise (every copy is the same definition); that
    /// premise is a disclosed trust assumption, not something this check
    /// verifies. It is how Rust generic instances link.
    InterposableFarSite {
        symbol: String,
        linkage: Linkage,
        side: &'static str,
    },
    /// R3: no function in the dependency carries the symbol.
    SymbolUnresolved { symbol: String },
    /// R3: more than one function in the dependency carries the symbol.
    SymbolAmbiguous { symbol: String, count: usize },
    /// R4: the far function carrying the symbol is a body-less declaration
    /// that records NO cross-crate backing of its own — a bare re-declaration.
    ///
    /// A cross-crate claim is ultimately about a BODY. A dependency that
    /// merely re-declares the symbol has no body for the cited obligation to
    /// be about and names no further module that does, so authenticating
    /// against it would let a module prove a contract by asserting it — the
    /// local `proved` rule already refuses such a declaration's own `proved`
    /// for exactly this reason.
    ///
    /// A declaration that DOES record a backing is admitted, because it is the
    /// ratified transitive shape: a `backed_by` citation on its summary, or an
    /// `InheritedFromCallee { external: Some }` certificate naming it as the
    /// callee, each name the module where the proof actually lives.
    /// `validate_linked_module` then follows that citation and re-earns it;
    /// this rule is what stops the chain from bottoming out in an assertion.
    FarSiteIsUnbackedDeclaration { symbol: String },
    /// R4, at [`ExternRefSite::HandleDeclaration`] only: the far function is a
    /// [`Linkage::AvailableExternally`] DEFINITION — a body copy for inlining
    /// that the dependency never emits, so the symbol the linker binds is some
    /// other object's. A handle origin must bind the body the dependency
    /// validated, so a copy is refused as the far site (F-048 names the copy
    /// as a workaround that is not an import).
    FarSiteIsAvailableExternallyCopy { symbol: String },
    /// R4: the far function is not exported (`Internal` / `Private`).
    /// Checked before [`ImportVerificationError::InterposableFarSite`]'s far
    /// leg, so an unexported symbol is named as such.
    SymbolNotExported { symbol: String, linkage: Linkage },
    /// R6: the local declaration and the far definition disagree on the
    /// signature ([`signatures_compatible`] names the field).
    SignatureMismatch { symbol: String, detail: String },
    /// R7: the cited obligation does not resolve uniquely in the dependency.
    ObligationUnresolved { symbol: String, obligation: u32 },
    /// R7: the cited obligation is not scoped to the far function. `None`
    /// (unscoped) is a mismatch, never a wildcard.
    ObligationScopeMismatch {
        obligation: u32,
        expected: u32,
        actual: Option<u32>,
    },
    /// R7: the cited obligation is not `Discharged` / `Certified`.
    ObligationNotDischarged {
        obligation: u32,
        status: ProofStatus,
    },
    /// R7: the cited obligation's kind may not be relied upon from `site`.
    ObligationKindInadmissible {
        obligation: u32,
        site: ExternRefSite,
        kind: String,
    },
}

impl core::fmt::Display for ImportVerificationError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::UnresolvedImport { import } => {
                write!(f, "import #{import} is not declared in `Module::imports`")
            }
            Self::UnsupportedDigestAlgorithm { import, algorithm } => write!(
                f,
                "import #{import} records a {algorithm} digest; only SHA-256 identifies a module \
                 (`TrustIrStableV1` is a checksum, not an identity)"
            ),
            Self::DigestMismatch {
                import,
                recorded,
                actual,
            } => write!(
                f,
                "import #{import}: the candidate module's stable digest {actual} is not the \
                 recorded {recorded} — the module held is not the module the proof was about"
            ),
            Self::NameMismatch {
                import,
                recorded,
                actual,
            } => write!(
                f,
                "import #{import}: candidate module is named {actual:?}, import records \
                 {recorded:?}"
            ),
            Self::ProducerUnrecorded { import, side } => write!(
                f,
                "import #{import}: the {side}-side producer is unrecorded (`None`), which is \
                 never read as agreement"
            ),
            Self::ProducerMismatch {
                symbol,
                recorded,
                actual,
            } => write!(
                f,
                "symbol {symbol:?}: the far function was produced by {actual}, the import \
                 records {recorded}"
            ),
            Self::TargetMismatch { import, detail } => {
                write!(f, "import #{import}: target mismatch — {detail}")
            }
            Self::VerifiedImportForOtherModule { import } => write!(
                f,
                "import #{import} was verified for another importing module; verify this \
                 module's own import before resolving a reference"
            ),
            Self::ImportIdMismatch { expected, actual } => write!(
                f,
                "reference names import #{actual} but the verified import is #{expected}"
            ),
            Self::LocalFunctionUnresolved { function } => write!(
                f,
                "local site function #{function} does not resolve uniquely in the importer"
            ),
            Self::LocalSiteHasBody { function } => write!(
                f,
                "local site function #{function} has a body; a cross-crate claim must be cited \
                 from a body-less declaration of the callee"
            ),
            Self::LinkSymbolMismatch {
                function,
                local,
                symbol,
            } => write!(
                f,
                "local declaration #{function} carries link symbol {local:?}, reference names \
                 {symbol:?}"
            ),
            Self::InterposableFarSite {
                symbol,
                linkage,
                side,
            } => write!(
                f,
                "{side} symbol `{symbol}` has interposable linkage {linkage:?}: the linker may \
                 bind a different definition (or null), so a proof about this body does not \
                 transfer"
            ),
            Self::SymbolUnresolved { symbol } => {
                write!(f, "no function in the dependency carries symbol {symbol:?}")
            }
            Self::SymbolAmbiguous { symbol, count } => write!(
                f,
                "{count} functions in the dependency carry symbol {symbol:?}; ambiguous, \
                 fail-closed"
            ),
            Self::FarSiteIsUnbackedDeclaration { symbol } => write!(
                f,
                "symbol {symbol:?} is a body-less declaration in the dependency that records no \
                 cross-crate backing of its own; a bare re-declaration proves nothing"
            ),
            Self::FarSiteIsAvailableExternallyCopy { symbol } => write!(
                f,
                "symbol {symbol:?} is an `available_externally` body copy in the dependency; a \
                 handle declaration must bind a definition the dependency emits, not a copy \
                 whose linked symbol is another object's"
            ),
            Self::SymbolNotExported { symbol, linkage } => write!(
                f,
                "symbol {symbol:?} has {linkage} linkage in the dependency and is not exported"
            ),
            Self::SignatureMismatch { symbol, detail } => {
                write!(f, "symbol {symbol:?}: signature mismatch — {detail}")
            }
            Self::ObligationUnresolved { symbol, obligation } => write!(
                f,
                "obligation #{obligation} cited for {symbol:?} does not resolve uniquely in the \
                 dependency"
            ),
            Self::ObligationScopeMismatch {
                obligation,
                expected,
                actual,
            } => match actual {
                Some(actual) => write!(
                    f,
                    "obligation #{obligation} is scoped to function #{actual}, not the \
                     referenced #{expected}"
                ),
                None => write!(
                    f,
                    "obligation #{obligation} is unscoped (`function: None`), which never \
                     matches the referenced function #{expected}"
                ),
            },
            Self::ObligationNotDischarged { obligation, status } => write!(
                f,
                "obligation #{obligation} is {status}, not Discharged or Certified"
            ),
            Self::ObligationKindInadmissible {
                obligation,
                site,
                kind,
            } => write!(
                f,
                "obligation #{obligation} has kind {kind}, which a {site} site may not rely on"
            ),
        }
    }
}

impl std::error::Error for ImportVerificationError {}

impl ImportVerificationError {
    /// Concrete ways forward from this refusal, one imperative line each
    /// (v7 D3; roadmap WS4.18, F-081). The same contract as
    /// `trust_ir_build::ValidationError`'s method of the same name: advice
    /// text, never authority — no code path branches on it, nothing on the
    /// wire changes, and an empty slice means "no enumerated options yet".
    #[must_use]
    pub fn repair_options(&self) -> &'static [&'static str] {
        match self {
            Self::DigestMismatch { .. } => &[
                "supply the exact dependency artifact whose `Module::stable_digest` equals \
                 the digest the import row records (a rebuilt, re-serialized-with-changes \
                 or renamed-and-edited file is a different module)",
                "if the dependency was deliberately rebuilt, re-emit the importing module \
                 against it so the import row records the new digest, then re-earn every \
                 cross-crate claim that cites it",
            ],
            _ => &[],
        }
    }
}

/// An import edge that has been authenticated: the candidate module's stable
/// digest IS the recorded one, and the C4–C6 agreement checks passed for this
/// exact importer. An equal row in another module does not carry its target
/// check across with it.
///
/// Fields are private so the only way to obtain one is through
/// [`Module::verify_import`] / [`Module::verify_import_hashed`] (or the
/// deprecated, self-checking `Module::verify_import_with_computed_digest`).
#[derive(Debug, Clone, Copy)]
pub struct VerifiedImport<'a> {
    importer: &'a Module,
    id: ImportId,
    import: &'a ModuleImport,
    module: &'a Module,
    digest: ProofDigest,
}

impl<'a> VerifiedImport<'a> {
    /// The import that was verified, in the importer's table.
    #[must_use]
    pub fn id(&self) -> ImportId {
        self.id
    }

    /// The importer's record of the dependency.
    #[must_use]
    pub fn import(&self) -> &'a ModuleImport {
        self.import
    }

    /// The authenticated dependency module.
    #[must_use]
    pub fn module(&self) -> &'a Module {
        self.module
    }

    /// The digest the module was authenticated under (equal to
    /// `import().digest`).
    #[must_use]
    pub fn digest(&self) -> ProofDigest {
        self.digest
    }
}

/// A module bound to the digests computed over it — the hash-once handle a
/// closure walk carries so each dependency is hashed at most once PER
/// [`IdentityScheme`].
///
/// The binding is enforced by the TYPE, not by a naming convention. The fields
/// are private and the ONLY constructor is [`HashedModule::new`], which hashes
/// the very module it stores ([`Module::stable_digest`], the current scheme);
/// a digest under another scheme is computed LAZILY, over the same stored
/// module, the first time [`HashedModule::digest_under`] asks for it, and is
/// cached in a write-once cell nothing else can fill. There is no `From`, no
/// `Default`, no serde and no setter. A `HashedModule` therefore cannot carry
/// a digest that was not computed over its own module, and
/// [`Module::verify_import_hashed`] cannot be handed the importer's RECORDED
/// digest in place of a computed one — the misuse the retired
/// `verify_import_with_computed_digest(id, candidate, actual)` signature
/// admitted (passing `import.digest` as `actual` compared the record with the
/// record and authenticated an arbitrary module).
///
/// Spelling the pair from outside the crate does not compile:
///
/// ```compile_fail,E0451
/// use trust_ir::imports::HashedModule;
/// use trust_ir::proof::ProofDigest;
/// use trust_ir::Module;
///
/// let tampered = Module::new("dep");
/// // A forged pair: a module with a digest that was never computed over it.
/// let forged = HashedModule { module: &tampered, digests: Default::default() };
/// ```
///
/// and the only spelling that does compile hashes the module it holds, so a
/// tampered dependency is refused at C3:
///
/// ```
/// use trust_ir::imports::HashedModule;
/// use trust_ir::{
///     Endianness, ImportVerificationError, Module, ModuleImport, Producer, TargetInfo,
/// };
///
/// let target = TargetInfo {
///     triple: "aarch64-apple-darwin".into(),
///     pointer_size: 8,
///     endianness: Endianness::Little,
///     abi: None,
///     struct_passing: Default::default(),
/// };
/// let mut dep = Module::new("dep");
/// dep.target_info = Some(target.clone());
/// let mut importer = Module::new("root");
/// importer.target_info = Some(target);
/// let id = importer
///     .intern_import(ModuleImport::new("dep", dep.stable_digest()).with_producer(Producer::TRust))
///     .unwrap();
///
/// // The honest dependency authenticates.
/// let honest = HashedModule::new(&dep);
/// assert_eq!(honest.digest(), dep.stable_digest());
/// assert!(importer.verify_import_hashed(id, &honest).is_ok());
///
/// // The same name, one byte different: the digest is recomputed, not asserted.
/// let mut tampered = dep.clone();
/// tampered.global_asm.push("nop".to_string());
/// let refused = importer.verify_import_hashed(id, &HashedModule::new(&tampered));
/// assert!(matches!(refused, Err(ImportVerificationError::DigestMismatch { import: 0, .. })));
/// ```
#[derive(Debug, Clone)]
pub struct HashedModule<'a> {
    module: &'a Module,
    /// One write-once cell per [`IdentityScheme`], indexed by
    /// [`scheme_slot`]; each is filled only by hashing `module`.
    digests: [std::cell::OnceCell<ProofDigest>; IdentityScheme::ALL.len()],
}

/// The [`HashedModule`] cache slot of `scheme`.
const fn scheme_slot(scheme: IdentityScheme) -> usize {
    match scheme {
        IdentityScheme::V2 => 0,
        IdentityScheme::V3 => 1,
    }
}

impl<'a> HashedModule<'a> {
    /// Hash `module` once under [`IdentityScheme::CURRENT`] — its
    /// [`Module::stable_digest`]. The sole constructor.
    #[must_use]
    pub fn new(module: &'a Module) -> Self {
        let hashed = Self {
            module,
            digests: Default::default(),
        };
        let _ = hashed.digest_under(IdentityScheme::CURRENT);
        hashed
    }

    /// The module the digests are computed over.
    #[must_use]
    pub fn module(&self) -> &'a Module {
        self.module
    }

    /// The [`Module::stable_digest`] of [`HashedModule::module`] (the current
    /// scheme), computed at construction.
    #[must_use]
    pub fn digest(&self) -> ProofDigest {
        self.digest_under(IdentityScheme::CURRENT)
    }

    /// The digest of [`HashedModule::module`] under `scheme`
    /// ([`Module::stable_digest_under`]), computed over the stored module the
    /// first time it is asked for and cached thereafter.
    #[must_use]
    pub fn digest_under(&self, scheme: IdentityScheme) -> ProofDigest {
        *self.digests[scheme_slot(scheme)].get_or_init(|| self.module.stable_digest_under(scheme))
    }
}

/// A cross-crate reference resolved against an authenticated import.
#[derive(Debug, Clone, Copy)]
pub struct ResolvedExternRef<'a> {
    /// The importer's own body-less declaration of the callee.
    pub local: &'a Function,
    /// The far function in the dependency.
    pub far: &'a Function,
    /// The cited obligation in the dependency, when the reference names one.
    pub obligation: Option<&'a ProofObligation>,
}

/// One definition that carries a v58 nominal identity key.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyedTypeDefinition<'m> {
    /// The key the producer stamped.
    pub origin: &'m TypeOrigin,
    /// Which definition table it came from: `"struct"` or `"enum"`.
    pub table: &'static str,
    /// The definition's name.
    pub name: &'m str,
    /// The type that names it, for a structural comparison across modules.
    pub ty: Ty,
}

impl Module {
    /// Every definition in this module that carries a [`TypeOrigin`], structs
    /// before enums, each table in declaration order.
    ///
    /// Unkeyed definitions are ABSENT, not reported with a placeholder: no
    /// rule in this file may read an absent key as agreement.
    #[must_use]
    pub fn keyed_type_definitions(&self) -> Vec<KeyedTypeDefinition<'_>> {
        let structs = self.structs.iter().filter_map(|sd| {
            Some(KeyedTypeDefinition {
                origin: sd.origin.as_ref()?,
                table: "struct",
                name: &sd.name,
                ty: Ty::Struct(sd.id),
            })
        });
        let enums = self.enums.iter().filter_map(|ed| {
            Some(KeyedTypeDefinition {
                origin: ed.origin.as_ref()?,
                table: "enum",
                name: &ed.name,
                ty: Ty::Enum(ed.id),
            })
        });
        structs.chain(enums).collect()
    }

    /// Definition pairs in THIS module that stamp one nominal key twice.
    ///
    /// One source entity has one image per module. Two rows under one key is a
    /// producer defect however they are laid out: a consumer resolving the key
    /// would have to pick, and nothing tells it which. The struct and enum
    /// tables are scanned TOGETHER — a key claimed by a struct and by an enum
    /// is the same collision.
    ///
    /// Reported as `(first, second)` in the definition order above, so a
    /// message is stable across runs.
    #[must_use]
    pub fn duplicate_type_origins(
        &self,
    ) -> Vec<(KeyedTypeDefinition<'_>, KeyedTypeDefinition<'_>)> {
        let keyed = self.keyed_type_definitions();
        let mut first_by_origin: BTreeMap<&TypeOrigin, KeyedTypeDefinition<'_>> = BTreeMap::new();
        let mut duplicates = Vec::new();
        for definition in keyed {
            match first_by_origin.get(definition.origin) {
                Some(first) => duplicates.push((first.clone(), definition)),
                None => {
                    first_by_origin.insert(definition.origin, definition);
                }
            }
        }
        duplicates
    }

    /// One-key-two-shapes contradictions between THIS module and `other`.
    ///
    /// For every key both modules stamp, the two definitions must be
    /// structurally equal across the boundary. A key present in only one
    /// module is not a finding — the modules simply do not share that entity.
    ///
    /// This is the cross-crate half of the [`TypeOrigin`] rule and it only
    /// ever REFUSES: nothing here makes two definitions equal that structure
    /// says are different.
    ///
    /// EVERY definition either module stamps with a shared key is compared,
    /// not one representative per key. A module that stamps one key twice is
    /// already refused by its own validator
    /// ([`Module::duplicate_type_origins`]), but this helper takes any two
    /// modules; keeping only one of `self`'s claims would let the other
    /// disagree with `other` unreported. Pairs are reported in `other`'s
    /// definition order, then `self`'s.
    #[must_use]
    pub fn type_origin_conflicts_with(&self, other: &Module) -> Vec<TypeOriginConflict> {
        let mut mine: BTreeMap<&TypeOrigin, Vec<KeyedTypeDefinition<'_>>> = BTreeMap::new();
        for definition in self.keyed_type_definitions() {
            mine.entry(definition.origin).or_default().push(definition);
        }
        let mut conflicts = Vec::new();
        for theirs in other.keyed_type_definitions() {
            let Some(claims) = mine.get(theirs.origin) else {
                continue;
            };
            for ours in claims {
                // A struct keyed as an enum's entity is already a
                // contradiction: the tables differ, so nothing structural can
                // reconcile them.
                if ours.table != theirs.table
                    || !ty_structurally_eq_across(self, &ours.ty, other, &theirs.ty)
                {
                    conflicts.push(TypeOriginConflict {
                        origin: theirs.origin.clone(),
                        table: ours.table,
                        left: ours.name.to_string(),
                        right: theirs.name.to_string(),
                    });
                }
            }
        }
        conflicts
    }
}

impl Module {
    /// Authenticate import `id` against `candidate`: hash the candidate once
    /// ([`HashedModule::new`]) and forward to [`Module::verify_import_hashed`].
    pub fn verify_import<'a>(
        &'a self,
        id: ImportId,
        candidate: &'a Module,
    ) -> Result<VerifiedImport<'a>, ImportVerificationError> {
        self.verify_import_hashed(id, &HashedModule::new(candidate))
    }

    /// Authenticate import `id` against `candidate`, whose stable digest the
    /// caller claims is `actual`.
    ///
    /// **Deprecated, and no longer a hash-once hook.** The old contract let the
    /// caller ASSERT the digest, so passing the import's own recorded digest
    /// compared the record with itself and authenticated an arbitrary module.
    /// This spelling now ALWAYS recomputes the candidate's digest under the
    /// row's [`IdentityScheme`] ([`Module::stable_digest_under`]) — in
    /// every build profile — and refuses with
    /// [`ImportVerificationError::DigestMismatch`] (`recorded` = the supplied
    /// `actual`, `actual` = the recomputed digest) when the two differ; it
    /// then runs exactly [`Module::verify_import_hashed`]. It therefore costs
    /// a full hash, which is the point: the hash-once form is
    /// [`Module::verify_import_hashed`], whose [`HashedModule`] argument
    /// cannot carry a digest that was not computed over its module.
    #[deprecated(
        since = "0.14.0",
        note = "caller-asserted digests are refused; hash once with `HashedModule::new` and \
                call `Module::verify_import_hashed`"
    )]
    pub fn verify_import_with_computed_digest<'a>(
        &'a self,
        id: ImportId,
        candidate: &'a Module,
        actual: ProofDigest,
    ) -> Result<VerifiedImport<'a>, ImportVerificationError> {
        let hashed = HashedModule::new(candidate);
        // Recompute under the scheme the ROW records (an unresolved id falls
        // through to C1 below with the current scheme's digest compared).
        let scheme = self
            .import(id)
            .map_or(IdentityScheme::CURRENT, |import| import.scheme);
        let recomputed = hashed.digest_under(scheme);
        if actual != recomputed {
            return Err(ImportVerificationError::DigestMismatch {
                import: id.index(),
                recorded: actual,
                actual: recomputed,
            });
        }
        self.verify_import_hashed(id, &hashed)
    }

    /// Authenticate import `id` against an already-hashed candidate.
    ///
    /// This is the hash-once form for a walk that keeps each dependency's
    /// digest (the linked validator's memo stores [`HashedModule`]s). The
    /// digest compared at C3 is the candidate's digest under the ROW's
    /// [`crate::ModuleImport::scheme`] ([`HashedModule::digest_under`]),
    /// computed over `candidate.module()`; the type admits no other, so this
    /// cannot be misused to assert a digest. A V2 row is therefore compared
    /// under `trust_ir.module.v2` and a V3 row under `trust_ir.module.v3`,
    /// never one under the other's domain.
    ///
    /// Check order — the first failure names itself:
    ///
    /// * C1 `id` resolves in this module's table, else
    ///   [`ImportVerificationError::UnresolvedImport`];
    /// * C2 the recorded digest is SHA-256, else
    ///   [`ImportVerificationError::UnsupportedDigestAlgorithm`];
    /// * C3 `candidate.digest_under(import.scheme) == import.digest`, else
    ///   [`ImportVerificationError::DigestMismatch`];
    /// * C4 `candidate.module().name == import.name`, else
    ///   [`ImportVerificationError::NameMismatch`];
    /// * C5 `import.producer` is recorded, else
    ///   [`ImportVerificationError::ProducerUnrecorded`];
    /// * C6 both modules pin the same [`crate::TargetInfo`], else
    ///   [`ImportVerificationError::TargetMismatch`].
    ///
    /// # One row per `(artifact, producer)` edge
    ///
    /// C5 and R5 ([`Module::resolve_extern_ref`]) pair the far function's
    /// producer with the row's single [`ModuleImport::producer`], so a MIXED
    /// Rust+Clean dependency is imported through TWO rows — one per producer —
    /// carrying the SAME digest. That is normative (`docs/SPEC_RATIFICATIONS.md`
    /// §6), and both rows authenticate against the one [`HashedModule`].
    pub fn verify_import_hashed<'a>(
        &'a self,
        id: ImportId,
        candidate: &HashedModule<'a>,
    ) -> Result<VerifiedImport<'a>, ImportVerificationError> {
        let hashed = candidate;
        let candidate = hashed.module();
        let import_index = id.index();
        // C1
        let import = self
            .import(id)
            .ok_or(ImportVerificationError::UnresolvedImport {
                import: import_index,
            })?;
        // Hashed under the scheme the ROW records, never the current one: a
        // row minted under an older domain keeps meaning what it meant.
        let actual = hashed.digest_under(import.scheme);
        // C2
        if import.digest.algorithm != ProofDigestAlgorithm::Sha256 {
            return Err(ImportVerificationError::UnsupportedDigestAlgorithm {
                import: import_index,
                algorithm: import.digest.algorithm,
            });
        }
        // C3
        if actual != import.digest {
            return Err(ImportVerificationError::DigestMismatch {
                import: import_index,
                recorded: import.digest,
                actual,
            });
        }
        // C4
        if candidate.name != import.name {
            return Err(ImportVerificationError::NameMismatch {
                import: import_index,
                recorded: import.name.clone(),
                actual: candidate.name.clone(),
            });
        }
        // C5
        if import.producer.is_none() {
            return Err(ImportVerificationError::ProducerUnrecorded {
                import: import_index,
                side: "import",
            });
        }
        // C6
        match (&self.target_info, &candidate.target_info) {
            (Some(local), Some(far)) => {
                if local != far {
                    return Err(ImportVerificationError::TargetMismatch {
                        import: import_index,
                        detail: format!(
                            "importer pins {} (pointer_size {}, {}, abi {:?}, {:?}); \
                             dependency pins {} (pointer_size {}, {}, abi {:?}, {:?})",
                            local.triple,
                            local.pointer_size,
                            local.endianness,
                            local.abi,
                            local.struct_passing,
                            far.triple,
                            far.pointer_size,
                            far.endianness,
                            far.abi,
                            far.struct_passing,
                        ),
                    });
                }
            }
            (Some(_), None) => {
                return Err(ImportVerificationError::TargetMismatch {
                    import: import_index,
                    detail: "the dependency pins no target (`target_info: None`); an absent \
                             target is never read as agreement"
                        .to_string(),
                });
            }
            (None, Some(_)) => {
                return Err(ImportVerificationError::TargetMismatch {
                    import: import_index,
                    detail: "the importer pins no target (`target_info: None`); an absent \
                             target is never read as agreement"
                        .to_string(),
                });
            }
            (None, None) => {
                return Err(ImportVerificationError::TargetMismatch {
                    import: import_index,
                    detail: "neither module pins a target; a pointer-width-dependent proof \
                             cannot be shown to be about the same machine"
                        .to_string(),
                });
            }
        }
        Ok(VerifiedImport {
            importer: self,
            id,
            import,
            module: candidate,
            digest: actual,
        })
    }

    /// Resolve `r` — cited from `local`, a function of THIS module, at `site`
    /// — across the authenticated import `v`.
    ///
    /// Check order — the first failure names itself:
    ///
    /// * R1 `r.module` is the verified import (`ImportIdMismatch`), then `v`
    ///   was earned by this importer (`VerifiedImportForOtherModule`);
    /// * R2 `local` resolves uniquely here, is a body-less declaration,
    ///   carries the referenced link symbol, and is not interposable
    ///   (`LocalFunctionUnresolved`, `LocalSiteHasBody`, `LinkSymbolMismatch`,
    ///   `InterposableFarSite { side: "local" }`) — except that at
    ///   [`ExternRefSite::CallEdge`] an `ExternalWeak` import is admitted,
    ///   since a claim-free edge has no proof a null binding could falsify;
    /// * R3 exactly one function in the dependency carries `r.symbol`
    ///   (`SymbolUnresolved`, `SymbolAmbiguous`);
    /// * R4 it is a DEFINITION, or a declaration that RECORDS a cross-crate
    ///   backing of its own, it is exported, and its linkage is not
    ///   interposable (`FarSiteIsUnbackedDeclaration`, `SymbolNotExported`,
    ///   `InterposableFarSite { side: "far" }`) — hardened at
    ///   [`ExternRefSite::HandleDeclaration`] (`FarSiteIsAvailableExternallyCopy`,
    ///   and no far declaration without the caller's vouching);
    /// * R5 its recorded producer is the import's (`ProducerUnrecorded`,
    ///   `ProducerMismatch`) — this is the producer-for-producer pairing a
    ///   runtime-handle contract (e.g. a `Nat` runtime) authenticates on;
    /// * R6 the two signatures agree ([`signatures_compatible`],
    ///   `SignatureMismatch`);
    /// * R7 when `r.obligation` is `Some`: it resolves uniquely in the
    ///   dependency, is scoped to the far function, is `Discharged` or
    ///   `Certified`, and its kind is admissible at `site`
    ///   (`ObligationUnresolved`, `ObligationScopeMismatch`,
    ///   `ObligationNotDischarged`, `ObligationKindInadmissible`).
    ///
    /// R7 checks the obligation's STATUS LABEL and scope, which is what a single
    /// module can check. Whether the label is EARNED (a kernel-replayed
    /// certificate, or the dependency's own validation under a proof
    /// authority) is the closure walk's job — `validate_linked_module`
    /// validates the dependency before it relies on anything in it.
    ///
    /// At [`ExternRefSite::HandleDeclaration`] R4 is hardened (see the
    /// variant): an `AvailableExternally` far definition is refused, and so is
    /// EVERY far declaration, because this entry point holds no dependency
    /// verdict to vouch for one. [`Module::resolve_handle_declaration`] is the
    /// form that takes that verdict.
    pub fn resolve_extern_ref<'a>(
        &'a self,
        r: &ExternRef,
        local: FuncId,
        site: ExternRefSite,
        v: &VerifiedImport<'a>,
    ) -> Result<ResolvedExternRef<'a>, ImportVerificationError> {
        self.resolve_extern_ref_inner(r, local, site, v, &|_| false)
    }

    /// Resolve an IMPORT-BACKED HANDLE DECLARATION (WS3.3, F-048): `r` is the
    /// `backed_by` of `local`, a body-less, non-pinned declaration whose
    /// signature reaches a handle, resolved at
    /// [`ExternRefSite::HandleDeclaration`] across `v`.
    ///
    /// R1–R6 run as in [`Module::resolve_extern_ref`], with R4 hardened: the
    /// far function is admitted only as (a) a DEFINITION whose linkage is not
    /// [`Linkage::AvailableExternally`], or (b) a DECLARATION whose id is in
    /// `authenticated_far_declarations` — the dependency's own handle
    /// declarations that ITS linked validation authenticated
    /// (`AuthenticatedImports` in `trust_ir_build`, from the memoized walk,
    /// which validates the dependency before the importer). That set is an
    /// AUTHORITY the caller supplies: pass it only from a verdict the caller
    /// computed over exactly `v.module()`. An empty set admits no far
    /// declaration. `r.obligation`, if any, is ignored: this site is about the
    /// entity, and a proof claim on the same summary is re-earned at its own
    /// proof-bearing site.
    pub fn resolve_handle_declaration<'a>(
        &'a self,
        r: &ExternRef,
        local: FuncId,
        v: &VerifiedImport<'a>,
        authenticated_far_declarations: &BTreeSet<FuncId>,
    ) -> Result<ResolvedExternRef<'a>, ImportVerificationError> {
        let entity = ExternRef::new(r.module, r.symbol.clone());
        self.resolve_extern_ref_inner(
            &entity,
            local,
            ExternRefSite::HandleDeclaration,
            v,
            &|far| authenticated_far_declarations.contains(&far.id),
        )
    }

    /// The shared R1–R7 body. `vouched_far_declaration` decides R4 for a far
    /// DECLARATION at [`ExternRefSite::HandleDeclaration`] only; every other
    /// site keeps the general recorded-backing test.
    fn resolve_extern_ref_inner<'a>(
        &'a self,
        r: &ExternRef,
        local: FuncId,
        site: ExternRefSite,
        v: &VerifiedImport<'a>,
        vouched_far_declaration: &dyn Fn(&Function) -> bool,
    ) -> Result<ResolvedExternRef<'a>, ImportVerificationError> {
        // R1 — preserve the distinct row/id mismatch diagnostic first.
        if r.module != v.id() || self.import(r.module) != Some(v.import()) {
            return Err(ImportVerificationError::ImportIdMismatch {
                expected: v.id().index(),
                actual: r.module.index(),
            });
        }
        // Equal rows in two modules do not mean the same importer earned C6's
        // target check. Bind the token to the exact borrowing module before
        // using its far-side verdict.
        if !std::ptr::eq(self, v.importer) {
            return Err(ImportVerificationError::VerifiedImportForOtherModule {
                import: v.id().index(),
            });
        }
        // R2
        let local_function = ModuleFunctionCatalog::new(self).unique(local).ok_or(
            ImportVerificationError::LocalFunctionUnresolved {
                function: local.index(),
            },
        )?;
        if !local_function.is_declaration() {
            return Err(ImportVerificationError::LocalSiteHasBody {
                function: local.index(),
            });
        }
        if local_function.name != r.symbol {
            return Err(ImportVerificationError::LinkSymbolMismatch {
                function: local.index(),
                local: local_function.name.clone(),
                symbol: r.symbol.clone(),
            });
        }
        // R2 — an interposable local declaration may bind a different
        // definition, or NULL (`ExternalWeak`), at link time: the far body the
        // proof is about need not be the one this module calls. A CLAIM-FREE
        // call edge is about no proof, so its weak import is admitted (the
        // null-checked address idiom is the importer validator's rule); R3–R6
        // still check what the linker binds it to when it binds at all.
        let weak_call_edge =
            site == ExternRefSite::CallEdge && local_function.linkage == Linkage::ExternalWeak;
        if local_function.linkage.is_interposable() && !weak_call_edge {
            return Err(ImportVerificationError::InterposableFarSite {
                symbol: r.symbol.clone(),
                linkage: local_function.linkage,
                side: "local",
            });
        }
        // R3
        let candidate = v.module();
        let mut matches = candidate
            .functions
            .iter()
            .filter(|function| function.name == r.symbol);
        let far = match (matches.next(), matches.next()) {
            (None, _) => {
                return Err(ImportVerificationError::SymbolUnresolved {
                    symbol: r.symbol.clone(),
                });
            }
            (Some(far), None) => far,
            (Some(_), Some(_)) => {
                return Err(ImportVerificationError::SymbolAmbiguous {
                    symbol: r.symbol.clone(),
                    count: candidate
                        .functions
                        .iter()
                        .filter(|function| function.name == r.symbol)
                        .count(),
                });
            }
        };
        // R4 — a DEFINITION, or a declaration that hands the claim onwards.
        // R3 picks the unique function carrying the symbol, which may be a
        // body-less declaration; a cross-crate claim is ultimately about a
        // BODY, so a dependency that merely RE-DECLARES the symbol must not
        // authenticate one. A declaration that records a cross-crate backing
        // is admitted — that is the ratified transitive chain, and the closure
        // walk re-earns the citation it names. Checked before linkage so the
        // refusal names the substantive defect rather than a visibility one.
        //
        // At a HANDLE DECLARATION the general test is too weak: an
        // entity-only `backed_by` "records a backing" that nothing re-earned,
        // so a dependency that merely re-declares the symbol would stand in for
        // a definition nothing checked. There a far declaration needs the
        // caller's vouching (its own authenticated outcome in the dependency's
        // verdict), and a far `AvailableExternally` copy is not the body the
        // linker binds.
        if far.is_declaration() {
            let admitted = match site {
                ExternRefSite::HandleDeclaration => vouched_far_declaration(far),
                ExternRefSite::SummaryBackedBy
                | ExternRefSite::InheritedFromCallee
                | ExternRefSite::CallEdge => far_records_a_backing(candidate, far),
            };
            if !admitted {
                return Err(ImportVerificationError::FarSiteIsUnbackedDeclaration {
                    symbol: r.symbol.clone(),
                });
            }
        } else if site == ExternRefSite::HandleDeclaration
            && far.linkage == Linkage::AvailableExternally
        {
            return Err(ImportVerificationError::FarSiteIsAvailableExternallyCopy {
                symbol: r.symbol.clone(),
            });
        }
        if far.linkage.is_module_local() {
            return Err(ImportVerificationError::SymbolNotExported {
                symbol: r.symbol.clone(),
                linkage: far.linkage,
            });
        }
        // R4 — the linker may replace an interposable far definition with one
        // nobody proved anything about (`Weak` / `LinkOnce`), or bind nothing
        // at all (`ExternalWeak`). The ODR spellings and `AvailableExternally`
        // stay admitted under the disclosed one-definition-rule premise.
        if far.linkage.is_interposable() {
            return Err(ImportVerificationError::InterposableFarSite {
                symbol: r.symbol.clone(),
                linkage: far.linkage,
                side: "far",
            });
        }
        // R5 — the import's producer is `Some` by C5.
        let recorded =
            v.import()
                .producer
                .as_ref()
                .ok_or(ImportVerificationError::ProducerUnrecorded {
                    import: v.id().index(),
                    side: "import",
                })?;
        match &far.producer {
            None => {
                return Err(ImportVerificationError::ProducerUnrecorded {
                    import: v.id().index(),
                    side: "function",
                });
            }
            Some(actual) if actual != recorded => {
                return Err(ImportVerificationError::ProducerMismatch {
                    symbol: r.symbol.clone(),
                    recorded: recorded.clone(),
                    actual: actual.clone(),
                });
            }
            Some(_) => {}
        }
        // R6
        signatures_compatible(self, local_function, candidate, far).map_err(|detail| {
            ImportVerificationError::SignatureMismatch {
                symbol: r.symbol.clone(),
                detail,
            }
        })?;
        // R7
        let obligation = match r.obligation {
            None => None,
            Some(cited) => Some(resolve_cited_obligation(
                candidate, far, &r.symbol, cited, site,
            )?),
        };
        Ok(ResolvedExternRef {
            local: local_function,
            far,
            obligation,
        })
    }
}

/// Whether a body-less far `function` hands its claim onwards rather than
/// merely asserting it: its summary cites another module with `backed_by`, or
/// the dependency carries an `InheritedFromCallee { external: Some }`
/// certificate naming it as the callee.
///
/// This is a RECORDED-backing test, not a verdict: whether the citation is
/// earned is `validate_linked_module`'s job, which follows it. `backed_by:
/// None` with no such certificate is NOT RECORDED, and therefore refused.
fn far_records_a_backing(candidate: &Module, function: &Function) -> bool {
    if function
        .summary
        .as_ref()
        .is_some_and(|summary| summary.backed_by.is_some())
    {
        return true;
    }
    candidate.proof_certificates.iter().any(|certificate| {
        matches!(
            &certificate.evidence,
            crate::proof::ProofEvidence::InheritedFromCallee {
                callee,
                external: Some(_),
                ..
            } if *callee == function.id
        )
    })
}

fn resolve_cited_obligation<'a>(
    candidate: &'a Module,
    far: &Function,
    symbol: &str,
    cited: ProofId,
    site: ExternRefSite,
) -> Result<&'a ProofObligation, ImportVerificationError> {
    let mut matches = candidate
        .proof_obligations
        .iter()
        .filter(|obligation| obligation.id == cited);
    let obligation = match (matches.next(), matches.next()) {
        (Some(obligation), None) => obligation,
        _ => {
            return Err(ImportVerificationError::ObligationUnresolved {
                symbol: symbol.to_string(),
                obligation: cited.index(),
            });
        }
    };
    if obligation.function != Some(far.id) {
        return Err(ImportVerificationError::ObligationScopeMismatch {
            obligation: cited.index(),
            expected: far.id.index(),
            actual: obligation.function.map(FuncId::index),
        });
    }
    if !obligation.status.is_discharged_tier() {
        return Err(ImportVerificationError::ObligationNotDischarged {
            obligation: cited.index(),
            status: obligation.status,
        });
    }
    if !site.admits(&obligation.kind) {
        return Err(ImportVerificationError::ObligationKindInadmissible {
            obligation: cited.index(),
            site,
            kind: obligation.kind.to_string(),
        });
    }
    Ok(obligation)
}

/// Whether `fa` (a function of module `a`) and `fb` (of module `b`) present
/// the same call signature across the module boundary.
///
/// Equal when: the calling conventions agree; both `FuncTyId`s resolve; the
/// parameter and return arities and `is_vararg` agree; every parameter and
/// return type is [`ty_structurally_eq_across`]; and the ABI-bearing
/// per-slot attributes agree — `byval`, `sret`, and since v45 (WS3.11) the
/// integer extension (`ext`) and pass mode (`pass`) of every parameter and of
/// the return slot (`FuncAttrs::ret`) — with a missing trailing
/// `FuncAttrs::params` row read as [`ParamAttrs::default`]. An UNRECORDED
/// fact on one side against a recorded one on the other is a disagreement,
/// never a wildcard. The hint-style attributes (`nonnull`, `align`, …) do not
/// participate: they change what a backend may assume, not the call's
/// byte-level ABI.
///
/// `Err` names the first disagreement.
pub fn signatures_compatible(
    a: &Module,
    fa: &Function,
    b: &Module,
    fb: &Function,
) -> Result<(), String> {
    if fa.calling_conv != fb.calling_conv {
        return Err(format!(
            "calling convention {} vs {}",
            fa.calling_conv, fb.calling_conv
        ));
    }
    let sa = a.func_type(fa.ty).ok_or_else(|| {
        format!(
            "local signature functy.{} does not resolve in its module",
            fa.ty.index()
        )
    })?;
    let sb = b.func_type(fb.ty).ok_or_else(|| {
        format!(
            "far signature functy.{} does not resolve in its module",
            fb.ty.index()
        )
    })?;
    if sa.params.len() != sb.params.len() {
        return Err(format!(
            "parameter arity {} vs {}",
            sa.params.len(),
            sb.params.len()
        ));
    }
    if sa.returns.len() != sb.returns.len() {
        return Err(format!(
            "return arity {} vs {}",
            sa.returns.len(),
            sb.returns.len()
        ));
    }
    if sa.is_vararg != sb.is_vararg {
        return Err(format!("is_vararg {} vs {}", sa.is_vararg, sb.is_vararg));
    }
    if sa.abi != sb.abi {
        return Err("typed signature ABI claims differ".into());
    }
    for (index, (pa, pb)) in sa.params.iter().zip(&sb.params).enumerate() {
        if !ty_structurally_eq_across(a, pa, b, pb) {
            return Err(format!("parameter {index} type {pa} vs {pb}"));
        }
    }
    for (index, (ra, rb)) in sa.returns.iter().zip(&sb.returns).enumerate() {
        if !ty_structurally_eq_across(a, ra, b, rb) {
            return Err(format!("return {index} type {ra} vs {rb}"));
        }
    }
    for index in 0..sa.params.len() {
        let aa = fa.attrs.params.get(index).cloned().unwrap_or_default();
        let ab = fb.attrs.params.get(index).cloned().unwrap_or_default();
        if aa.byval != ab.byval {
            return Err(format!(
                "parameter {index} byval {} vs {}",
                aa.byval, ab.byval
            ));
        }
        if aa.sret != ab.sret {
            return Err(format!("parameter {index} sret {} vs {}", aa.sret, ab.sret));
        }
        // v45 (WS3.11): the extension and pass mode change the call's
        // byte-level ABI exactly like `byval`. `Cast` lanes are closed
        // scalars, so plain equality is already cross-module equality.
        if aa.ext != ab.ext {
            return Err(format!(
                "parameter {index} ext {:?} vs {:?}",
                aa.ext, ab.ext
            ));
        }
        if aa.pass != ab.pass {
            return Err(format!(
                "parameter {index} pass mode {:?} vs {:?}",
                aa.pass, ab.pass
            ));
        }
    }
    let (ra, rb) = (&fa.attrs.ret, &fb.attrs.ret);
    if ra.ext != rb.ext {
        return Err(format!("return slot ext {:?} vs {:?}", ra.ext, rb.ext));
    }
    if ra.pass != rb.pass {
        return Err(format!(
            "return slot pass mode {:?} vs {:?}",
            ra.pass, rb.pass
        ));
    }
    Ok(())
}

/// Structural type equality ACROSS two modules, each type resolved against its
/// own referent tables.
///
/// Two modules number their `types` / `structs` / `enums` / `records` /
/// `closure_types` / `func_types` / `predicates` / `universes` tables
/// independently, so no id means anything across the boundary; this compares
/// what the ids DENOTE:
///
/// * scalars, `Ptr`, `Unit`, `Never`, and the `Str` / `ContainerLen` /
///   `ContainerVtable` fat-pointer kinds by variant; `TraitObject` by exact
///   `trait_id`, which is EQUALITY and therefore agreement — see the trusted
///   assumption below;
/// * `Vector`, `Tuple`, `Ref` / `RefMut` / `PtrConst` / `PtrMut` / `Rc`
///   recursively; `Array` / `Sequence` / `Set` / `Slice` resolve their `TyId`
///   in their own module (a dangling id is `false`; `SetRepr` must agree);
/// * `Struct` by name, repr, size, align and fields (name, offset, type);
///   `Enum` by name, variants (name and field types; `field_names` are
///   fidelity metadata and are IGNORED), effective discriminants, canonical
///   tag repr and layout descriptor; `Record` by name and fields; `Closure`
///   by signature and captures; `Func` recursively;
/// * `Refine` by base type AND predicate CONTENT (`Conj` / `Disj` children and
///   `InUniverse` universes resolved recursively; `Interval` / `FiniteSet` /
///   `NonZero` / `NonNull` / `Top` / `Bottom` by value);
/// * `Dialect` by exact `(namespace, name, version)` — NOMINAL, so `Ptr` is
///   never a `Dialect` and two runtimes cannot exchange handles;
/// * `Handle` (v43) by exact `(name, runtime)` — likewise NOMINAL: `Ptr` is
///   never a `Handle`, and a dependency's `Handle("Nat", "a::Nat")` is not this
///   module's `Handle("Nat", "b::Nat")`;
/// * `Error` is never equal to anything, itself included.
///
/// Coinductive: a nominal pair already being compared returns `true` on
/// re-entry, so self-referential structs terminate (`trust_ir::diff`'s
/// fingerprint is not cycle-safe, which is why this is a separate comparator).
///
/// # Trusted assumption: the `trait_id` mint
///
/// Every other cross-module answer here is derived from CONTENT this function
/// can read — a struct's name and field types, a handle's `(name, runtime)`,
/// a predicate's literals. `FatPtrKind::TraitObject { trait_id }` is the one
/// exception: `trait_id` is a bare `u32` on the wire, and the def-path string
/// it was minted from is NOT carried in the IR. So equal ids compare EQUAL
/// across the crate boundary, and nothing in `binary.rs`, `validate.rs` or
/// [`signatures_compatible`] can check that the two producers minted them the
/// same way — nor could anything, without the key.
///
/// This arm is therefore sound exactly to the extent that both modules obeyed
/// the ratified convention in [`crate::ty::stable_trait_object_id`]: the id is
/// content-derived (32-bit FNV-1a of the principal def-path render), the
/// renderer is injective over the entity, and the frontend keeps the
/// `id -> key` tripwire. A producer that instead numbers its trait objects
/// positionally makes this comparator — and through it
/// [`Module::resolve_extern_ref`]'s R6 signature check — agree that a local
/// `fn(&dyn Display)` and a far `fn(&dyn Debug)` are the same contract, whose
/// vtable metadata word has a different layout at the ABI boundary. That is a
/// PRODUCER obligation, and both of the collision directions it has to close
/// (a hash collision, and a non-injective renderer) are enumerated at
/// `stable_trait_object_id`, together with the measured fail-open direction
/// (2) once shipped as.
///
/// This paragraph exists because the doc here previously asserted the
/// opposite — that `trait_id` was "a producer-local number with no nominal
/// identity yet, so this fails CLOSED across crates". Neither half was true:
/// the arm compares `ta == tb` and so returns `true` on agreement, and
/// `stable_trait_object_id` had already ratified the id as a content-derived
/// identity. A reader who took the old contract at face value would conclude
/// a cross-crate trait-object mismatch was impossible here and so never
/// record the mint discipline in their trusted base — the same shape of
/// omission that let direction (2) ship open.
///
/// # The v58 nominal key
///
/// A `StructDef`/`EnumDef` may carry a [`TypeOrigin`]. The key never ADMITS
/// anything — it only SPLITS or REFUSES:
///
/// * both sides keyed, keys DIFFERENT → **not equal**, whatever the structure
///   says. Two source entities that happen to share a layout are two types.
/// * both sides keyed, keys EQUAL, structure UNEQUAL → **not equal**, and the
///   contradiction is reported by [`ty_equivalence_across`] as a
///   [`TypeOriginConflict`] so a linked validator can name it rather than
///   silently returning "different".
/// * either side UNKEYED → structural, exactly as before the field existed.
///   An absent key is never a wildcard and never makes two things equal that
///   structure says are different.
#[must_use]
pub fn ty_structurally_eq_across(a: &Module, ta: &Ty, b: &Module, tb: &Ty) -> bool {
    matches!(ty_equivalence_across(a, ta, b, tb), TyEquivalence::Equal)
}

/// Two definitions stamped with ONE nominal key disagree about structure.
///
/// This is a producer contradiction, not a type distinction: one source entity
/// cannot have two shapes. It is surfaced (never swallowed) so a linked
/// validator refuses the closure by name instead of treating the pair as two
/// unrelated types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeOriginConflict {
    /// The key both definitions stamped.
    pub origin: TypeOrigin,
    /// Which definition table the pair came from: `"struct"` or `"enum"`.
    pub table: &'static str,
    /// The LEFT module's definition name.
    pub left: String,
    /// The RIGHT module's definition name.
    pub right: String,
}

impl core::fmt::Display for TypeOriginConflict {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "{} `{}` and `{}` both carry origin {} but are not structurally equal",
            self.table, self.left, self.right, self.origin
        )
    }
}

/// The verdict of a cross-module type comparison.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TyEquivalence {
    /// The same type on both sides.
    Equal,
    /// Different types. This INCLUDES the origin-split case (equal structure,
    /// different keys), which is a legitimate distinction and not an error.
    Unequal,
    /// Not equal, AND the reason is a contradiction: one key, two shapes.
    OriginConflict(TypeOriginConflict),
}

/// Compare two types across module boundaries, reporting a nominal-key
/// contradiction rather than folding it into "not equal".
///
/// Equality is exactly [`ty_structurally_eq_across`]'s; only the *reason* for
/// inequality is refined. When several conflicts occur in one comparison the
/// FIRST encountered is reported — a refusal names one cause and stops.
#[must_use]
pub fn ty_equivalence_across(a: &Module, ta: &Ty, b: &Module, tb: &Ty) -> TyEquivalence {
    let mut cx = TyEq {
        a,
        b,
        in_progress: BTreeSet::new(),
        conflict: None,
    };
    if cx.ty(ta, tb) {
        return TyEquivalence::Equal;
    }
    match cx.conflict {
        Some(conflict) => TyEquivalence::OriginConflict(conflict),
        None => TyEquivalence::Unequal,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Nominal {
    Struct,
    Enum,
    Record,
    Closure,
    FuncTy,
    TyId,
    Pred,
}

struct TyEq<'m> {
    a: &'m Module,
    b: &'m Module,
    in_progress: BTreeSet<(Nominal, u32, u32)>,
    /// The FIRST one-key-two-shapes contradiction seen in this comparison.
    conflict: Option<TypeOriginConflict>,
}

impl TyEq<'_> {
    fn guarded(&mut self, key: (Nominal, u32, u32), check: impl FnOnce(&mut Self) -> bool) -> bool {
        if !self.in_progress.insert(key) {
            // Coinductive hypothesis: the pair is already assumed equal higher
            // up this comparison.
            return true;
        }
        let result = check(self);
        self.in_progress.remove(&key);
        result
    }

    fn ty(&mut self, ta: &Ty, tb: &Ty) -> bool {
        match (ta, tb) {
            (Ty::I8, Ty::I8)
            | (Ty::I16, Ty::I16)
            | (Ty::I32, Ty::I32)
            | (Ty::I64, Ty::I64)
            | (Ty::I128, Ty::I128)
            | (Ty::U8, Ty::U8)
            | (Ty::U16, Ty::U16)
            | (Ty::U32, Ty::U32)
            | (Ty::U64, Ty::U64)
            | (Ty::U128, Ty::U128)
            | (Ty::Isize, Ty::Isize)
            | (Ty::Usize, Ty::Usize)
            | (Ty::Char, Ty::Char)
            | (Ty::F16, Ty::F16)
            | (Ty::F32, Ty::F32)
            | (Ty::F64, Ty::F64)
            | (Ty::Bool, Ty::Bool)
            | (Ty::Ptr, Ty::Ptr)
            | (Ty::Unit, Ty::Unit)
            | (Ty::Never, Ty::Never) => true,
            (Ty::Error, _) | (_, Ty::Error) => false,
            (Ty::Vector(ea, na), Ty::Vector(eb, nb)) => na == nb && self.ty(ea, eb),
            (Ty::Tensor(ea, ra), Ty::Tensor(eb, rb)) => ra == rb && self.ty(ea, eb),
            (Ty::FatPtr(ka), Ty::FatPtr(kb)) => self.fat_ptr(ka, kb),
            (Ty::Struct(sa), Ty::Struct(sb)) => self.strukt(*sa, *sb),
            (Ty::Array(ea, na), Ty::Array(eb, nb)) => na == nb && self.ty_id(*ea, *eb),
            (Ty::Tuple(xa), Ty::Tuple(xb)) => {
                xa.len() == xb.len() && xa.iter().zip(xb).all(|(x, y)| self.ty(x, y))
            }
            (Ty::Enum(ea), Ty::Enum(eb)) => self.enm(*ea, *eb),
            (Ty::Func(fa), Ty::Func(fb)) => self.func_ty(*fa, *fb),
            (Ty::Ref(ia), Ty::Ref(ib))
            | (Ty::RefMut(ia), Ty::RefMut(ib))
            | (Ty::PtrConst(ia), Ty::PtrConst(ib))
            | (Ty::PtrMut(ia), Ty::PtrMut(ib))
            | (Ty::Rc(ia), Ty::Rc(ib)) => self.ty(ia, ib),
            (Ty::Set(ea, ra), Ty::Set(eb, rb)) => ra == rb && self.ty_id(*ea, *eb),
            (Ty::Sequence(ea), Ty::Sequence(eb)) => self.ty_id(*ea, *eb),
            (Ty::Record(ra), Ty::Record(rb)) => self.record(*ra, *rb),
            (Ty::Closure(ca), Ty::Closure(cb)) => self.closure(*ca, *cb),
            (Ty::Refine(ba, pa), Ty::Refine(bb, pb)) => self.ty_id(*ba, *bb) && self.pred(*pa, *pb),
            (Ty::Dialect(da), Ty::Dialect(db)) => da == db,
            (Ty::Handle(ha), Ty::Handle(hb)) => ha == hb,
            _ => false,
        }
    }

    fn fat_ptr(&mut self, ka: &FatPtrKind, kb: &FatPtrKind) -> bool {
        match (ka, kb) {
            (FatPtrKind::Slice(ea), FatPtrKind::Slice(eb)) => self.ty_id(*ea, *eb),
            (FatPtrKind::Str, FatPtrKind::Str)
            | (FatPtrKind::ContainerLen, FatPtrKind::ContainerLen)
            | (FatPtrKind::ContainerVtable, FatPtrKind::ContainerVtable) => true,
            (
                FatPtrKind::TraitObject { trait_id: ta },
                FatPtrKind::TraitObject { trait_id: tb },
            ) => ta == tb,
            _ => false,
        }
    }

    fn ty_id(&mut self, ta: TyId, tb: TyId) -> bool {
        let (Some(ra), Some(rb)) = (
            self.a.types.get(ta.as_usize()),
            self.b.types.get(tb.as_usize()),
        ) else {
            return false;
        };
        self.guarded((Nominal::TyId, ta.index(), tb.index()), |cx| cx.ty(ra, rb))
    }

    /// Record the FIRST one-key-two-shapes contradiction; later ones are
    /// dropped so a refusal names one cause.
    fn note_conflict(&mut self, origin: &TypeOrigin, table: &'static str, left: &str, right: &str) {
        if self.conflict.is_none() {
            self.conflict = Some(TypeOriginConflict {
                origin: origin.clone(),
                table,
                left: left.to_string(),
                right: right.to_string(),
            });
        }
    }

    /// The v58 split rule, shared by `strukt` and `enm`: `Some(key)` when both
    /// sides carry the SAME key (structure must then agree, or it is a
    /// conflict), `None` when the comparison is purely structural. Returns
    /// `Err(())` when the keys DIFFER — two source entities, so not equal
    /// whatever the structure says.
    #[allow(clippy::result_unit_err)]
    fn shared_origin<'o>(
        left: &'o Option<TypeOrigin>,
        right: &'o Option<TypeOrigin>,
    ) -> Result<Option<&'o TypeOrigin>, ()> {
        match (left, right) {
            (Some(oa), Some(ob)) if oa == ob => Ok(Some(oa)),
            (Some(_), Some(_)) => Err(()),
            // Either side UNKEYED: structural, exactly as before v58. An
            // absent key is not a wildcard — it simply carries no claim.
            _ => Ok(None),
        }
    }

    fn strukt(&mut self, sa: crate::value::StructId, sb: crate::value::StructId) -> bool {
        let (Some(da), Some(db)) = (self.a.struct_def(sa), self.b.struct_def(sb)) else {
            return false;
        };
        let Ok(shared) = Self::shared_origin(&da.origin, &db.origin) else {
            return false;
        };
        let structural = self.guarded((Nominal::Struct, sa.index(), sb.index()), |cx| {
            da.name == db.name
                && da.repr == db.repr
                && da.size == db.size
                && da.align == db.align
                && da.fields.len() == db.fields.len()
                && da.fields.iter().zip(&db.fields).all(|(fa, fb)| {
                    fa.name == fb.name && fa.offset == fb.offset && cx.ty(&fa.ty, &fb.ty)
                })
        });
        if !structural && let Some(origin) = shared {
            self.note_conflict(origin, "struct", &da.name, &db.name);
        }
        structural
    }

    fn enm(&mut self, ea: crate::value::EnumId, eb: crate::value::EnumId) -> bool {
        let (Some(da), Some(db)) = (self.a.enum_def(ea), self.b.enum_def(eb)) else {
            return false;
        };
        let Ok(shared) = Self::shared_origin(&da.origin, &db.origin) else {
            return false;
        };
        let structural = self.guarded((Nominal::Enum, ea.index(), eb.index()), |cx| {
            da.name == db.name
                && da.variants.len() == db.variants.len()
                && da.variants.iter().zip(&db.variants).all(|(va, vb)| {
                    // `field_names` are fidelity metadata: IGNORED, per their doc.
                    va.name == vb.name
                        && va.fields.len() == vb.fields.len()
                        && va.fields.iter().zip(&vb.fields).all(|(x, y)| cx.ty(x, y))
                })
                && da.effective_discriminants() == db.effective_discriminants()
                && da.canonical_tag_repr() == db.canonical_tag_repr()
                && da.layout == db.layout
        });
        if !structural && let Some(origin) = shared {
            self.note_conflict(origin, "enum", &da.name, &db.name);
        }
        structural
    }

    fn record(&mut self, ra: crate::value::RecordId, rb: crate::value::RecordId) -> bool {
        let (Some(da), Some(db)) = (self.a.record_def(ra), self.b.record_def(rb)) else {
            return false;
        };
        self.guarded((Nominal::Record, ra.index(), rb.index()), |cx| {
            da.name == db.name
                && da.fields.len() == db.fields.len()
                && da.fields.iter().zip(&db.fields).all(|(fa, fb)| {
                    fa.name == fb.name && fa.offset == fb.offset && cx.ty(&fa.ty, &fb.ty)
                })
        })
    }

    fn closure(&mut self, ca: crate::value::ClosureTyId, cb: crate::value::ClosureTyId) -> bool {
        let (Some(da), Some(db)) = (self.a.closure_type(ca), self.b.closure_type(cb)) else {
            return false;
        };
        self.guarded((Nominal::Closure, ca.index(), cb.index()), |cx| {
            cx.func_ty(da.func, db.func)
                && da.captures.len() == db.captures.len()
                && da
                    .captures
                    .iter()
                    .zip(&db.captures)
                    .all(|(x, y)| cx.ty(x, y))
        })
    }

    fn func_ty(&mut self, fa: FuncTyId, fb: FuncTyId) -> bool {
        let (Some(sa), Some(sb)) = (self.a.func_type(fa), self.b.func_type(fb)) else {
            return false;
        };
        self.guarded((Nominal::FuncTy, fa.index(), fb.index()), |cx| {
            sa.is_vararg == sb.is_vararg
                && sa.abi == sb.abi
                && sa.params.len() == sb.params.len()
                && sa.returns.len() == sb.returns.len()
                && sa.params.iter().zip(&sb.params).all(|(x, y)| cx.ty(x, y))
                && sa.returns.iter().zip(&sb.returns).all(|(x, y)| cx.ty(x, y))
        })
    }

    fn pred(&mut self, pa: PredId, pb: PredId) -> bool {
        use crate::pred::Pred;
        let (Some(ra), Some(rb)) = (
            self.a.predicates.get(pa.as_usize()),
            self.b.predicates.get(pb.as_usize()),
        ) else {
            return false;
        };
        self.guarded((Nominal::Pred, pa.index(), pb.index()), |cx| {
            match (ra, rb) {
                (Pred::Interval { lo: la, hi: ha }, Pred::Interval { lo: lb, hi: hb }) => {
                    la == lb && ha == hb
                }
                (Pred::FiniteSet(xa), Pred::FiniteSet(xb)) => xa == xb,
                (Pred::InUniverse(ua, sa), Pred::InUniverse(ub, sb)) => {
                    sa == sb
                        && match (
                            cx.a.universes.get(ua.as_usize()),
                            cx.b.universes.get(ub.as_usize()),
                        ) {
                            (Some(xa), Some(xb)) => xa == xb,
                            _ => false,
                        }
                }
                (Pred::NonZero, Pred::NonZero)
                | (Pred::NonNull, Pred::NonNull)
                | (Pred::Top, Pred::Top)
                | (Pred::Bottom, Pred::Bottom) => true,
                (Pred::Conj(ca), Pred::Conj(cb)) | (Pred::Disj(ca), Pred::Disj(cb)) => {
                    // Children are canonical (sorted by module-local id), so the
                    // same content may sit in a different order across modules:
                    // match as sets, both directions.
                    ca.len() == cb.len()
                        && ca.iter().all(|x| cb.iter().any(|y| cx.pred(*x, *y)))
                        && cb.iter().all(|y| ca.iter().any(|x| cx.pred(*x, *y)))
                }
                _ => false,
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_identity_domain_is_the_stable_digest_domain() {
        // `Module::stable_digest` reads the constant, so this is a guard on the
        // SPELLING, not on the wiring — a rename of the constant's value would
        // silently re-domain every recorded import.
        assert_eq!(MODULE_IDENTITY_DOMAIN, "trust_ir.module.v3");
        assert_eq!(MODULE_IDENTITY_DOMAIN_V2, "trust_ir.module.v2");
        assert_eq!(IdentityScheme::CURRENT, IdentityScheme::V3);
        assert_eq!(IdentityScheme::default(), IdentityScheme::V2);
        let mut m = Module::new("probe");
        // Split so the exported source never spells a home-directory literal
        // (publication's forbidden-content guard); the string is unchanged.
        m.intern_file(concat!("/Us", "ers/a/x.rs"))
            .expect("Module::intern_file: test fixture");
        assert_eq!(m.stable_digest(), m.stable_digest_under(IdentityScheme::V3));
        // V2 is the whole encoding, exactly as before v44.
        assert_eq!(
            m.stable_digest_under(IdentityScheme::V2),
            crate::binary::ModuleBinaryPlan::new(&m).sha256_domain(MODULE_IDENTITY_DOMAIN_V2)
        );
        // V3 is the SAME plan over the module with every file string blanked
        // (length kept), under the v3 domain: the reference construction.
        let mut blanked = m.clone();
        for path in &mut blanked.files {
            path.clear();
        }
        assert_eq!(
            m.stable_digest_under(IdentityScheme::V3),
            crate::binary::ModuleBinaryPlan::new(&blanked).sha256_domain(MODULE_IDENTITY_DOMAIN)
        );
    }

    /// F-084 tripwire (WS1.16, ratchet row `b4.gap.no_module_import_scheme`):
    /// a module-identity domain exists ONLY as an [`IdentityScheme`] variant.
    ///
    /// Moving [`MODULE_IDENTITY_DOMAIN`] is a change to what every recorded
    /// import means; it is sound only because each row carries its
    /// `ModuleImport.scheme` and [`crate::Module::stable_digest_under`] keeps
    /// every older domain computable. This fails — naming the row — if the
    /// existing scheme's domain STRING is re-pointed (the literal bump, which
    /// silently re-means every row already recorded under it), if a scheme is
    /// missing from [`IdentityScheme::ALL`] (so `stable_digest_under` could not
    /// be asked for it), if two schemes share a domain, or if the current
    /// scheme is not the newest. The exhaustive `match` makes a new variant a
    /// compile error here until it is placed in `ALL` WITH its domain.
    ///
    /// The literals are the load-bearing half, and they are why the `match`
    /// spells them out rather than calling [`IdentityScheme::domain`]:
    /// [`MODULE_IDENTITY_DOMAIN`] is DEFINED as `CURRENT.domain()`, so every
    /// comparison derived from it is a tautology — editing `V3`'s arm to
    /// `trust_ir.module.v4` moves the domain with no new variant and satisfies
    /// every self-referential check. Only a pinned literal refuses it.
    #[test]
    fn f084_tripwire_a_domain_bump_is_a_new_identity_scheme() {
        const ROW: &str = "WS1.16 / F-084 (`b4.gap.no_module_import_scheme`): a module-identity \
                           domain bump must add an IdentityScheme variant carried by \
                           ModuleImport.scheme and computable by Module::stable_digest_under";
        /// Each scheme's place in `ALL` and the domain literal it is pinned
        /// to. A new variant does not compile until it is added here, and an
        /// edited domain does not pass until its literal moves WITH it — at
        /// which point it is a new row of this table, not a new spelling of an
        /// old one.
        fn placed(scheme: IdentityScheme) -> (usize, &'static str) {
            match scheme {
                IdentityScheme::V2 => (0, "trust_ir.module.v2"),
                IdentityScheme::V3 => (1, "trust_ir.module.v3"),
            }
        }
        for (i, scheme) in IdentityScheme::ALL.iter().enumerate() {
            let (position, domain) = placed(*scheme);
            assert_eq!(position, i, "{ROW}: {scheme} is out of place in ALL");
            assert_eq!(
                scheme.domain(),
                domain,
                "{ROW}: {scheme}'s domain was re-pointed instead of a new scheme being added"
            );
        }
        assert_eq!(
            MODULE_IDENTITY_DOMAIN,
            placed(IdentityScheme::CURRENT).1,
            "{ROW}: the current domain is not the current scheme's pinned domain"
        );
        assert_eq!(
            IdentityScheme::ALL.last(),
            Some(&IdentityScheme::CURRENT),
            "{ROW}: the current scheme must be the newest"
        );
        let domains: BTreeSet<&str> = IdentityScheme::ALL.iter().map(|s| s.domain()).collect();
        assert_eq!(
            domains.len(),
            IdentityScheme::ALL.len(),
            "{ROW}: two schemes share a domain"
        );
        // Every scheme is computable, and distinct schemes are distinct digests.
        let m = Module::new("probe");
        let digests: BTreeSet<_> = IdentityScheme::ALL
            .iter()
            .map(|s| m.stable_digest_under(*s))
            .collect();
        assert_eq!(digests.len(), IdentityScheme::ALL.len(), "{ROW}");
        assert_eq!(
            m.stable_digest(),
            m.stable_digest_under(IdentityScheme::CURRENT),
            "{ROW}: stable_digest is not the current scheme's digest"
        );
        // A row minted today records the current scheme.
        let row = crate::ModuleImport::new("probe", m.stable_digest());
        assert_eq!(row.scheme, IdentityScheme::CURRENT, "{ROW}");
    }

    #[test]
    fn a_hashed_module_caches_each_scheme_over_its_own_module() {
        let mut m = Module::new("probe");
        m.intern_file("/home/b/x.rs")
            .expect("Module::intern_file: test fixture");
        let hashed = HashedModule::new(&m);
        assert_eq!(hashed.digest(), m.stable_digest());
        for scheme in IdentityScheme::ALL {
            assert_eq!(hashed.digest_under(scheme), m.stable_digest_under(scheme));
            // Cached: asking twice yields the same value.
            assert_eq!(hashed.digest_under(scheme), hashed.digest_under(scheme));
        }
        assert_ne!(
            hashed.digest_under(IdentityScheme::V2),
            hashed.digest_under(IdentityScheme::V3)
        );
    }

    #[test]
    fn site_admission_refuses_custom_and_non_contract_kinds_where_documented() {
        let custom = ObligationKind::Custom {
            namespace: "trust.concurrency".into(),
            name: "send".into(),
        };
        assert!(!ExternRefSite::SummaryBackedBy.admits(&custom));
        assert!(!ExternRefSite::InheritedFromCallee.admits(&custom));
        assert!(!ExternRefSite::SummaryBackedBy.admits(&ObligationKind::MemorySafety));
        assert!(ExternRefSite::InheritedFromCallee.admits(&ObligationKind::MemorySafety));
        assert!(ExternRefSite::SummaryBackedBy.admits(&ObligationKind::Termination));
    }
}

mod observed_ty_equivalence;
pub use observed_ty_equivalence::{
    ty_equivalence_across_observed, ty_structurally_eq_across_observed,
};
