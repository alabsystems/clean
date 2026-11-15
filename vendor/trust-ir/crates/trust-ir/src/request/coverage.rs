// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Consumer-derived input coverage: the sealed [`NativeCoverageAttestation`]
//! and the [`NativeCoverageResultReplay`] seam a consumer re-verifies it with.
//!
//! # The principle
//!
//! Coverage — how much of the input space a discharge covered — is a verdict
//! the CONSUMER derives from evidence it re-checks itself. No producer-written
//! row is a source of coverage. `trust_ir_build::coverage_establishment_report`
//! derives it from exactly two bases, and they answer DIFFERENT questions:
//!
//! * **K, a kernel-replayed claim — per CERTIFICATE**:
//!   [`NativeVerificationBundle::kernel_replayed_certificates`] names the
//!   certificates this process re-checked in the Clean kernel and the
//!   [`KernelClaimFamily`](crate::proof::KernelClaimFamily) of the claim each
//!   replay re-established. The certificate's own evidence WAS the replayed
//!   proof, so the verdict is about that certificate. It cites nothing, so it
//!   has no cycle.
//! * **R, a verified solver result — per OBLIGATION**: a row of the sealed
//!   attestation below CITES (never states) a solver result for an
//!   obligation — the solved bundle, its replay context, its request, its
//!   evidence bundle and the result artifacts, each by digest — and the
//!   consumer recomputes every digest and has a [`NativeCoverageResultReplay`]
//!   implementation re-verify the result before any bound is derived. The row
//!   names NO certificate: nothing ties the result's bytes to any
//!   certificate's evidence, so a verdict derived from it is about the
//!   obligation's claim and vouches for no certificate (schema 1 let a row
//!   label any certificate of the obligation — a `Trusted` one included —
//!   with somebody else's result).
//!
//! # Why the attestation is outside every digest
//!
//! The in-module row it replaces (`ProofCertificate::assurance`) cited a
//! request by digest. A request's replay transcript binds the module digest
//! (that is correct anti-transplant binding), and the module digest covers the
//! row: row → module digest → transcript → request digest → row, with no fixed
//! point. The attestation is read by nothing earlier in the chain — dependency
//! order is module → request → evidence → attestation — so it can be produced
//! after the solve, and it binds the SOLVED bundle, never the admitted one, so
//! it survives a certificate write-back: the consumer checks that the admitted
//! bundle recomputes the same REPLAY CONTEXT
//! (`NativeVerificationBundle::coverage_replay_context_digest`).
//!
//! # The replay context
//!
//! A result is solved in a CONTEXT, not in its obligation alone: a replayer
//! that re-translates the problem from the solved bundle may read any
//! obligation of it (an assumed `Precondition`, a `LoopInvariant`), every
//! function body, summary and callee contract, and the compiler facts. The
//! replay context is the WHOLE solved bundle minus an explicit allowlist of
//! write-back state (`NativeVerificationBundle::coverage_replay_context_digest`)
//! — the default is BOUND, so a field nobody thought about is bound, not
//! forgotten — and the consumer requires the solved and the admitted bundle to
//! recompute the same digest of it. A context carrying what no wire image can
//! bind (a clean-expr `ProofAnnotation::Goal`) still has a digest of
//! everything else, which is still checked, but nothing is established from
//! it.
//!
//! # What a replay may assume
//!
//! NOTHING the consumer does not bind and check. The request's typed replay
//! atoms are not premises (an `Assumption` atom leaves the result without a
//! bound; an `Assertion` atom must state exactly the claim of the obligation it
//! cites, or the bundle is refused), and another obligation's claim is a
//! premise only when the replay NAMES it ([`NativeReplayedResult::premises`]):
//! the consumer then establishes the result only if every named premise is
//! itself established — unboundedly, in the same report, with no cycle — and
//! refuses it when one is `Failed`.
//!
//! Nothing here is a verdict. The types carry citations; the rule that turns
//! them into a bound lives in `trust_ir_build`, and the replay that makes a
//! citation mean anything lives in the verifier that owns the result
//! (trust-mc's `NativeTrustIrCoverageReplayer`).

use super::*;

/// Schema version of a [`NativeCoverageAttestation`]. EXACT-match on read: a
/// consumer refuses every other number (it is a sealed cross-repo artifact,
/// not a file format with a read range). Schema 1 (rows naming a certificate,
/// no replay context) is refused as stale.
pub const NATIVE_COVERAGE_ATTESTATION_SCHEMA_VERSION: u32 = 2;

/// Digest domain of [`NativeCoverageAttestation::stable_digest`] and
/// [`NativeCoverageAttestationRow::stable_digest`] (one domain, a leading tag
/// byte separating the two images). Registered in `wire-allocations.toml`;
/// tracks [`NATIVE_COVERAGE_ATTESTATION_SCHEMA_VERSION`].
pub const NATIVE_COVERAGE_ATTESTATION_DIGEST_DOMAIN: &str =
    "trust_ir.native.coverage.attestation.v2";

/// Digest domain of `NativeVerificationBundle::coverage_replay_context_digest`.
/// Registered in `wire-allocations.toml`. v2 hashes the whole bundle minus an
/// explicit write-back allowlist; v1 (an enumerated list: executable content,
/// the claim digests, the compiler facts) is burned.
pub const NATIVE_COVERAGE_REPLAY_CONTEXT_DIGEST_DOMAIN: &str =
    "trust_ir.native.coverage.replay_context.v2";

/// Tag byte of a whole-attestation digest image.
const ATTESTATION_IMAGE_TAG: u8 = 0;
/// Tag byte of a single-row digest image.
const ROW_IMAGE_TAG: u8 = 1;

/// A sealed list of verified-solver-result CITATIONS, one per
/// (obligation, solved bundle, request) — basis R of consumer-derived
/// coverage.
///
/// Deliberately inside NO digest: not the module's, not a request's, not an
/// evidence bundle's, not the [`NativeVerificationBundle`]'s. Mutating it
/// moves only [`Self::stable_digest`].
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeCoverageAttestation {
    pub schema_version: u32,
    pub rows: Vec<NativeCoverageAttestationRow>,
}

/// One citation: "obligation `obligation` (claim `obligation_digest`) has the
/// result a solver produced for request `request_digest` of the solved bundle
/// `solved_bundle_digest`, in the replay context
/// `solved_replay_context_digest`, whose evidence is `evidence_bundle_digest`
/// and whose result bytes are `result_artifacts`."
///
/// It names NO certificate, on purpose: a solver result is evidence about the
/// obligation's claim, and nothing binds its bytes to any certificate's
/// evidence, so a consumer's verdict from it is per obligation and never reads
/// as vouching for a certificate.
///
/// It has NO bound field, on purpose: the bound is derived by the consumer
/// from the request's mode and options and the strength the replayer
/// re-established, and a field here would be a producer-written second source
/// of truth.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeCoverageAttestationRow {
    /// The obligation whose coverage is cited.
    pub obligation: ProofId,
    /// `Module::obligation_digest(obligation)` of the SOLVED module: the claim
    /// the result is about. The admitted module must carry the same claim.
    pub obligation_digest: ProofDigest,
    /// `Module::stable_digest` of the solved module.
    pub solved_module_digest: ProofDigest,
    /// `Module::executable_content_digest_v1` of the solved module; the
    /// admitted module must carry the same executable content.
    pub solved_executable_content_digest: ProofDigest,
    /// `NativeVerificationBundle::coverage_replay_context_digest(..).digest`
    /// of the solved bundle: everything the replay may establish the result
    /// from that a wire image binds. The solved bundle must recompute it (else
    /// the row lies about its own context) and so must the admitted bundle
    /// (else the context drifted between the solve and the admission) — also
    /// when a clean-expr Goal on either side leaves the result undetermined.
    pub solved_replay_context_digest: ProofDigest,
    /// `NativeVerificationBundle::stable_digest` of the solved bundle.
    pub solved_bundle_digest: ProofDigest,
    /// `NativeVerificationRequest::stable_digest` of the request that was solved.
    pub request_digest: ProofDigest,
    /// `NativeEvidenceBundle::stable_digest` of that request's result evidence.
    pub evidence_bundle_digest: ProofDigest,
    /// The result artifacts the replayer reads (their bytes arrive as
    /// [`NativeEvidenceArtifactAttachment`]s), each one a descriptor of the
    /// cited evidence bundle.
    pub result_artifacts: Vec<NativeEvidenceArtifact>,
}

/// Why a [`NativeCoverageAttestation`] is malformed on its face.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeCoverageAttestationError {
    /// `schema_version` is not [`NATIVE_COVERAGE_ATTESTATION_SCHEMA_VERSION`].
    UnsupportedSchemaVersion(u32),
    /// Two rows cite the same result (solved bundle and request) for the same
    /// obligation.
    DuplicateRow {
        obligation: ProofId,
        solved_bundle_digest: ProofDigest,
        request_digest: ProofDigest,
    },
    /// A digest a row cites is not SHA-256 (the legacy stable checksum is
    /// collision-prone and never selects authority), or is all-zero.
    NonCryptographicDigest { row: usize, field: &'static str },
}

impl core::fmt::Display for NativeCoverageAttestationError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::UnsupportedSchemaVersion(found) => write!(
                f,
                "coverage attestation schema version {found} is not the supported \
                 {NATIVE_COVERAGE_ATTESTATION_SCHEMA_VERSION} (exact match)"
            ),
            Self::DuplicateRow {
                obligation,
                solved_bundle_digest,
                request_digest,
            } => write!(
                f,
                "two coverage attestation rows cite obligation #{} with request {} of solved \
                 bundle {}",
                obligation.index(),
                request_digest,
                solved_bundle_digest
            ),
            Self::NonCryptographicDigest { row, field } => write!(
                f,
                "coverage attestation row {row}: `{field}` is not a non-zero SHA-256 digest"
            ),
        }
    }
}

impl std::error::Error for NativeCoverageAttestationError {}

impl NativeCoverageAttestation {
    /// An attestation at the current schema.
    #[must_use]
    pub fn new(rows: Vec<NativeCoverageAttestationRow>) -> Self {
        Self {
            schema_version: NATIVE_COVERAGE_ATTESTATION_SCHEMA_VERSION,
            rows,
        }
    }

    /// Structural validity only: exact schema version, no two rows citing the
    /// same (obligation, solved bundle, request), and every cited digest a
    /// non-zero SHA-256. Says nothing about whether any citation resolves —
    /// that is the consumer's rule.
    pub fn validate(&self) -> Result<(), Vec<NativeCoverageAttestationError>> {
        let mut errors = Vec::new();
        if self.schema_version != NATIVE_COVERAGE_ATTESTATION_SCHEMA_VERSION {
            errors.push(NativeCoverageAttestationError::UnsupportedSchemaVersion(
                self.schema_version,
            ));
        }
        let mut seen = BTreeSet::new();
        for (index, row) in self.rows.iter().enumerate() {
            if !seen.insert((row.obligation, row.solved_bundle_digest, row.request_digest)) {
                errors.push(NativeCoverageAttestationError::DuplicateRow {
                    obligation: row.obligation,
                    solved_bundle_digest: row.solved_bundle_digest,
                    request_digest: row.request_digest,
                });
            }
            let digests: [(&'static str, &ProofDigest); 7] = [
                ("obligation_digest", &row.obligation_digest),
                ("solved_module_digest", &row.solved_module_digest),
                (
                    "solved_executable_content_digest",
                    &row.solved_executable_content_digest,
                ),
                (
                    "solved_replay_context_digest",
                    &row.solved_replay_context_digest,
                ),
                ("solved_bundle_digest", &row.solved_bundle_digest),
                ("request_digest", &row.request_digest),
                ("evidence_bundle_digest", &row.evidence_bundle_digest),
            ];
            for (field, digest) in digests {
                if digest.algorithm != ProofDigestAlgorithm::Sha256 || digest.is_zero() {
                    errors.push(NativeCoverageAttestationError::NonCryptographicDigest {
                        row: index,
                        field,
                    });
                }
            }
            for artifact in &row.result_artifacts {
                if artifact.digest.algorithm != ProofDigestAlgorithm::Sha256
                    || artifact.digest.is_zero()
                {
                    errors.push(NativeCoverageAttestationError::NonCryptographicDigest {
                        row: index,
                        field: "result_artifacts.digest",
                    });
                }
            }
        }
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    /// SHA-256 identity of the whole attestation under
    /// [`NATIVE_COVERAGE_ATTESTATION_DIGEST_DOMAIN`]: the schema version and
    /// every row's [`NativeCoverageAttestationRow::stable_digest`], in sorted
    /// order (row order is not identity).
    #[must_use]
    pub fn stable_digest(&self) -> ProofDigest {
        let mut rows: Vec<ProofDigest> = self
            .rows
            .iter()
            .map(NativeCoverageAttestationRow::stable_digest)
            .collect();
        rows.sort();
        let mut bytes = Vec::new();
        write_u8_stable(&mut bytes, ATTESTATION_IMAGE_TAG);
        write_u32_stable(&mut bytes, self.schema_version);
        write_len_stable(&mut bytes, rows.len());
        for row in &rows {
            write_digest_stable(&mut bytes, row);
        }
        ProofDigest::sha256_domain(NATIVE_COVERAGE_ATTESTATION_DIGEST_DOMAIN, &bytes)
    }
}

impl NativeCoverageAttestationRow {
    /// SHA-256 identity of one row (every field, artifacts in sorted order),
    /// under [`NATIVE_COVERAGE_ATTESTATION_DIGEST_DOMAIN`] with the row tag.
    #[must_use]
    pub fn stable_digest(&self) -> ProofDigest {
        let mut bytes = Vec::new();
        write_u8_stable(&mut bytes, ROW_IMAGE_TAG);
        write_u32_stable(&mut bytes, self.obligation.index());
        write_digest_stable(&mut bytes, &self.obligation_digest);
        write_digest_stable(&mut bytes, &self.solved_module_digest);
        write_digest_stable(&mut bytes, &self.solved_executable_content_digest);
        write_digest_stable(&mut bytes, &self.solved_replay_context_digest);
        write_digest_stable(&mut bytes, &self.solved_bundle_digest);
        write_digest_stable(&mut bytes, &self.request_digest);
        write_digest_stable(&mut bytes, &self.evidence_bundle_digest);
        write_evidence_artifacts_stable(&mut bytes, &self.result_artifacts);
        ProofDigest::sha256_domain(NATIVE_COVERAGE_ATTESTATION_DIGEST_DOMAIN, &bytes)
    }
}

/// Why a bundle has no replay-context digest
/// ([`NativeVerificationBundle::coverage_replay_context_digest`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum NativeReplayContextUnavailable {
    /// The obligation table cannot be indexed (a duplicated function, block or
    /// proof id, a dangling site, a scope/site disagreement): an ambiguous
    /// context has no identity, and a consumer REFUSES rather than guess.
    Unindexable,
}

impl core::fmt::Display for NativeReplayContextUnavailable {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Unindexable => f.write_str("its obligation table cannot be indexed"),
        }
    }
}

/// A bundle's replay-context identity
/// ([`NativeVerificationBundle::coverage_replay_context_digest`]): the digest
/// a row cites, and whether a result may TRANSFER on it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NativeReplayContextDigest {
    /// Everything in the context a wire image binds: the whole bundle but its
    /// write-back allowlist. ALWAYS computed, so a row citing it is always
    /// checked — on the solved side against the citation, on the admitted
    /// side against the solved side — whatever else is undetermined.
    pub digest: ProofDigest,
    /// The first function carrying a clean-expr `ProofAnnotation::Goal`,
    /// which every binary writer excludes from the wire image and therefore
    /// from `digest`. `Some` means NOTHING transfers on `digest` (a replayer
    /// could read the Goal, and a different one would go unseen): a consumer
    /// leaves the result UNDETERMINED unless one of its checks refuses it —
    /// the digest comparisons among them, which a Goal neither causes nor
    /// excuses.
    pub unbound_goal: Option<FuncId>,
}

impl NativeReplayContextDigest {
    /// The digest a result may transfer on: `Ok(digest)` when no Goal lies
    /// outside it, else `Err` naming the function that carries one.
    pub fn transferable(self) -> Result<ProofDigest, FuncId> {
        match self.unbound_goal {
            None => Ok(self.digest),
            Some(function) => Err(function),
        }
    }
}

impl NativeVerificationBundle {
    /// SHA-256 identity of this bundle's REPLAY CONTEXT under
    /// [`NATIVE_COVERAGE_REPLAY_CONTEXT_DIGEST_DOMAIN`]: everything a
    /// [`NativeCoverageResultReplay`] may establish a result from, and nothing
    /// an honest certificate write-back rewrites.
    ///
    /// # The default is BOUND
    ///
    /// The image is the WHOLE bundle — [`Self::stable_digest`], over every
    /// bundle field, with the module by its wire identity
    /// ([`crate::Module::stable_digest`]: every function body, summary,
    /// attribute and proof annotation the writer encodes, every obligation's
    /// kind, formula, description, source, site and spec, every type, global,
    /// import, file table and spec module) — with ONLY the write-back
    /// allowlist below erased. The erasure destructures the bundle, the
    /// module, each function and each obligation with no `..`, so a field
    /// added to any of them is a compile error there until someone classifies
    /// it — and the classification that costs nothing is "bound".
    ///
    /// # The write-back allowlist (erased)
    ///
    /// * every obligation's `status`, the `proof_certificates` table and the
    ///   `obligation_diagnostics` sidecar — what a write-back records;
    /// * the carriers that bind the module digest, which a write-back moves:
    ///   `trust_ir_module_digest` (recomputed over the erased module), the
    ///   `lineage` manifest (its nodes name the module digest and the
    ///   certificates), and every request and evidence bundle (evidence binds
    ///   the module digest; the ONE request and evidence bundle a result cites
    ///   are bound by the attestation row's own digests).
    ///
    /// Everything else — the obligation table's claims, ids and order, every
    /// function field (its `body_gate` license and `display_path`, which the
    /// claim digest of an obligation scoped to the function binds already,
    /// and the summary's `proved` flag, which executable content binds
    /// already), the compiler facts, the adapter input, the producer and
    /// provenance, the serialization and diagnostics policies — is bound: a
    /// write-back that changes any of it moves this digest, and the consumer
    /// refuses the transfer (the safe direction).
    ///
    /// # A Goal outside the digest
    ///
    /// A clean-expr `Goal` is in no wire image, so it is outside the digest:
    /// the digest is still computed — a row cites it and a consumer checks
    /// it, and two contexts whose digests differ drifted outside their Goals
    /// — but [`NativeReplayContextDigest::unbound_goal`] names the function
    /// carrying one, and nothing transfers on such a context.
    ///
    /// # No digest
    ///
    /// `Err(`[`NativeReplayContextUnavailable::Unindexable`]`)` when the
    /// obligation table cannot be indexed. Like every module digest it PANICS
    /// on a module with no wire identity; probe
    /// `trust_ir_build::wire_identity_blocker` first. `fmt`-gated, because the
    /// indexability probe is.
    #[cfg(feature = "fmt")]
    pub fn coverage_replay_context_digest(
        &self,
    ) -> Result<NativeReplayContextDigest, NativeReplayContextUnavailable> {
        if self.module.obligation_digest_index().is_none() {
            return Err(NativeReplayContextUnavailable::Unindexable);
        }
        let erased = self.coverage_write_back_erased();
        let mut bytes = Vec::new();
        write_digest_stable(&mut bytes, &erased.stable_digest());
        Ok(NativeReplayContextDigest {
            digest: ProofDigest::sha256_domain(
                NATIVE_COVERAGE_REPLAY_CONTEXT_DIGEST_DOMAIN,
                &bytes,
            ),
            unbound_goal: first_unbound_goal(&self.module),
        })
    }
}

/// The first function carrying a clean-expr `ProofAnnotation::Goal` — on the
/// function or on any node of its body — which no binary writer encodes.
#[cfg(feature = "fmt")]
fn first_unbound_goal(module: &Module) -> Option<FuncId> {
    #[cfg(feature = "clean-expr")]
    {
        let is_goal = |annotation: &crate::proof::ProofAnnotation| {
            matches!(annotation, crate::proof::ProofAnnotation::Goal(_))
        };
        module
            .functions
            .iter()
            .find(|function| {
                function.proofs.iter().any(is_goal)
                    || function
                        .blocks
                        .iter()
                        .flat_map(|block| &block.body)
                        .any(|node| node.proofs.iter().any(is_goal))
            })
            .map(|function| function.id)
    }
    #[cfg(not(feature = "clean-expr"))]
    {
        // The variant does not exist in this build.
        let _ = module;
        None
    }
}

/// Erase EXACTLY the module half of the coverage write-back allowlist
/// ([`NativeVerificationBundle::coverage_replay_context_digest`]). Every
/// destructuring below lists every field with no `..`: a new field is a
/// compile error until it is classified, and `_` (bound) is the default.
#[cfg(feature = "fmt")]
pub(crate) fn erase_module_write_back_state(module: &mut Module) {
    let Module {
        name: _,
        functions,
        structs: _,
        enums: _,
        records: _,
        closure_types: _,
        globals: _,
        func_types: _,
        types: _,
        proof_obligations,
        proof_certificates,
        target_info: _,
        files: _,
        obligation_diagnostics,
        spec_modules: _,
        universes: _,
        predicates: _,
        global_asm: _,
        imports: _,
        tuple_layouts: _,
        completeness: _,
        drop_glue: _,
        closure_layouts: _,
        blobs: _,
    } = module;
    // ERASED: the certificate table and the diagnostics sidecar.
    proof_certificates.clear();
    obligation_diagnostics.clear();
    for obligation in proof_obligations.iter_mut() {
        let ProofObligation {
            id: _,
            kind: _,
            // ERASED: verification progress.
            status,
            description: _,
            formula: _,
            function: _,
            source: _,
            site: _,
            spec: _,
        } = obligation;
        *status = ProofStatus::Pending;
    }
    for function in functions.iter() {
        // Every function field is BOUND.
        let Function {
            id: _,
            name: _,
            ty: _,
            entry: _,
            blocks: _,
            proofs: _,
            calling_conv: _,
            linkage: _,
            attrs: _,
            summary: _,
            producer: _,
            value_names: _,
            scopes: _,
            source_provenance: _,
            body_gate: _,
            display_path: _,
            section: _,
            visibility: _,
            retained: _,
        } = function;
    }
}

/// How strong a result a [`NativeCoverageResultReplay`] implementation
/// independently RE-ESTABLISHED — the strength half of the bound
/// `trust_ir_build` derives (the other half is the request's own mode and
/// options, and the two must agree).
///
/// `#[non_exhaustive]`: a consumer's table over it needs a fail-closed
/// wildcard, so a strength added here derives no bound downstream until that
/// table names it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[non_exhaustive]
pub enum NativeReplayedStrength {
    /// A CHC "valid" verdict re-derived: the query is unreachable from every
    /// state, at every depth.
    ChcValidity,
    /// A PDR/IC3 inductive invariant re-validated against the Horn clauses.
    PdrInvariant,
    /// A weakest-precondition proof under a whole-heap frame re-derived.
    WeakestPreconditionFullHeap,
    /// A bounded model check re-derived to exactly `depth` unwindings. It
    /// attests the depth-bounded check only — NOT that any unwinding
    /// assertion was re-checked — so it never licenses completeness.
    BoundedUnwind { depth: u64 },
}

impl NativeReplayedStrength {
    /// Stable lowercase spelling for diagnostics and fingerprints.
    #[must_use]
    pub fn code(self) -> String {
        match self {
            Self::ChcValidity => "chc_validity".to_string(),
            Self::PdrInvariant => "pdr_invariant".to_string(),
            Self::WeakestPreconditionFullHeap => "weakest_precondition_full_heap".to_string(),
            Self::BoundedUnwind { depth } => format!("bounded_unwind:{depth}"),
        }
    }
}

/// What a replayer RE-ESTABLISHED for one cited result: the strength, the
/// obligations the re-derived result actually models (an obligation the
/// request lists but the result does not model is not covered by it), and
/// the PREMISES it rests on.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeReplayedResult {
    pub obligations: Vec<ProofId>,
    pub strength: NativeReplayedStrength,
    /// Every OTHER obligation whose claim the re-verified result ASSUMED
    /// without proving it — an assumed `Precondition`, a callee postcondition
    /// a call-site proof context lets the caller rely on, a `LoopInvariant`
    /// taken as given. The replay contract (clause 6) requires the list to be
    /// complete. The consumer establishes the result only when every premise
    /// is itself established `Unbounded` in the same report, with no cycle
    /// (an obligation listed as its own premise, directly or through others,
    /// never is), and refuses the bundle when a premise is `Failed`.
    #[cfg_attr(feature = "serde", serde(default))]
    pub premises: Vec<ProofId>,
}

impl NativeReplayedResult {
    /// A result that assumed no other obligation's claim.
    #[must_use]
    pub fn new(obligations: Vec<ProofId>, strength: NativeReplayedStrength) -> Self {
        Self {
            obligations,
            strength,
            premises: Vec::new(),
        }
    }

    /// The same result, resting on `premises`.
    #[must_use]
    pub fn assuming(mut self, premises: Vec<ProofId>) -> Self {
        self.premises = premises;
        self
    }
}

/// Why a replay could not decide, as opposed to finding the result wrong.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[non_exhaustive]
pub enum NativeCoverageReplayInconclusive {
    /// The replay ran out of its time or resource budget.
    Budget,
    /// The replayer does not support this result shape, mode or artifact.
    Unsupported,
    /// A cited obligation is not modeled by the re-translated problem.
    UnmodeledObligation,
    /// The solved bundle holds constructs whose meaning only a live source
    /// authority can vouch for (consumer replay is default-deny for them).
    SourceAuthorityOnly,
}

impl NativeCoverageReplayInconclusive {
    /// Stable lowercase spelling for diagnostics.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            Self::Budget => "budget",
            Self::Unsupported => "unsupported",
            Self::UnmodeledObligation => "unmodeled_obligation",
            Self::SourceAuthorityOnly => "source_authority_only",
        }
    }
}

/// A replay that did not re-establish a result.
///
/// The arms are NOT interchangeable, and the difference is the consumer's
/// verdict: [`Self::Invalid`] and [`Self::Refuted`] say a producer cited a
/// result that is wrong or that disproves what it claims (the whole bundle is
/// refused), while [`Self::Inconclusive`] says only that nothing was
/// established (the obligation stays undetermined). A replayer must never
/// report a wrong result as inconclusive.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum NativeCoverageReplayRefusal {
    /// The cited result was replayed and is WRONG: a Horn clause fails under
    /// the invariant model, the model does not parse strictly, the result is
    /// about another request, the bytes are not canonical, …
    Invalid { detail: String },
    /// The replay independently established a REFUTATION of `obligations`
    /// (a counterexample the replayer re-checked).
    Refuted {
        obligations: Vec<ProofId>,
        detail: String,
    },
    /// The replay could not decide.
    Inconclusive {
        reason: NativeCoverageReplayInconclusive,
        detail: String,
    },
}

/// The seam through which a consumer re-verifies a cited solver result
/// (basis R). Zero-dependency on purpose: `trust_ir` defines it, the verifier
/// that owns the result format implements it (trust-mc's
/// `NativeTrustIrCoverageReplayer`), and `trust_ir_build` calls it.
///
/// # Soundness contract (implementors MUST uphold)
///
/// `Ok(result)` only when, IN THIS PROCESS, the implementation has
///
/// 1. re-translated the problem freshly from `solved` and `request` — never
///    from a producer's cached translation;
/// 2. read the result ONLY from `attachments` (bytes whose digests the caller
///    has already matched against `evidence`'s descriptors) and parsed them
///    strictly;
/// 3. re-verified the result against the re-translated problem (for an
///    invariant model: every Horn clause holds; for a validity verdict: the
///    structural / acyclic re-derivation succeeds; for a bounded check: the
///    unwinding depth);
/// 4. listed in `result.obligations` only obligations the re-translated problem
///    actually models;
/// 5. established the result from the REPLAY CONTEXT alone (below), assuming
///    NOTHING the consumer does not bind and check;
/// 6. named in `result.premises` EVERY other obligation whose claim the result
///    assumed rather than proved.
///
/// Any failure to re-verify is [`NativeCoverageReplayRefusal::Invalid`] (the
/// result is wrong) or [`NativeCoverageReplayRefusal::Inconclusive`] (nothing
/// was decided) — never `Ok`. The implementation is part of the consumer's
/// trusted base: a stub that returns `Ok` without replaying must never be
/// linked into a release consumer, and a test double must say so in its name
/// and be `cfg(test)`-gated.
///
/// # The replay context: what `Ok` may depend on
///
/// `Ok` must be a function of ONLY
///
/// * `solved`'s replay context — exactly what
///   `NativeVerificationBundle::coverage_replay_context_digest` binds: the
///   whole bundle but its write-back allowlist (every function body, summary
///   and callee contract, every obligation's CLAIM, the compiler facts, …);
/// * `request`'s mode, typed options and listed obligations, and `evidence`
///   and `attachments` — each bound by digest by the caller.
///
/// Everything in the allowlist is write-back state and MUST NOT be a premise
/// of `Ok`: any obligation's `status` (a `Discharged` sibling is not a lemma),
/// the `proof_certificates` table (another obligation's certificate is not a
/// lemma either — nobody re-checks it here), the `obligation_diagnostics`
/// sidecar, and the bundle's lineage manifest, its other requests and its
/// other evidence bundles. An implementation MAY read
/// any of them to REFUSE (re-validating the whole solved bundle is expected);
/// it may ESTABLISH only from the context. The consumer requires the admitted
/// bundle to recompute the SAME context digest, so nothing the replay may use
/// can change between the solve and the admission.
///
/// # Premises: what a result may ASSUME
///
/// NOTHING the consumer does not bind and check:
///
/// * the request's `provenance.replay_context` atoms are NOT premises and NOT
///   goals. Each obligation's goal is its CLAIM in the context. The consumer
///   derives no bound from a request carrying an `Assumption` atom (or an
///   unsupported-mode entry), and REFUSES the bundle when an `Assertion` atom
///   does not state exactly the formula of the obligation it cites;
/// * another obligation's claim MAY be assumed — the context binds it, site
///   and all — but only when it is named in `result.premises`. The consumer
///   establishes the result only if every named premise is itself established
///   `Unbounded` in the same report (by a kernel-replayed certificate or by
///   another verified result), with no cycle, and REFUSES the bundle when a
///   named premise is `Failed` or is no obligation of the module. An unnamed
///   premise is a breach of this contract the consumer cannot detect: that is
///   why the replayer is trusted base.
pub trait NativeCoverageResultReplay {
    fn replay(
        &self,
        solved: &NativeVerificationBundle,
        request: &NativeVerificationRequest,
        evidence: &NativeEvidenceBundle,
        attachments: &[NativeEvidenceArtifactAttachment],
    ) -> Result<NativeReplayedResult, NativeCoverageReplayRefusal>;
}
