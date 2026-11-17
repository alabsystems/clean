// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The refusals of a `kernel-verified.json` reader (unit P6, slice 1 of
//! `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`; design
//! `designs/2026-11-16-p6-acceptance-identity.md`).

/// Why a `kernel-verified.json` manifest, or an operation on one, was refused.
///
/// Every reader goes through the validating deserializer, so a manifest that
/// names no theory or no checker, or names them inconsistently, never exists
/// in memory.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ManifestError {
    /// `schema_version` is not 2 (or absent). Schema 1 names neither the
    /// theory nor the checker; under P6 it is not evidence and is never
    /// upgraded, because inventing its identity would be the discarded draft.
    #[error(
        "schema_version {found} names no theory and no checker; under P6 it is not evidence \
         and no lane reads it. Re-run the producer that wrote it (`clean mathverse \
         stamp-verified ... --manifest`, `mathverse_shard verify-kernel --corpus \
         --emit-verified`, `mathverse_shard coq-import`, or the sharded driver) to write \
         schema 2; for a Coq baseline run `scripts/coq_refresh.sh --rebaseline`"
    )]
    UnsupportedSchema {
        /// The value found (`"absent"` when the key is missing).
        found: String,
    },
    /// A schema-2 manifest without its `identity` record.
    #[error("schema 2 manifest carries no `identity`: it names no theory and no checker")]
    NoIdentity,
    /// The theory and the checker entry cannot belong together.
    #[error("forged identity: {0}")]
    ForgedIdentity(&'static str),
    /// A reference-theory identity. No producer in this build writes one
    /// (slice 1b lands the reference producer and its reader together).
    #[error(
        "reference-tier identity: no reference producer exists in this build, so no reader \
         accepts one (P6 slice 1b lands the producer, the receipt checks and the reader together)"
    )]
    NoReferenceProducer,
    /// The stored tier is not the tier the theory and the checker derive.
    #[error("stored tier `{stored}` is not the derived tier `{derived}`")]
    TierMismatch {
        /// The tier the file states.
        stored: &'static str,
        /// The tier its theory and checker derive.
        derived: &'static str,
    },
    /// The stored discipline is not the one the profile derives.
    #[error("stored discipline `{stored}` is not `{derived}`, the discipline its profile derives")]
    DisciplineMismatch {
        /// The discipline the file states.
        stored: &'static str,
        /// The discipline its theory profile derives.
        derived: &'static str,
    },
    /// `accepted` is not the number of `accepted_names`, or a name repeats.
    #[error("accepted count {count} does not match the {names} distinct accepted names")]
    CountMismatch {
        /// The stated count.
        count: usize,
        /// The number of distinct names.
        names: usize,
    },
    /// A field has the wrong shape (a digest that is not hex, a parse error).
    #[error("malformed manifest: {0}")]
    Malformed(String),
    /// A development manifest was offered where a grant needs a reference
    /// acceptance (P2 clause 1: a development check confers no kernel label).
    #[error(
        "development-tier manifest confers no label: {purpose} needs a reference acceptance \
         (P2 clause 1), and no reference producer exists in this build"
    )]
    DevelopmentTier {
        /// What the caller wanted to do with it.
        purpose: &'static str,
    },
    /// Two manifests that must come from one checker (or one build) do not.
    #[error("identity mismatch: {0}")]
    IdentityMismatch(String),
    /// A merge was asked to merge nothing.
    #[error("nothing to merge: a consolidated manifest needs at least one sidecar")]
    EmptyMerge,
    /// The running executable could not be hashed, so no identity can be
    /// written for this process.
    #[error("cannot capture the executable identity: {0}")]
    ExecutableUnreadable(String),
    /// A kernel setting this schema has no name for.
    #[error("unnamed kernel setting: {0}")]
    UnnamedSetting(String),
}
