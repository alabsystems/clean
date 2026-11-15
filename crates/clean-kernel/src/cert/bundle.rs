// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof certificate bundles for downstream consumption.
//!
//! A `.cleancert` file packages proof certificates for a complete Lean project
//! into a single distributable artifact. Downstream tools (LLVM2, tRust) can
//! verify the bundle using only `clean-kernel` -- no elaborator, no tactic
//! engine, no parser.
//!
//! # Bundle Format
//!
//! A `.cleancert` bundle is a zstd-compressed bincode archive containing:
//! - A [`CertBundleManifest`] with per-theorem entries
//! - Per-theorem [`ProofCert`] binaries
//! - Per-theorem [`CrossProjectCert`] records
//! - A serialized [`Environment`] snapshot for verification
//! - A [`ProofArchiveMetadata`] trust chain
//!
//! # Usage
//!
//! ```text
//! use clean_kernel::cert::bundle::CertBundle;
//!
//! let bundle = CertBundle::load("tmir-proofs.cleancert")?;
//! let result = bundle.verify_all()?;
//! assert!(result.all_passed());
//! assert!(bundle.has_theorem("TMir.dce_pure_inst"));
//! ```

use std::collections::{HashMap, HashSet};
use std::io::{Read, Write};
use std::path::Path;

use serde::{Deserialize, Serialize};

use crate::env::{CertificationAudit, CertificationIssue, ConstantKind, Environment};
use crate::name::Name;

use super::bundle_recheck::{
    rebuild_from_canonical_base, BundleEnvironmentRecheck, RebuiltEnvironment,
};
use super::compression::limits::{
    decode_bincode_limited, decode_certificate_bincode_limited, read_unknown_bounded,
    MAX_COMPRESSED_ARCHIVE_BYTES, MAX_STREAM_CERT_BYTES, MAX_UNCOMPRESSED_ARCHIVE_BYTES,
};
use super::cross_project::CrossProjectCert;
use super::metadata::{ProofArchiveMetadata, TrustLevel};
use super::types::ProofCert;
use super::CertVerifier;

/// Current bundle format version.
const BUNDLE_VERSION: u32 = 1;

/// Magic bytes at the start of a `.cleancert` file.
const BUNDLE_MAGIC: &[u8; 8] = b"L5CERT\x00\x01";

/// Maximum theorem/certificate entries in one bundle.
const MAX_BUNDLE_ENTRIES: usize = 1_000_000;

/// Maximum serialized environment payload in one bundle.
const MAX_BUNDLE_ENV_BYTES: usize = 256 * 1024 * 1024;

/// Maximum UTF-8 bytes in one serialized theorem-map key.
const MAX_BUNDLE_NAME_BYTES: usize = 16 * 1024;

// ────────────────────────────────────────────────────────────────────────────
// Error type
// ────────────────────────────────────────────────────────────────────────────

/// Errors from bundle creation, loading, or verification.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum CertBundleError {
    /// IO error reading or writing a bundle file.
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    /// Bincode serialization/deserialization failure.
    #[error("serialization error: {0}")]
    Serialization(String),

    /// Zstd compression/decompression failure.
    #[error("compression error: {0}")]
    Compression(String),

    /// The file does not start with the expected magic bytes.
    #[error("invalid bundle: bad magic bytes")]
    InvalidMagic,

    /// Bundle version is not supported.
    #[error("unsupported bundle version: {0}")]
    UnsupportedVersion(u32),

    /// A theorem referenced in the manifest is missing from the bundle data.
    #[error("theorem '{0}' listed in manifest but missing from bundle")]
    MissingTheorem(String),

    /// Certificate verification failed for a specific theorem.
    #[error("verification failed for theorem '{name}': {reason}")]
    VerificationFailed {
        /// Theorem that failed verification.
        name: String,
        /// Reason for the failure.
        reason: String,
    },

    /// Environment hash does not match the manifest.
    #[error("environment hash mismatch: expected {expected}, got {actual}")]
    EnvHashMismatch {
        /// Hash recorded in the manifest.
        expected: String,
        /// Hash of the deserialized environment.
        actual: String,
    },

    /// Bundle input exceeds a fail-closed resource or structural limit.
    #[error("bundle resource limit: {0}")]
    ResourceLimit(String),

    /// Bundle manifest/content metadata is internally inconsistent.
    #[error("invalid bundle manifest: {0}")]
    InvalidManifest(String),
}

// ────────────────────────────────────────────────────────────────────────────
// Manifest types
// ────────────────────────────────────────────────────────────────────────────

/// Per-theorem entry in the bundle manifest.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct CertBundleEntry {
    /// Fully qualified theorem name.
    pub name: String,
    /// SHA-256 hash of the theorem type expression.
    pub type_hash: String,
    /// SHA-256 hash of the proof term.
    pub proof_hash: String,
    /// Trust level of this theorem.
    pub trust_level: TrustLevel,
    /// Whether the theorem is free of `sorry` axioms.
    pub sorry_free: bool,
}

/// Bundle manifest embedded in `.cleancert` archives.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct CertBundleManifest {
    /// Bundle format version.
    pub version: u32,
    /// Source project name.
    pub project: String,
    /// clean version that produced the bundle.
    pub clean_version: String,
    /// SHA-256 hash of the serialized environment snapshot.
    pub env_hash: String,
    /// Per-theorem entries.
    pub theorems: Vec<CertBundleEntry>,
    /// Overall trust level (minimum of all theorems).
    pub trust_level: TrustLevel,
}

// ────────────────────────────────────────────────────────────────────────────
// Inspection report
// ────────────────────────────────────────────────────────────────────────────

/// Structural issue surfaced by [`CertBundle::inspect`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum BundleInspectIssue {
    /// The theorem is listed in the manifest but has no embedded certificate.
    MissingCertificate,
    /// The theorem is marked kernel-verified but has no cross-project certificate.
    MissingCrossProjectCertificate,
    /// The theorem is listed in the manifest but missing from the environment snapshot.
    MissingEnvironmentDeclaration,
    /// The theorem exists in the environment snapshot but has no proof term/value.
    MissingProofTerm,
}

impl BundleInspectIssue {
    /// Stable machine-readable label for CLI and JSON output.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::MissingCertificate => "missing-certificate",
            Self::MissingCrossProjectCertificate => "missing-cross-project-certificate",
            Self::MissingEnvironmentDeclaration => "missing-environment-declaration",
            Self::MissingProofTerm => "missing-proof-term",
        }
    }
}

/// Per-theorem inspection metadata for a bundle entry.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct BundleInspectEntry {
    /// Fully qualified theorem name.
    pub name: String,
    /// Trust level recorded in the manifest.
    pub trust_level: TrustLevel,
    /// Whether the theorem is marked `sorry`-free in the manifest.
    pub sorry_free: bool,
    /// The theorem type recovered from the embedded environment, if any.
    pub theorem_type: Option<String>,
    /// The declaration kind found in the environment snapshot.
    pub declaration_kind: Option<&'static str>,
    /// Whether the theorem has an embedded certificate in the bundle.
    pub has_certificate: bool,
    /// Whether the theorem is present in the environment snapshot.
    pub has_environment_declaration: bool,
    /// Whether the environment declaration includes a proof term/value.
    pub has_proof_term: bool,
    /// Whether a cross-project certificate is present for the theorem.
    pub has_cross_project_certificate: bool,
    /// Type hash from the manifest, if available.
    pub type_hash: Option<String>,
    /// Proof hash from the manifest, if available.
    pub proof_hash: Option<String>,
    /// Structural problems detected while inspecting the bundle.
    pub issues: Vec<BundleInspectIssue>,
}

impl BundleInspectEntry {
    /// True when the theorem is ready for replay verification.
    #[must_use]
    pub fn is_ready(&self) -> bool {
        self.issues.is_empty()
    }
}

/// Aggregate inspection report for a `.cleancert` bundle.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct BundleInspectReport {
    /// Number of theorems listed in the manifest.
    pub theorem_count: usize,
    /// Number of theorems with certificate + environment declaration + proof term.
    pub ready_count: usize,
    /// Number of theorems with at least one structural issue.
    pub incomplete_count: usize,
    /// Per-theorem inspection entries in manifest order.
    pub entries: Vec<BundleInspectEntry>,
}

// ────────────────────────────────────────────────────────────────────────────
// Verification result
// ────────────────────────────────────────────────────────────────────────────

/// Result of verifying all certificates in a bundle.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct BundleVerifyResult {
    /// Number of theorems that passed verification.
    pub passed: usize,
    /// Number of theorems that failed verification.
    pub failed: usize,
    /// Per-theorem failure reasons (empty if all passed).
    pub failures: Vec<(String, String)>,
    /// Overall trust level from the manifest.
    pub trust_level: TrustLevel,
    /// The `Axiom`-kind declarations of the bundle's environment, each
    /// theorem's axioms, and the declarations each theorem rests on that the
    /// kernel did not re-derive — disclosed whatever the verdict
    /// ([`BundleAxiomDisclosure`]).
    pub axioms: BundleAxiomDisclosure,
    /// What re-deriving the bundle's environment from the canonical base found
    /// ([`super::bundle_recheck`]). Every replay counted above ran in the
    /// rebuilt environment, never in the bundle's own.
    pub environment: BundleEnvironmentRecheck,
}

/// What a bundle's replay verdicts assume: the `Axiom`-kind declarations its
/// embedded environment holds (partitioned), the axioms each manifest
/// theorem's constant closure reaches, and every declaration a theorem's
/// closure reaches that the kernel did NOT re-derive from the canonical base.
///
/// A replay verdict is relative to the environment it replays in, and a bundle
/// author chooses that environment: `axiom proofIrrel : False` then a theorem
/// citing it replays perfectly. So every verify and stats report discloses
/// the environment's axioms, and verification FAILS when a declaration uses a
/// reserved ambient name (a foundational axiom's or a trust marker's,
/// structurally or by printed form) without being the kernel's canonical
/// declaration of it ([`Environment::non_canonical_ambient_declarations`]).
///
/// **What "axiom" means here, exactly.** Only `Axiom`-kind declarations are
/// listed as axioms. That is not every assumption a bundle can smuggle in: a
/// `Theorem`-kind `fakeFalse : False := True.intro` inserted without a kernel
/// check is an assumption in all but kind, and before 2026-09-28 this type
/// claimed to list "every axiom" while a theorem resting on such a declaration
/// verified with nothing listed. The axiom lists are the complete account of
/// what a PASSING theorem assumes beyond the canonical foundations only
/// because verification re-derives every other declaration of the bundle
/// environment from the canonical base ([`super::bundle_recheck`]) and fails
/// a theorem whose closure reaches one it could not re-derive; those are
/// listed in [`Self::theorem_unchecked_dependencies`], which is therefore
/// empty for every theorem that passes. The canonical foundations (the
/// quotient primitives among them, which are `Axiom`-kind) are listed but
/// never counted as a theorem's assumptions. A closure is the set of constants
/// reachable through declaration types and values.
///
/// Names are rendered with [`Name::to_unambiguous_string`], so a one-component
/// `«Quot.sound»` never reads as the kernel's `Quot.sound`, and an invisible
/// or non-ASCII character is shown as an escape.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct BundleAxiomDisclosure {
    /// The kernel's canonical foundational axioms present (structural name AND
    /// exact canonical statement).
    pub canonical_foundations: Vec<String>,
    /// Trust markers (`sorry`, `sorryAx`, `trustedArith`, `trustedAy`) present
    /// as axioms.
    pub trust_markers: Vec<String>,
    /// Every other axiom: an assumption the kernel does not own.
    pub other_axioms: Vec<String>,
    /// Declarations of any kind under a reserved ambient name that are NOT the
    /// kernel's canonical declaration, each with the reason. Non-empty fails
    /// verification.
    pub non_canonical_ambient: Vec<(String, String)>,
    /// Per manifest theorem (manifest order): every `Axiom`-kind declaration
    /// in its constant closure that is not a canonical foundation — domain
    /// axioms and trust markers alike.
    pub theorem_assumptions: Vec<(String, Vec<String>)>,
    /// Per manifest theorem (manifest order): every declaration in its
    /// constant closure (itself included) that the kernel did not re-derive
    /// from the canonical base — refused, or resting on one that was. Any
    /// entry fails the theorem. Empty for a theorem that passes.
    pub theorem_unchecked_dependencies: Vec<(String, Vec<String>)>,
}

impl BundleAxiomDisclosure {
    /// Compute the disclosure for the bundle environment `env`, the manifest
    /// theorem names, and the outcome of re-deriving `env` from the canonical
    /// base (`Err` when the base itself could not be built: then nothing was
    /// re-derived, and every theorem says so).
    #[must_use]
    pub(crate) fn of_bundle(
        env: &Environment,
        theorems: &[String],
        rebuilt: Result<&RebuiltEnvironment, &str>,
    ) -> Self {
        let mut out = Self::default();
        for info in env.constants() {
            if info.kind != ConstantKind::Axiom {
                continue;
            }
            let rendered = info.name.to_unambiguous_string();
            if crate::env::is_canonical_foundational_constant(info) {
                out.canonical_foundations.push(rendered);
            } else if crate::env::is_trust_marker(&info.name) {
                out.trust_markers.push(rendered);
            } else {
                out.other_axioms.push(rendered);
            }
        }
        out.canonical_foundations.sort();
        out.trust_markers.sort();
        out.other_axioms.sort();
        out.non_canonical_ambient = env
            .non_canonical_ambient_declarations()
            .into_iter()
            .map(|(name, detail)| (name.to_unambiguous_string(), detail))
            .collect();
        let mut closure = crate::env::DomainAxiomClosure::new();
        out.theorem_assumptions = theorems
            .iter()
            .map(|theorem| {
                let name = Name::from_string(theorem);
                let mut assumed: Vec<String> = closure
                    .assumptions_of_name(env, &name)
                    .iter()
                    .filter(|axiom| !env.is_canonical_foundational_axiom(axiom))
                    .map(Name::to_unambiguous_string)
                    .collect();
                assumed.sort();
                (theorem.clone(), assumed)
            })
            .collect();
        out.theorem_unchecked_dependencies = theorems
            .iter()
            .map(|theorem| {
                let unchecked = match rebuilt {
                    Ok(rebuilt) => rebuilt
                        .unchecked_in_closure(env, &Name::from_string(theorem))
                        .into_iter()
                        .map(|(name, _)| name.to_unambiguous_string())
                        .collect(),
                    Err(reason) => vec![format!("[nothing re-derived: {reason}]")],
                };
                (theorem.clone(), unchecked)
            })
            .collect();
        out
    }

    /// Every axiom in the environment that is not a canonical foundation.
    #[must_use]
    pub fn assumption_count(&self) -> usize {
        self.trust_markers.len() + self.other_axioms.len()
    }

    /// The verification failure a non-canonical ambient declaration forces,
    /// or `None` for an environment whose reserved names are all the kernel's.
    #[must_use]
    pub fn ambient_failure(&self) -> Option<String> {
        if self.non_canonical_ambient.is_empty() {
            return None;
        }
        let listed: Vec<String> = self
            .non_canonical_ambient
            .iter()
            .map(|(name, detail)| format!("`{name}`: {detail}"))
            .collect();
        Some(format!(
            "the bundle environment declares a reserved kernel name without the kernel's \
             canonical declaration: {}",
            listed.join("; ")
        ))
    }
}

impl BundleVerifyResult {
    /// True if every theorem in the bundle passed verification.
    #[must_use]
    pub fn all_passed(&self) -> bool {
        self.failed == 0
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Internal serializable archive
// ────────────────────────────────────────────────────────────────────────────

/// The serializable payload inside a `.cleancert` file (after decompression).
#[derive(Serialize, Deserialize)]
struct BundleArchive {
    manifest: CertBundleManifest,
    env_bytes: Vec<u8>,
    certs: HashMap<String, Vec<u8>>,
    xproj_certs: HashMap<String, Vec<u8>>,
    trust_chain: Option<ProofArchiveMetadata>,
}

// ────────────────────────────────────────────────────────────────────────────
// CertBundle
// ────────────────────────────────────────────────────────────────────────────

/// A loadable proof certificate bundle.
///
/// Bundles package per-theorem [`ProofCert`] binaries and
/// [`CrossProjectCert`] records together with a minimal [`Environment`]
/// snapshot so downstream tools can verify theorems using only the kernel.
pub struct CertBundle {
    manifest: CertBundleManifest,
    env: Environment,
    certs: HashMap<Name, ProofCert>,
    xproj_certs: HashMap<Name, CrossProjectCert>,
    trust_chain: Option<ProofArchiveMetadata>,
    /// `env` re-derived from the canonical base, computed on first use.
    /// `env` is never mutated after construction, so one rebuild serves every
    /// verification of this bundle.
    rebuilt: std::sync::OnceLock<Result<RebuiltEnvironment, String>>,
}

impl std::fmt::Debug for CertBundle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CertBundle")
            .field("project", &self.manifest.project)
            .field("theorem_count", &self.certs.len())
            .field("trust_level", &self.manifest.trust_level)
            .finish_non_exhaustive()
    }
}

impl CertBundle {
    // ── Construction ──────────────────────────────────────────────────────

    /// Build a new bundle from constituent parts.
    ///
    /// The caller provides the environment, per-theorem certificates, and
    /// cross-project certificates. The builder computes hashes and assembles
    /// the manifest.
    pub fn build(
        project: &str,
        clean_version: &str,
        env: Environment,
        certs: HashMap<Name, ProofCert>,
        xproj_certs: HashMap<Name, CrossProjectCert>,
        trust_chain: Option<ProofArchiveMetadata>,
    ) -> Result<Self, CertBundleError> {
        validate_trust_chain_metadata(trust_chain.as_ref())?;
        let env_bytes = bincode::serde::encode_to_vec(&env, bincode::config::standard())
            .map_err(|e| CertBundleError::Serialization(e.to_string()))?;
        let env_hash = sha256_hex(&env_bytes);

        let cert_names: HashSet<&Name> = certs.keys().collect();
        for name in xproj_certs.keys() {
            if !cert_names.contains(name) {
                return Err(CertBundleError::InvalidManifest(format!(
                    "cross-project certificate '{}' has no scoped proof certificate",
                    name
                )));
            }
        }

        let mut names: Vec<&Name> = certs.keys().collect();
        names.sort_by_key(|name| name.to_string());
        let mut entries = Vec::with_capacity(certs.len());

        for name in names {
            let canonical = name.to_string();
            ensure_canonical_bundle_name(&canonical)?;
            let (type_hash, proof_hash, sorry_free) = declaration_metadata(&env, name, &canonical)?;
            let xproj = xproj_certs.get(name);
            if let Some(xproj) = xproj {
                validate_cross_project_metadata(&canonical, &type_hash, &proof_hash, xproj, &env)?;
            }
            entries.push(CertBundleEntry {
                name: canonical,
                type_hash,
                proof_hash,
                // A serialized manifest is a claim, not replay evidence.  In
                // particular, CrossProjectCert is self-authored transport
                // metadata and cannot establish kernel authority on its own.
                trust_level: TrustLevel::Unverified,
                sorry_free,
            });
        }

        let min_trust = aggregate_trust(&entries);
        let manifest = CertBundleManifest {
            version: BUNDLE_VERSION,
            project: project.to_string(),
            clean_version: clean_version.to_string(),
            env_hash,
            theorems: entries,
            trust_level: min_trust,
        };

        let bundle = Self {
            manifest,
            env,
            certs,
            xproj_certs,
            trust_chain,
            rebuilt: std::sync::OnceLock::new(),
        };
        validate_bundle_contents(
            &bundle.manifest,
            &bundle.env,
            &bundle.certs,
            &bundle.xproj_certs,
        )?;
        // The trust constructor never packages an environment in which a
        // reserved kernel name denotes anything but the kernel's declaration.
        if let Some(reason) = bundle.axiom_disclosure().ambient_failure() {
            return Err(CertBundleError::InvalidManifest(reason));
        }
        bundle.ensure_all_replay_valid()?;
        Ok(bundle)
    }

    /// Assemble a **non-authoritative** bundle view for readiness diagnostics.
    ///
    /// [`Self::build`] is the *trust* constructor: it refuses to mint a
    /// manifest entry for a theorem with no replayable proof term, because a
    /// manifest entry is a claim of proof authority and an assumed theorem has
    /// none. Readiness diagnostics need the opposite capability — they must be
    /// able to *represent* the deficient state in order to report it, which is
    /// the whole point of [`BundleInspectIssue::MissingProofTerm`].
    ///
    /// Everything produced here is quarantined:
    ///
    /// * every entry, and the aggregate, is pinned to
    ///   [`TrustLevel::Unverified`], so an assumed theorem can never be
    ///   rendered as proved or certified;
    /// * `proof_hash` stays empty when there is no proof term, so no hash is
    ///   ever fabricated for material that does not exist;
    /// * [`Self::save`], [`Self::verify_all`] and [`Self::verify_theorem`]
    ///   re-run the full trust validation and therefore still reject it.
    ///
    /// The supported operation on the result is [`Self::inspect`].
    pub fn for_inspection(
        project: &str,
        clean_version: &str,
        env: Environment,
        certs: HashMap<Name, ProofCert>,
        xproj_certs: HashMap<Name, CrossProjectCert>,
    ) -> Result<Self, CertBundleError> {
        if certs.len() > MAX_BUNDLE_ENTRIES || xproj_certs.len() > MAX_BUNDLE_ENTRIES {
            return Err(CertBundleError::ResourceLimit(
                "bundle entry count exceeds maximum".to_string(),
            ));
        }
        let env_bytes = bincode::serde::encode_to_vec(&env, bincode::config::standard())
            .map_err(|e| CertBundleError::Serialization(e.to_string()))?;
        let env_hash = sha256_hex(&env_bytes);

        let mut names: Vec<&Name> = certs.keys().collect();
        names.sort_by_key(|name| name.to_string());
        let mut entries = Vec::with_capacity(certs.len());
        for name in names {
            let (type_hash, proof_hash, sorry_free) = diagnostic_declaration_metadata(&env, name)?;
            entries.push(CertBundleEntry {
                name: name.to_string(),
                type_hash,
                proof_hash,
                // Nothing in a diagnostics view has been replayed, so nothing
                // in it carries authority.
                trust_level: TrustLevel::Unverified,
                sorry_free,
            });
        }

        Ok(Self {
            manifest: CertBundleManifest {
                version: BUNDLE_VERSION,
                project: project.to_string(),
                clean_version: clean_version.to_string(),
                env_hash,
                theorems: entries,
                trust_level: TrustLevel::Unverified,
            },
            env,
            certs,
            xproj_certs,
            trust_chain: None,
            rebuilt: std::sync::OnceLock::new(),
        })
    }

    // ── Persistence ──────────────────────────────────────────────────────

    /// Save the bundle to a `.cleancert` file.
    // Trust: file I/O + `bincode` serialization, NOT proof-soundness TCB. The
    // refuted assertions are panic paths inside the opaque `bincode` dependency;
    // scoped out of MIR verification (serialization correctness is not what the
    // kernel's soundness rests on).
    #[cfg_attr(trust_verify, trust::skip)]
    pub fn save(&self, path: impl AsRef<Path>) -> Result<(), CertBundleError> {
        validate_bundle_contents(&self.manifest, &self.env, &self.certs, &self.xproj_certs)?;
        self.ensure_all_replay_valid()?;
        self.write_archive(path)
    }

    /// Serialize and write the archive, validating nothing. [`Self::save`] is
    /// the only production caller, after its validation; tests use it to write
    /// the hand-made files an attacker would.
    // Trust: file I/O + `bincode` serialization, as `save`.
    #[cfg_attr(trust_verify, trust::skip)]
    fn write_archive(&self, path: impl AsRef<Path>) -> Result<(), CertBundleError> {
        let env_bytes = bincode::serde::encode_to_vec(&self.env, bincode::config::standard())
            .map_err(|e| CertBundleError::Serialization(e.to_string()))?;

        let mut cert_map = HashMap::with_capacity(self.certs.len());
        for (name, cert) in &self.certs {
            let bytes = bincode::serde::encode_to_vec(cert, bincode::config::standard())
                .map_err(|e| CertBundleError::Serialization(e.to_string()))?;
            cert_map.insert(name.to_string(), bytes);
        }

        let mut xproj_map = HashMap::with_capacity(self.xproj_certs.len());
        for (name, xproj) in &self.xproj_certs {
            let bytes = bincode::serde::encode_to_vec(xproj, bincode::config::standard())
                .map_err(|e| CertBundleError::Serialization(e.to_string()))?;
            xproj_map.insert(name.to_string(), bytes);
        }

        let archive = BundleArchive {
            manifest: self.manifest.clone(),
            env_bytes,
            certs: cert_map,
            xproj_certs: xproj_map,
            trust_chain: self.trust_chain.clone(),
        };
        validate_bundle_archive(&archive)?;

        let uncompressed = bincode::serde::encode_to_vec(&archive, bincode::config::standard())
            .map_err(|e| CertBundleError::Serialization(e.to_string()))?;
        if uncompressed.len() > MAX_UNCOMPRESSED_ARCHIVE_BYTES {
            return Err(CertBundleError::ResourceLimit(format!(
                "uncompressed bundle size {} exceeds maximum {MAX_UNCOMPRESSED_ARCHIVE_BYTES}",
                uncompressed.len()
            )));
        }

        let compressed = zstd::encode_all(uncompressed.as_slice(), 3)
            .map_err(|e| CertBundleError::Compression(e.to_string()))?;
        if compressed.len() > MAX_COMPRESSED_ARCHIVE_BYTES {
            return Err(CertBundleError::ResourceLimit(format!(
                "compressed bundle size {} exceeds maximum {MAX_COMPRESSED_ARCHIVE_BYTES}",
                compressed.len()
            )));
        }

        let mut file = std::fs::File::create(path)?;
        file.write_all(BUNDLE_MAGIC)?;
        file.write_all(&compressed)?;
        file.flush()?;

        Ok(())
    }

    /// Load a bundle from a `.cleancert` file.
    ///
    /// Fails closed: the manifest must agree with the embedded environment and
    /// every certificate must replay. Use [`Self::load_for_inspection`] when
    /// the goal is to diagnose a file this rejects.
    pub fn load(path: impl AsRef<Path>) -> Result<Self, CertBundleError> {
        let bundle = Self::decode_archive_file(path)?;
        validate_bundle_contents(
            &bundle.manifest,
            &bundle.env,
            &bundle.certs,
            &bundle.xproj_certs,
        )?;
        bundle.ensure_all_replay_valid()?;
        Ok(bundle)
    }

    /// Load a `.cleancert` file for **readiness diagnostics only**.
    ///
    /// This performs the same structural decoding as [`Self::load`] — magic,
    /// resource limits, archive shape, environment hash — but deliberately
    /// skips the manifest/environment agreement and certificate replay checks,
    /// so a file that `load` rejects can still be described to the user by
    /// [`Self::inspect`] instead of collapsing into a single opaque error.
    ///
    /// The result is quarantined: every recorded trust claim is overwritten
    /// with [`TrustLevel::Unverified`], because nothing here has been replayed.
    /// A forged manifest asserting [`TrustLevel::KernelVerified`] for an
    /// assumed theorem is therefore reported as unverified and incomplete,
    /// never as certified.
    pub fn load_for_inspection(path: impl AsRef<Path>) -> Result<Self, CertBundleError> {
        let mut bundle = Self::decode_archive_file(path)?;
        bundle.quarantine_trust_claims();
        Ok(bundle)
    }

    /// Structural decode shared by [`Self::load`] and
    /// [`Self::load_for_inspection`]. Performs no trust validation.
    fn decode_archive_file(path: impl AsRef<Path>) -> Result<Self, CertBundleError> {
        let file = std::fs::File::open(path)?;
        let raw = read_unknown_bounded(
            file,
            MAX_COMPRESSED_ARCHIVE_BYTES + BUNDLE_MAGIC.len(),
            "certificate bundle file",
        )
        .map_err(CertBundleError::ResourceLimit)?;

        if raw.len() < BUNDLE_MAGIC.len() || &raw[..BUNDLE_MAGIC.len()] != BUNDLE_MAGIC {
            return Err(CertBundleError::InvalidMagic);
        }

        let compressed = &raw[BUNDLE_MAGIC.len()..];
        let mut decoder = zstd::stream::Decoder::new(std::io::Cursor::new(compressed))
            .map_err(|e| CertBundleError::Compression(e.to_string()))?
            .single_frame();
        let decompressed = read_unknown_bounded(
            &mut decoder,
            MAX_UNCOMPRESSED_ARCHIVE_BYTES,
            "certificate bundle payload",
        )
        .map_err(CertBundleError::ResourceLimit)?;
        let mut trailing = [0_u8; 1];
        if decoder
            .get_mut()
            .read(&mut trailing)
            .map_err(CertBundleError::Io)?
            != 0
        {
            return Err(CertBundleError::Compression(
                "trailing bytes after bundle zstd frame".to_string(),
            ));
        }

        let archive: BundleArchive =
            decode_bincode_limited(&decompressed).map_err(CertBundleError::Serialization)?;
        validate_bundle_archive(&archive)?;

        if archive.manifest.version != BUNDLE_VERSION {
            return Err(CertBundleError::UnsupportedVersion(
                archive.manifest.version,
            ));
        }

        // Verify environment hash.
        let actual_env_hash = sha256_hex(&archive.env_bytes);
        if actual_env_hash != archive.manifest.env_hash {
            return Err(CertBundleError::EnvHashMismatch {
                expected: archive.manifest.env_hash.clone(),
                actual: actual_env_hash,
            });
        }

        let env: Environment =
            decode_bincode_limited(&archive.env_bytes).map_err(CertBundleError::Serialization)?;

        let mut certs = HashMap::with_capacity(archive.certs.len());
        for (name_str, bytes) in &archive.certs {
            let cert: ProofCert = decode_certificate_bincode_limited(bytes)
                .map_err(CertBundleError::Serialization)?;
            certs.insert(Name::from_string(name_str), cert);
        }

        let mut xproj_certs = HashMap::with_capacity(archive.xproj_certs.len());
        for (name_str, bytes) in &archive.xproj_certs {
            let xproj: CrossProjectCert =
                decode_bincode_limited(bytes).map_err(CertBundleError::Serialization)?;
            xproj_certs.insert(Name::from_string(name_str), xproj);
        }

        Ok(Self {
            manifest: archive.manifest,
            env,
            certs,
            xproj_certs,
            trust_chain: archive.trust_chain,
            rebuilt: std::sync::OnceLock::new(),
        })
    }

    /// Strip every recorded trust claim from a bundle that has not been
    /// replay-validated. Serialized trust is a claim, never evidence.
    ///
    /// The digests go with the trust level, and for the same reason. A
    /// quarantined read validates nothing, so `type_hash` and `proof_hash` are
    /// just two more attacker-chosen strings in the file — and unlike
    /// `trust_level` they *look* like evidence, which is worse: a forged
    /// bundle could otherwise render a 64-hex `proof_hash` directly beside
    /// `has_proof_term: false`, inviting a reader to believe some proof was
    /// hashed. Clearing them costs nothing, because every fact the inspect
    /// report actually asserts — `declaration_kind`, `theorem_type`,
    /// `has_proof_term`, `MissingProofTerm` — is derived from the EMBEDDED
    /// ENVIRONMENT DECLARATION rather than the manifest (see
    /// [`Self::inspect_manifest_entry`]), and `inspect` renders an empty digest
    /// as `None`. This is the same discipline [`Self::for_inspection`] already
    /// applies in memory, where `proof_hash` is left empty rather than
    /// fabricated when a declaration has no proof term.
    fn quarantine_trust_claims(&mut self) {
        for entry in &mut self.manifest.theorems {
            entry.trust_level = TrustLevel::Unverified;
            entry.type_hash.clear();
            entry.proof_hash.clear();
        }
        self.manifest.trust_level = TrustLevel::Unverified;
    }

    // ── Verification ─────────────────────────────────────────────────────

    /// Verify all certificates in the bundle against the embedded environment.
    ///
    /// Fails closed on a structurally invalid bundle: [`validate_bundle_contents`]
    /// runs first, so a manifest entry that is not a well-formed claim of proof
    /// authority (for example a theorem with no proof term) is rejected outright
    /// rather than replayed. Use [`Self::verify_all_for_inspection`] when the
    /// goal is to *describe* a bundle this refuses.
    pub fn verify_all(&self) -> Result<BundleVerifyResult, CertBundleError> {
        validate_bundle_contents(&self.manifest, &self.env, &self.certs, &self.xproj_certs)?;
        Ok(self.replay_every_manifest_entry())
    }

    /// Replay every manifest entry and report the outcome, for **readiness
    /// diagnostics only**.
    ///
    /// [`Self::verify_all`] is the trust verb, and its up-front structural gate
    /// is the point of it: an entry claiming proof authority for a theorem with
    /// no proof term is refused, not verified. That refusal stays. But a
    /// refusal is a single opaque error, and the readiness vocabulary
    /// ([`BundleInspectIssue::MissingProofTerm`], `incomplete`, `ready_count`)
    /// exists precisely to say *which* theorem is not ready and *why*. This
    /// entry point supplies the per-theorem shape those renderers need by
    /// skipping only the structural gate — no replay, agreement, or audit check
    /// is relaxed.
    ///
    /// The result is non-authoritative, and structurally so:
    ///
    /// * [`BundleVerifyResult::trust_level`] is pinned to
    ///   [`TrustLevel::Unverified`], so a bundle the trust gate would reject can
    ///   never acquire a trust verdict by taking this path;
    /// * a theorem with no proof term always fails
    ///   [`Self::verify_theorem`] with "declaration has no proof term", so it is
    ///   always counted in `failed` and can never appear in `passed`.
    ///
    /// Callers are still expected to fail (exit non-zero) — this reports what is
    /// wrong, it does not condone it.
    #[must_use]
    pub fn verify_all_for_inspection(&self) -> BundleVerifyResult {
        BundleVerifyResult {
            // Nothing reached through the diagnostics path carries authority,
            // however the individual replays turned out.
            trust_level: TrustLevel::Unverified,
            ..self.replay_every_manifest_entry()
        }
    }

    /// Replay each manifest entry and tally the outcome.
    ///
    /// Deliberately performs no structural validation: the caller decides
    /// whether the [`validate_bundle_contents`] gate applies, which is the only
    /// difference between [`Self::verify_all`] and
    /// [`Self::verify_all_for_inspection`].
    fn replay_every_manifest_entry(&self) -> BundleVerifyResult {
        let mut passed = 0usize;
        let mut failed = 0usize;
        let mut failures = Vec::new();
        let mut verified_trust = Vec::with_capacity(self.manifest.theorems.len());
        let axioms = self.axiom_disclosure();
        let ambient_failure = axioms.ambient_failure();

        for entry in &self.manifest.theorems {
            let name = Name::from_string(&entry.name);
            // A reserved kernel name held by anything but the kernel's own
            // declaration poisons every verdict replayed in this environment:
            // each theorem fails, whatever its own replay says.
            let outcome = match &ambient_failure {
                Some(reason) => Err(CertBundleError::VerificationFailed {
                    name: entry.name.clone(),
                    reason: reason.clone(),
                }),
                None => self.verify_single(&name),
            };
            match outcome {
                Ok(trust) => {
                    passed += 1;
                    verified_trust.push(trust);
                }
                Err(e) => {
                    failed += 1;
                    failures.push((entry.name.clone(), e.to_string()));
                    verified_trust.push(TrustLevel::Unverified);
                }
            }
        }

        BundleVerifyResult {
            passed,
            failed,
            failures,
            trust_level: verified_trust
                .into_iter()
                .reduce(trust_min)
                .unwrap_or(TrustLevel::Unverified),
            axioms,
            environment: self.environment_recheck(),
        }
    }

    /// Verify a single named theorem.
    ///
    /// Fails, like [`Self::verify_all`], when the environment holds a
    /// non-canonical declaration under a reserved kernel name.
    pub fn verify_theorem(&self, name: &Name) -> Result<(), CertBundleError> {
        if let Some(reason) = self.axiom_disclosure().ambient_failure() {
            return Err(CertBundleError::VerificationFailed {
                name: name.to_string(),
                reason,
            });
        }
        self.verify_single(name).map(|_| ())
    }

    /// The embedded environment's axioms, each manifest theorem's axioms, and
    /// the declarations each theorem rests on that the kernel did not
    /// re-derive ([`BundleAxiomDisclosure`]).
    #[must_use]
    pub fn axiom_disclosure(&self) -> BundleAxiomDisclosure {
        BundleAxiomDisclosure::of_bundle(
            &self.env,
            &self.theorem_names(),
            self.rebuilt().map_err(String::as_str),
        )
    }

    /// What re-deriving the embedded environment from the canonical base
    /// found ([`super::bundle_recheck`]).
    #[must_use]
    pub fn environment_recheck(&self) -> BundleEnvironmentRecheck {
        match self.rebuilt() {
            Ok(rebuilt) => rebuilt.report.clone(),
            Err(reason) => BundleEnvironmentRecheck::unavailable(reason),
        }
    }

    /// The embedded environment re-derived from the canonical base, built on
    /// first use.
    fn rebuilt(&self) -> Result<&RebuiltEnvironment, &String> {
        self.rebuilt
            .get_or_init(|| rebuild_from_canonical_base(&self.env))
            .as_ref()
    }

    /// Inspect every theorem listed in the manifest and report bundle readiness.
    #[must_use]
    pub fn inspect(&self) -> BundleInspectReport {
        let entries: Vec<BundleInspectEntry> = self
            .manifest
            .theorems
            .iter()
            .map(|entry| self.inspect_manifest_entry(entry))
            .collect();
        let ready_count = entries.iter().filter(|entry| entry.is_ready()).count();
        let theorem_count = entries.len();

        BundleInspectReport {
            theorem_count,
            ready_count,
            incomplete_count: theorem_count.saturating_sub(ready_count),
            entries,
        }
    }

    /// Get the cross-project certificate for a theorem (for LLVM2 trust chain).
    #[must_use]
    pub fn cross_project_cert(&self, name: &Name) -> Option<&CrossProjectCert> {
        self.xproj_certs.get(name)
    }

    /// Check whether a specific theorem is present in the bundle.
    #[must_use]
    pub fn has_theorem(&self, name: &str) -> bool {
        let n = Name::from_string(name);
        self.certs.contains_key(&n)
    }

    /// Get the serialized manifest claim for a specific theorem.
    ///
    /// Manifest claims deliberately remain [`TrustLevel::Unverified`].
    /// Established authority is returned only by [`Self::verify_all`], after
    /// certificate replay and a full environment certification audit.
    #[must_use]
    pub fn trust_level(&self, name: &Name) -> Option<TrustLevel> {
        self.manifest
            .theorems
            .iter()
            .find(|e| Name::from_string(&e.name) == *name)
            .map(|e| e.trust_level)
    }

    // ── Accessors ────────────────────────────────────────────────────────

    /// Access the bundle manifest.
    #[must_use]
    pub fn manifest(&self) -> &CertBundleManifest {
        &self.manifest
    }

    /// Access the embedded environment.
    #[must_use]
    pub fn env(&self) -> &Environment {
        &self.env
    }

    /// Access informational producer metadata, if present.
    ///
    /// This self-authored metadata is structurally validated on ingress but is
    /// never used to elevate [`BundleVerifyResult::trust_level`].
    #[must_use]
    pub fn trust_chain(&self) -> Option<&ProofArchiveMetadata> {
        self.trust_chain.as_ref()
    }

    /// Return the number of theorems in the bundle.
    #[must_use]
    pub fn theorem_count(&self) -> usize {
        self.certs.len()
    }

    /// List all theorem names in the bundle.
    #[must_use]
    pub fn theorem_names(&self) -> Vec<String> {
        self.manifest
            .theorems
            .iter()
            .map(|e| e.name.clone())
            .collect()
    }

    // ── Internal helpers ─────────────────────────────────────────────────

    /// Verify a single theorem by name.
    fn verify_single(&self, name: &Name) -> Result<TrustLevel, CertBundleError> {
        let manifest_entry = self
            .manifest
            .theorems
            .iter()
            .find(|entry| Name::from_string(&entry.name) == *name)
            .ok_or_else(|| CertBundleError::MissingTheorem(name.to_string()))?;
        let cert = self
            .certs
            .get(name)
            .ok_or_else(|| CertBundleError::MissingTheorem(name.to_string()))?;
        let xproj = self.xproj_certs.get(name);

        if manifest_entry.trust_level == TrustLevel::KernelVerified && xproj.is_none() {
            return Err(CertBundleError::VerificationFailed {
                name: name.to_string(),
                reason: "kernel-verified theorem missing cross-project certificate".to_string(),
            });
        }

        // Nothing below consults the bundle's own environment. It is
        // re-derived from the canonical base first (`bundle_recheck`): a
        // declaration the author inserted without a kernel check — a
        // `Theorem`-kind `fakeFalse : False := True.intro`, a prelude family
        // with other content — is refused there, and so is every theorem
        // whose closure reaches it. Replay then runs in the REBUILT
        // environment, which holds nothing the kernel did not re-derive.
        let rebuilt = self
            .rebuilt()
            .map_err(|reason| CertBundleError::VerificationFailed {
                name: name.to_string(),
                reason: reason.clone(),
            })?;
        if !rebuilt.report.redefined_base.is_empty() {
            return Err(CertBundleError::VerificationFailed {
                name: name.to_string(),
                reason: format!(
                    "the bundle environment redefines canonical prelude declaration(s) {}; \
                     nothing replayed against it is credited",
                    rebuilt.report.redefined_base.join(", ")
                ),
            });
        }
        let unchecked = rebuilt.unchecked_in_closure(&self.env, name);
        if !unchecked.is_empty() {
            let listed: Vec<String> = unchecked
                .iter()
                .map(|(dep, why)| {
                    format!(
                        "`{}`: {}",
                        dep.to_unambiguous_string(),
                        super::bundle_recheck::first_line(why)
                    )
                })
                .collect();
            return Err(CertBundleError::VerificationFailed {
                name: name.to_string(),
                reason: format!(
                    "rests on declaration(s) the kernel did not re-derive from the canonical \
                     base: {}",
                    listed.join("; ")
                ),
            });
        }
        let env = &rebuilt.env;

        // Look up the declaration in the rebuilt environment (the same
        // declaration the bundle holds: the rebuild compared them).
        let decl = env
            .get_const(name)
            .ok_or_else(|| CertBundleError::VerificationFailed {
                name: name.to_string(),
                reason: "theorem not found in environment".to_string(),
            })?;

        let value = decl
            .value
            .as_ref()
            .ok_or_else(|| CertBundleError::VerificationFailed {
                name: name.to_string(),
                reason: "declaration has no proof term".to_string(),
            })?;

        // Use the CertVerifier to replay the certificate against the proof term.
        let mut verifier = CertVerifier::new(env);
        let verified_type =
            verifier
                .verify(cert, value)
                .map_err(|e| CertBundleError::VerificationFailed {
                    name: name.to_string(),
                    reason: e.to_string(),
                })?;
        // The independent-replay guarantee lives in `verifier.verify` above
        // (the certificate re-derives the proof's type step by step). The
        // FINAL comparison of two CLOSED top-level types is a definitional-
        // equality question on which the kernel's own checker is the
        // authority — and it carries the full rule set (notably structure
        // eta, which the cert lane's context-free engine cannot implement
        // soundly: its raw-de-Bruijn comparison has no binder context for
        // the same-structure type guard). The cert-lane fragment is a strict
        // subset of kernel def-eq, so this accepts nothing `add_decl` would
        // not have (first exercised by the clean-mtype Sigma statements,
        // 2026-08-06).
        let tc = crate::tc::TypeChecker::with_mode(env, env.mode());
        if !tc.is_def_eq(&verified_type, &decl.type_) {
            return Err(CertBundleError::VerificationFailed {
                name: name.to_string(),
                reason: format!(
                    "replayed proof type {verified_type:?} does not match declaration type {:?}",
                    decl.type_
                ),
            });
        }

        // Verify cross-project cert if present.
        if let Some(xproj) = xproj {
            xproj
                .verify(env)
                .map_err(|e| CertBundleError::VerificationFailed {
                    name: name.to_string(),
                    reason: format!("cross-project cert mismatch: {e}"),
                })?;
        }

        if xproj.is_none() {
            return Ok(TrustLevel::Unverified);
        }

        // Replay establishes that this certificate matches the stored proof
        // term.  Strong authority additionally requires a fresh, rooted audit
        // of the exact `term : goal` judgment and its complete type/value
        // dependency closure.  This rejects forged or structurally admitted
        // dependencies and prevents deserialization from minting transient
        // kernel provenance for value-less kernel objects.
        let audit = env.audit_certification(&decl.type_, value);
        Ok(trust_from_certification_audit(&audit))
    }

    fn ensure_all_replay_valid(&self) -> Result<(), CertBundleError> {
        for entry in &self.manifest.theorems {
            self.verify_single(&Name::from_string(&entry.name))?;
        }
        Ok(())
    }

    fn inspect_manifest_entry(&self, entry: &CertBundleEntry) -> BundleInspectEntry {
        let name = Name::from_string(&entry.name);
        let has_certificate = self.certs.contains_key(&name);
        let has_cross_project_certificate = self.xproj_certs.contains_key(&name);
        let requires_cross_project_certificate = entry.trust_level == TrustLevel::KernelVerified;
        let mut theorem_type = None;
        let mut declaration_kind = None;
        let mut has_environment_declaration = false;
        let mut has_proof_term = false;

        if let Some(decl) = self.env.get_const(&name) {
            has_environment_declaration = true;
            theorem_type = Some(decl.type_.to_string());
            has_proof_term = decl.value.is_some();
            declaration_kind = Some(match decl.kind {
                ConstantKind::Definition => "definition",
                ConstantKind::Axiom => "axiom",
                ConstantKind::Theorem => "theorem",
                ConstantKind::Opaque => "opaque",
            });
        }

        let mut issues = Vec::new();
        if !has_certificate {
            issues.push(BundleInspectIssue::MissingCertificate);
        }
        if requires_cross_project_certificate && !has_cross_project_certificate {
            issues.push(BundleInspectIssue::MissingCrossProjectCertificate);
        }
        if !has_environment_declaration {
            issues.push(BundleInspectIssue::MissingEnvironmentDeclaration);
        } else if !has_proof_term {
            issues.push(BundleInspectIssue::MissingProofTerm);
        }

        BundleInspectEntry {
            name: entry.name.clone(),
            trust_level: entry.trust_level,
            sorry_free: entry.sorry_free,
            theorem_type,
            declaration_kind,
            has_certificate,
            has_environment_declaration,
            has_proof_term,
            has_cross_project_certificate,
            type_hash: (!entry.type_hash.is_empty()).then(|| entry.type_hash.clone()),
            proof_hash: (!entry.proof_hash.is_empty()).then(|| entry.proof_hash.clone()),
            issues,
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Helpers
// ────────────────────────────────────────────────────────────────────────────

fn validate_bundle_archive(archive: &BundleArchive) -> Result<(), CertBundleError> {
    if archive.manifest.version != BUNDLE_VERSION {
        return Err(CertBundleError::UnsupportedVersion(
            archive.manifest.version,
        ));
    }
    validate_trust_chain_metadata(archive.trust_chain.as_ref())?;

    for (kind, count) in [
        ("manifest theorem", archive.manifest.theorems.len()),
        ("certificate", archive.certs.len()),
        ("cross-project certificate", archive.xproj_certs.len()),
    ] {
        if count > MAX_BUNDLE_ENTRIES {
            return Err(CertBundleError::ResourceLimit(format!(
                "{kind} count {count} exceeds maximum {MAX_BUNDLE_ENTRIES}"
            )));
        }
    }

    if archive.env_bytes.len() > MAX_BUNDLE_ENV_BYTES {
        return Err(CertBundleError::ResourceLimit(format!(
            "environment payload size {} exceeds maximum {MAX_BUNDLE_ENV_BYTES}",
            archive.env_bytes.len()
        )));
    }

    for (kind, entries) in [
        ("certificate", &archive.certs),
        ("cross-project certificate", &archive.xproj_certs),
    ] {
        for (name, bytes) in entries {
            if name.len() > MAX_BUNDLE_NAME_BYTES {
                return Err(CertBundleError::ResourceLimit(format!(
                    "{kind} name has {} bytes, exceeding maximum {MAX_BUNDLE_NAME_BYTES}",
                    name.len()
                )));
            }
            if bytes.len() > MAX_STREAM_CERT_BYTES {
                return Err(CertBundleError::ResourceLimit(format!(
                    "{kind} '{name}' has {} bytes, exceeding maximum {MAX_STREAM_CERT_BYTES}",
                    bytes.len()
                )));
            }
        }
    }

    let mut manifest_names = HashSet::with_capacity(archive.manifest.theorems.len());
    let mut canonical_names = HashSet::with_capacity(archive.manifest.theorems.len());
    for entry in &archive.manifest.theorems {
        if entry.name.len() > MAX_BUNDLE_NAME_BYTES {
            return Err(CertBundleError::ResourceLimit(format!(
                "manifest theorem name has {} bytes, exceeding maximum {MAX_BUNDLE_NAME_BYTES}",
                entry.name.len()
            )));
        }
        let canonical = ensure_canonical_bundle_name(&entry.name)?;
        if !manifest_names.insert(entry.name.as_str()) || !canonical_names.insert(canonical) {
            return Err(CertBundleError::InvalidManifest(format!(
                "duplicate theorem entry '{}'",
                entry.name
            )));
        }
    }

    let cert_names: HashSet<&str> = archive.certs.keys().map(String::as_str).collect();
    if cert_names != manifest_names {
        return Err(CertBundleError::InvalidManifest(
            "manifest theorem names must exactly match certificate keys".to_string(),
        ));
    }
    let xproj_names: HashSet<&str> = archive.xproj_certs.keys().map(String::as_str).collect();
    if !xproj_names.is_subset(&manifest_names) {
        return Err(CertBundleError::InvalidManifest(
            "cross-project certificate keys must be scoped to manifest theorems".to_string(),
        ));
    }
    if archive.manifest.trust_level != aggregate_trust(&archive.manifest.theorems) {
        return Err(CertBundleError::InvalidManifest(
            "aggregate trust level does not match theorem entries".to_string(),
        ));
    }

    Ok(())
}

fn validate_trust_chain_metadata(
    metadata: Option<&ProofArchiveMetadata>,
) -> Result<(), CertBundleError> {
    if let Some(metadata) = metadata {
        metadata.validate_chain().map_err(|error| {
            CertBundleError::InvalidManifest(format!(
                "informational trust-chain metadata is malformed: {error}"
            ))
        })?;
    }
    Ok(())
}

fn ensure_canonical_bundle_name(raw: &str) -> Result<Name, CertBundleError> {
    if raw.is_empty() {
        return Err(CertBundleError::InvalidManifest(
            "theorem name must not be empty".to_string(),
        ));
    }
    let name = Name::from_string(raw);
    if name.to_string() != raw {
        return Err(CertBundleError::InvalidManifest(format!(
            "theorem name '{raw}' is not in canonical form"
        )));
    }
    Ok(name)
}

fn declaration_metadata(
    env: &Environment,
    name: &Name,
    display_name: &str,
) -> Result<(String, String, bool), CertBundleError> {
    let declaration = env.get_const(name).ok_or_else(|| {
        CertBundleError::InvalidManifest(format!(
            "theorem '{display_name}' is missing from the environment"
        ))
    })?;
    let proof = declaration.value.as_ref().ok_or_else(|| {
        CertBundleError::InvalidManifest(format!("theorem '{display_name}' has no proof term"))
    })?;
    let type_bytes = bincode::serde::encode_to_vec(&declaration.type_, bincode::config::standard())
        .map_err(|error| CertBundleError::Serialization(error.to_string()))?;
    let proof_bytes = bincode::serde::encode_to_vec(proof, bincode::config::standard())
        .map_err(|error| CertBundleError::Serialization(error.to_string()))?;
    Ok((
        sha256_hex(&type_bytes),
        sha256_hex(&proof_bytes),
        closure_sorry_free(env, name, proof),
    ))
}

/// Whether a theorem is `sorry`-free as a bundle manifest must claim it: no
/// sorry occurrence in its own proof AND none in its constant closure (a
/// theorem proved from a sorry'd lemma, or through `def s := @sorryAx`, is
/// not sorry-free).
fn closure_sorry_free(env: &Environment, name: &Name, proof: &crate::Expr) -> bool {
    !proof.has_sorry()
        && !crate::env::DomainAxiomClosure::new()
            .trust_markers_of_name(env, name)
            .iter()
            .any(crate::env::is_sorry_marker)
}

/// Best-effort manifest metadata for a diagnostics view.
///
/// Where [`declaration_metadata`] *rejects* a theorem whose declaration has no
/// proof term, this records what actually exists and leaves the rest empty, so
/// [`CertBundle::inspect`] can report the deficiency instead of the caller
/// getting an opaque construction failure. It never invents a `proof_hash` for
/// a proof that does not exist.
fn diagnostic_declaration_metadata(
    env: &Environment,
    name: &Name,
) -> Result<(String, String, bool), CertBundleError> {
    let Some(declaration) = env.get_const(name) else {
        return Ok((String::new(), String::new(), true));
    };
    let type_bytes = bincode::serde::encode_to_vec(&declaration.type_, bincode::config::standard())
        .map_err(|error| CertBundleError::Serialization(error.to_string()))?;
    let type_hash = sha256_hex(&type_bytes);
    let Some(proof) = declaration.value.as_ref() else {
        // No proof term: vacuously `sorry`-free, but the entry is flagged
        // `missing-proof-term` and pinned to `Unverified` by the caller.
        return Ok((type_hash, String::new(), true));
    };
    let proof_bytes = bincode::serde::encode_to_vec(proof, bincode::config::standard())
        .map_err(|error| CertBundleError::Serialization(error.to_string()))?;
    Ok((
        type_hash,
        sha256_hex(&proof_bytes),
        closure_sorry_free(env, name, proof),
    ))
}

fn validate_cross_project_metadata(
    theorem_name: &str,
    type_hash: &str,
    proof_hash: &str,
    xproj: &CrossProjectCert,
    env: &Environment,
) -> Result<(), CertBundleError> {
    if xproj.theorem_name != theorem_name {
        return Err(CertBundleError::InvalidManifest(format!(
            "cross-project certificate key '{theorem_name}' names theorem '{}'",
            xproj.theorem_name
        )));
    }
    if xproj.theorem_type_hash != type_hash || xproj.proof_hash != proof_hash {
        return Err(CertBundleError::InvalidManifest(format!(
            "cross-project hashes for '{theorem_name}' do not match manifest/environment content"
        )));
    }
    xproj.verify(env).map_err(|error| {
        CertBundleError::InvalidManifest(format!(
            "cross-project certificate for '{theorem_name}' is invalid: {error}"
        ))
    })
}

fn validate_bundle_contents(
    manifest: &CertBundleManifest,
    env: &Environment,
    certs: &HashMap<Name, ProofCert>,
    xproj_certs: &HashMap<Name, CrossProjectCert>,
) -> Result<(), CertBundleError> {
    if manifest.version != BUNDLE_VERSION {
        return Err(CertBundleError::UnsupportedVersion(manifest.version));
    }
    if manifest.theorems.len() > MAX_BUNDLE_ENTRIES
        || certs.len() > MAX_BUNDLE_ENTRIES
        || xproj_certs.len() > MAX_BUNDLE_ENTRIES
    {
        return Err(CertBundleError::ResourceLimit(
            "bundle entry count exceeds maximum".to_string(),
        ));
    }

    let mut entries = HashMap::with_capacity(manifest.theorems.len());
    for entry in &manifest.theorems {
        let name = ensure_canonical_bundle_name(&entry.name)?;
        if entries.insert(name, entry).is_some() {
            return Err(CertBundleError::InvalidManifest(format!(
                "duplicate canonical theorem entry '{}'",
                entry.name
            )));
        }
    }
    if entries.len() != certs.len()
        || certs.keys().any(|name| !entries.contains_key(name))
        || entries.keys().any(|name| !certs.contains_key(name))
    {
        return Err(CertBundleError::InvalidManifest(
            "manifest theorem names must exactly match proof certificate keys".to_string(),
        ));
    }
    if xproj_certs.keys().any(|name| !certs.contains_key(name)) {
        return Err(CertBundleError::InvalidManifest(
            "cross-project certificate keys must be scoped to proof certificates".to_string(),
        ));
    }

    for (name, entry) in entries {
        let display_name = name.to_string();
        let (type_hash, proof_hash, sorry_free) = declaration_metadata(env, &name, &display_name)?;
        if entry.type_hash != type_hash || entry.proof_hash != proof_hash {
            return Err(CertBundleError::InvalidManifest(format!(
                "manifest hashes for '{display_name}' do not match the environment"
            )));
        }
        if entry.sorry_free != sorry_free {
            return Err(CertBundleError::InvalidManifest(format!(
                "manifest sorry metadata for '{display_name}' does not match the proof term"
            )));
        }

        let xproj = xproj_certs.get(&name);
        // Manifest metadata is never established authority.  Replay and the
        // rooted environment audit happen only on a live CertBundle.
        let expected_trust = TrustLevel::Unverified;
        if entry.trust_level != expected_trust {
            return Err(CertBundleError::InvalidManifest(format!(
                "manifest trust for '{display_name}' does not match certificate evidence"
            )));
        }
        if let Some(xproj) = xproj {
            validate_cross_project_metadata(&display_name, &type_hash, &proof_hash, xproj, env)?;
        }
    }

    let actual_trust = aggregate_trust(&manifest.theorems);
    if manifest.trust_level != actual_trust {
        return Err(CertBundleError::InvalidManifest(
            "aggregate trust level does not match theorem evidence".to_string(),
        ));
    }
    Ok(())
}

/// Compute a SHA-256 hex digest of a byte slice.
fn sha256_hex(data: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    use std::fmt::Write as _;
    let hash = Sha256::digest(data);
    let mut out = String::with_capacity(64);
    for byte in hash.as_slice() {
        let _ = write!(&mut out, "{byte:02x}");
    }
    out
}

/// Return the more conservative of two trust levels.
fn trust_min(a: TrustLevel, b: TrustLevel) -> TrustLevel {
    let rank = |t: TrustLevel| -> u8 {
        match t {
            TrustLevel::Unverified => 0,
            TrustLevel::Axiom => 1,
            TrustLevel::SmtBacked => 2,
            TrustLevel::KernelVerified => 3,
        }
    };
    if rank(a) <= rank(b) {
        a
    } else {
        b
    }
}

fn aggregate_trust(entries: &[CertBundleEntry]) -> TrustLevel {
    entries
        .iter()
        .map(|entry| entry.trust_level)
        .reduce(trust_min)
        .unwrap_or(TrustLevel::Unverified)
}

fn trust_from_certification_audit(audit: &CertificationAudit) -> TrustLevel {
    if audit.is_certified() {
        TrustLevel::KernelVerified
    } else if !audit.issues.is_empty()
        && audit
            .issues
            .iter()
            .all(|issue| matches!(issue, CertificationIssue::NonFoundationalAxiom { .. }))
    {
        // A checked judgment whose only disclosed authority is an explicit
        // domain axiom is classified as such, never kernel-verified.
        TrustLevel::Axiom
    } else {
        TrustLevel::Unverified
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cert::cross_project::{ProverInfo, ProverSystem};
    use crate::cert::types::ProofCert;
    use crate::{Declaration, Expr};

    fn prover() -> ProverInfo {
        ProverInfo::new(ProverSystem::Clean, "test", Some("0.1.0".to_string()))
    }

    /// Build a minimal test environment with two theorems (True.intro : True).
    fn test_env_and_certs() -> (
        Environment,
        HashMap<Name, ProofCert>,
        HashMap<Name, CrossProjectCert>,
    ) {
        let mut env = Environment::with_prelude();

        let true_ty = Expr::const_(Name::from_string("True"), vec![]);
        let true_intro = Expr::const_(Name::from_string("True.intro"), vec![]);
        let thm_name = Name::from_string("Test.trivial");

        env.add_decl(Declaration::Theorem {
            name: thm_name.clone(),
            level_params: vec![],
            type_: true_ty,
            value: true_intro.clone(),
        })
        .expect("register theorem");

        // Build a simple Const certificate for True.intro : True
        let cert = ProofCert::Const {
            name: Name::from_string("True.intro"),
            levels: vec![],
            type_: Box::new(Expr::const_(Name::from_string("True"), vec![])),
        };

        let xproj = CrossProjectCert::from_environment(&env, "Test.trivial", prover(), vec![])
            .expect("build xproj cert");

        let mut certs = HashMap::new();
        certs.insert(thm_name.clone(), cert);

        let mut xproj_certs = HashMap::new();
        xproj_certs.insert(thm_name, xproj);

        (env, certs, xproj_certs)
    }

    #[test]
    fn test_bundle_build_and_accessors() {
        let (env, certs, xproj_certs) = test_env_and_certs();
        let bundle = CertBundle::build("test-project", "0.1.0", env, certs, xproj_certs, None)
            .expect("build bundle");

        assert_eq!(bundle.theorem_count(), 1);
        assert!(bundle.has_theorem("Test.trivial"));
        assert!(!bundle.has_theorem("Nonexistent"));
        assert_eq!(bundle.manifest().project, "test-project");
        assert_eq!(bundle.manifest().version, BUNDLE_VERSION);
        assert!(!bundle.manifest().env_hash.is_empty());
        assert_eq!(bundle.theorem_names(), vec!["Test.trivial"]);
    }

    #[test]
    fn test_bundle_save_load_roundtrip() {
        let (env, certs, xproj_certs) = test_env_and_certs();
        let bundle = CertBundle::build("test-project", "0.1.0", env, certs, xproj_certs, None)
            .expect("build bundle");

        let dir = tempfile::tempdir().expect("create temp dir");
        let path = dir.path().join("test.cleancert");

        bundle.save(&path).expect("save bundle");

        let loaded = CertBundle::load(&path).expect("load bundle");
        assert_eq!(loaded.theorem_count(), 1);
        assert!(loaded.has_theorem("Test.trivial"));
        assert_eq!(loaded.manifest().project, "test-project");
        assert_eq!(loaded.manifest().env_hash, bundle.manifest().env_hash);
    }

    #[test]
    fn test_bundle_verify_all() {
        let (env, certs, xproj_certs) = test_env_and_certs();
        let bundle = CertBundle::build("test-project", "0.1.0", env, certs, xproj_certs, None)
            .expect("build bundle");

        let result = bundle.verify_all().expect("verify_all");
        assert!(result.all_passed(), "failures: {:?}", result.failures);
        assert_eq!(result.passed, 1);
        assert_eq!(result.failed, 0);
        // Every declaration was re-derived: the prelude's pinned to the
        // canonical base, the theorem re-admitted by the kernel.
        assert!(result.environment.passed(), "{:?}", result.environment);
        assert_eq!(result.environment.constants_readmitted, 1);
        assert_eq!(result.environment.families_readmitted, 0);
        assert!(result.environment.pinned_to_base > 100);
        assert_eq!(
            result.axioms.theorem_unchecked_dependencies,
            vec![("Test.trivial".to_string(), Vec::<String>::new())]
        );
    }

    #[test]
    fn test_bundle_verify_single_theorem() {
        let (env, certs, xproj_certs) = test_env_and_certs();
        let bundle = CertBundle::build("test-project", "0.1.0", env, certs, xproj_certs, None)
            .expect("build bundle");

        let name = Name::from_string("Test.trivial");
        bundle
            .verify_theorem(&name)
            .expect("single theorem verification should pass");
    }

    #[test]
    fn test_bundle_verify_axiom_fails_missing_proof_term() {
        let mut env = Environment::with_prelude();
        let axiom_name = Name::from_string("Test.assumed");
        env.add_decl(Declaration::Axiom {
            name: axiom_name.clone(),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("True"), vec![]),
        })
        .expect("register axiom");

        let mut certs = HashMap::new();
        certs.insert(
            axiom_name.clone(),
            ProofCert::Const {
                name: Name::from_string("True.intro"),
                levels: vec![],
                type_: Box::new(Expr::const_(Name::from_string("True"), vec![])),
            },
        );

        let err = CertBundle::build("test-project", "0.1.0", env, certs, HashMap::new(), None)
            .expect_err("axioms cannot be packaged as replayable theorems");
        assert!(matches!(
            err,
            CertBundleError::InvalidManifest(ref reason)
                if reason.contains("has no proof term")
        ));
    }

    #[test]
    fn test_bundle_verify_missing_theorem_fails() {
        let (env, certs, xproj_certs) = test_env_and_certs();
        let bundle = CertBundle::build("test-project", "0.1.0", env, certs, xproj_certs, None)
            .expect("build bundle");

        let name = Name::from_string("Nonexistent");
        let err = bundle
            .verify_theorem(&name)
            .expect_err("missing theorem should fail");
        assert!(matches!(err, CertBundleError::MissingTheorem(_)));
    }

    #[test]
    fn test_bundle_load_invalid_magic() {
        let dir = tempfile::tempdir().expect("create temp dir");
        let path = dir.path().join("bad.cleancert");
        std::fs::write(&path, b"not a cert bundle").expect("write bad file");

        let err = CertBundle::load(&path).expect_err("should reject bad magic");
        assert!(matches!(err, CertBundleError::InvalidMagic));
    }

    #[test]
    fn test_bundle_cross_project_cert_accessor() {
        let (env, certs, xproj_certs) = test_env_and_certs();
        let bundle = CertBundle::build("test-project", "0.1.0", env, certs, xproj_certs, None)
            .expect("build bundle");

        let name = Name::from_string("Test.trivial");
        let xproj = bundle.cross_project_cert(&name);
        assert!(xproj.is_some());
        assert_eq!(xproj.unwrap().theorem_name, "Test.trivial");
    }

    #[test]
    fn test_bundle_trust_level_accessor() {
        let (env, certs, xproj_certs) = test_env_and_certs();
        let bundle = CertBundle::build("test-project", "0.1.0", env, certs, xproj_certs, None)
            .expect("build bundle");

        let name = Name::from_string("Test.trivial");
        let trust = bundle.trust_level(&name);
        assert!(trust.is_some());
        assert_eq!(trust.unwrap(), TrustLevel::Unverified);

        let verified = bundle.verify_all().expect("establish live trust");
        assert_eq!(verified.trust_level, TrustLevel::KernelVerified);
    }

    #[test]
    fn test_bundle_save_load_verify_roundtrip() {
        let (env, certs, xproj_certs) = test_env_and_certs();
        let bundle = CertBundle::build("test-project", "0.1.0", env, certs, xproj_certs, None)
            .expect("build bundle");

        let dir = tempfile::tempdir().expect("create temp dir");
        let path = dir.path().join("roundtrip.cleancert");

        bundle.save(&path).expect("save");
        let loaded = CertBundle::load(&path).expect("load");

        // Deserialization mints no provenance: the loaded environment carries
        // no kernel-check claim for anything in it.
        assert_eq!(
            loaded
                .env()
                .declaration_verification(&Name::from_string("Test.trivial")),
            None,
            "deserialization must not mint transient kernel-object provenance"
        );
        // Authority is re-EARNED instead: verification re-derives the whole
        // environment from the canonical base (`bundle_recheck`) and replays
        // and audits in the rebuilt environment, which the kernel checked.
        // Until 2026-09-28 the replay ran in the deserialized environment and
        // a loaded bundle could only ever report `Unverified`.
        let result = loaded.verify_all().expect("verify_all after load");
        assert!(result.all_passed(), "failures: {:?}", result.failures);
        assert!(result.environment.passed(), "{:?}", result.environment);
        assert_eq!(result.environment.constants_readmitted, 1);
        assert_eq!(result.trust_level, TrustLevel::KernelVerified);
    }

    #[test]
    fn test_bundle_inspect_marks_ready_theorem() {
        let (env, certs, xproj_certs) = test_env_and_certs();
        let bundle = CertBundle::build("test-project", "0.1.0", env, certs, xproj_certs, None)
            .expect("build bundle");

        let report = bundle.inspect();
        assert_eq!(report.theorem_count, 1);
        assert_eq!(report.ready_count, 1);
        assert_eq!(report.incomplete_count, 0);

        let entry = &report.entries[0];
        assert_eq!(entry.name, "Test.trivial");
        assert_eq!(entry.declaration_kind, Some("theorem"));
        assert_eq!(entry.theorem_type.as_deref(), Some("True"));
        assert!(entry.has_certificate);
        assert!(entry.has_environment_declaration);
        assert!(entry.has_proof_term);
        assert!(entry.has_cross_project_certificate);
        assert!(entry.is_ready());
        assert!(entry.issues.is_empty());
    }

    #[test]
    fn test_bundle_inspect_reports_missing_certificate() {
        let (env, certs, xproj_certs) = test_env_and_certs();
        let mut bundle = CertBundle::build("test-project", "0.1.0", env, certs, xproj_certs, None)
            .expect("build bundle");
        bundle.certs.clear();

        let report = bundle.inspect();
        assert_eq!(report.ready_count, 0);
        assert_eq!(report.incomplete_count, 1);
        assert_eq!(
            report.entries[0].issues,
            vec![BundleInspectIssue::MissingCertificate]
        );
    }

    #[test]
    fn test_bundle_inspect_reports_missing_cross_project_certificate() {
        let (env, certs, xproj_certs) = test_env_and_certs();
        let bundle = CertBundle::build("test-project", "0.1.0", env, certs, xproj_certs, None)
            .expect("build bundle");

        let dir = tempfile::tempdir().expect("create temp dir");
        let path = dir.path().join("missing-xproj.cleancert");
        bundle.save(&path).expect("save bundle");

        let mut loaded = CertBundle::load(&path).expect("load bundle");
        loaded.manifest.theorems[0].trust_level = TrustLevel::KernelVerified;
        loaded.manifest.trust_level = TrustLevel::KernelVerified;
        loaded.xproj_certs.clear();

        let report = loaded.inspect();
        assert_eq!(report.ready_count, 0);
        assert_eq!(report.incomplete_count, 1);

        let entry = &report.entries[0];
        assert_eq!(entry.name, "Test.trivial");
        assert_eq!(entry.trust_level, TrustLevel::KernelVerified);
        assert!(entry.has_certificate);
        assert!(entry.has_environment_declaration);
        assert!(entry.has_proof_term);
        assert!(!entry.has_cross_project_certificate);
        assert_eq!(
            entry.issues,
            vec![BundleInspectIssue::MissingCrossProjectCertificate]
        );
    }

    #[test]
    fn test_bundle_inspect_reports_missing_environment_declaration() {
        let (env, certs, xproj_certs) = test_env_and_certs();
        let mut bundle = CertBundle::build("test-project", "0.1.0", env, certs, xproj_certs, None)
            .expect("build bundle");
        bundle.manifest.theorems.push(CertBundleEntry {
            name: "Test.ghost".to_string(),
            type_hash: String::new(),
            proof_hash: String::new(),
            trust_level: TrustLevel::Unverified,
            sorry_free: true,
        });

        let report = bundle.inspect();
        let ghost = report
            .entries
            .iter()
            .find(|entry| entry.name == "Test.ghost")
            .expect("ghost entry present");
        assert_eq!(ghost.declaration_kind, None);
        assert_eq!(ghost.theorem_type, None);
        assert!(!ghost.has_environment_declaration);
        assert_eq!(
            ghost.issues,
            vec![
                BundleInspectIssue::MissingCertificate,
                BundleInspectIssue::MissingEnvironmentDeclaration,
            ]
        );
    }

    #[test]
    fn test_bundle_inspect_reports_missing_proof_term() {
        let mut env = Environment::with_prelude();
        let axiom_name = Name::from_string("Test.assumed");
        env.add_decl(Declaration::Axiom {
            name: axiom_name.clone(),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("True"), vec![]),
        })
        .expect("register axiom");

        let mut certs = HashMap::new();
        certs.insert(
            axiom_name,
            ProofCert::Const {
                name: Name::from_string("True.intro"),
                levels: vec![],
                type_: Box::new(Expr::const_(Name::from_string("True"), vec![])),
            },
        );

        // Inspection intentionally accepts an incomplete in-memory fixture;
        // construction/persistence reject it because there is no replayable
        // proof term.
        let bundle =
            CertBundle::for_inspection("inspection-only", "0.1.0", env, certs, HashMap::new())
                .expect("assemble diagnostics view");

        let report = bundle.inspect();
        let entry = &report.entries[0];
        assert_eq!(entry.declaration_kind, Some("axiom"));
        assert_eq!(entry.theorem_type.as_deref(), Some("True"));
        assert!(entry.has_certificate);
        assert!(entry.has_environment_declaration);
        assert!(!entry.has_proof_term);
        assert_eq!(entry.issues, vec![BundleInspectIssue::MissingProofTerm]);
        assert_eq!(report.ready_count, 0);
        assert_eq!(report.incomplete_count, 1);

        // The diagnostics view must never become a trust laundering path: an
        // assumed theorem stays `Unverified`, records no proof hash, and the
        // bundle is still refused by every authority-bearing operation.
        assert_eq!(entry.trust_level, TrustLevel::Unverified);
        assert_eq!(entry.proof_hash, None);
        assert_eq!(bundle.manifest().trust_level, TrustLevel::Unverified);
        assert!(matches!(
            bundle.verify_all(),
            Err(CertBundleError::InvalidManifest(ref reason))
                if reason.contains("has no proof term")
        ));
        assert!(matches!(
            bundle.verify_theorem(&Name::from_string("Test.assumed")),
            Err(CertBundleError::VerificationFailed { ref reason, .. })
                if reason == "declaration has no proof term"
        ));
        let dir = tempfile::tempdir().expect("create temp dir");
        assert!(matches!(
            bundle.save(dir.path().join("quarantined.cleancert")),
            Err(CertBundleError::InvalidManifest(ref reason))
                if reason.contains("has no proof term")
        ));
    }

    /// The diagnostics replay must *report* an unproved theorem as failed —
    /// and must never let it, or the bundle carrying it, acquire authority.
    #[test]
    fn test_verify_all_for_inspection_reports_failure_without_conferring_trust() {
        let mut env = Environment::with_prelude();
        let axiom_name = Name::from_string("Test.assumed");
        env.add_decl(Declaration::Axiom {
            name: axiom_name.clone(),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("True"), vec![]),
        })
        .expect("register axiom");

        let mut certs = HashMap::new();
        certs.insert(
            axiom_name,
            ProofCert::Const {
                name: Name::from_string("True.intro"),
                levels: vec![],
                type_: Box::new(Expr::const_(Name::from_string("True"), vec![])),
            },
        );

        let bundle =
            CertBundle::for_inspection("inspection-only", "0.1.0", env, certs, HashMap::new())
                .expect("assemble diagnostics view");

        // The trust verb still refuses the bundle outright.
        assert!(matches!(
            bundle.verify_all(),
            Err(CertBundleError::InvalidManifest(ref reason))
                if reason.contains("has no proof term")
        ));

        // The diagnostics verb describes the same deficiency instead.
        let result = bundle.verify_all_for_inspection();
        assert_eq!(result.passed, 0);
        assert_eq!(result.failed, 1);
        assert!(!result.all_passed());
        assert_eq!(
            result.trust_level,
            TrustLevel::Unverified,
            "a bundle the trust gate rejects must never gain a trust verdict"
        );
        let (name, reason) = &result.failures[0];
        assert_eq!(name, "Test.assumed");
        assert_eq!(
            reason,
            "verification failed for theorem 'Test.assumed': declaration has no proof term"
        );
    }

    /// Even when every replay succeeds, a bundle that the structural gate
    /// rejects must not be laundered into a trust verdict by the diagnostics
    /// verb.
    #[test]
    fn test_verify_all_for_inspection_never_mints_trust_for_a_rejected_bundle() {
        let (env, certs, xproj_certs) = test_env_and_certs();
        let mut bundle = CertBundle::build("test-project", "0.1.0", env, certs, xproj_certs, None)
            .expect("build bundle");
        let authoritative = bundle.verify_all().expect("verify built bundle");
        assert_eq!(authoritative.failed, 0);

        // Corrupt the manifest so the structural gate refuses the bundle while
        // every certificate still replays.
        for entry in &mut bundle.manifest.theorems {
            entry.type_hash = "00".repeat(32);
        }
        assert!(matches!(
            bundle.verify_all(),
            Err(CertBundleError::InvalidManifest(ref reason))
                if reason.contains("do not match the environment")
        ));

        let diagnostic = bundle.verify_all_for_inspection();
        assert_eq!(diagnostic.failed, 0, "replay itself still succeeds");
        assert_eq!(
            diagnostic.trust_level,
            TrustLevel::Unverified,
            "the diagnostics path is never a source of authority"
        );
    }

    /// Regression guard for the readiness-diagnostics path: a `.cleancert`
    /// the trust loader refuses must still be *describable*, and the forged
    /// `KernelVerified` claim it carries must be reported as `Unverified`.
    #[test]
    fn test_bundle_load_for_inspection_never_honors_a_forged_trust_claim() {
        let mut env = Environment::with_prelude();
        let axiom_name = Name::from_string("Test.assumed");
        env.add_decl(Declaration::Axiom {
            name: axiom_name.clone(),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("True"), vec![]),
        })
        .expect("register axiom");

        let cert = ProofCert::Const {
            name: Name::from_string("True.intro"),
            levels: vec![],
            type_: Box::new(Expr::const_(Name::from_string("True"), vec![])),
        };
        let env_bytes =
            bincode::serde::encode_to_vec(&env, bincode::config::standard()).expect("encode env");
        let cert_bytes =
            bincode::serde::encode_to_vec(&cert, bincode::config::standard()).expect("encode cert");
        let archive = BundleArchive {
            manifest: CertBundleManifest {
                version: BUNDLE_VERSION,
                project: "forged".to_string(),
                clean_version: "0.1.0".to_string(),
                env_hash: sha256_hex(&env_bytes),
                theorems: vec![CertBundleEntry {
                    name: "Test.assumed".to_string(),
                    type_hash: "00".repeat(32),
                    proof_hash: "11".repeat(32),
                    // The forgery under test: kernel authority asserted for a
                    // theorem that has no proof term at all.
                    trust_level: TrustLevel::KernelVerified,
                    sorry_free: true,
                }],
                trust_level: TrustLevel::KernelVerified,
            },
            env_bytes,
            certs: HashMap::from([("Test.assumed".to_string(), cert_bytes)]),
            xproj_certs: HashMap::new(),
            trust_chain: None,
        };

        let dir = tempfile::tempdir().expect("create temp dir");
        let path = dir.path().join("forged.cleancert");
        let uncompressed = bincode::serde::encode_to_vec(&archive, bincode::config::standard())
            .expect("encode archive");
        let compressed = zstd::encode_all(uncompressed.as_slice(), 3).expect("compress archive");
        let mut bytes = BUNDLE_MAGIC.to_vec();
        bytes.extend_from_slice(&compressed);
        std::fs::write(&path, &bytes).expect("write forged bundle");

        // The trust loader fails closed.
        assert!(matches!(
            CertBundle::load(&path),
            Err(CertBundleError::InvalidManifest(ref reason))
                if reason.contains("has no proof term")
        ));

        // The diagnostic loader says *what* is wrong, with no authority.
        let bundle = CertBundle::load_for_inspection(&path).expect("diagnostic read");
        let report = bundle.inspect();
        assert_eq!(report.ready_count, 0);
        assert_eq!(report.incomplete_count, 1);
        let entry = &report.entries[0];
        assert_eq!(entry.name, "Test.assumed");
        assert_eq!(entry.declaration_kind, Some("axiom"));
        assert!(!entry.has_proof_term);
        assert_eq!(entry.issues, vec![BundleInspectIssue::MissingProofTerm]);
        assert_eq!(
            entry.trust_level,
            TrustLevel::Unverified,
            "a forged manifest claim must never survive a quarantined read"
        );
        assert_eq!(bundle.manifest().trust_level, TrustLevel::Unverified);

        // The digests are attacker-chosen too, and they LOOK like evidence in a
        // way `trust_level` does not: rendering the forged `11..` beside
        // `has_proof_term: false` would invite a reader to believe some proof
        // was hashed. Nothing validated them on this path, so they must not
        // reach the report at all. The fixture forges both, so this fails if
        // either is echoed.
        assert_eq!(
            entry.proof_hash, None,
            "a quarantined read must not present an unvalidated proof_hash as fact"
        );
        assert_eq!(
            entry.type_hash, None,
            "a quarantined read must not present an unvalidated type_hash as fact"
        );
        assert!(
            bundle
                .manifest()
                .theorems
                .iter()
                .all(|e| e.type_hash.is_empty() && e.proof_hash.is_empty()),
            "the quarantined manifest itself must carry no unvalidated digest"
        );

        assert!(bundle.verify_all().is_err());
    }

    #[test]
    fn test_bundle_verify_kernel_verified_missing_cross_project_certificate_fails() {
        let (env, certs, xproj_certs) = test_env_and_certs();
        let bundle = CertBundle::build("test-project", "0.1.0", env, certs, xproj_certs, None)
            .expect("build bundle");

        let dir = tempfile::tempdir().expect("create temp dir");
        let path = dir.path().join("verify-missing-xproj.cleancert");
        bundle.save(&path).expect("save bundle");

        let mut loaded = CertBundle::load(&path).expect("load bundle");
        loaded.manifest.theorems[0].trust_level = TrustLevel::KernelVerified;
        loaded.manifest.trust_level = TrustLevel::KernelVerified;
        loaded.xproj_certs.clear();

        let name = Name::from_string("Test.trivial");
        let err = loaded
            .verify_theorem(&name)
            .expect_err("kernel-verified theorem without xproj should fail");
        assert!(matches!(
            err,
            CertBundleError::VerificationFailed { ref reason, .. }
                if reason == "kernel-verified theorem missing cross-project certificate"
        ));
    }

    #[test]
    fn bundle_replay_checks_the_declared_theorem_type_before_building() {
        let mut env = Environment::with_prelude();
        let name = Name::from_string("Test.falseClaim");
        env.add_decl_structural(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("False"), vec![]),
            value: Expr::const_(Name::from_string("True.intro"), vec![]),
        })
        .expect("structural fixture");

        let mut certs = HashMap::new();
        certs.insert(
            name.clone(),
            ProofCert::Const {
                name: Name::from_string("True.intro"),
                levels: vec![],
                type_: Box::new(Expr::const_(Name::from_string("True"), vec![])),
            },
        );
        let mut xproj = HashMap::new();
        xproj.insert(
            name,
            CrossProjectCert::from_environment(&env, "Test.falseClaim", prover(), vec![])
                .expect("self-authored transport record"),
        );

        let error = CertBundle::build("test", "0.1.0", env, certs, xproj, None)
            .expect_err("transport metadata must not hide a replayed type mismatch");
        // Refused before any replay: the kernel does not re-admit
        // `Test.falseClaim : False := True.intro` into the rebuilt
        // environment, so there is nothing to replay it against.
        assert!(
            matches!(
                error,
                CertBundleError::VerificationFailed { ref reason, .. }
                    if reason.contains("`Test.falseClaim`")
                        && reason.contains("the kernel refused it")
            ),
            "{error}"
        );
    }

    /// `Test.bad : False := Test.fakeFalse`, where `Test.fakeFalse : False :=
    /// True.intro` is a `Theorem`-kind declaration inserted WITHOUT a kernel
    /// check (`add_decl_structural`), with its certificate and transport
    /// record. Returns `(env, certs, xproj)`.
    fn forged_false_parts() -> (
        Environment,
        HashMap<Name, ProofCert>,
        HashMap<Name, CrossProjectCert>,
    ) {
        let mut env = Environment::with_prelude();
        let fake = Name::from_string("Test.fakeFalse");
        let target = Name::from_string("Test.bad");
        let false_ty = Expr::const_(Name::from_string("False"), vec![]);

        env.add_decl_structural(Declaration::Theorem {
            name: fake.clone(),
            level_params: vec![],
            type_: false_ty.clone(),
            value: Expr::const_(Name::from_string("True.intro"), vec![]),
        })
        .expect("structural forged dependency");
        env.add_decl(Declaration::Theorem {
            name: target.clone(),
            level_params: vec![],
            type_: false_ty.clone(),
            value: Expr::const_(fake.clone(), vec![]),
        })
        .expect("target checks against the dependency's advertised type");

        let mut certs = HashMap::new();
        certs.insert(
            target.clone(),
            ProofCert::Const {
                name: fake,
                levels: vec![],
                type_: Box::new(false_ty),
            },
        );
        let mut xproj = HashMap::new();
        xproj.insert(
            target,
            CrossProjectCert::from_environment(&env, "Test.bad", prover(), vec![])
                .expect("transport record"),
        );
        (env, certs, xproj)
    }

    /// The certificate of `theorem` replays against `env` itself — what
    /// verification checked before 2026-09-28.
    fn replays_in_the_authors_environment(
        env: &Environment,
        certs: &HashMap<Name, ProofCert>,
        theorem: &str,
    ) {
        let name = Name::from_string(theorem);
        let decl = env.get_const(&name).expect("declared");
        let value = decl.value.clone().expect("proof term");
        let replayed = CertVerifier::new(env)
            .verify(&certs[&name], &value)
            .expect("the author's environment replays the certificate");
        assert!(
            crate::tc::TypeChecker::new(env).is_def_eq(&replayed, &decl.type_),
            "the replayed type is the declared statement"
        );
    }

    /// A declaration the bundle author inserted without a kernel check fails
    /// every theorem resting on it — at `build`, at `load`, and in the trust
    /// verb over a hand-made file that skipped both — and is disclosed.
    ///
    /// Measured on ad89a748b, where this test asserted the OPPOSITE
    /// (`all_passed() == true`, since f88cde40d): `build` packaged the bundle,
    /// `save` wrote it, `verify_all` passed `Test.bad : False` with
    /// `theorem_assumptions` `Test.bad: []` (the forgery is `Theorem`-kind, so
    /// no axiom list names it), and `clean kernel cert verify` on the file
    /// exited 0, "ALL PASSED".
    #[test]
    fn forged_dependency_cannot_earn_kernel_verified_bundle_trust() {
        let (env, certs, xproj) = forged_false_parts();
        replays_in_the_authors_environment(&env, &certs, "Test.bad");

        let error = CertBundle::build(
            "test",
            "0.1.0",
            env.clone(),
            certs.clone(),
            xproj.clone(),
            None,
        )
        .expect_err("a forged dependency must not be packaged");
        assert!(
            error
                .to_string()
                .contains("`Test.fakeFalse`: the kernel refused it"),
            "{error}"
        );

        // A hand-made file that skipped `build`.
        let view = CertBundle::for_inspection("test", "0.1.0", env, certs, xproj).expect("view");
        let dir = tempfile::tempdir().expect("temp dir");
        let path = dir.path().join("fakefalse.cleancert");
        view.write_archive(&path).expect("write the hand-made file");
        let error = CertBundle::load(&path).expect_err("the trust loader must refuse it");
        assert!(error.to_string().contains("`Test.fakeFalse`"), "{error}");

        // The trust verb fails it, naming the forged dependency.
        let result = view.verify_all().expect("structurally valid bundle");
        assert!(!result.all_passed());
        assert_eq!((result.passed, result.failed), (0, 1));
        assert_eq!(result.trust_level, TrustLevel::Unverified);
        let reason = &result.failures[0].1;
        assert!(
            reason.contains("did not re-derive from the canonical base")
                && reason.contains("`Test.fakeFalse`: the kernel refused it"),
            "{reason}"
        );
        let refusals = &result.environment.refusals;
        assert!(
            refusals.iter().any(
                |(name, why)| name == "Test.fakeFalse" && why.contains("the kernel refused it")
            ),
            "{refusals:?}"
        );
        assert!(
            refusals
                .iter()
                .any(|(name, why)| name == "Test.bad" && why.contains("depends on Test.fakeFalse")),
            "{refusals:?}"
        );
        assert!(result.environment.redefined_base.is_empty());
        // Disclosed: no axiom list names a `Theorem`-kind forgery, the
        // unchecked-dependency list does.
        assert_eq!(
            result.axioms.theorem_assumptions,
            vec![("Test.bad".to_string(), Vec::<String>::new())]
        );
        assert_eq!(
            result.axioms.theorem_unchecked_dependencies,
            vec![(
                "Test.bad".to_string(),
                vec!["Test.bad".to_string(), "Test.fakeFalse".to_string()]
            )]
        );

        // The quarantined read describes the file and still fails it.
        let quarantined = CertBundle::load_for_inspection(&path).expect("quarantined read");
        let diagnostics = quarantined.verify_all_for_inspection();
        assert_eq!((diagnostics.passed, diagnostics.failed), (0, 1));
    }

    /// A refusal fails exactly the theorems whose closure reaches it: an
    /// honest theorem beside the forgery verifies, in the rebuilt
    /// environment, where the forgery does not exist.
    #[test]
    fn a_refused_declaration_fails_only_the_theorems_resting_on_it() {
        let (mut env, mut certs, mut xproj) = forged_false_parts();
        let honest = Name::from_string("Test.trivial");
        let true_ty = Expr::const_(Name::from_string("True"), vec![]);
        env.add_decl(Declaration::Theorem {
            name: honest.clone(),
            level_params: vec![],
            type_: true_ty.clone(),
            value: Expr::const_(Name::from_string("True.intro"), vec![]),
        })
        .expect("honest theorem");
        certs.insert(
            honest.clone(),
            ProofCert::Const {
                name: Name::from_string("True.intro"),
                levels: vec![],
                type_: Box::new(true_ty),
            },
        );
        xproj.insert(
            honest,
            CrossProjectCert::from_environment(&env, "Test.trivial", prover(), vec![])
                .expect("transport record"),
        );
        let view = CertBundle::for_inspection("test", "0.1.0", env, certs, xproj).expect("view");
        let result = view.verify_all().expect("structurally valid bundle");
        assert_eq!(
            (result.passed, result.failed),
            (1, 1),
            "{:?}",
            result.failures
        );
        assert_eq!(result.failures[0].0, "Test.bad");
        assert!(!result.environment.passed());
        assert_eq!(
            result.axioms.theorem_unchecked_dependencies,
            vec![
                (
                    "Test.bad".to_string(),
                    vec!["Test.bad".to_string(), "Test.fakeFalse".to_string()]
                ),
                ("Test.trivial".to_string(), Vec::<String>::new()),
            ]
        );
    }

    /// The names the canonical-statement check reads BY NAME (`Iff` and `Eq`
    /// in `propext`'s statement, `Nonempty` in `Classical.choice`'s, `Eq` in
    /// the quotient's, `Bool` in `sorryAx`'s) and `True` / `False` are pinned
    /// to the canonical prelude's declarations: a bundle holding any of them
    /// with other content fails EVERY theorem, even one that never mentions
    /// it.
    #[test]
    fn a_bundle_cannot_redefine_the_prelude_vocabulary() {
        for vocabulary in ["Iff", "Eq", "Nonempty", "True", "False", "Bool"] {
            let (mut env, certs, xproj) = test_env_and_certs();
            let name = Name::from_string(vocabulary);
            let mut forged = env
                .get_const(&name)
                .expect("the prelude declares it")
                .clone();
            forged.type_ = Expr::sort(crate::Level::succ(crate::Level::succ(crate::Level::zero())));
            env.add_constant_for_test(forged);
            let view =
                CertBundle::for_inspection("test", "0.1.0", env, certs, xproj).expect("view");
            let result = view.verify_all().expect("structurally valid bundle");
            assert_eq!(
                (result.passed, result.failed),
                (0, 1),
                "{vocabulary}: {:?}",
                result.failures
            );
            assert_eq!(
                result.environment.redefined_base,
                vec![format!("family {vocabulary}")],
                "{vocabulary}"
            );
            assert!(
                result.failures[0]
                    .1
                    .contains("redefines canonical prelude declaration(s) family"),
                "{vocabulary}: {:?}",
                result.failures
            );
        }
    }

    /// The attack the vocabulary pin stops, on `False`: an environment whose
    /// `False` has a constructor proves `False`, and the certificate replays
    /// in the author's environment.
    #[test]
    fn an_inhabited_false_in_the_bundle_environment_is_refused() {
        let mut env = Environment::with_prelude();
        let false_name = Name::from_string("False");
        let intro = Name::from_string("False.intro");
        let false_ty = Expr::const_(false_name.clone(), vec![]);
        let mut family = env.get_inductive(&false_name).expect("False").clone();
        family.constructor_names = vec![intro.clone()];
        env.forge_family_records_for_test(
            vec![family],
            vec![crate::inductive::ConstructorVal {
                name: intro.clone(),
                inductive_name: false_name,
                level_params: vec![],
                type_: false_ty.clone(),
                num_params: 0,
                num_fields: 0,
                constructor_idx: 0,
            }],
            vec![],
        );
        env.add_constant_for_test(crate::env::ConstantInfo::new(
            intro.clone(),
            vec![],
            false_ty.clone(),
            None,
            false,
        ));
        let target = Name::from_string("Test.bad");
        env.add_decl(Declaration::Theorem {
            name: target.clone(),
            level_params: vec![],
            type_: false_ty.clone(),
            value: Expr::const_(intro.clone(), vec![]),
        })
        .expect("checks in the forged environment");
        let mut certs = HashMap::new();
        certs.insert(
            target,
            ProofCert::Const {
                name: intro,
                levels: vec![],
                type_: Box::new(false_ty),
            },
        );
        replays_in_the_authors_environment(&env, &certs, "Test.bad");

        let view =
            CertBundle::for_inspection("test", "0.1.0", env, certs, HashMap::new()).expect("view");
        let result = view.verify_all().expect("structurally valid bundle");
        assert_eq!((result.passed, result.failed), (0, 1));
        assert_eq!(
            result.environment.redefined_base,
            vec!["family False".to_string()]
        );
    }

    /// The attack the vocabulary pin stops, on `Iff`: with a field-less
    /// `Iff.intro`, `propext` — still the kernel's canonical declaration BY
    /// ITS STATEMENT, which names `Iff` — proves `True = False`.
    #[test]
    fn a_trivialized_iff_does_not_let_propext_prove_true_eq_false() {
        use crate::expr::BinderInfo;
        let mut env = Environment::with_prelude();
        let iff = Name::from_string("Iff");
        let intro = Name::from_string("Iff.intro");
        let prop = Expr::prop();
        let forged_ty = Expr::pi(
            BinderInfo::Implicit,
            prop.clone(),
            Expr::pi(
                BinderInfo::Implicit,
                prop.clone(),
                Expr::apps(Expr::const_(iff, vec![]), [Expr::bvar(1), Expr::bvar(0)]),
            ),
        );
        let mut ctor = env.get_constructor(&intro).expect("Iff.intro").clone();
        ctor.type_ = forged_ty.clone();
        ctor.num_fields = 0;
        env.forge_family_records_for_test(vec![], vec![ctor], vec![]);
        let mut info = env.get_const(&intro).expect("Iff.intro").clone();
        info.type_ = forged_ty;
        env.add_constant_for_test(info);

        let t = Expr::const_(Name::from_string("True"), vec![]);
        let f = Expr::const_(Name::from_string("False"), vec![]);
        let true_eq_false = Expr::apps(
            Expr::const_(
                Name::from_string("Eq"),
                vec![crate::Level::succ(crate::Level::zero())],
            ),
            [prop, t.clone(), f.clone()],
        );
        let helper = Name::from_string("Test.helper");
        env.add_decl(Declaration::Theorem {
            name: helper.clone(),
            level_params: vec![],
            type_: true_eq_false.clone(),
            value: Expr::apps(
                Expr::const_(Name::from_string("propext"), vec![]),
                [
                    t.clone(),
                    f.clone(),
                    Expr::apps(Expr::const_(intro, vec![]), [t, f]),
                ],
            ),
        })
        .expect("propext's statement reads the forged Iff");
        let target = Name::from_string("Test.bad");
        env.add_decl(Declaration::Theorem {
            name: target.clone(),
            level_params: vec![],
            type_: true_eq_false.clone(),
            value: Expr::const_(helper.clone(), vec![]),
        })
        .expect("target");
        // The name-level canonical checks cannot see it: `propext` is
        // untouched and its statement still names `Iff`.
        assert!(env.is_canonical_foundational_axiom(&Name::from_string("propext")));
        assert!(env.non_canonical_ambient_declarations().is_empty());
        let mut certs = HashMap::new();
        certs.insert(
            target,
            ProofCert::Const {
                name: helper,
                levels: vec![],
                type_: Box::new(true_eq_false),
            },
        );
        replays_in_the_authors_environment(&env, &certs, "Test.bad");

        let view =
            CertBundle::for_inspection("test", "0.1.0", env, certs, HashMap::new()).expect("view");
        let result = view.verify_all().expect("structurally valid bundle");
        assert_eq!((result.passed, result.failed), (0, 1));
        assert_eq!(
            result.environment.redefined_base,
            vec!["family Iff".to_string()]
        );
    }

    /// A bundle declaring an inductive family: honest, it is re-admitted with
    /// its recursors regenerated; with the ι-rules of its recursor swapped
    /// (`Two.rec` computing the wrong branch), the regenerated rule refuses
    /// it and everything resting on the family.
    #[test]
    fn a_bundle_family_is_readmitted_with_its_recursor_regenerated() {
        use crate::inductive::{Constructor, InductiveDecl, InductiveType};
        for tamper in [false, true] {
            let mut env = Environment::with_prelude();
            let two = Name::from_string("Test.Two");
            let a = Name::from_string("Test.Two.a");
            let ty = Expr::const_(two.clone(), vec![]);
            env.add_inductive(InductiveDecl {
                level_params: vec![],
                num_params: 0,
                types: vec![InductiveType {
                    name: two.clone(),
                    type_: Expr::sort(crate::Level::succ(crate::Level::zero())),
                    constructors: vec![
                        Constructor {
                            name: a.clone(),
                            type_: ty.clone(),
                        },
                        Constructor {
                            name: Name::from_string("Test.Two.b"),
                            type_: ty.clone(),
                        },
                    ],
                }],
            })
            .expect("family");
            if tamper {
                let rec_name = Name::from_string("Test.Two.rec");
                let mut rec = env.get_recursor(&rec_name).expect("Two.rec").clone();
                let first = rec.rules[0].rhs.clone();
                rec.rules[0].rhs = rec.rules[1].rhs.clone();
                rec.rules[1].rhs = first;
                env.forge_family_records_for_test(vec![], vec![], vec![rec]);
            }
            let a_eq_a = Expr::apps(
                Expr::const_(
                    Name::from_string("Eq"),
                    vec![crate::Level::succ(crate::Level::zero())],
                ),
                [
                    ty.clone(),
                    Expr::const_(a.clone(), vec![]),
                    Expr::const_(a.clone(), vec![]),
                ],
            );
            let helper = Name::from_string("Test.helper");
            env.add_decl(Declaration::Theorem {
                name: helper.clone(),
                level_params: vec![],
                type_: a_eq_a.clone(),
                value: Expr::apps(
                    Expr::const_(
                        Name::from_string("Eq.refl"),
                        vec![crate::Level::succ(crate::Level::zero())],
                    ),
                    [ty.clone(), Expr::const_(a.clone(), vec![])],
                ),
            })
            .expect("helper");
            let target = Name::from_string("Test.refl");
            env.add_decl(Declaration::Theorem {
                name: target.clone(),
                level_params: vec![],
                type_: a_eq_a.clone(),
                value: Expr::const_(helper.clone(), vec![]),
            })
            .expect("target");
            let mut certs = HashMap::new();
            certs.insert(
                target,
                ProofCert::Const {
                    name: helper,
                    levels: vec![],
                    type_: Box::new(a_eq_a),
                },
            );
            let view = CertBundle::for_inspection("test", "0.1.0", env, certs, HashMap::new())
                .expect("view");
            let result = view.verify_all().expect("structurally valid bundle");
            if tamper {
                assert_eq!((result.passed, result.failed), (0, 1));
                assert!(
                    result.environment.refusals.iter().any(|(name, why)| {
                        name == "family Test.Two"
                            && why.contains("Test.Two.rec")
                            && why.contains("ι-rule right-hand side")
                    }),
                    "{:?}",
                    result.environment
                );
            } else {
                assert!(result.all_passed(), "{:?}", result.failures);
                assert!(result.environment.passed(), "{:?}", result.environment);
                assert_eq!(result.environment.families_readmitted, 1);
            }
        }
    }

    /// Every name the kernel reduces or builds by name that the canonical
    /// base does NOT hold is refused outside the base: the declared meaning
    /// and the built-in one would both be live. (One the base holds is pinned
    /// to the base's declaration instead, as every base name is.)
    #[test]
    fn a_kernel_by_name_constant_outside_the_base_is_refused() {
        let base = Environment::with_prelude();
        let absent: Vec<&str> = crate::cert::KERNEL_BY_NAME_CONSTANTS
            .iter()
            .copied()
            .filter(|n| base.get_const(&Name::from_string(n)).is_none())
            .collect();
        // Measured 2026-09-28: Nat.gcd, Lean.reduceBool, Lean.reduceNat,
        // optParam, autoParam, semiOutParam. Never vacuous.
        assert!(
            !absent.is_empty(),
            "every by-name constant is in the base; this test would test nothing"
        );
        for key in absent {
            let (mut env, mut certs, _) = test_env_and_certs();
            let name = Name::from_string(key);
            let nat = Expr::const_(Name::from_string("Nat"), vec![]);
            env.add_decl(Declaration::Axiom {
                name: name.clone(),
                level_params: vec![],
                type_: nat.clone(),
            })
            .expect("the author's environment accepts it");
            let target = Name::from_string("Test.usesKey");
            let nat_eq = Expr::apps(
                Expr::const_(
                    Name::from_string("Eq"),
                    vec![crate::Level::succ(crate::Level::zero())],
                ),
                [
                    nat.clone(),
                    Expr::const_(name.clone(), vec![]),
                    Expr::const_(name.clone(), vec![]),
                ],
            );
            let helper = Name::from_string("Test.keyHelper");
            env.add_decl(Declaration::Theorem {
                name: helper.clone(),
                level_params: vec![],
                type_: nat_eq.clone(),
                value: Expr::apps(
                    Expr::const_(
                        Name::from_string("Eq.refl"),
                        vec![crate::Level::succ(crate::Level::zero())],
                    ),
                    [nat, Expr::const_(name.clone(), vec![])],
                ),
            })
            .expect("helper");
            env.add_decl(Declaration::Theorem {
                name: target.clone(),
                level_params: vec![],
                type_: nat_eq.clone(),
                value: Expr::const_(helper.clone(), vec![]),
            })
            .expect("target");
            certs.insert(
                target,
                ProofCert::Const {
                    name: helper,
                    levels: vec![],
                    type_: Box::new(nat_eq),
                },
            );
            let view = CertBundle::for_inspection("test", "0.1.0", env, certs, HashMap::new())
                .expect("view");
            let result = view.verify_all().expect("structurally valid bundle");
            assert!(
                result.failures.iter().any(|(t, _)| t == "Test.usesKey"),
                "{key}: {:?}",
                result.failures
            );
            assert!(
                result.environment.refusals.iter().any(|(n, why)| {
                    *n == name.to_unambiguous_string()
                        && why.contains("the kernel reduces or builds by name")
                }),
                "{key}: {:?}",
                result.environment
            );
        }
    }

    #[test]
    fn explicit_domain_axiom_is_classified_as_axiom_not_kernel_verified() {
        let mut env = Environment::with_prelude();
        let axiom = Name::from_string("Test.domainAssumption");
        let target = Name::from_string("Test.usesDomainAssumption");
        let true_ty = Expr::const_(Name::from_string("True"), vec![]);
        env.add_decl(Declaration::Axiom {
            name: axiom.clone(),
            level_params: vec![],
            type_: true_ty.clone(),
        })
        .expect("domain axiom");
        env.add_decl(Declaration::Theorem {
            name: target.clone(),
            level_params: vec![],
            type_: true_ty.clone(),
            value: Expr::const_(axiom.clone(), vec![]),
        })
        .expect("axiom-dependent theorem");

        let mut certs = HashMap::new();
        certs.insert(
            target.clone(),
            ProofCert::Const {
                name: axiom,
                levels: vec![],
                type_: Box::new(true_ty),
            },
        );
        let mut xproj = HashMap::new();
        xproj.insert(
            target,
            CrossProjectCert::from_environment(&env, "Test.usesDomainAssumption", prover(), vec![])
                .expect("transport record"),
        );

        let bundle = CertBundle::build("test", "0.1.0", env, certs, xproj, None).expect("bundle");
        let result = bundle.verify_all().expect("verification result");
        assert!(result.all_passed());
        assert_eq!(result.trust_level, TrustLevel::Axiom);
    }

    /// A theorem proved from `axiom <spoof> : True` in a prelude env, with its
    /// certificate. Returns `(env, certs, theorem)`.
    fn env_with_axiom_backed_theorem(
        axiom: &Name,
    ) -> (Environment, HashMap<Name, ProofCert>, Name) {
        let mut env = Environment::with_prelude();
        let target = Name::from_string("Test.bad");
        let true_ty = Expr::const_(Name::from_string("True"), vec![]);
        env.add_decl(Declaration::Axiom {
            name: axiom.clone(),
            level_params: vec![],
            type_: true_ty.clone(),
        })
        .expect("axiom fixture");
        env.add_decl(Declaration::Theorem {
            name: target.clone(),
            level_params: vec![],
            type_: true_ty.clone(),
            value: Expr::const_(axiom.clone(), vec![]),
        })
        .expect("axiom-backed theorem");
        let mut certs = HashMap::new();
        certs.insert(
            target.clone(),
            ProofCert::Const {
                name: axiom.clone(),
                levels: vec![],
                type_: Box::new(true_ty),
            },
        );
        (env, certs, target)
    }

    /// `kernel cert verify` discloses every axiom of the bundle environment
    /// and each theorem's assumptions: a replay that passes relative to a user
    /// axiom (here the fictional `proofIrrel`, once whitelisted by name) says
    /// so, instead of reading as a clean pass.
    #[test]
    fn verify_all_discloses_every_environment_axiom_and_theorem_assumption() {
        let axiom = Name::from_string("proofIrrel");
        let (env, certs, target) = env_with_axiom_backed_theorem(&axiom);
        let bundle =
            CertBundle::build("test", "0.1.0", env, certs, HashMap::new(), None).expect("bundle");
        let result = bundle.verify_all().expect("verification result");
        assert!(result.all_passed());
        assert!(result.axioms.non_canonical_ambient.is_empty());
        assert_eq!(
            result
                .axioms
                .other_axioms
                .iter()
                .filter(|a| *a == "proofIrrel")
                .count(),
            1
        );
        assert!(!result
            .axioms
            .canonical_foundations
            .contains(&"proofIrrel".to_string()));
        for foundation in ["propext", "Quot.sound", "Classical.choice"] {
            assert!(
                result
                    .axioms
                    .canonical_foundations
                    .contains(&foundation.to_string()),
                "{foundation} is disclosed as a canonical foundation"
            );
        }
        assert_eq!(
            result.axioms.theorem_assumptions,
            vec![(target.to_string(), vec!["proofIrrel".to_string()])]
        );
        assert_eq!(bundle.axiom_disclosure(), result.axioms);
    }

    /// A declaration whose ONE component prints as a kernel-owned axiom
    /// (`«Quot.sound»`) poisons every verdict replayed in its environment: the
    /// trust constructor refuses to package it, and a view of it fails every
    /// theorem, naming the spoof unambiguously.
    #[test]
    fn bundle_with_printed_form_foundation_spoof_is_refused_and_fails_verification() {
        let spoof = Name::anon().str("Quot.sound");
        let (env, certs, target) = env_with_axiom_backed_theorem(&spoof);
        let error = CertBundle::build(
            "test",
            "0.1.0",
            env.clone(),
            certs.clone(),
            HashMap::new(),
            None,
        )
        .expect_err("a spoofed reserved name must not be packaged");
        assert!(error.to_string().contains("«Quot.sound»"), "{error}");

        let view = CertBundle::for_inspection("test", "0.1.0", env, certs, HashMap::new())
            .expect("diagnostics view");
        let result = view.verify_all_for_inspection();
        assert_eq!(result.passed, 0);
        assert_eq!(result.failed, 1);
        assert!(result.failures[0].1.contains("«Quot.sound»"));
        assert_eq!(
            result
                .axioms
                .non_canonical_ambient
                .iter()
                .map(|(name, _)| name.as_str())
                .collect::<Vec<_>>(),
            vec!["«Quot.sound»"]
        );
        assert!(result
            .axioms
            .other_axioms
            .contains(&"«Quot.sound»".to_string()));
        assert!(view.verify_theorem(&target).is_err());
    }

    #[test]
    fn verify_all_never_reports_manifest_trust_after_replay_failure() {
        let (env, certs, xproj_certs) = test_env_and_certs();
        let mut bundle = CertBundle::build("test-project", "0.1.0", env, certs, xproj_certs, None)
            .expect("build bundle");
        bundle.certs.insert(
            Name::from_string("Test.trivial"),
            ProofCert::Sort {
                level: crate::Level::zero(),
            },
        );

        let result = bundle
            .verify_all()
            .expect("metadata remains internally valid");
        assert_eq!(result.passed, 0);
        assert_eq!(result.failed, 1);
        assert_eq!(result.trust_level, TrustLevel::Unverified);
    }

    #[test]
    fn manifest_cannot_claim_established_trust() {
        let (env, certs, xproj_certs) = test_env_and_certs();
        let mut bundle = CertBundle::build("test-project", "0.1.0", env, certs, xproj_certs, None)
            .expect("build bundle");
        bundle.manifest.theorems[0].trust_level = TrustLevel::KernelVerified;
        bundle.manifest.trust_level = TrustLevel::KernelVerified;

        assert!(matches!(
            bundle.verify_all(),
            Err(CertBundleError::InvalidManifest(message))
                if message.contains("does not match certificate evidence")
        ));
    }

    #[test]
    fn bundle_loader_rejects_trailing_or_concatenated_zstd_data() {
        use std::io::Write as _;

        let (env, certs, xproj_certs) = test_env_and_certs();
        let bundle = CertBundle::build("test-project", "0.1.0", env, certs, xproj_certs, None)
            .expect("build bundle");
        let dir = tempfile::tempdir().expect("temp dir");

        for (index, suffix) in [
            vec![0x42],
            zstd::encode_all(&b"second frame"[..], 3).expect("second zstd frame"),
        ]
        .into_iter()
        .enumerate()
        {
            let path = dir.path().join(format!("bad-{index}.cleancert"));
            bundle.save(&path).expect("save bundle");
            std::fs::OpenOptions::new()
                .append(true)
                .open(&path)
                .expect("open append")
                .write_all(&suffix)
                .expect("append suffix");
            assert!(matches!(
                CertBundle::load(&path),
                Err(CertBundleError::Compression(message))
                    if message.contains("trailing bytes")
            ));
        }
    }

    #[test]
    fn test_trust_min_ordering() {
        assert_eq!(
            trust_min(TrustLevel::KernelVerified, TrustLevel::Axiom),
            TrustLevel::Axiom
        );
        assert_eq!(
            trust_min(TrustLevel::Unverified, TrustLevel::KernelVerified),
            TrustLevel::Unverified
        );
        assert_eq!(
            trust_min(TrustLevel::SmtBacked, TrustLevel::SmtBacked),
            TrustLevel::SmtBacked
        );
    }

    #[test]
    fn test_sha256_hex_deterministic() {
        let a = sha256_hex(b"hello");
        let b = sha256_hex(b"hello");
        assert_eq!(a, b);
        assert_eq!(a.len(), 64);
        // Known SHA-256 of "hello"
        assert_eq!(
            a,
            "2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824"
        );
    }
}
