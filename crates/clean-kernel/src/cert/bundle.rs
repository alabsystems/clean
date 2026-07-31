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
        };
        validate_bundle_contents(
            &bundle.manifest,
            &bundle.env,
            &bundle.certs,
            &bundle.xproj_certs,
        )?;
        bundle.ensure_all_replay_valid()?;
        Ok(bundle)
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
    pub fn load(path: impl AsRef<Path>) -> Result<Self, CertBundleError> {
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

        validate_bundle_contents(&archive.manifest, &env, &certs, &xproj_certs)?;

        let bundle = Self {
            manifest: archive.manifest,
            env,
            certs,
            xproj_certs,
            trust_chain: archive.trust_chain,
        };
        bundle.ensure_all_replay_valid()?;
        Ok(bundle)
    }

    // ── Verification ─────────────────────────────────────────────────────

    /// Verify all certificates in the bundle against the embedded environment.
    pub fn verify_all(&self) -> Result<BundleVerifyResult, CertBundleError> {
        validate_bundle_contents(&self.manifest, &self.env, &self.certs, &self.xproj_certs)?;
        let mut passed = 0usize;
        let mut failed = 0usize;
        let mut failures = Vec::new();
        let mut verified_trust = Vec::with_capacity(self.manifest.theorems.len());

        for entry in &self.manifest.theorems {
            let name = Name::from_string(&entry.name);
            match self.verify_single(&name) {
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

        Ok(BundleVerifyResult {
            passed,
            failed,
            failures,
            trust_level: verified_trust
                .into_iter()
                .reduce(trust_min)
                .unwrap_or(TrustLevel::Unverified),
        })
    }

    /// Verify a single named theorem.
    pub fn verify_theorem(&self, name: &Name) -> Result<(), CertBundleError> {
        self.verify_single(name).map(|_| ())
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

        // Look up the declaration in the environment.
        let decl = self
            .env
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
        let mut verifier = CertVerifier::new(&self.env);
        let verified_type =
            verifier
                .verify(cert, value)
                .map_err(|e| CertBundleError::VerificationFailed {
                    name: name.to_string(),
                    reason: e.to_string(),
                })?;
        if !verifier.def_eq(&verified_type, &decl.type_) {
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
                .verify(&self.env)
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
        let audit = self.env.audit_certification(&decl.type_, value);
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
        !proof.has_sorry(),
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

        let result = loaded.verify_all().expect("verify_all after load");
        assert!(result.all_passed(), "failures: {:?}", result.failures);
        assert_eq!(
            result.trust_level,
            TrustLevel::Unverified,
            "deserialization must not mint transient kernel-object provenance"
        );
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
        let env_bytes =
            bincode::serde::encode_to_vec(&env, bincode::config::standard()).expect("encode env");
        let bundle = CertBundle {
            manifest: CertBundleManifest {
                version: BUNDLE_VERSION,
                project: "inspection-only".to_string(),
                clean_version: "0.1.0".to_string(),
                env_hash: sha256_hex(&env_bytes),
                theorems: vec![CertBundleEntry {
                    name: "Test.assumed".to_string(),
                    type_hash: String::new(),
                    proof_hash: String::new(),
                    trust_level: TrustLevel::Unverified,
                    sorry_free: true,
                }],
                trust_level: TrustLevel::Unverified,
            },
            env,
            certs,
            xproj_certs: HashMap::new(),
            trust_chain: None,
        };

        let report = bundle.inspect();
        let entry = &report.entries[0];
        assert_eq!(entry.declaration_kind, Some("axiom"));
        assert_eq!(entry.theorem_type.as_deref(), Some("True"));
        assert!(entry.has_certificate);
        assert!(entry.has_environment_declaration);
        assert!(!entry.has_proof_term);
        assert_eq!(entry.issues, vec![BundleInspectIssue::MissingProofTerm]);
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
        assert!(matches!(
            error,
            CertBundleError::VerificationFailed { ref reason, .. }
                if reason.contains("does not match declaration type")
        ));
    }

    #[test]
    fn forged_dependency_cannot_earn_kernel_verified_bundle_trust() {
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

        let bundle =
            CertBundle::build("test", "0.1.0", env, certs, xproj, None).expect("replay succeeds");
        let result = bundle.verify_all().expect("verification result");
        assert!(result.all_passed(), "certificate replay should still pass");
        assert_eq!(
            result.trust_level,
            TrustLevel::Unverified,
            "the rooted audit must expose the forged dependency"
        );
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
