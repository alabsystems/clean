// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Production [`SigningBackend`] backed by **GCP Cloud KMS asymmetric signing**.
//!
//! # Why KMS (the trust story)
//!
//! The signing root must never live in the repo, in a container image, or on
//! the public front-end. With KMS the private key lives in Google's HSM and the
//! publisher (the sole minter, see [`crate::trust_sign::publisher`]) only ever
//! *calls* `asymmetricSign`. A repo or operator compromise can, at worst,
//! mis-call the key — and even a mis-signed verdict is caught by the consumer's
//! own kernel re-check, because the signature attests **provenance**, not truth.
//!
//! # Offline-feasible implementation: shell out to `gcloud`
//!
//! There is no pure-Rust GCP KMS client in `Cargo.lock` (adding one would mutate
//! the lock, which this lane forbids). The publisher host has the `gcloud` CLI
//! and KMS access, so [`GcpKmsBackend`] shells out to
//! `gcloud kms asymmetric-sign`. The argv is fully deterministic and
//! [tested without a live call](#tests) by injecting a [`CommandRunner`].
//!
//! > **REST alternative (documented, not the offline impl):** the same operation
//! > is `POST .../cryptoKeyVersions/{v}:asymmetricSign` with a base64 `digest`
//! > body; the response carries a base64 `signature`. If a future lane vendors a
//! > pure-Rust GCP client (or a thin reqwest+oauth caller) in the lock, the
//! > [`CommandRunner`] seam lets it replace the shell-out without touching the
//! > [`SigningBackend`] trait, the schema, or any caller. Prefer the vendored
//! > client when it lands; until then the shell-out is the real implementation.
//!
//! # Verification needs NO KMS calls
//!
//! [`GcpKmsVerifier`] holds the KMS **public key** (fetched once via
//! `gcloud kms keys versions get-public-key`, then cached/published with the
//! Core) and verifies locally over `ring`. Consumers and the service therefore
//! verify offline; only the publisher ever talks to KMS.
//!
//! See `designs/2026-06-24-mathverse-phase2-trust-the-archive.md` §3.2 / §7 for
//! the keyring/key/IAM setup.

use std::process::Command;

use ring::signature::{
    UnparsedPublicKey, ECDSA_P256_SHA256_ASN1, ED25519, RSA_PKCS1_2048_8192_SHA256,
};

use super::backend::{SigningBackend, SigningError, VerifyingBackend};
use super::gcp_kms_der::{pem_to_der, spki_to_ring_public_key};

/// The KMS asymmetric-sign key algorithm family this backend understands. Each
/// maps to a GCP `CryptoKeyVersionAlgorithm`, a `gcloud --digest-algorithm`
/// flag, and the `sig_alg` label written into the signed verdict.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum GcpKmsKeyType {
    /// `EC_SIGN_ED25519` — preferred; matches the local Ed25519 backend so the
    /// on-disk `sig_alg` is identical. The "digest" is the message itself
    /// (Ed25519 is not prehashed): `gcloud` takes `--input-file`, no digest.
    Ed25519,
    /// `RSA_SIGN_PKCS1_2048_SHA256` (and the 3072/4096 SHA-256 siblings) —
    /// RSASSA-PKCS1-v1_5 over a SHA-256 prehash.
    RsaPkcs1Sha256,
    /// `EC_SIGN_P256_SHA256` — ECDSA over P-256 with a SHA-256 prehash; the
    /// signature is ASN.1/DER (KMS's encoding).
    EcdsaP256Sha256,
}

impl GcpKmsKeyType {
    /// The `sig_alg` label written into the record (a verifier selects its
    /// backend by this label).
    #[must_use]
    pub fn sig_alg(self) -> &'static str {
        match self {
            Self::Ed25519 => "ed25519",
            Self::RsaPkcs1Sha256 => "rsa-pkcs1-sha256",
            Self::EcdsaP256Sha256 => "ecdsa-p256-sha256",
        }
    }

    /// The GCP `CryptoKeyVersionAlgorithm` digest family. `None` for Ed25519,
    /// which signs the raw message (no prehash). `Some("sha256")` for the
    /// prehashed families — this is the `gcloud --digest-algorithm` value.
    #[must_use]
    pub fn digest_algorithm(self) -> Option<&'static str> {
        match self {
            Self::Ed25519 => None,
            Self::RsaPkcs1Sha256 | Self::EcdsaP256Sha256 => Some("sha256"),
        }
    }

    /// Parse a key type from its `sig_alg` label.
    #[must_use]
    pub fn from_sig_alg(label: &str) -> Option<Self> {
        match label {
            "ed25519" => Some(Self::Ed25519),
            "rsa-pkcs1-sha256" => Some(Self::RsaPkcs1Sha256),
            "ecdsa-p256-sha256" => Some(Self::EcdsaP256Sha256),
            _ => None,
        }
    }
}

/// The fully-qualified Cloud KMS crypto-key-version resource. Every component is
/// part of the resource name; `key_id` embeds the whole path so a rotated key
/// (a new `version`) stays attributable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GcpKmsConfig {
    pub project: String,
    pub location: String,
    pub keyring: String,
    pub key: String,
    pub version: String,
    pub key_type: GcpKmsKeyType,
}

impl GcpKmsConfig {
    /// Build a config from explicit components.
    #[must_use]
    pub fn new(
        project: impl Into<String>,
        location: impl Into<String>,
        keyring: impl Into<String>,
        key: impl Into<String>,
        version: impl Into<String>,
        key_type: GcpKmsKeyType,
    ) -> Self {
        Self {
            project: project.into(),
            location: location.into(),
            keyring: keyring.into(),
            key: key.into(),
            version: version.into(),
            key_type,
        }
    }

    /// Read the KMS configuration from the process environment:
    /// `MATHVERSE_KMS_PROJECT`, `_LOCATION`, `_KEYRING`, `_KEY`, `_VERSION`,
    /// and `_KEY_TYPE` (one of `ed25519` | `rsa-pkcs1-sha256` |
    /// `ecdsa-p256-sha256`; default `ed25519`).
    ///
    /// # Errors
    /// Returns [`SigningError::Key`] if any of the five required components is
    /// unset/empty, or if `MATHVERSE_KMS_KEY_TYPE` is set to an unknown label.
    pub fn from_env() -> Result<Self, SigningError> {
        fn req(name: &str) -> Result<String, SigningError> {
            std::env::var(name)
                .ok()
                .filter(|s| !s.is_empty())
                .ok_or_else(|| {
                    SigningError::Key(format!("{name} must be set for the gcp-kms backend"))
                })
        }
        let key_type = match std::env::var("MATHVERSE_KMS_KEY_TYPE") {
            Ok(s) if !s.is_empty() => GcpKmsKeyType::from_sig_alg(&s).ok_or_else(|| {
                SigningError::Key(format!("unknown MATHVERSE_KMS_KEY_TYPE `{s}`"))
            })?,
            _ => GcpKmsKeyType::Ed25519,
        };
        Ok(Self {
            project: req("MATHVERSE_KMS_PROJECT")?,
            location: req("MATHVERSE_KMS_LOCATION")?,
            keyring: req("MATHVERSE_KMS_KEYRING")?,
            key: req("MATHVERSE_KMS_KEY")?,
            version: req("MATHVERSE_KMS_VERSION")?,
            key_type,
        })
    }

    /// The full crypto-key-version resource name. This is also the `key_id`
    /// embedded in every signed verdict.
    #[must_use]
    pub fn resource_name(&self) -> String {
        format!(
            "projects/{}/locations/{}/keyRings/{}/cryptoKeys/{}/cryptoKeyVersions/{}",
            self.project, self.location, self.keyring, self.key, self.version
        )
    }

    /// The `gcloud kms asymmetric-sign` argv that signs `input_file`, writing the
    /// raw signature to `signature_file`. Deterministic and unit-tested without
    /// a live call.
    #[must_use]
    pub fn sign_argv(&self, input_file: &str, signature_file: &str) -> Vec<String> {
        let mut argv = vec![
            "kms".to_string(),
            "asymmetric-sign".to_string(),
            format!("--location={}", self.location),
            format!("--keyring={}", self.keyring),
            format!("--key={}", self.key),
            format!("--version={}", self.version),
            format!("--project={}", self.project),
            format!("--input-file={input_file}"),
            format!("--signature-file={signature_file}"),
        ];
        if let Some(digest) = self.key_type.digest_algorithm() {
            argv.push(format!("--digest-algorithm={digest}"));
        }
        argv
    }

    /// The `gcloud kms keys versions get-public-key` argv that writes the SPKI
    /// PEM public key to `output_file`. Run once to seed [`GcpKmsVerifier`].
    #[must_use]
    pub fn get_public_key_argv(&self, output_file: &str) -> Vec<String> {
        vec![
            "kms".to_string(),
            "keys".to_string(),
            "versions".to_string(),
            "get-public-key".to_string(),
            self.version.clone(),
            format!("--location={}", self.location),
            format!("--keyring={}", self.keyring),
            format!("--key={}", self.key),
            format!("--project={}", self.project),
            format!("--output-file={output_file}"),
        ]
    }
}

/// Runs the `gcloud` argv. The default [`GcloudCommandRunner`] shells out; tests
/// inject a fake so the argv is asserted WITHOUT a live KMS call or credentials.
pub trait CommandRunner: Send + Sync {
    /// Invoke `gcloud <args...>` after the caller has written the input file.
    /// On success the raw signature bytes must have been written to the
    /// `--signature-file` path the caller chose; this returns those bytes.
    ///
    /// `signature_file` is the path the caller passed in the argv; the runner
    /// reads it back after `gcloud` exits. Returns [`SigningError::Sign`] on a
    /// non-zero exit or an unreadable signature.
    fn run_sign(&self, args: &[String], signature_file: &str) -> Result<Vec<u8>, SigningError>;
}

/// The real runner: spawns `gcloud` and reads the signature file it wrote.
#[derive(Clone, Copy, Debug, Default)]
pub struct GcloudCommandRunner;

impl CommandRunner for GcloudCommandRunner {
    fn run_sign(&self, args: &[String], signature_file: &str) -> Result<Vec<u8>, SigningError> {
        let output = Command::new("gcloud")
            .args(args)
            .output()
            .map_err(|e| SigningError::Sign(format!("spawn gcloud: {e}")))?;
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(SigningError::Sign(format!(
                "gcloud kms asymmetric-sign exited {}: {}",
                output.status, stderr
            )));
        }
        std::fs::read(signature_file)
            .map_err(|e| SigningError::Sign(format!("read signature file {signature_file}: {e}")))
    }
}

/// A GCP Cloud KMS asymmetric-signing backend. The private key never leaves
/// Google's HSM; this only *calls* KMS. `is_asymmetric() == true`.
pub struct GcpKmsBackend {
    key_id: String,
    config: GcpKmsConfig,
    runner: Box<dyn CommandRunner>,
}

impl GcpKmsBackend {
    /// Build a backend that shells out to the real `gcloud` CLI.
    #[must_use]
    pub fn new(config: GcpKmsConfig) -> Self {
        Self::with_runner(config, Box::new(GcloudCommandRunner))
    }

    /// Build a backend with a custom [`CommandRunner`] (used in tests to assert
    /// the argv without a live call, or by a future vendored REST client).
    #[must_use]
    pub fn with_runner(config: GcpKmsConfig, runner: Box<dyn CommandRunner>) -> Self {
        Self {
            key_id: format!("gcp-kms:{}", config.resource_name()),
            config,
            runner,
        }
    }

    /// The config (key resource + type).
    #[must_use]
    pub fn config(&self) -> &GcpKmsConfig {
        &self.config
    }
}

impl SigningBackend for GcpKmsBackend {
    fn key_id(&self) -> &str {
        &self.key_id
    }

    fn sig_alg(&self) -> &str {
        self.config.key_type.sig_alg()
    }

    fn is_asymmetric(&self) -> bool {
        true
    }

    fn sign(&self, canonical_bytes: &[u8]) -> Result<Vec<u8>, SigningError> {
        // Write the message to a tempfile, hand the path to gcloud, read the
        // raw signature back. We never pass the message on argv (it can be
        // large / contain bytes the shell would mangle).
        let dir = tempfile_dir()?;
        let input_path = dir.path().join("verdict.bin");
        let sig_path = dir.path().join("verdict.sig");
        let input_str = path_str(&input_path)?;
        let sig_str = path_str(&sig_path)?;
        std::fs::write(&input_path, canonical_bytes)
            .map_err(|e| SigningError::Sign(format!("write KMS input file: {e}")))?;
        let argv = self.config.sign_argv(&input_str, &sig_str);
        self.runner.run_sign(&argv, &sig_str)
    }
}

/// The verifier counterpart: holds only the KMS PUBLIC key (SPKI), so consumers
/// verify offline with NO KMS calls. Built from the PEM `gcloud … get-public-key`
/// returns, then cached/published with the Core.
#[derive(Clone, Debug)]
pub struct GcpKmsVerifier {
    key_id: String,
    key_type: GcpKmsKeyType,
    /// Raw public-key bytes in the form `ring` expects: a 32-byte key for
    /// Ed25519, the uncompressed SEC1 point for ECDSA, or the PKCS#1
    /// `RSAPublicKey` DER for RSA.
    ring_public_key: Vec<u8>,
}

impl GcpKmsVerifier {
    /// Build a verifier from a `key_id`, the key type, and the SPKI PEM the KMS
    /// `get-public-key` call returns (the `-----BEGIN PUBLIC KEY-----` block).
    ///
    /// # Errors
    /// [`SigningError::Key`] if the PEM is malformed or its SPKI does not carry
    /// the public key in the shape `ring` needs for `key_type`.
    pub fn from_spki_pem(
        key_id: impl Into<String>,
        key_type: GcpKmsKeyType,
        spki_pem: &str,
    ) -> Result<Self, SigningError> {
        let der = pem_to_der(spki_pem, "PUBLIC KEY")?;
        let ring_public_key = spki_to_ring_public_key(&der, key_type)?;
        Ok(Self {
            key_id: key_id.into(),
            key_type,
            ring_public_key,
        })
    }
}

impl VerifyingBackend for GcpKmsVerifier {
    fn key_id(&self) -> &str {
        &self.key_id
    }

    fn sig_alg(&self) -> &str {
        self.key_type.sig_alg()
    }

    fn is_asymmetric(&self) -> bool {
        true
    }

    fn verify(&self, canonical_bytes: &[u8], signature: &[u8]) -> Result<(), SigningError> {
        let key = &self.ring_public_key;
        let result = match self.key_type {
            GcpKmsKeyType::Ed25519 => {
                UnparsedPublicKey::new(&ED25519, key).verify(canonical_bytes, signature)
            }
            GcpKmsKeyType::RsaPkcs1Sha256 => {
                UnparsedPublicKey::new(&RSA_PKCS1_2048_8192_SHA256, key)
                    .verify(canonical_bytes, signature)
            }
            GcpKmsKeyType::EcdsaP256Sha256 => UnparsedPublicKey::new(&ECDSA_P256_SHA256_ASN1, key)
                .verify(canonical_bytes, signature),
        };
        result.map_err(|e| SigningError::Verify(format!("{}: {e}", self.key_type.sig_alg())))
    }
}

/// Create a private tempdir for the sign input/output files.
fn tempfile_dir() -> Result<TempDir, SigningError> {
    TempDir::new().map_err(|e| SigningError::Sign(format!("create tempdir: {e}")))
}

/// Render a path as UTF-8 for an argv flag.
fn path_str(path: &std::path::Path) -> Result<String, SigningError> {
    path.to_str()
        .map(str::to_string)
        .ok_or_else(|| SigningError::Sign("non-UTF-8 tempfile path".to_string()))
}

/// A tiny self-cleaning temp directory (the `tempfile` crate is a dev-dependency
/// only, so the production sign path uses this minimal owned-dir instead).
struct TempDir {
    path: std::path::PathBuf,
}

impl TempDir {
    fn new() -> std::io::Result<Self> {
        use std::time::{SystemTime, UNIX_EPOCH};
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let path =
            std::env::temp_dir().join(format!("mathverse-kms-{}-{nanos}", std::process::id()));
        std::fs::create_dir_all(&path)?;
        Ok(Self { path })
    }

    fn path(&self) -> &std::path::Path {
        &self.path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

#[cfg(test)]
#[path = "gcp_kms_tests.rs"]
mod tests;
