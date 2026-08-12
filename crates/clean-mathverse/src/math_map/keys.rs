// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trusted-key policy and Ed25519 manifest signature verification.
//!
//! Every rule here is fail-closed. A key is usable for signature verification
//! only when it is registered for the exact `(service, key_id, algorithm)`
//! triple, has `status = "trusted"`, and is not the shipped placeholder. A
//! manifest signature is accepted only when a real Ed25519 verification over a
//! domain-separated, service- and key-bound payload succeeds.
//!
//! Engine note: the original prototype used `ed25519-dalek`'s `verify_strict`.
//! `ed25519-dalek` is not in this workspace's dependency graph; `ring 0.17`
//! is, and it is already the crate's Ed25519 engine (see
//! [`crate::trust_sign::Ed25519Verifier`]). `ring`'s `ED25519` performs RFC 8032
//! verification with canonical-encoding and reduced-`S` enforcement, so
//! swapping the engine does not relax any check this module depends on.

use std::fs;
use std::path::{Path, PathBuf};

use ring::signature::{UnparsedPublicKey, ED25519};
use serde::{Deserialize, Serialize};

use super::bundle::hex_decode;
use super::DEFAULT_TRUSTED_KEYS_TOML;

/// Placeholder public key shipped in the registry; never usable for signatures.
pub const PLACEHOLDER_PUBLIC_KEY: &str = "REPLACE_WITH_REAL_MATH_MAP_ED25519_PUBLIC_KEY";
/// Domain separator prefixed to every signed manifest payload.
pub const MATH_MAP_MANIFEST_DOMAIN_SEPARATOR: &[u8] = b"MathMapManifestV1\0";
/// Hard cap on the manifest bytes a signature may cover.
pub const MAX_MANIFEST_SIZE: usize = 1024 * 1024;
/// Raw Ed25519 public key length.
const ED25519_PUBLIC_KEY_LEN: usize = 32;
/// Raw Ed25519 signature length.
const ED25519_SIGNATURE_LEN: usize = 64;
/// Stable identifier for the verification engine recorded in reports.
const ED25519_VERIFIER_ID: &str = "ed25519-ring-strict-v1";

/// The operator-controlled registry of signing keys per producing service.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TrustedKeyRegistry {
    /// Registry contract version.
    pub schema_version: String,
    /// Registered keys.
    #[serde(default)]
    pub keys: Vec<TrustedKey>,
}

/// One registered signing key.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TrustedKey {
    /// Producing service this key signs for.
    pub service: String,
    /// Stable key identifier.
    pub key_id: String,
    /// Signature algorithm; only `ed25519` is supported.
    pub algorithm: String,
    /// Hex-encoded raw public key.
    pub public_key: String,
    /// `trusted` or `disabled`.
    #[serde(default = "default_trusted_status")]
    pub status: String,
}

/// Outcome of a successful manifest signature verification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SignatureVerification {
    /// Producing service.
    pub service: String,
    /// Key that verified the signature.
    pub key_id: String,
    /// Algorithm the key uses.
    pub algorithm: String,
    /// Whether the verification was genuine public-key cryptography.
    pub cryptographic: bool,
    /// Stable verifier engine identifier.
    pub verifier: String,
}

/// Why a manifest signature or trusted key was rejected.
#[derive(Debug, thiserror::Error)]
pub enum TrustedKeyRegistryError {
    /// Filesystem failure.
    #[error("failed to read MathMap trusted key registry at {path}: {source}")]
    Io {
        /// Registry path.
        path: PathBuf,
        /// Underlying error.
        #[source]
        source: std::io::Error,
    },
    /// TOML decode failure.
    #[error("failed to parse MathMap trusted key registry TOML at {path}: {source}")]
    Toml {
        /// Registry path.
        path: PathBuf,
        /// Underlying error.
        #[source]
        source: toml::de::Error,
    },
    /// No key at all is registered for the service.
    #[error("no active trusted key is registered for service `{service}`")]
    UnregisteredService {
        /// Producing service.
        service: String,
    },
    /// No key with that id is registered for the service.
    #[error("no active trusted key with id `{key_id}` is registered for service `{service}`")]
    UnregisteredKeyId {
        /// Producing service.
        service: String,
        /// Requested key id.
        key_id: String,
    },
    /// The service has keys, but all of them are disabled.
    #[error(
        "trusted key registry only contains disabled keys for service `{service}`: {key_ids:?}"
    )]
    DisabledService {
        /// Producing service.
        service: String,
        /// Disabled key ids.
        key_ids: Vec<String>,
    },
    /// The bundle carried an empty signature.
    #[error("manifest signature is empty for service `{service}`")]
    EmptySignature {
        /// Producing service.
        service: String,
    },
    /// The registered key uses an unsupported algorithm.
    #[error(
        "trusted key `{key_id}` for service `{service}` uses unsupported algorithm `{algorithm}`"
    )]
    UnsupportedAlgorithm {
        /// Producing service.
        service: String,
        /// Key id.
        key_id: String,
        /// Requested algorithm.
        algorithm: String,
    },
    /// The verifier returned a key that is not registered and active.
    #[error(
        "manifest signature for service `{service}` did not verify with registered trusted key `{key_id}`"
    )]
    UnregisteredSignature {
        /// Producing service.
        service: String,
        /// Key id the verifier reported.
        key_id: String,
    },
    /// The signature named a disabled key.
    #[error(
        "manifest signature for service `{service}` references disabled trusted key `{key_id}` using `{algorithm}`"
    )]
    DisabledSignatureKey {
        /// Producing service.
        service: String,
        /// Key id.
        key_id: String,
        /// Algorithm.
        algorithm: String,
    },
    /// The registered key is still the shipped placeholder.
    #[error(
        "trusted key `{key_id}` for service `{service}` still uses the disabled placeholder public key"
    )]
    PlaceholderPublicKey {
        /// Producing service.
        service: String,
        /// Key id.
        key_id: String,
    },
    /// The registered public key could not be decoded.
    #[error(
        "trusted key `{key_id}` for service `{service}` has malformed ed25519 public key: {reason}"
    )]
    MalformedPublicKey {
        /// Producing service.
        service: String,
        /// Key id.
        key_id: String,
        /// Decode diagnostic.
        reason: String,
    },
    /// The bundle signature bytes were not a raw 64-byte Ed25519 signature.
    #[error("manifest signature for service `{service}` and trusted key `{key_id}` is malformed: {reason}")]
    MalformedSignature {
        /// Producing service.
        service: String,
        /// Key id.
        key_id: String,
        /// Decode diagnostic.
        reason: String,
    },
    /// The cryptographic check failed.
    #[error(
        "cryptographic signature verification failed for service `{service}` using trusted key `{key_id}`"
    )]
    VerificationFailed {
        /// Producing service.
        service: String,
        /// Key id.
        key_id: String,
    },
    /// The manifest exceeded the signable size limit.
    #[error("manifest size {size} exceeds maximum limit of {MAX_MANIFEST_SIZE} bytes")]
    ManifestTooLarge {
        /// Observed manifest size.
        size: usize,
    },
}

/// A structural defect in the registry file itself.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TrustedKeyRegistryValidationError {
    /// The same `(service, key_id, algorithm)` triple appears more than once.
    DuplicateKey {
        /// Producing service.
        service: String,
        /// Key id.
        key_id: String,
        /// Algorithm.
        algorithm: String,
    },
    /// `status` is neither `trusted` nor `disabled`.
    UnsupportedStatus {
        /// Producing service.
        service: String,
        /// Key id.
        key_id: String,
        /// Rejected status.
        status: String,
    },
    /// A key marked `trusted` still holds the shipped placeholder public key.
    TrustedPlaceholderPublicKey {
        /// Producing service.
        service: String,
        /// Key id.
        key_id: String,
    },
}

/// Verifies a manifest signature against the trusted-key registry.
pub trait ManifestSignatureVerifier {
    /// Verify `signature` over the EXACT `raw_manifest_json` bytes.
    ///
    /// Implementations must fail closed: any doubt is an error, never an `Ok`
    /// with `cryptographic: false` unless the verifier is explicitly a
    /// non-cryptographic test double.
    fn verify_manifest(
        &self,
        service: &str,
        key_id: &str,
        raw_manifest_json: &[u8],
        signature: &[u8],
        keys: &TrustedKeyRegistry,
    ) -> Result<SignatureVerification, TrustedKeyRegistryError>;
}

/// Non-cryptographic test double. Only compiled for tests, and only ever
/// accepted when `require_cryptographic_signature` is off.
#[derive(Debug, Clone, Copy, Default)]
#[cfg(test)]
pub struct SkeletonSignatureVerifier;

#[cfg(test)]
impl ManifestSignatureVerifier for SkeletonSignatureVerifier {
    fn verify_manifest(
        &self,
        service: &str,
        key_id: &str,
        _raw_manifest_json: &[u8],
        signature: &[u8],
        keys: &TrustedKeyRegistry,
    ) -> Result<SignatureVerification, TrustedKeyRegistryError> {
        if signature.is_empty() {
            return Err(TrustedKeyRegistryError::EmptySignature {
                service: service.to_owned(),
            });
        }
        let key = keys.active_key(service, key_id, "ed25519")?;
        Ok(SignatureVerification {
            service: service.to_owned(),
            key_id: key.key_id.clone(),
            algorithm: key.algorithm.clone(),
            cryptographic: false,
            verifier: "skeleton-non-cryptographic-test-verifier".to_owned(),
        })
    }
}

/// The real Ed25519 manifest verifier.
#[derive(Debug, Clone, Copy, Default)]
pub struct Ed25519SignatureVerifier;

impl ManifestSignatureVerifier for Ed25519SignatureVerifier {
    fn verify_manifest(
        &self,
        service: &str,
        key_id: &str,
        raw_manifest_json: &[u8],
        signature: &[u8],
        keys: &TrustedKeyRegistry,
    ) -> Result<SignatureVerification, TrustedKeyRegistryError> {
        if raw_manifest_json.len() > MAX_MANIFEST_SIZE {
            return Err(TrustedKeyRegistryError::ManifestTooLarge {
                size: raw_manifest_json.len(),
            });
        }
        if signature.is_empty() {
            return Err(TrustedKeyRegistryError::EmptySignature {
                service: service.to_owned(),
            });
        }
        let key = keys.active_key(service, key_id, "ed25519")?;

        // Strict encoding enforcement: registry public keys are hex-only, so a
        // base64 or raw-byte key is a registry defect, not an alternate form.
        let public_key_bytes = hex_decode(&key.public_key).map_err(|err| {
            TrustedKeyRegistryError::MalformedPublicKey {
                service: service.to_owned(),
                key_id: key.key_id.clone(),
                reason: format!("public_key in registry must be hex: {err}"),
            }
        })?;
        if public_key_bytes.len() != ED25519_PUBLIC_KEY_LEN {
            return Err(TrustedKeyRegistryError::MalformedPublicKey {
                service: service.to_owned(),
                key_id: key.key_id.clone(),
                reason: format!("public key must be exactly {ED25519_PUBLIC_KEY_LEN} bytes"),
            });
        }

        // Strict format enforcement: raw 64 bytes, never a DER or base64 wrapper.
        if signature.len() != ED25519_SIGNATURE_LEN {
            return Err(TrustedKeyRegistryError::MalformedSignature {
                service: service.to_owned(),
                key_id: key.key_id.clone(),
                reason: format!("signature must be exactly {ED25519_SIGNATURE_LEN} raw bytes"),
            });
        }

        // Context-bound payload: prevents replaying a signature across services
        // or across key ids inside one service.
        let payload = manifest_signature_payload(service, key_id, raw_manifest_json);

        UnparsedPublicKey::new(&ED25519, &public_key_bytes)
            .verify(&payload, signature)
            .map_err(|_| TrustedKeyRegistryError::VerificationFailed {
                service: service.to_owned(),
                key_id: key.key_id.clone(),
            })?;

        Ok(SignatureVerification {
            service: service.to_owned(),
            key_id: key.key_id.clone(),
            algorithm: key.algorithm.clone(),
            cryptographic: true,
            verifier: ED25519_VERIFIER_ID.to_owned(),
        })
    }
}

/// Build the domain-separated, service- and key-bound signing payload.
#[must_use]
pub(crate) fn manifest_signature_payload(
    service: &str,
    key_id: &str,
    raw_manifest_json: &[u8],
) -> Vec<u8> {
    let mut payload = Vec::with_capacity(
        MATH_MAP_MANIFEST_DOMAIN_SEPARATOR.len()
            + service.len()
            + 1
            + key_id.len()
            + 1
            + raw_manifest_json.len(),
    );
    payload.extend_from_slice(MATH_MAP_MANIFEST_DOMAIN_SEPARATOR);
    payload.extend_from_slice(service.as_bytes());
    payload.push(0);
    payload.extend_from_slice(key_id.as_bytes());
    payload.push(0);
    payload.extend_from_slice(raw_manifest_json);
    payload
}

impl TrustedKeyRegistry {
    /// The registry compiled into the binary.
    ///
    /// # Panics
    ///
    /// Panics if the bundled `trusted_keys.toml` does not parse, which is a
    /// build-time invariant violation rather than a runtime condition.
    #[must_use]
    pub fn builtin() -> Self {
        Self::from_toml_str(DEFAULT_TRUSTED_KEYS_TOML)
            .expect("bundled MathMap trusted key registry must parse")
    }

    /// Load a registry from a TOML file.
    pub fn load(path: impl AsRef<Path>) -> Result<Self, TrustedKeyRegistryError> {
        let path = path.as_ref();
        let text = fs::read_to_string(path).map_err(|source| TrustedKeyRegistryError::Io {
            path: path.to_owned(),
            source,
        })?;
        toml::from_str(&text).map_err(|source| TrustedKeyRegistryError::Toml {
            path: path.to_owned(),
            source,
        })
    }

    /// Parse a registry from TOML text.
    pub fn from_toml_str(text: &str) -> Result<Self, toml::de::Error> {
        toml::from_str(text)
    }

    /// The first key usable for signatures for `service`, if any.
    #[must_use]
    pub fn active_key_for_service(&self, service: &str) -> Option<&TrustedKey> {
        self.keys
            .iter()
            .find(|key| key.service == service && key.is_active_for_signatures())
    }

    /// Like [`Self::active_key_for_service`], but reports WHY no key is usable.
    pub fn active_key_for_service_or_error(
        &self,
        service: &str,
    ) -> Result<&TrustedKey, TrustedKeyRegistryError> {
        if let Some(key) = self.active_key_for_service(service) {
            return Ok(key);
        }

        let service_keys: Vec<&TrustedKey> = self
            .keys
            .iter()
            .filter(|key| key.service == service)
            .collect();
        if service_keys.is_empty() {
            return Err(TrustedKeyRegistryError::UnregisteredService {
                service: service.to_owned(),
            });
        }

        if let Some(key) = service_keys
            .iter()
            .find(|key| key.status == "trusted" && key.has_placeholder_public_key())
        {
            return Err(TrustedKeyRegistryError::PlaceholderPublicKey {
                service: key.service.clone(),
                key_id: key.key_id.clone(),
            });
        }

        Err(TrustedKeyRegistryError::DisabledService {
            service: service.to_owned(),
            key_ids: service_keys.iter().map(|key| key.key_id.clone()).collect(),
        })
    }

    /// Whether the exact `(service, key_id, algorithm)` triple is registered and active.
    #[must_use]
    pub fn has_active_key(&self, service: &str, key_id: &str, algorithm: &str) -> bool {
        self.active_key(service, key_id, algorithm).is_ok()
    }

    /// Look up an active key by exact `(service, key_id, algorithm)` triple.
    pub fn active_key(
        &self,
        service: &str,
        key_id: &str,
        algorithm: &str,
    ) -> Result<&TrustedKey, TrustedKeyRegistryError> {
        let Some(key) = self.keys.iter().find(|key| {
            key.service == service && key.key_id == key_id && key.algorithm == algorithm
        }) else {
            return Err(TrustedKeyRegistryError::UnregisteredKeyId {
                service: service.to_owned(),
                key_id: key_id.to_owned(),
            });
        };
        if key.status != "trusted" {
            return Err(TrustedKeyRegistryError::DisabledSignatureKey {
                service: service.to_owned(),
                key_id: key_id.to_owned(),
                algorithm: algorithm.to_owned(),
            });
        }
        if key.has_placeholder_public_key() {
            return Err(TrustedKeyRegistryError::PlaceholderPublicKey {
                service: service.to_owned(),
                key_id: key_id.to_owned(),
            });
        }
        Ok(key)
    }

    /// Structural defects in the registry file, in deterministic order.
    #[must_use]
    pub fn validation_errors(&self) -> Vec<TrustedKeyRegistryValidationError> {
        let mut errors = Vec::new();
        let mut seen = std::collections::BTreeSet::new();
        for key in &self.keys {
            let identity = (&key.service, &key.key_id, &key.algorithm);
            if !seen.insert(identity) {
                errors.push(TrustedKeyRegistryValidationError::DuplicateKey {
                    service: key.service.clone(),
                    key_id: key.key_id.clone(),
                    algorithm: key.algorithm.clone(),
                });
            }
            if key.status != "trusted" && key.status != "disabled" {
                errors.push(TrustedKeyRegistryValidationError::UnsupportedStatus {
                    service: key.service.clone(),
                    key_id: key.key_id.clone(),
                    status: key.status.clone(),
                });
            }
            if key.status == "trusted" && key.has_placeholder_public_key() {
                errors.push(
                    TrustedKeyRegistryValidationError::TrustedPlaceholderPublicKey {
                        service: key.service.clone(),
                        key_id: key.key_id.clone(),
                    },
                );
            }
        }
        errors
    }

    /// Validate the registry file structure.
    pub fn validate(&self) -> Result<(), Vec<TrustedKeyRegistryValidationError>> {
        let errors = self.validation_errors();
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

impl TrustedKey {
    /// Whether this key may be used to verify signatures.
    #[must_use]
    pub fn is_active_for_signatures(&self) -> bool {
        self.status == "trusted" && !self.has_placeholder_public_key()
    }

    /// Whether this key still holds the shipped placeholder public key.
    #[must_use]
    pub fn has_placeholder_public_key(&self) -> bool {
        self.public_key == PLACEHOLDER_PUBLIC_KEY
    }
}

fn default_trusted_status() -> String {
    "trusted".to_owned()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::math_map::bundle::hex_lower;
    use ring::rand::SystemRandom;
    use ring::signature::{Ed25519KeyPair, KeyPair};

    fn key(service: &str, key_id: &str, status: &str, public_key: &str) -> TrustedKey {
        TrustedKey {
            service: service.to_owned(),
            key_id: key_id.to_owned(),
            algorithm: "ed25519".to_owned(),
            public_key: public_key.to_owned(),
            status: status.to_owned(),
        }
    }

    fn generate_keypair() -> Ed25519KeyPair {
        let rng = SystemRandom::new();
        let pkcs8 = Ed25519KeyPair::generate_pkcs8(&rng).expect("keypair generates");
        Ed25519KeyPair::from_pkcs8(pkcs8.as_ref()).expect("keypair loads")
    }

    #[test]
    fn test_disabled_builtin_placeholder_is_not_active() {
        let registry = TrustedKeyRegistry::builtin();

        assert!(!registry.has_active_key("math_map", "math_map-placeholder-disabled", "ed25519"));
        assert!(matches!(
            registry.active_key_for_service_or_error("math_map"),
            Err(TrustedKeyRegistryError::DisabledService { key_ids, .. })
                if key_ids == vec!["math_map-placeholder-disabled".to_owned()]
        ));
        assert!(registry.validate().is_ok());
    }

    #[test]
    fn test_trusted_placeholder_public_key_is_not_active() {
        let registry = TrustedKeyRegistry {
            schema_version: "clean-math_map-trusted-keys-v1".to_owned(),
            keys: vec![key(
                "math_map",
                "placeholder",
                "trusted",
                PLACEHOLDER_PUBLIC_KEY,
            )],
        };

        assert!(!registry.has_active_key("math_map", "placeholder", "ed25519"));
        assert!(matches!(
            registry.active_key("math_map", "placeholder", "ed25519"),
            Err(TrustedKeyRegistryError::PlaceholderPublicKey { key_id, .. })
                if key_id == "placeholder"
        ));
        assert_eq!(
            registry.validation_errors(),
            vec![
                TrustedKeyRegistryValidationError::TrustedPlaceholderPublicKey {
                    service: "math_map".to_owned(),
                    key_id: "placeholder".to_owned(),
                }
            ]
        );
    }

    #[test]
    fn test_active_key_reports_disabled_vs_unregistered() {
        let registry = TrustedKeyRegistry {
            schema_version: "clean-math_map-trusted-keys-v1".to_owned(),
            keys: vec![key(
                "math_map",
                "disabled-key",
                "disabled",
                &"00".repeat(32),
            )],
        };

        assert!(matches!(
            registry.active_key("math_map", "disabled-key", "ed25519"),
            Err(TrustedKeyRegistryError::DisabledSignatureKey { key_id, .. })
                if key_id == "disabled-key"
        ));
        assert!(matches!(
            registry.active_key("math_map", "missing-key", "ed25519"),
            Err(TrustedKeyRegistryError::UnregisteredKeyId { key_id, .. })
                if key_id == "missing-key"
        ));
    }

    #[test]
    fn test_validation_errors_are_deterministic() {
        let registry = TrustedKeyRegistry {
            schema_version: "clean-math_map-trusted-keys-v1".to_owned(),
            keys: vec![
                key("math_map", "dup", "trusted", &"00".repeat(32)),
                key("math_map", "dup", "trusted", &"01".repeat(32)),
                key("math_map", "unknown-status", "revoked", &"02".repeat(32)),
                key("math_map", "placeholder", "trusted", PLACEHOLDER_PUBLIC_KEY),
            ],
        };

        assert_eq!(
            registry.validation_errors(),
            vec![
                TrustedKeyRegistryValidationError::DuplicateKey {
                    service: "math_map".to_owned(),
                    key_id: "dup".to_owned(),
                    algorithm: "ed25519".to_owned(),
                },
                TrustedKeyRegistryValidationError::UnsupportedStatus {
                    service: "math_map".to_owned(),
                    key_id: "unknown-status".to_owned(),
                    status: "revoked".to_owned(),
                },
                TrustedKeyRegistryValidationError::TrustedPlaceholderPublicKey {
                    service: "math_map".to_owned(),
                    key_id: "placeholder".to_owned(),
                },
            ]
        );
    }

    #[test]
    fn test_ed25519_verifier_accepts_valid_signature() {
        let keypair = generate_keypair();
        let service = "math_map";
        let key_id = "test-key";
        let raw_manifest_json = b"test payload";

        let payload = manifest_signature_payload(service, key_id, raw_manifest_json);
        let signature = keypair.sign(&payload);

        let registry = TrustedKeyRegistry {
            schema_version: "clean-math_map-trusted-keys-v1".to_owned(),
            keys: vec![key(
                service,
                key_id,
                "trusted",
                &hex_lower(keypair.public_key().as_ref()),
            )],
        };

        let verification = Ed25519SignatureVerifier
            .verify_manifest(
                service,
                key_id,
                raw_manifest_json,
                signature.as_ref(),
                &registry,
            )
            .expect("authentic signature verifies");

        assert!(verification.cryptographic);
        assert_eq!(verification.verifier, ED25519_VERIFIER_ID);
    }

    #[test]
    fn test_ed25519_verifier_rejects_tampered_payload() {
        let keypair = generate_keypair();
        let service = "math_map";
        let key_id = "test-key";

        let payload = manifest_signature_payload(service, key_id, b"test payload");
        let signature = keypair.sign(&payload);

        let registry = TrustedKeyRegistry {
            schema_version: "clean-math_map-trusted-keys-v1".to_owned(),
            keys: vec![key(
                service,
                key_id,
                "trusted",
                &hex_lower(keypair.public_key().as_ref()),
            )],
        };

        let result = Ed25519SignatureVerifier.verify_manifest(
            service,
            key_id,
            b"tampered payload",
            signature.as_ref(),
            &registry,
        );

        assert!(matches!(
            result,
            Err(TrustedKeyRegistryError::VerificationFailed { .. })
        ));
    }

    #[test]
    fn test_ed25519_verifier_rejects_tampered_signature() {
        let keypair = generate_keypair();
        let service = "math_map";
        let key_id = "test-key";
        let raw_manifest_json = b"test payload";

        let payload = manifest_signature_payload(service, key_id, raw_manifest_json);
        let mut sig_bytes = keypair.sign(&payload).as_ref().to_vec();
        sig_bytes[0] ^= 0xFF;

        let registry = TrustedKeyRegistry {
            schema_version: "clean-math_map-trusted-keys-v1".to_owned(),
            keys: vec![key(
                service,
                key_id,
                "trusted",
                &hex_lower(keypair.public_key().as_ref()),
            )],
        };

        let result = Ed25519SignatureVerifier.verify_manifest(
            service,
            key_id,
            raw_manifest_json,
            &sig_bytes,
            &registry,
        );

        assert!(matches!(
            result,
            Err(TrustedKeyRegistryError::VerificationFailed { .. })
        ));
    }

    #[test]
    fn test_ed25519_verifier_rejects_cross_key_id_replay() {
        let keypair = generate_keypair();
        let service = "math_map";
        let raw_manifest_json = b"test payload";

        // Sign for `key-a`, then present the same signature as `key-b` with the
        // same public key registered under both ids.
        let payload = manifest_signature_payload(service, "key-a", raw_manifest_json);
        let signature = keypair.sign(&payload);
        let public_key = hex_lower(keypair.public_key().as_ref());

        let registry = TrustedKeyRegistry {
            schema_version: "clean-math_map-trusted-keys-v1".to_owned(),
            keys: vec![
                key(service, "key-a", "trusted", &public_key),
                key(service, "key-b", "trusted", &public_key),
            ],
        };

        let result = Ed25519SignatureVerifier.verify_manifest(
            service,
            "key-b",
            raw_manifest_json,
            signature.as_ref(),
            &registry,
        );

        assert!(matches!(
            result,
            Err(TrustedKeyRegistryError::VerificationFailed { .. })
        ));
    }

    #[test]
    fn test_ed25519_verifier_rejects_wrong_length_signature() {
        let keypair = generate_keypair();
        let registry = TrustedKeyRegistry {
            schema_version: "clean-math_map-trusted-keys-v1".to_owned(),
            keys: vec![key(
                "math_map",
                "test-key",
                "trusted",
                &hex_lower(keypair.public_key().as_ref()),
            )],
        };

        let result = Ed25519SignatureVerifier
            .verify_manifest("math_map", "test-key", b"payload", &[0u8; 63], &registry);

        assert!(matches!(
            result,
            Err(TrustedKeyRegistryError::MalformedSignature { .. })
        ));
    }

    #[test]
    fn test_ed25519_verifier_rejects_oversized_manifest() {
        let registry = TrustedKeyRegistry {
            schema_version: "clean-math_map-trusted-keys-v1".to_owned(),
            keys: vec![key("math_map", "test-key", "trusted", &"00".repeat(32))],
        };
        let oversized = vec![b'x'; MAX_MANIFEST_SIZE + 1];

        let result = Ed25519SignatureVerifier
            .verify_manifest("math_map", "test-key", &oversized, &[0u8; 64], &registry);

        assert!(matches!(
            result,
            Err(TrustedKeyRegistryError::ManifestTooLarge { .. })
        ));
    }
}
