// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the GCP Cloud KMS backend.
//!
//! These run WITHOUT a live KMS call or any credentials:
//! * argv construction is asserted directly (no spawn);
//! * the public-key verify path round-trips against a REAL Ed25519 key whose
//!   public half we wrap in a standard SPKI/PEM — the same encoding KMS emits;
//! * the `sign()` plumbing is driven by a fake [`CommandRunner`] that returns a
//!   REAL Ed25519 signature (we never fake a KMS signature as valid).

use base64::Engine as _;
use ring::rand::SystemRandom;
use ring::signature::{Ed25519KeyPair, KeyPair};

use super::*;

/// The 12-byte SPKI prefix for an Ed25519 SubjectPublicKeyInfo, per RFC 8410:
/// `SEQUENCE { SEQUENCE { OID 1.3.101.112 }, BIT STRING (0 unused, 32 bytes) }`.
/// Wrapping a raw 32-byte Ed25519 public key with this is the exact encoding
/// `gcloud kms keys versions get-public-key` returns for an `EC_SIGN_ED25519`
/// key, so this is a faithful test vector, not a mock.
const ED25519_SPKI_PREFIX: [u8; 12] = [
    0x30, 0x2a, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70, 0x03, 0x21, 0x00,
];

/// Build a standard SPKI PEM from a raw 32-byte Ed25519 public key.
fn ed25519_spki_pem(raw_pubkey: &[u8]) -> String {
    let mut der = ED25519_SPKI_PREFIX.to_vec();
    der.extend_from_slice(raw_pubkey);
    let b64 = base64::engine::general_purpose::STANDARD.encode(&der);
    format!("-----BEGIN PUBLIC KEY-----\n{b64}\n-----END PUBLIC KEY-----\n")
}

fn test_config(key_type: GcpKmsKeyType) -> GcpKmsConfig {
    GcpKmsConfig::new(
        "mv-prod",
        "us-central1",
        "mathverse-signing",
        "verdict-signer",
        "3",
        key_type,
    )
}

#[test]
fn test_resource_name_is_full_version_path() {
    let cfg = test_config(GcpKmsKeyType::Ed25519);
    assert_eq!(
        cfg.resource_name(),
        "projects/mv-prod/locations/us-central1/keyRings/mathverse-signing/\
         cryptoKeys/verdict-signer/cryptoKeyVersions/3"
    );
}

#[test]
fn test_sign_argv_ed25519_has_no_digest_algorithm() {
    let cfg = test_config(GcpKmsKeyType::Ed25519);
    let argv = cfg.sign_argv("/tmp/in.bin", "/tmp/out.sig");
    assert_eq!(
        argv,
        vec![
            "kms",
            "asymmetric-sign",
            "--location=us-central1",
            "--keyring=mathverse-signing",
            "--key=verdict-signer",
            "--version=3",
            "--project=mv-prod",
            "--input-file=/tmp/in.bin",
            "--signature-file=/tmp/out.sig",
        ]
    );
    // Ed25519 is not prehashed → no --digest-algorithm flag.
    assert!(!argv.iter().any(|a| a.starts_with("--digest-algorithm")));
}

#[test]
fn test_sign_argv_rsa_and_ecdsa_carry_sha256_digest() {
    for kt in [
        GcpKmsKeyType::RsaPkcs1Sha256,
        GcpKmsKeyType::EcdsaP256Sha256,
    ] {
        let argv = test_config(kt).sign_argv("/tmp/in.bin", "/tmp/out.sig");
        assert!(
            argv.contains(&"--digest-algorithm=sha256".to_string()),
            "{kt:?} must prehash with sha256"
        );
    }
}

#[test]
fn test_get_public_key_argv_is_correct() {
    let cfg = test_config(GcpKmsKeyType::Ed25519);
    assert_eq!(
        cfg.get_public_key_argv("/tmp/pub.pem"),
        vec![
            "kms",
            "keys",
            "versions",
            "get-public-key",
            "3",
            "--location=us-central1",
            "--keyring=mathverse-signing",
            "--key=verdict-signer",
            "--project=mv-prod",
            "--output-file=/tmp/pub.pem",
        ]
    );
}

#[test]
fn test_sig_alg_labels_match_key_type() {
    assert_eq!(GcpKmsKeyType::Ed25519.sig_alg(), "ed25519");
    assert_eq!(GcpKmsKeyType::RsaPkcs1Sha256.sig_alg(), "rsa-pkcs1-sha256");
    assert_eq!(
        GcpKmsKeyType::EcdsaP256Sha256.sig_alg(),
        "ecdsa-p256-sha256"
    );
    assert_eq!(
        GcpKmsKeyType::from_sig_alg("ecdsa-p256-sha256"),
        Some(GcpKmsKeyType::EcdsaP256Sha256)
    );
    assert_eq!(GcpKmsKeyType::from_sig_alg("nope"), None);
}

#[test]
fn test_backend_key_id_embeds_full_resource_and_is_asymmetric() {
    let backend = GcpKmsBackend::new(test_config(GcpKmsKeyType::Ed25519));
    assert!(backend.key_id().starts_with("gcp-kms:projects/mv-prod/"));
    assert_eq!(backend.sig_alg(), "ed25519");
    assert!(backend.is_asymmetric());
}

/// A fake runner that signs the message-file's bytes with a REAL Ed25519 key —
/// standing in for KMS without a live call. It reads the input file the backend
/// wrote (asserting the argv carries it), signs the real bytes, and writes the
/// real signature to the signature-file. This is a genuine Ed25519 signature,
/// not a forged "always-valid" stub.
struct FakeEd25519KmsRunner {
    key_pair: Ed25519KeyPair,
    pkcs8: Vec<u8>,
    expected_argv: std::sync::Mutex<Vec<String>>,
}

impl FakeEd25519KmsRunner {
    fn new() -> Self {
        let rng = SystemRandom::new();
        let pkcs8 = Ed25519KeyPair::generate_pkcs8(&rng).expect("generate pkcs8");
        let key_pair = Ed25519KeyPair::from_pkcs8(pkcs8.as_ref()).expect("from pkcs8");
        Self {
            key_pair,
            pkcs8: pkcs8.as_ref().to_vec(),
            expected_argv: std::sync::Mutex::new(Vec::new()),
        }
    }

    fn public_key_pem(&self) -> String {
        ed25519_spki_pem(self.key_pair.public_key().as_ref())
    }
}

impl CommandRunner for FakeEd25519KmsRunner {
    fn run_sign(&self, args: &[String], signature_file: &str) -> Result<Vec<u8>, SigningError> {
        // Record the argv so the test can assert it WITHOUT a live call.
        *self.expected_argv.lock().expect("argv lock") = args.to_vec();
        // The backend passes --input-file=<path>; locate and read it, exactly as
        // gcloud would, then sign the REAL bytes.
        let input_path = args
            .iter()
            .find_map(|a| a.strip_prefix("--input-file="))
            .ok_or_else(|| SigningError::Sign("argv missing --input-file".to_string()))?;
        let msg = std::fs::read(input_path)
            .map_err(|e| SigningError::Sign(format!("read input: {e}")))?;
        // A FRESH key pair from the same pkcs8 (Ed25519KeyPair is not Clone).
        let signer = Ed25519KeyPair::from_pkcs8(&self.pkcs8)
            .map_err(|e| SigningError::Sign(format!("reload: {e}")))?;
        let sig = signer.sign(&msg);
        std::fs::write(signature_file, sig.as_ref())
            .map_err(|e| SigningError::Sign(format!("write sig: {e}")))?;
        Ok(sig.as_ref().to_vec())
    }
}

#[test]
fn test_ed25519_kms_sign_then_local_pubkey_verify_round_trips() {
    let runner = Box::new(FakeEd25519KmsRunner::new());
    let pubkey_pem = runner.public_key_pem();
    let backend = GcpKmsBackend::with_runner(test_config(GcpKmsKeyType::Ed25519), runner);

    let msg = b"canonical verdict bytes for the KMS round-trip";
    let sig = backend
        .sign(msg)
        .expect("KMS sign plumbing produces a signature");

    // Verify against the CACHED public key — no KMS call.
    let verifier = GcpKmsVerifier::from_spki_pem(
        backend.key_id().to_string(),
        GcpKmsKeyType::Ed25519,
        &pubkey_pem,
    )
    .expect("parse SPKI PEM");
    verifier
        .verify(msg, &sig)
        .expect("a real Ed25519 signature verifies against the published public key");
    assert!(verifier.is_asymmetric());
    assert_eq!(verifier.sig_alg(), "ed25519");
}

#[test]
fn test_kms_tampered_message_fails_closed() {
    let runner = Box::new(FakeEd25519KmsRunner::new());
    let pubkey_pem = runner.public_key_pem();
    let backend = GcpKmsBackend::with_runner(test_config(GcpKmsKeyType::Ed25519), runner);
    let sig = backend.sign(b"original bytes").expect("sign");
    let verifier =
        GcpKmsVerifier::from_spki_pem("k", GcpKmsKeyType::Ed25519, &pubkey_pem).expect("pem");
    let err = verifier
        .verify(b"tampered bytes", &sig)
        .expect_err("a different message must fail verification");
    assert!(matches!(err, SigningError::Verify(_)));
}

#[test]
fn test_spki_pem_parse_recovers_the_raw_ed25519_key() {
    let rng = SystemRandom::new();
    let pkcs8 = Ed25519KeyPair::generate_pkcs8(&rng).expect("pkcs8");
    let kp = Ed25519KeyPair::from_pkcs8(pkcs8.as_ref()).expect("kp");
    let raw = kp.public_key().as_ref().to_vec();
    let pem = ed25519_spki_pem(&raw);
    let der = pem_to_der(&pem, "PUBLIC KEY").expect("decode pem");
    let recovered = spki_to_ring_public_key(&der, GcpKmsKeyType::Ed25519).expect("parse spki");
    assert_eq!(
        recovered, raw,
        "SPKI parse must recover the raw 32-byte key"
    );
}

#[test]
fn test_malformed_pem_fails_closed() {
    let err = GcpKmsVerifier::from_spki_pem("k", GcpKmsKeyType::Ed25519, "not a pem")
        .expect_err("garbage PEM must be rejected");
    assert!(matches!(err, SigningError::Key(_)));
}

/// Backend selection from the environment. Env vars are process-global, so both
/// the "resolves" and "missing fails closed" scenarios live in ONE serial test
/// to avoid a cross-thread race with the parallel test runner.
#[test]
fn test_config_from_env_selection_and_fail_closed() {
    let all_vars = [
        "MATHVERSE_KMS_PROJECT",
        "MATHVERSE_KMS_LOCATION",
        "MATHVERSE_KMS_KEYRING",
        "MATHVERSE_KMS_KEY",
        "MATHVERSE_KMS_VERSION",
        "MATHVERSE_KMS_KEY_TYPE",
    ];
    crate::process_env::with_env_edits(|env| {
        // 1. Missing required components → fail closed.
        for k in all_vars {
            env.remove(k);
        }
        let err = GcpKmsConfig::from_env().expect_err("missing components must fail closed");
        assert!(matches!(err, SigningError::Key(_)));

        // 2. Fully set → resolves with the env-selected key type and resource.
        let set = [
            ("MATHVERSE_KMS_PROJECT", "mv-prod"),
            ("MATHVERSE_KMS_LOCATION", "us-central1"),
            ("MATHVERSE_KMS_KEYRING", "mathverse-signing"),
            ("MATHVERSE_KMS_KEY", "verdict-signer"),
            ("MATHVERSE_KMS_VERSION", "7"),
            ("MATHVERSE_KMS_KEY_TYPE", "rsa-pkcs1-sha256"),
        ];
        for (k, v) in set {
            env.set(k, v);
        }
        let cfg = GcpKmsConfig::from_env().expect("env config resolves");
        assert_eq!(cfg.key_type, GcpKmsKeyType::RsaPkcs1Sha256);
        assert_eq!(cfg.version, "7");
        assert!(cfg.resource_name().ends_with("/cryptoKeyVersions/7"));

        // 3. Default key type is ed25519 when _KEY_TYPE is unset.
        env.remove("MATHVERSE_KMS_KEY_TYPE");
        let cfg = GcpKmsConfig::from_env().expect("resolves with default key type");
        assert_eq!(cfg.key_type, GcpKmsKeyType::Ed25519);
    });
}
