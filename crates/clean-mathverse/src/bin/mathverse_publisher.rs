// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `mathverse_publisher` — the PRIVILEGED Phase-2.1 publisher: the only process
//! that holds a signing key and the only place a queued submission is
//! re-verified and minted.
//!
//! For each `pending` submission staged by the public front-end
//! (`mathverse_serve`'s `POST /submit`), the publisher:
//!
//! 1. re-runs the ONE trust verdict (`graduate::recheck::recheck_and_classify`)
//!    in a FRESH kernel environment via the attestation bridge
//!    (`trust_sign::attest`) — never forked, never weakened;
//! 2. builds + signs a `mathverse-signed-verdict-v1` from that attestation
//!    (a foundational re-check -> `KernelVerified`; anything else -> `Rejected`;
//!    the signer cannot upgrade a non-foundational attestation);
//! 3. on `KernelVerified`: writes the signed verdict to `<out>/verdicts/` (where
//!    `mathverse_serve`'s /verdict + /audit serve it) and stages the re-checked
//!    declaration to `<out>/archive/`; marks the submission `KernelVerified`;
//! 4. otherwise: writes the signed `Rejected` verdict (when produced) and marks
//!    the submission `Rejected` with a reason.
//!
//! A malformed / unverifiable / non-foundational submission is `Rejected`,
//! never silently accepted. The signature attests PROVENANCE, not correctness —
//! correctness stays independently re-verifiable via the de Bruijn digest.
//!
//! Backend selection (offline, `--locked`-clean) mirrors `mathverse_reauditor`:
//!   - default: real Ed25519 over `ring` (`is_asymmetric = true`). A fresh dev
//!     keypair is generated and its PKCS#8 secret + public key written beside
//!     the output (secret never committed). Pass `--secret <pk8>` to reuse a
//!     persisted key.
//!   - `--gcp-kms`: the PRODUCTION GCP Cloud KMS backend (`is_asymmetric=true`).
//!     The signing key lives in Google's HSM; the publisher only *calls*
//!     `gcloud kms asymmetric-sign`. The key resource is read from the env
//!     (`MATHVERSE_KMS_PROJECT` / `_LOCATION` / `_KEYRING` / `_KEY` / `_VERSION`
//!     / `_KEY_TYPE`). The publisher's service account needs
//!     `roles/cloudkms.signerVerifier` on the key (see the Phase-2 design §7).
//!     The public key is fetched once via
//!     `gcloud kms keys versions get-public-key` and published with the Core so
//!     consumers verify offline; this binary does not hold the secret.
//!   - `--hmac-dev`: the HMAC-SHA256 keyed-hash fallback (`is_asymmetric=false`),
//!     DEV ONLY; a consumer policy must refuse it for published trust.
//!
//! Usage:
//!   mathverse_publisher <queue-dir> <out-dir> [--hmac-dev | --gcp-kms] \
//!     [--secret <pk8>] [--commit <sha>]

use std::path::Path;
use std::process::ExitCode;

use anyhow::{anyhow, Context, Result};
use clean_mathverse::trust_sign::{
    process_queue, Ed25519LocalBackend, GcpKmsBackend, GcpKmsConfig, HmacDevBackend, PublishReport,
    PublisherPaths, SigningBackend, SubmissionQueue,
};

/// Which signing backend the operator selected on the command line.
#[derive(Clone, Copy, PartialEq, Eq)]
enum BackendKind {
    Ed25519Local,
    GcpKms,
    HmacDev,
}

/// A coarse RFC-3339-ish UTC timestamp from the wall clock (mirrors the
/// re-auditor binary; the schema requires a deterministic UTC string, not
/// calendar precision).
fn now_rfc3339_utc() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    format!("1970-01-01T00:00:00Z+{secs}s")
}

fn run(
    queue_dir: &Path,
    out_dir: &Path,
    backend_kind: BackendKind,
    secret_path: Option<&str>,
    commit: &str,
) -> Result<PublishReport> {
    let queue = SubmissionQueue::open(queue_dir)
        .with_context(|| format!("open submission queue {}", queue_dir.display()))?;
    std::fs::create_dir_all(out_dir)
        .with_context(|| format!("create out dir {}", out_dir.display()))?;
    let paths = PublisherPaths::under(out_dir);
    let verified_at = now_rfc3339_utc();

    if backend_kind == BackendKind::GcpKms {
        // PRODUCTION: the signing key lives in Google's HSM. This process only
        // calls KMS; it never holds the secret. The public key must be fetched
        // out-of-band (`gcloud kms keys versions get-public-key`) and published
        // with the Core so consumers verify offline.
        let config = GcpKmsConfig::from_env()
            .map_err(|e| anyhow!("GCP KMS config (set MATHVERSE_KMS_* env vars): {e}"))?;
        let backend = GcpKmsBackend::new(config);
        eprintln!(
            "[publisher] backend = gcp-kms ({}, is_asymmetric={}) — key = {}",
            backend.sig_alg(),
            SigningBackend::is_asymmetric(&backend),
            backend.key_id()
        );
        eprintln!(
            "[publisher] publish the KMS public key with the Core: \
             `gcloud {}`",
            backend
                .config()
                .get_public_key_argv("publisher-pubkey.pem")
                .join(" ")
        );
        return process_queue(&queue, &backend, &paths, commit, &verified_at).map_err(Into::into);
    }

    if backend_kind == BackendKind::HmacDev {
        let backend = HmacDevBackend::new(
            "hmac-dev:publisher",
            b"REPLACE-WITH-ED25519-OR-KMS-secret".to_vec(),
        );
        eprintln!(
            "[publisher] backend = hmac-sha256 (is_asymmetric=false) — DEV ONLY, not a \
             public-key attestation"
        );
        process_queue(&queue, &backend, &paths, commit, &verified_at).map_err(Into::into)
    } else {
        let (backend, secret) = match secret_path {
            Some(p) => {
                let pk8 = std::fs::read(p).with_context(|| format!("read secret {p}"))?;
                let backend = Ed25519LocalBackend::from_pkcs8("ed25519-local:publisher", &pk8)
                    .map_err(|e| anyhow!("load ed25519 secret: {e}"))?;
                (backend, None)
            }
            None => {
                let (backend, secret) = Ed25519LocalBackend::generate("ed25519-local:publisher")
                    .map_err(|e| anyhow!("ed25519 keygen: {e}"))?;
                (backend, Some(secret))
            }
        };
        // Publish the public key (verifiable offline) and, for a freshly-generated
        // key, the secret (never committed) beside the output.
        std::fs::write(
            out_dir.join("publisher-pubkey.bin"),
            backend.public_key_bytes(),
        )
        .context("write public key")?;
        if let Some(secret) = secret {
            std::fs::write(out_dir.join("publisher-secret.pk8"), &secret)
                .context("write secret")?;
        }
        eprintln!(
            "[publisher] backend = ed25519 (is_asymmetric={}) — public key written to {}",
            SigningBackend::is_asymmetric(&backend),
            out_dir.join("publisher-pubkey.bin").display()
        );
        process_queue(&queue, &backend, &paths, commit, &verified_at).map_err(Into::into)
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!(
            "usage: mathverse_publisher <queue-dir> <out-dir> [--hmac-dev | --gcp-kms] \
             [--secret <pk8>] [--commit <sha>]"
        );
        eprintln!();
        eprintln!(
            "Re-verifies every PENDING submission under <queue-dir> in a FRESH kernel via the"
        );
        eprintln!("single trust verdict, signs a mathverse-signed-verdict-v1, and publishes the");
        eprintln!(
            "KernelVerified ones to <out-dir>/verdicts (+ archive). Rejected submissions are"
        );
        eprintln!("never minted green. Signatures attest provenance, not correctness.");
        return ExitCode::from(2);
    }
    let queue_dir = Path::new(&args[1]);
    let out_dir = Path::new(&args[2]);
    let use_hmac = args.iter().any(|a| a == "--hmac-dev");
    let use_gcp_kms = args.iter().any(|a| a == "--gcp-kms");
    if use_hmac && use_gcp_kms {
        eprintln!("[publisher] FATAL: choose at most one of --hmac-dev / --gcp-kms");
        return ExitCode::from(2);
    }
    let backend_kind = if use_gcp_kms {
        BackendKind::GcpKms
    } else if use_hmac {
        BackendKind::HmacDev
    } else {
        BackendKind::Ed25519Local
    };
    let secret_path = args
        .iter()
        .position(|a| a == "--secret")
        .and_then(|i| args.get(i + 1))
        .map(String::as_str);
    let commit = args
        .iter()
        .position(|a| a == "--commit")
        .and_then(|i| args.get(i + 1))
        .cloned()
        .unwrap_or_else(|| "unknown-commit".to_string());

    let report = match run(queue_dir, out_dir, backend_kind, secret_path, &commit) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("[publisher] FATAL: {e:#}");
            return ExitCode::FAILURE;
        }
    };

    println!("=== mathverse publisher ===");
    println!("  queue:              {}", queue_dir.display());
    println!("  out:                {}", out_dir.display());
    println!("  processed:          {}", report.results.len());
    println!("  KernelVerified:     {}", report.kernel_verified);
    println!("  rejected:           {}", report.rejected);
    println!("  verdicts written:   {}/verdicts", out_dir.display());
    println!("  declarations staged:{}/archive", out_dir.display());
    ExitCode::SUCCESS
}
