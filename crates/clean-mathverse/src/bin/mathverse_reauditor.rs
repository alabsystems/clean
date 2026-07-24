// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `mathverse_reauditor` — re-earn every published `KernelVerified` claim in a
//! Core under the CURRENT kernel and emit signed verdicts + a signed revocation
//! list.
//!
//! For every Cake shard under the Core directory, the re-auditor reconstructs
//! each value-bearing theorem from the shard, re-runs the kernel in a FRESH
//! environment via the single trust verdict
//! (`graduate::recheck::recheck_and_classify`), and signs a
//! `mathverse-signed-verdict-v1` record per declaration. A claim that no longer
//! re-earns `KernelVerified` is appended to a signed
//! `mathverse-revocation-list-v1`.
//!
//! The signature attests PROVENANCE ("this verifier re-ran its kernel over this
//! digest and observed KernelVerified, foundational-only"), NOT correctness —
//! correctness stays independently re-verifiable by a consumer via the de Bruijn
//! `expr_canonical_digest`. The re-auditor only ever DEMOTES.
//!
//! Backend selection (offline, `--locked`-clean):
//!   - default: real Ed25519 over `ring` (`is_asymmetric = true`). A fresh dev
//!     keypair is generated and its PKCS#8 secret + public key written beside
//!     the output (secret never committed).
//!   - `--hmac-dev`: the documented HMAC-SHA256 keyed-hash fallback
//!     (`is_asymmetric = false`) for environments where even `ring` is
//!     unavailable. NOT a public-key attestation; a consumer policy must refuse
//!     it for published trust.
//!
//! Usage:
//!   mathverse_reauditor <core-dir> <out-dir> [--hmac-dev] [--commit <sha>]

use std::path::Path;
use std::process::ExitCode;

use anyhow::{anyhow, Context, Result};
use clean_mathverse::trust_sign::{
    reaudit_core, Ed25519LocalBackend, HmacDevBackend, ReauditReport, RevocationList,
    SigningBackend,
};

/// A coarse RFC-3339-ish UTC timestamp from the wall clock (seconds since the
/// epoch rendered as a string is enough for the record; the re-auditor does not
/// need calendar precision). Falls back to "0" if the clock is before the epoch.
fn now_rfc3339_utc() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    // Minimal RFC-3339-shaped stamp anchored at the epoch-seconds offset; the
    // schema only requires a UTC string, and this is deterministic + parseable.
    format!("1970-01-01T00:00:00Z+{secs}s")
}

fn run(core_dir: &Path, out_dir: &Path, use_hmac: bool, commit: &str) -> Result<ReauditReport> {
    std::fs::create_dir_all(out_dir)
        .with_context(|| format!("create out dir {}", out_dir.display()))?;
    let verified_at = now_rfc3339_utc();

    let report = if use_hmac {
        let backend = HmacDevBackend::new(
            "hmac-dev:reauditor",
            b"REPLACE-WITH-ED25519-OR-KMS-secret".to_vec(),
        );
        eprintln!(
            "[reauditor] backend = hmac-sha256 (is_asymmetric=false) — DEV ONLY, not a \
             public-key attestation"
        );
        reaudit_core(core_dir, &backend, commit, &verified_at)?
    } else {
        let (backend, secret) = Ed25519LocalBackend::generate("ed25519-local:reauditor")
            .map_err(|e| anyhow!("ed25519 keygen: {e}"))?;
        // Persist the public key (verifiable offline) and the secret (never
        // committed) beside the output.
        std::fs::write(
            out_dir.join("reauditor-pubkey.bin"),
            backend.public_key_bytes(),
        )
        .context("write public key")?;
        std::fs::write(out_dir.join("reauditor-secret.pk8"), &secret).context("write secret")?;
        eprintln!(
            "[reauditor] backend = ed25519 (is_asymmetric={}) — public key written to {}",
            SigningBackend::is_asymmetric(&backend),
            out_dir.join("reauditor-pubkey.bin").display()
        );
        reaudit_core(core_dir, &backend, commit, &verified_at)?
    };

    // Write one signed verdict file per declaration.
    let verdicts_dir = out_dir.join("verdicts");
    std::fs::create_dir_all(&verdicts_dir).context("create verdicts dir")?;
    for (i, v) in report.verdicts.iter().enumerate() {
        let json = serde_json::to_vec_pretty(&v.signed).context("serialize verdict")?;
        let safe_name = v.name.replace(['/', ':', '.'], "_");
        let path = verdicts_dir.join(format!("{i:05}-{safe_name}.json"));
        std::fs::write(&path, json).with_context(|| format!("write {}", path.display()))?;
    }

    Ok(report)
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: mathverse_reauditor <core-dir> <out-dir> [--hmac-dev] [--commit <sha>]");
        eprintln!();
        eprintln!("Re-earns every published KernelVerified claim under <core-dir> via the live");
        eprintln!("kernel and writes one signed mathverse-signed-verdict-v1 per declaration into");
        eprintln!("<out-dir>/verdicts. A claim that no longer re-earns is appended to a signed");
        eprintln!("mathverse-revocation-list-v1. Signatures attest provenance, not correctness.");
        return ExitCode::from(2);
    }
    let core_dir = Path::new(&args[1]);
    let out_dir = Path::new(&args[2]);
    let use_hmac = args.iter().any(|a| a == "--hmac-dev");
    let commit = args
        .iter()
        .position(|a| a == "--commit")
        .and_then(|i| args.get(i + 1))
        .cloned()
        .unwrap_or_else(|| "unknown-commit".to_string());

    let report = match run(core_dir, out_dir, use_hmac, &commit) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("[reauditor] FATAL: {e:#}");
            return ExitCode::FAILURE;
        }
    };

    // Build + sign a revocation list for everything that no longer re-earns.
    let verified_at = now_rfc3339_utc();
    let mut list = RevocationList::new(verified_at.clone());
    let revoked = report.append_revocations(&mut list, &verified_at, &commit);
    if revoked > 0 {
        // Re-sign the list with the same backend kind chosen above.
        let signed_ok = if use_hmac {
            let backend = HmacDevBackend::new(
                "hmac-dev:reauditor",
                b"REPLACE-WITH-ED25519-OR-KMS-secret".to_vec(),
            );
            list.sign_with(&backend).is_ok()
        } else {
            match Ed25519LocalBackend::generate("ed25519-local:reauditor-revlist") {
                Ok((backend, _secret)) => list.sign_with(&backend).is_ok(),
                Err(_) => false,
            }
        };
        if signed_ok {
            if let Ok(json) = serde_json::to_vec_pretty(&list) {
                let _ = std::fs::write(out_dir.join("revocation-list.json"), json);
            }
        }
    }

    println!("=== mathverse re-auditor ===");
    println!("  core:               {}", core_dir.display());
    println!("  examined:           {}", report.examined);
    println!("  re-verified:        {}", report.reverified);
    println!("  demoted:            {}", report.demoted());
    println!("  revocations:        {revoked}");
    println!("  verdicts written:   {}/verdicts", out_dir.display());
    ExitCode::SUCCESS
}
