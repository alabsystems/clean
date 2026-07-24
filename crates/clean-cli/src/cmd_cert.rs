// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof certificate verification command handlers.

use anyhow::{anyhow, bail, Context};
use clean_elab::cert::external::verify_alethe_certificate;
use clean_elab::cert::{
    verify_entailment_certificate, verify_farkas_certificate, ExternalCertificate,
};
use clean_kernel::cert::{CertVerifier, ProofCert};
use clean_kernel::cli::CertCommands;
use clean_kernel::{Environment, Expr};
use rayon::prelude::*;
use std::path::Path;
use std::time::Instant;

pub(crate) fn handle_cert_command(command: CertCommands) -> anyhow::Result<()> {
    match command {
        CertCommands::Verify {
            cert,
            expr,
            env,
            minimal_env,
            verbose,
        } => cert_verify(&cert, &expr, env.as_deref(), minimal_env, verbose),
        CertCommands::VerifyExternal { cert, verbose } => cert_verify_external(&cert, verbose),
        CertCommands::VerifyExternalBatch {
            certs,
            threads,
            verbose,
        } => cert_verify_external_batch(&certs, threads, verbose),
    }
}

fn load_cert_env(env_path: Option<&Path>, minimal_env: bool) -> anyhow::Result<Environment> {
    if let Some(path) = env_path {
        let env_content = std::fs::read_to_string(path)?;
        let env: Environment = serde_json::from_str(&env_content)
            .map_err(|e| anyhow::anyhow!("Failed to parse environment: {e}"))?;
        Ok(env)
    } else if minimal_env {
        Ok(Environment::new())
    } else {
        Ok(Environment::with_prelude())
    }
}

fn cert_verify(
    cert_path: &Path,
    expr_path: &Path,
    env_path: Option<&Path>,
    minimal_env: bool,
    verbose: bool,
) -> anyhow::Result<()> {
    let cert_content = std::fs::read_to_string(cert_path)?;
    let cert: ProofCert = serde_json::from_str(&cert_content)
        .map_err(|e| anyhow::anyhow!("Failed to parse certificate: {e}"))?;

    let expr_content = std::fs::read_to_string(expr_path)?;
    let expr: Expr = serde_json::from_str(&expr_content)
        .map_err(|e| anyhow::anyhow!("Failed to parse expression: {e}"))?;

    let env = load_cert_env(env_path, minimal_env)?;
    let mut verifier = CertVerifier::with_mode(&env, env.mode());

    let start = Instant::now();
    match verifier.verify(&cert, &expr) {
        Ok(ty) => {
            let elapsed = start.elapsed();
            println!("Certificate verification: PASSED");
            if verbose {
                let ty_pp = clean_server::proof_state::pp_expr(&ty, &env);
                println!("  Verified type: {}", ty_pp);
            }
            println!("  Verified in {:.3}s", elapsed.as_secs_f64());
            Ok(())
        }
        Err(err) => {
            let elapsed = start.elapsed();
            println!("Certificate verification: FAILED");
            println!("  Error: {err}");
            println!("  Time: {:.3}s", elapsed.as_secs_f64());
            std::process::exit(1);
        }
    }
}

fn load_external_certificate(cert_path: &Path) -> anyhow::Result<ExternalCertificate> {
    let cert_content = std::fs::read_to_string(cert_path).with_context(|| {
        format!(
            "Failed to read external certificate file: {}",
            cert_path.display()
        )
    })?;
    serde_json::from_str(&cert_content).with_context(|| {
        format!(
            "Failed to parse external certificate JSON: {}",
            cert_path.display()
        )
    })
}

fn load_external_certificate_batch(certs_path: &Path) -> anyhow::Result<Vec<ExternalCertificate>> {
    let certs_content = std::fs::read_to_string(certs_path).with_context(|| {
        format!(
            "Failed to read external certificate batch file: {}",
            certs_path.display()
        )
    })?;
    serde_json::from_str(&certs_content).with_context(|| {
        format!(
            "Failed to parse external certificate batch JSON: {}",
            certs_path.display()
        )
    })
}

fn external_certificate_label(cert: &ExternalCertificate) -> &'static str {
    match cert {
        ExternalCertificate::Farkas(_) => "Farkas infeasibility",
        ExternalCertificate::Entailment(_) => "Entailment",
        ExternalCertificate::Alethe(_) => "Alethe SMT proof",
    }
}

fn verify_external_certificate(cert: &ExternalCertificate) -> anyhow::Result<Vec<String>> {
    match cert {
        ExternalCertificate::Farkas(farkas) => {
            let contradiction_value = verify_farkas_certificate(farkas)
                .map_err(|err| anyhow!("{}: {}", err.code.as_str(), err.detail))?;
            Ok(vec![
                format!("Constraints: {}", farkas.constraints.len()),
                format!(
                    "Contradiction value: {}",
                    contradiction_value.to_compact_string()
                ),
            ])
        }
        ExternalCertificate::Entailment(entailment) => {
            let (derived_bound, claimed_bound) = verify_entailment_certificate(entailment)
                .map_err(|err| anyhow!("{}: {}", err.code.as_str(), err.detail))?;
            Ok(vec![
                format!("Premises: {}", entailment.premises.len()),
                format!("Derived bound: {}", derived_bound.to_compact_string()),
                format!("Claimed bound: {}", claimed_bound.to_compact_string()),
            ])
        }
        ExternalCertificate::Alethe(alethe) => match verify_alethe_certificate(alethe) {
            Ok(true) => Ok(vec![
                format!(
                    "Problem bytes: {}, proof bytes: {}",
                    alethe.problem.len(),
                    alethe.proof.len()
                ),
                "Proof status: fully verified".to_string(),
            ]),
            Ok(false) => bail!(
                "proof_verification_failed: Alethe proof was accepted only as holey or incomplete"
            ),
            Err(err) => bail!("{}: {}", err.code.as_str(), err.detail),
        },
    }
}

struct BatchItemResult {
    index: usize,
    success: bool,
    message: String,
}

fn verify_external_batch_item(index: usize, cert: &ExternalCertificate) -> BatchItemResult {
    let kind = external_certificate_label(cert);
    match verify_external_certificate(cert) {
        Ok(_) => BatchItemResult {
            index,
            success: true,
            message: format!("{kind}: PASSED"),
        },
        Err(err) => BatchItemResult {
            index,
            success: false,
            message: format!("{kind}: FAILED — {err}"),
        },
    }
}

fn cert_verify_external(cert_path: &Path, verbose: bool) -> anyhow::Result<()> {
    let cert = load_external_certificate(cert_path)?;
    let cert_type = external_certificate_label(&cert);
    let start = Instant::now();

    match verify_external_certificate(&cert) {
        Ok(detail_lines) => {
            let elapsed = start.elapsed();
            println!("External certificate verification: PASSED");
            println!("  Type: {cert_type}");
            if verbose {
                for detail in detail_lines {
                    println!("  {detail}");
                }
            }
            println!("  Verified in {:.6}s", elapsed.as_secs_f64());
            Ok(())
        }
        Err(err) => {
            let elapsed = start.elapsed();
            println!("External certificate verification: FAILED");
            println!("  Type: {cert_type}");
            println!("  Error: {err}");
            println!("  Time: {:.6}s", elapsed.as_secs_f64());
            Err(err)
        }
    }
}

fn cert_verify_external_batch(
    certs_path: &Path,
    threads: usize,
    verbose: bool,
) -> anyhow::Result<()> {
    let certs = load_external_certificate_batch(certs_path)?;
    if certs.is_empty() {
        println!("No certificates to verify.");
        return Ok(());
    }

    println!("Verifying {} external certificates...", certs.len());

    let start = Instant::now();
    let results: Vec<BatchItemResult> = if threads == 0 {
        certs
            .iter()
            .enumerate()
            .map(|(index, cert)| verify_external_batch_item(index, cert))
            .collect()
    } else {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build()
            .context("Failed to build rayon thread pool")?;
        pool.install(|| {
            certs
                .par_iter()
                .enumerate()
                .map(|(index, cert)| verify_external_batch_item(index, cert))
                .collect()
        })
    };

    let elapsed = start.elapsed();
    let passed = results.iter().filter(|result| result.success).count();
    let failed = results.len() - passed;

    if verbose || failed > 0 {
        for result in &results {
            if verbose || !result.success {
                println!("  [{}] {}", result.index, result.message);
            }
        }
    }

    println!(
        "Batch verification complete: {}/{} passed, {} failed",
        passed,
        results.len(),
        failed
    );
    println!("  Total time: {:.6}s", elapsed.as_secs_f64());

    if failed > 0 {
        bail!("batch verification failed for {failed} certificate(s)");
    }

    Ok(())
}
