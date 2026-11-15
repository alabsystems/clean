// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for external certificate CLI commands (verify-external, verify-external-batch).

use super::cli_args::{Cli, Commands};
use super::cmd_cert::handle_cert_command;
#[cfg(feature = "carcara-verify")]
use clean_elab::cert::external::ExternalCertificate;
use clean_kernel::cli::CertCommands;
use std::fs;
use std::path::{Path, PathBuf};

fn fixture_path(name: &str) -> PathBuf {
    let workspace_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crate directory should have workspace parent")
        .parent()
        .expect("workspace root should exist");
    workspace_root
        .join("tests/fixtures/external_certificates")
        .join(name)
}

// ========== CLI parsing tests ==========

#[test]
fn cli_parse_cert_verify_external() {
    use clap::Parser;
    let cli = Cli::try_parse_from(["clean", "cert", "verify-external", "cert.json"]).unwrap();
    match cli.command {
        Commands::Cert { command } => match command {
            CertCommands::VerifyExternal {
                cert,
                verbose,
                timeout_ms,
            } => {
                assert_eq!(cert, PathBuf::from("cert.json"));
                assert!(!verbose);
                assert_eq!(timeout_ms, 600_000);
            }
            _ => panic!("Expected VerifyExternal command"),
        },
        _ => panic!("Expected Cert command"),
    }
}

#[test]
fn cli_parse_cert_verify_external_verbose() {
    use clap::Parser;
    let cli = Cli::try_parse_from(["clean", "cert", "verify-external", "-v", "cert.json"]).unwrap();
    match cli.command {
        Commands::Cert { command } => match command {
            CertCommands::VerifyExternal { verbose, .. } => {
                assert!(verbose);
            }
            _ => panic!("Expected VerifyExternal command"),
        },
        _ => panic!("Expected Cert command"),
    }
}

#[test]
fn cli_parse_cert_verify_external_batch() {
    use clap::Parser;
    let cli =
        Cli::try_parse_from(["clean", "cert", "verify-external-batch", "certs.json"]).unwrap();
    match cli.command {
        Commands::Cert { command } => match command {
            CertCommands::VerifyExternalBatch {
                certs,
                threads,
                verbose,
                timeout_ms,
            } => {
                assert_eq!(certs, PathBuf::from("certs.json"));
                assert_eq!(threads, 0);
                assert!(!verbose);
                assert_eq!(timeout_ms, 600_000);
            }
            _ => panic!("Expected VerifyExternalBatch command"),
        },
        _ => panic!("Expected Cert command"),
    }
}

#[test]
fn cli_parse_cert_verify_external_batch_threads() {
    use clap::Parser;
    let cli = Cli::try_parse_from([
        "clean",
        "cert",
        "verify-external-batch",
        "-t",
        "4",
        "-v",
        "certs.json",
    ])
    .unwrap();
    match cli.command {
        Commands::Cert { command } => match command {
            CertCommands::VerifyExternalBatch {
                threads, verbose, ..
            } => {
                assert_eq!(threads, 4);
                assert!(verbose);
            }
            _ => panic!("Expected VerifyExternalBatch command"),
        },
        _ => panic!("Expected Cert command"),
    }
}

#[test]
fn cli_parse_cert_verify_external_timeout() {
    use clap::Parser;
    let cli = Cli::try_parse_from([
        "clean",
        "cert",
        "verify-external",
        "--timeout-ms",
        "0",
        "cert.json",
    ])
    .unwrap();
    match cli.command {
        Commands::Cert {
            command: CertCommands::VerifyExternal { timeout_ms, .. },
        } => assert_eq!(timeout_ms, 0),
        _ => panic!("Expected VerifyExternal command"),
    }
}

// ========== Integration tests ==========

#[test]
fn cert_verify_external_fixture_farkas_passes() {
    handle_cert_command(CertCommands::VerifyExternal {
        cert: fixture_path("gamma_crown_farkas_valid.json"),
        verbose: false,
        timeout_ms: 600_000,
    })
    .expect("gamma-crown Farkas fixture should verify");
}

#[test]
fn cert_verify_external_fixture_entailment_passes() {
    handle_cert_command(CertCommands::VerifyExternal {
        cert: fixture_path("gamma_crown_entailment_valid.json"),
        verbose: true,
        timeout_ms: 600_000,
    })
    .expect("gamma-crown entailment fixture should verify");
}

#[test]
fn cert_verify_external_fixture_batch_passes() {
    handle_cert_command(CertCommands::VerifyExternalBatch {
        certs: fixture_path("gamma_crown_batch_valid.json"),
        threads: 2,
        verbose: true,
        timeout_ms: 600_000,
    })
    .expect("gamma-crown batch fixture should verify");
}

#[test]
fn cert_verify_external_fixture_alethe_matches_feature_gate() {
    let result = handle_cert_command(CertCommands::VerifyExternal {
        cert: fixture_path("ay_alethe_envelope.json"),
        verbose: true,
        timeout_ms: 600_000,
    });

    #[cfg(feature = "carcara-verify")]
    result.expect("Alethe fixture should verify when carcara-verify is enabled");

    #[cfg(not(feature = "carcara-verify"))]
    {
        let err =
            result.expect_err("Alethe fixture should report verifier gate without carcara-verify");
        let err_text = format!("{err:#}");
        assert!(
            err_text.contains("carcara-verify feature required"),
            "expected carcara feature gate error, got: {err_text}"
        );
    }
}

#[cfg(feature = "carcara-verify")]
#[test]
fn cert_verify_external_fixture_alethe_holey_reports_verification_failure() {
    let dir = tempfile::tempdir().expect("tempdir should be created");
    let cert_path = dir.path().join("ay_alethe_holey.json");
    let json = fs::read_to_string(fixture_path("ay_alethe_envelope.json"))
        .expect("Alethe fixture should be readable");
    let mut cert: ExternalCertificate =
        serde_json::from_str(&json).expect("Alethe fixture should deserialize");
    match &mut cert {
        ExternalCertificate::Alethe(alethe) => {
            let marker = ":rule ";
            let start = alethe
                .proof
                .find(marker)
                .map(|i| i + marker.len())
                .expect("Alethe fixture proof should contain a rule marker");
            let end = alethe.proof[start..]
                .find(|c: char| c.is_whitespace() || c == ')')
                .map(|i| start + i)
                .expect("Alethe fixture rule should terminate");
            assert_ne!(
                &alethe.proof[start..end],
                "hole",
                "fixture mutation must change the rule name"
            );
            alethe.proof = format!("{}hole{}", &alethe.proof[..start], &alethe.proof[end..]);
        }
        other => panic!("expected Alethe fixture, got {other:?}"),
    }
    fs::write(
        &cert_path,
        serde_json::to_vec(&cert).expect("mutated Alethe fixture should serialize"),
    )
    .expect("mutated Alethe fixture should be writable");

    let err = handle_cert_command(CertCommands::VerifyExternal {
        cert: cert_path,
        verbose: true,
        timeout_ms: 600_000,
    })
    .expect_err("holey Alethe fixture should fail at the CLI boundary");
    let err_text = format!("{err:#}");
    assert!(
        err_text.contains("proof_verification_failed"),
        "CLI should classify holey Alethe proofs as proof_verification_failed: {err_text}"
    );
    assert!(
        err_text.contains("holey or incomplete"),
        "CLI should preserve the holey/incomplete failure detail: {err_text}"
    );
}

#[test]
fn cert_verify_external_invalid_json_fails() {
    let dir = tempfile::tempdir().expect("tempdir should be created");
    let cert_path = dir.path().join("invalid.json");
    fs::write(&cert_path, "not valid json").expect("write should succeed");

    let result = handle_cert_command(CertCommands::VerifyExternal {
        cert: cert_path,
        verbose: false,
        timeout_ms: 600_000,
    });
    assert!(result.is_err(), "invalid JSON should fail");
}

#[test]
fn cert_verify_external_nonexistent_fails() {
    let result = handle_cert_command(CertCommands::VerifyExternal {
        cert: PathBuf::from("/nonexistent/cert.json"),
        verbose: false,
        timeout_ms: 600_000,
    });
    assert!(result.is_err(), "nonexistent file should fail");
}

#[test]
fn cert_verify_external_batch_empty() {
    let dir = tempfile::tempdir().expect("tempdir should be created");
    let certs_path = dir.path().join("empty.json");
    fs::write(&certs_path, "[]").expect("write should succeed");

    handle_cert_command(CertCommands::VerifyExternalBatch {
        certs: certs_path,
        threads: 0,
        verbose: false,
        timeout_ms: 600_000,
    })
    .expect("Empty batch should succeed");
}

/// `--timeout-ms` bounds an Alethe check: `refl` over two chains of conjunctions of two quantifiers
/// over the level below, named apart, where level `i`'s two quantifiers bind `x(i-1)` at different
/// indices and the leaves read every `xi`, compares every path with that path's bindings, `2^40`
/// times, which the vendored checker's step budget does not bound (`third-party/carcara/
/// DOWNSTREAM.md`, "The checker stops at a deadline"). It is refused as `timeout` once the limit
/// passes.
#[cfg(feature = "carcara-verify")]
#[test]
fn cert_verify_external_alethe_stops_at_its_timeout() {
    let declarations: String = (0..=40)
        .map(|i| format!("(declare-const x{i} Int)"))
        .collect();
    let problem =
        format!("(set-logic ALL)(declare-const p Bool){declarations}(assert p)(assert (not p))");
    let leaves: String = (0..=40).map(|i| format!(" (= x{i} 0)")).collect();
    // The levels are defined in the proof, where the binders they are used under capture the names
    // `xi` their definitions read (a problem's definitions may not be captured).
    let mut proof =
        format!("(define-fun a0 () Bool (and{leaves}))(define-fun b0 () Bool (and{leaves}))");
    for i in 1..=40 {
        let j = i - 1;
        proof += &format!(
            "(define-fun a{i} () Bool \
               (and (forall ((x{j} Int)) a{j}) (forall ((y Int) (x{j} Int)) a{j})))\
             (define-fun b{i} () Bool \
               (and (forall ((x{j} Int)) b{j}) (forall ((w Int) (x{j} Int)) b{j})))"
        );
    }
    proof += "(step t1 (cl (= (forall ((x40 Int)) a40) (forall ((x40 Int)) b40))) :rule refl)\
        (assume h1 p)(assume h2 (not p))(step t2 (cl) :rule resolution :premises (h1 h2))";
    let cert = serde_json::json!({
        "type": "alethe_certificate",
        "version": "1.0",
        "problem": problem,
        "proof": proof,
    });
    let dir = tempfile::tempdir().expect("tempdir should be created");
    let cert_path = dir.path().join("alpha_chain.json");
    fs::write(&cert_path, cert.to_string()).expect("write should succeed");

    let started = std::time::Instant::now();
    let err = handle_cert_command(CertCommands::VerifyExternal {
        cert: cert_path,
        verbose: false,
        timeout_ms: 200,
    })
    .expect_err("the check must stop at its timeout");
    assert!(format!("{err:#}").contains("timeout"), "{err:#}");
    assert!(started.elapsed() < std::time::Duration::from_secs(60));
}
