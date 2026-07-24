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
            CertCommands::VerifyExternal { cert, verbose } => {
                assert_eq!(cert, PathBuf::from("cert.json"));
                assert!(!verbose);
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
            } => {
                assert_eq!(certs, PathBuf::from("certs.json"));
                assert_eq!(threads, 0);
                assert!(!verbose);
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

// ========== Integration tests ==========

#[test]
fn cert_verify_external_fixture_farkas_passes() {
    handle_cert_command(CertCommands::VerifyExternal {
        cert: fixture_path("gamma_crown_farkas_valid.json"),
        verbose: false,
    })
    .expect("gamma-crown Farkas fixture should verify");
}

#[test]
fn cert_verify_external_fixture_entailment_passes() {
    handle_cert_command(CertCommands::VerifyExternal {
        cert: fixture_path("gamma_crown_entailment_valid.json"),
        verbose: true,
    })
    .expect("gamma-crown entailment fixture should verify");
}

#[test]
fn cert_verify_external_fixture_batch_passes() {
    handle_cert_command(CertCommands::VerifyExternalBatch {
        certs: fixture_path("gamma_crown_batch_valid.json"),
        threads: 2,
        verbose: true,
    })
    .expect("gamma-crown batch fixture should verify");
}

#[test]
fn cert_verify_external_fixture_alethe_matches_feature_gate() {
    let result = handle_cert_command(CertCommands::VerifyExternal {
        cert: fixture_path("ay_alethe_envelope.json"),
        verbose: true,
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
    });
    assert!(result.is_err(), "invalid JSON should fail");
}

#[test]
fn cert_verify_external_nonexistent_fails() {
    let result = handle_cert_command(CertCommands::VerifyExternal {
        cert: PathBuf::from("/nonexistent/cert.json"),
        verbose: false,
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
    })
    .expect("Empty batch should succeed");
}
