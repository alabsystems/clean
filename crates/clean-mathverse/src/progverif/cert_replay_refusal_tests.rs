// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn assert_refused(strategy: &dyn CertReplayStrategy, format: CertificateFormat, bytes: &[u8]) {
    let cert = Certificate::new(format, bytes.to_vec(), "untrusted-producer")
        .with_metadata("verified", "true");
    match strategy
        .replay(&cert)
        .expect_err("no statement-bound checker is available")
    {
        CertReplayError::ReplayUnavailable { format: name } => {
            assert_eq!(name, cert.format.name());
        }
        other => panic!("wrong reason for refusing {}: {other}", strategy.name()),
    }
}

#[test]
fn alethe_assumption_and_forged_step_cannot_mint_replay() {
    let strategy = AletheLfReplayStrategy::new();
    for bytes in [
        b"(assume ax false)".as_slice(),
        b"(step bad (cl) :rule invented)".as_slice(),
        b"(assume h1 (not P))\n(step t1 (cl P Q) :rule resolution)".as_slice(),
    ] {
        assert_refused(&strategy, CertificateFormat::AletheLF, bytes);
    }
}

#[test]
fn drat_empty_clause_and_unparsed_text_cannot_mint_replay() {
    let strategy = DratReplayStrategy::new();
    for bytes in [
        b"0\n".as_slice(),
        b"not a proof\n".as_slice(),
        b"1 2 0\n-1 3 0\nd 1 2 0\n4 0\n".as_slice(),
    ] {
        assert_refused(&strategy, CertificateFormat::Drat, bytes);
    }
}

#[test]
fn binary_drat_markers_cannot_mint_replay() {
    assert_refused(
        &DratReplayStrategy::new(),
        CertificateFormat::Drat,
        &[b'a', 0],
    );
}

#[test]
fn lrat_empty_clause_and_unparsed_text_cannot_mint_replay() {
    let strategy = DratReplayStrategy::new();
    for bytes in [b"1 0 0\n".as_slice(), b"not a proof\n".as_slice()] {
        assert_refused(&strategy, CertificateFormat::Lrat, bytes);
    }
}

#[test]
fn unimplemented_replayers_advertise_no_checked_formats() {
    assert!(AletheLfReplayStrategy::new().supported_formats().is_empty());
    assert!(DratReplayStrategy::new().supported_formats().is_empty());
}

#[test]
fn malformed_or_empty_inputs_do_not_imply_a_parser_is_available() {
    let alethe = AletheLfReplayStrategy;
    let drat = DratReplayStrategy;
    for bytes in [b"".as_slice(), b" \n".as_slice(), &[0xff, 0xfe]] {
        assert_refused(&alethe, CertificateFormat::AletheLF, bytes);
        assert_refused(&drat, CertificateFormat::Drat, bytes);
        assert_refused(&drat, CertificateFormat::Lrat, bytes);
    }
}

#[test]
fn unrelated_formats_remain_explicitly_unsupported() {
    let cases: [(&dyn CertReplayStrategy, Vec<CertificateFormat>); 2] = [
        (
            &AletheLfReplayStrategy,
            vec![
                CertificateFormat::SmtLib2,
                CertificateFormat::Drat,
                CertificateFormat::Lrat,
                CertificateFormat::Lfsc,
                CertificateFormat::Custom("custom".into()),
            ],
        ),
        (
            &DratReplayStrategy,
            vec![
                CertificateFormat::SmtLib2,
                CertificateFormat::AletheLF,
                CertificateFormat::Lfsc,
                CertificateFormat::Custom("custom".into()),
            ],
        ),
    ];
    for (strategy, formats) in cases {
        for format in formats {
            let cert = Certificate::new(format.clone(), b"0".to_vec(), "untrusted-producer");
            match strategy.replay(&cert).expect_err("format is unsupported") {
                CertReplayError::UnsupportedFormat { format: name } => {
                    assert_eq!(name, format.name())
                }
                other => panic!("wrong reason for refusing {}: {other}", strategy.name()),
            }
        }
    }
}
