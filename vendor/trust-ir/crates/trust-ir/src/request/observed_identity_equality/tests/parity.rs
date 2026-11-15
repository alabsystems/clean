// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn tool_equality_covers_all_four_raw_fields() {
    let a = tool();
    assert!(tool_run(&a, &a).0);
    let mut bs = Vec::new();
    let mut b = a.clone();
    b.name.push('x');
    bs.push(b);
    let mut b = a.clone();
    b.version = Some("x".into());
    bs.push(b);
    let mut b = a.clone();
    b.revision = Some("x".into());
    bs.push(b);
    let mut b = a.clone();
    b.digest = Some(ProofDigest::sha256([8; 32]));
    bs.push(b);
    for b in bs {
        assert!(!tool_run(&a, &b).0);
    }
}
#[test]
fn tool_optional_none_and_some_empty_remain_distinct() {
    for field in [0, 1, 2] {
        let a = NativeToolIdentity::new("raw");
        let mut b = a.clone();
        match field {
            0 => b.version = Some(String::new()),
            1 => b.revision = Some(String::new()),
            _ => b.digest = Some(ProofDigest::sha256([0; 32])),
        }
        assert!(!tool_run(&a, &b).0);
        assert!(!tool_run(&b, &a).0);
    }
}
#[test]
fn canonical_aliases_do_not_replace_raw_provenance_equality() {
    for (a, b) in [
        ("TrustMC", "trust_mc"),
        ("trust-mc", "trustmc"),
        ("ay", "AY"),
        (" v ", "v"),
    ] {
        let a = NativeToolIdentity::new(a);
        let b = NativeToolIdentity::new(b);
        assert!(!tool_run(&a, &b).0);
    }
}
#[test]
fn malformed_but_identical_tool_digest_records_compare_equal_without_validation() {
    let mut a = NativeToolIdentity::new(" ");
    a.version = Some("".into());
    a.digest = Some(ProofDigest {
        algorithm: ProofDigestAlgorithm::TrustIrStableV1,
        bytes: [0; 32],
    });
    assert!(tool_run(&a, &a.clone()).0);
}
#[test]
fn replay_equality_covers_engine_invocation_and_optional_digest() {
    let a = replay();
    assert!(replay_run(&a, &a).0);
    let mut b = a.clone();
    b.engine.push('x');
    assert!(!replay_run(&a, &b).0);
    let mut b = a.clone();
    b.invocation.push('x');
    assert!(!replay_run(&a, &b).0);
    let mut b = a.clone();
    b.transcript_digest = None;
    assert!(!replay_run(&a, &b).0);
}
#[test]
fn replay_empty_and_malformed_equal_data_remain_equal() {
    let mut a = ProofReplayIdentity::new("", "");
    assert!(replay_run(&a, &a.clone()).0);
    a.transcript_digest = Some(ProofDigest {
        algorithm: ProofDigestAlgorithm::TrustIrStableV1,
        bytes: [0; 32],
    });
    assert!(replay_run(&a, &a.clone()).0);
}
#[test]
fn long_same_length_final_byte_differences_are_read_without_truncation() {
    let mut a = tool();
    a.name = "λ🦀".repeat(800) + "a";
    let mut b = a.clone();
    b.name.pop();
    b.name.push('b');
    assert!(!tool_run(&a, &b).0);
    let mut a = replay();
    a.invocation = "λ🦀".repeat(800) + "a";
    let mut b = a.clone();
    b.invocation.pop();
    b.invocation.push('b');
    assert!(!replay_run(&a, &b).0);
}
#[test]
fn digest_algorithm_and_every_recorded_byte_are_part_of_equality() {
    let a = tool();
    for i in 0..32 {
        let mut b = a.clone();
        b.digest.as_mut().unwrap().bytes[i] ^= 1;
        assert!(!tool_run(&a, &b).0);
    }
    let mut b = a.clone();
    b.digest.as_mut().unwrap().algorithm = ProofDigestAlgorithm::TrustIrStableV1;
    assert!(!tool_run(&a, &b).0);
}
