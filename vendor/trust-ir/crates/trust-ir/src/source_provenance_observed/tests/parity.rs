// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn complete_ordered_unicode_name_place_preimage_matches_original_binding_check() {
    let source = fixture();
    assert!(parity(&source));
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        binding_digest(&source, &mut session, site()).unwrap(),
        source.compute_binding_digest()
    );
}
#[test]
fn empty_maps_and_semantically_invalid_rows_are_identity_only_not_authority() {
    let mut source = SourceProvenance::new(ProofDigest::zero(), ProofDigest::zero(), vec![]);
    assert!(parity(&source));
    source.loops = fixture().loops;
    source.loops[1].source_loop_id = 0;
    source.loops[0].bindings[0].name = " ".into();
    assert!(!parity(&source));
    // Reconstructing fixture input through the existing constructor keeps the
    // same behavior even though full validator injectivity/blank checks refuse.
    let source = SourceProvenance::new(
        source.compiler_source_digest,
        source.semantic_body_digest,
        source.loops,
    );
    assert!(parity(&source));
}
#[test]
fn every_ordered_identity_field_and_stored_digest_tamper_is_detected() {
    let source = fixture();
    let mut cases = Vec::new();
    let mut s = source.clone();
    s.schema += 1;
    cases.push(s);
    let mut s = source.clone();
    s.compiler_source_digest.bytes[31] ^= 1;
    cases.push(s);
    let mut s = source.clone();
    s.semantic_body_digest.algorithm = ProofDigestAlgorithm::Sha256;
    cases.push(s);
    let mut s = source.clone();
    s.binding_digest.bytes[0] ^= 1;
    cases.push(s);
    let mut s = source.clone();
    s.loops.swap(0, 1);
    cases.push(s);
    let mut s = source.clone();
    s.loops[0].source_loop_id += 1;
    cases.push(s);
    let mut s = source.clone();
    s.loops[0].hir_local_id += 1;
    cases.push(s);
    let mut s = source.clone();
    s.loops[0].header = BlockId::new(11);
    cases.push(s);
    let mut s = source.clone();
    s.loops[0].bindings.swap(0, 1);
    cases.push(s);
    let mut s = source.clone();
    s.loops[0].bindings[0].name.push('λ');
    cases.push(s);
    let mut s = source.clone();
    s.loops[0].bindings[0].hir_local_id += 1;
    cases.push(s);
    let mut s = source.clone();
    s.loops[0].bindings[0].place = SourcePlace::LoopParameter { index: 2 };
    cases.push(s);
    let mut s = source;
    s.loops[0].bindings[0].place = SourcePlace::FunctionParameter { index: 3 };
    cases.push(s);
    for source in cases {
        assert!(!parity(&source));
    }
}
#[test]
fn both_input_digest_algorithm_tags_and_all32bytes_match_original_encoding() {
    for compiler in [
        ProofDigestAlgorithm::Sha256,
        ProofDigestAlgorithm::TrustIrStableV1,
    ] {
        for body in [
            ProofDigestAlgorithm::Sha256,
            ProofDigestAlgorithm::TrustIrStableV1,
        ] {
            for byte in [0, 1, 255] {
                let source = SourceProvenance::new(
                    digest(compiler, byte),
                    digest(body, byte),
                    fixture().loops,
                );
                assert!(parity(&source));
            }
        }
    }
}
#[test]
fn wide_name_payload_is_fully_bound_and_not_truncated_to_a_chunk_prefix() {
    let mut source = fixture();
    source.loops[0].bindings[0].name = "λ".repeat(7000);
    let source = SourceProvenance::new(
        source.compiler_source_digest,
        source.semantic_body_digest,
        source.loops,
    );
    assert!(parity(&source));
    let mut tampered = source;
    tampered.loops[0].bindings[0].name.push('z');
    assert!(!parity(&tampered));
}
#[test]
fn original_big_endian_count_saturation_is_not_a_payload_truncation_policy() {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut writer = Writer {
        session: &mut session,
        site: site(),
        bytes: Vec::new(),
    };
    for n in [0usize, 1, u32::MAX as usize] {
        writer.count(n).unwrap();
    }
    if let Some(n) = (u32::MAX as usize).checked_add(1) {
        writer.count(n).unwrap();
        assert_eq!(&writer.bytes[12..], &u32::MAX.to_be_bytes());
    }
    assert_eq!(&writer.bytes[..4], &0u32.to_be_bytes());
    assert_eq!(&writer.bytes[4..8], &1u32.to_be_bytes());
    assert_eq!(&writer.bytes[8..12], &u32::MAX.to_be_bytes());
    writer.retire();
    assert_eq!(writer.bytes.capacity(), 0);
    let source = fixture();
    let mut writer = Writer {
        session: writer.session,
        site: site(),
        bytes: Vec::new(),
    };
    writer.preimage(&source).unwrap();
    let names = source
        .loops
        .iter()
        .flat_map(|row| &row.bindings)
        .map(|row| 13 + row.name.len())
        .sum::<usize>();
    assert_eq!(writer.bytes.len(), 74 + 16 * source.loops.len() + names);
    writer.retire();
}
