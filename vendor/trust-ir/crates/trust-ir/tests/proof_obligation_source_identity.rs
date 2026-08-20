// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_ir::value::{FuncId, ProofId};
use trust_ir::{
    Module, ObligationKind, ProofDigest, ProofObligation, ProofObligationSourceIdentity,
    ProofObligationSourceRange, ProofStatus, PublicObligationIdentity,
};

fn source_identity() -> ProofObligationSourceIdentity {
    ProofObligationSourceIdentity::new("Rust + Lean::módulo α", "assertión exacta 7")
        .with_range(ProofObligationSourceRange {
            file: 0,
            start_line: 17,
            start_col: 3,
            end_line: 19,
            end_col: 11,
        })
        .with_public(PublicObligationIdentity {
            obligation_id: "rust:crate::checked_add/assert:7".to_string(),
            semantic_digest: ProofDigest::sha256_domain(
                "proof-obligation-source-test.v1",
                b"public claim",
            ),
        })
}

fn module_with_source() -> Module {
    let mut module = Module::new("source_identity");
    module.intern_file("src/módulo.rs");
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(7),
            ObligationKind::Precondition,
            ProofStatus::Pending,
            "frontend assertion",
        )
        .with_function(FuncId::new(3))
        .with_source(source_identity()),
    );
    module
}

#[test]
fn lookup_preserves_sparse_proof_ids_and_exact_source_text() {
    let module = module_with_source();
    let source = module
        .proof_obligation_source(ProofId::new(7))
        .expect("sparse proof id lookup");
    assert_eq!(source, &source_identity());
    assert_eq!(source.range.expect("range").end_line, 19);
    assert_eq!(source.range.expect("range").end_col, 11);
    assert!(module.proof_obligation_source(ProofId::new(0)).is_none());
}

#[test]
fn module_stable_digest_binds_every_embedded_source_identity_field() {
    let module = module_with_source();
    let digest = module.stable_digest();
    let mutations: &[fn(&mut ProofObligationSourceIdentity)] = &[
        |source| source.source_id.push('!'),
        |source| source.assertion_id.push('!'),
        |source| source.range.as_mut().unwrap().file += 1,
        |source| source.range.as_mut().unwrap().start_line += 1,
        |source| source.range.as_mut().unwrap().start_col += 1,
        |source| source.range.as_mut().unwrap().end_line += 1,
        |source| source.range.as_mut().unwrap().end_col += 1,
        |source| source.public.as_mut().unwrap().obligation_id.push('!'),
        |source| source.public.as_mut().unwrap().semantic_digest.bytes[0] ^= 1,
    ];
    for mutate in mutations {
        let mut changed = module.clone();
        mutate(changed.proof_obligations[0].source.as_mut().unwrap());
        assert_ne!(
            changed.stable_digest(),
            digest,
            "source mutation must invalidate the module identity"
        );
    }
}

#[cfg(feature = "binary")]
#[test]
fn binary_current_version_roundtrip_preserves_complete_embedded_identity() {
    let module = module_with_source();
    let encoded = trust_ir::binary::serialize_module(&module);
    // The embedded obligation-source identity landed in v28 and has been
    // written unconditionally since v29 (the merged-superset version; v26..=v28
    // are ambiguous-lineage and refused on read — see the VERSION ledger in
    // binary.rs). v30 appended the typed-value-model tables, v31 extended enum
    // records additively, v32 appended value names, and v33 appended lexical
    // scopes, and v34 appended the obligation SITE backref. That is why this
    // assertion tracks the current version rather than pinning 29: the
    // source-identity bytes are unmoved by those changes, and the round-trip
    // below is what proves it.
    assert_eq!(
        u32::from_le_bytes(encoded[8..12].try_into().unwrap()),
        trust_ir::binary::VERSION,
    );
    let decoded = trust_ir::binary::deserialize_module(&encoded).expect("decode module");
    assert_eq!(decoded, module);
}

#[cfg(feature = "parser")]
#[test]
fn text_roundtrip_preserves_complete_embedded_identity() {
    let module = module_with_source();
    let text = module.to_string();
    assert!(text.contains("source \"Rust + Lean::módulo α\""));
    assert!(text.contains("range 0 17 3 19 11"));
    let decoded = trust_ir::parser::parse_module(&text).expect("parse source identity");
    assert_eq!(decoded, module);
}

#[cfg(feature = "serde")]
#[test]
fn serde_roundtrips_source_after_explicit_none_function() {
    let mut obligation = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Precondition,
        ProofStatus::Pending,
        "unscoped",
    );
    obligation.source = Some(source_identity());

    let json = serde_json::to_string(&obligation).expect("encode JSON");
    assert!(
        json.contains("\"function\":null"),
        "function None must occupy its positional slot before source: {json}"
    );
    let from_json: ProofObligation = serde_json::from_str(&json).expect("decode JSON");
    assert_eq!(from_json, obligation);

    let messagepack = rmp_serde::to_vec(&obligation).expect("encode MessagePack");
    let from_messagepack: ProofObligation =
        rmp_serde::from_slice(&messagepack).expect("decode MessagePack");
    assert_eq!(from_messagepack, obligation);
}

#[cfg(feature = "serde")]
#[test]
fn legacy_serde_obligation_defaults_trailing_source_to_none() {
    #[derive(serde::Serialize)]
    struct LegacyProofObligation {
        id: ProofId,
        kind: ObligationKind,
        status: ProofStatus,
        description: String,
        formula: Option<trust_ir::ProofFormula>,
        function: Option<FuncId>,
    }

    let legacy = LegacyProofObligation {
        id: ProofId::new(4),
        kind: ObligationKind::Postcondition,
        status: ProofStatus::Pending,
        description: "legacy".to_string(),
        formula: None,
        function: Some(FuncId::new(2)),
    };
    let messagepack = rmp_serde::to_vec(&legacy).expect("encode legacy MessagePack");
    let decoded: ProofObligation =
        rmp_serde::from_slice(&messagepack).expect("decode legacy MessagePack");
    assert_eq!(decoded.id, ProofId::new(4));
    assert_eq!(decoded.function, Some(FuncId::new(2)));
    assert!(decoded.source.is_none());

    let json = serde_json::to_string(&legacy).expect("encode legacy JSON");
    let decoded: ProofObligation = serde_json::from_str(&json).expect("decode legacy JSON");
    assert!(decoded.source.is_none());
}
