// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![cfg(feature = "native-transport-json")]

use trust_ir::request::transport::{
    NATIVE_BUNDLE_REPLAY_FORMULA_REF_ENCODING, native_bundle_transport_payload,
    rehydrate_native_bundle_transport_payload,
};
use trust_ir::request::*;
use trust_ir::{
    FuncId, Module, ObligationKind, ProofDigest, ProofFormula, ProofId, ProofLineageManifest,
    ProofObligation, ProofStatus,
};

// Synthetic codec inputs only: these tests claim neither source provenance nor
// native admission/replay. The compiler tests exercise its genuine native input.
fn bundle() -> NativeVerificationBundle {
    let shared = ProofFormula::smtlib2("(= result arg)", "Bool");
    let mut module = Module::new("transport-codec");
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Pending,
            "codec input",
        )
        .with_formula(shared.clone()),
    );
    let source = ProofDigest::sha256_domain("trust-ir.test.codec-source.v1", b"codec");
    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TRust,
        NativeAdapterInput::RustMir {
            body_digest: source,
        },
        module.stable_digest(),
        module,
        ProofLineageManifest::default(),
    );
    for id in [3, 4] {
        let mut provenance = NativeRequestProvenance::new(
            NativeVerifierSuite::TrustWp,
            NativeToolIdentity::new("trust-wp"),
        );
        provenance.replay_context = NativeReplayContext::default()
            .with_atom(
                NativeReplayAtom::assertion(NativeReplayAtomId::new(0), shared.clone())
                    .with_obligation(ProofId::new(0)),
            )
            .with_atom(
                NativeReplayAtom::assumption(
                    NativeReplayAtomId::new(1),
                    ProofFormula::smtlib2("true", "Bool"),
                )
                .with_obligation(ProofId::new(0)),
            );
        bundle
            .requests
            .push(NativeVerificationRequest::TrustWp(TrustWpNativeRequest {
                id: NativeRequestId::new(id),
                mode: TrustWpVerificationMode::WeakestPrecondition,
                function: FuncId::new(0),
                obligations: vec![ProofId::new(0)],
                lineage_roots: vec![],
                options: TrustWpRequestOptions::default(),
                diagnostics: NativeDiagnosticsPolicy::default(),
                provenance,
            }));
    }
    bundle
}

fn scoped(mut bundle: NativeVerificationBundle) -> NativeVerificationBundle {
    bundle.requests.retain(
        |request| matches!(request, NativeVerificationRequest::TrustWp(wp) if wp.id.index() == 3),
    );
    assert_eq!(bundle.requests.len(), 1);
    bundle
}

#[test]
fn shared_formula_transport_restores_the_exact_typed_bundle_and_digest() {
    let bundle = bundle();
    let payload = native_bundle_transport_payload(&bundle).unwrap();
    assert_eq!(
        payload["encoding"],
        NATIVE_BUNDLE_REPLAY_FORMULA_REF_ENCODING
    );
    assert_eq!(payload.as_object().unwrap().len(), 2);
    for request in payload["bundle"]["requests"].as_array().unwrap() {
        let atoms = request["TrustWp"]["provenance"]["replay_context"]["atoms"]
            .as_array()
            .unwrap();
        assert_eq!(
            atoms[0]["formula_ref"],
            serde_json::json!({"obligation": 0})
        );
        assert!(atoms[0].get("formula").is_none());
        assert!(atoms[1].get("formula_ref").is_none());
        assert_eq!(
            atoms[1]["formula"],
            serde_json::to_value(&bundle.requests[0].provenance().replay_context.atoms[1].formula)
                .unwrap()
        );
    }
    let restored = rehydrate_native_bundle_transport_payload(&payload).unwrap();
    assert_eq!(restored, bundle);
    assert_eq!(restored.stable_digest(), bundle.stable_digest());
    assert_eq!(native_bundle_transport_payload(&restored).unwrap(), payload);
    // Both admitted transport shapes remain valid. Re-encoding a fully
    // inline bundle may choose references; that is not loss of typed content.
    let mut inline = payload.clone();
    inline["bundle"] = serde_json::to_value(&bundle).unwrap();
    assert_eq!(
        rehydrate_native_bundle_transport_payload(&inline).unwrap(),
        bundle
    );
    let mut reordered = inline.clone();
    let object = reordered["bundle"].as_object_mut().unwrap();
    let producer = object.remove("producer").unwrap();
    object.insert("producer".into(), producer);
    assert_eq!(
        rehydrate_native_bundle_transport_payload(&reordered).unwrap(),
        bundle
    );
    // The compressed inner object is deliberately not a typed bundle.
    assert!(serde_json::from_value::<NativeVerificationBundle>(payload["bundle"].clone()).is_err());
}

#[test]
fn scoped_identity_retains_selected_input_after_lossless_transport() {
    let original = bundle();
    let payload = native_bundle_transport_payload(&original).unwrap();
    let restored = rehydrate_native_bundle_transport_payload(&payload).unwrap();
    let expected = scoped(original.clone()).stable_digest();
    assert_eq!(scoped(restored.clone()).stable_digest(), expected);
    assert_ne!(restored.stable_digest(), expected);

    let mut other_request = restored.clone();
    if let NativeVerificationRequest::TrustWp(wp) = &mut other_request.requests[1] {
        wp.options.max_abduced_preconditions += 1;
    }
    assert_ne!(other_request.stable_digest(), restored.stable_digest());
    assert_eq!(scoped(other_request).stable_digest(), expected);

    let mut selected_request = restored.clone();
    if let NativeVerificationRequest::TrustWp(wp) = &mut selected_request.requests[0] {
        wp.options.max_abduced_preconditions += 1;
    }
    assert_ne!(scoped(selected_request).stable_digest(), expected);

    let mut original_input = restored;
    original_input
        .provenance
        .producer_version
        .push_str("changed");
    assert_ne!(scoped(original_input).stable_digest(), expected);
}

#[test]
fn shared_formula_transport_refuses_ambiguous_mismatched_and_changed_references() {
    let payload = native_bundle_transport_payload(&bundle()).unwrap();
    for mutation in 0..10 {
        let mut changed = payload.clone();
        let atom = &mut changed["bundle"]["requests"][0]["TrustWp"]["provenance"]["replay_context"]
            ["atoms"][0];
        match mutation {
            0 => atom["formula_ref"]["obligation"] = 1.into(),
            1 => {
                atom["obligation"] = 1.into();
                atom["formula_ref"]["obligation"] = 1.into();
            }
            2 => atom["formula"] = serde_json::json!({"schema": "x", "payload": "y"}),
            3 => atom["formula_ref"]["extra"] = true.into(),
            4 => {
                let byte = &mut atom["payload_digest"]["bytes"][0];
                *byte = (byte.as_u64().unwrap() ^ 1).into();
            }
            5 => {
                changed["bundle"]["module"]["proof_obligations"][0]["formula"]["payload"] =
                    "false".into();
            }
            6 => {
                let obligations = changed["bundle"]["module"]["proof_obligations"]
                    .as_array_mut()
                    .unwrap();
                obligations.push(obligations[0].clone());
            }
            7 => changed["encoding"] = "unsupported".into(),
            8 => {
                changed["bundle"]["requests"][0]["TrustWp"]
                    .as_object_mut()
                    .unwrap()
                    .remove("options")
                    .unwrap();
            }
            _ => changed["bundle"]["requests"][0]["TrustWp"]["unknown_identity"] = true.into(),
        }
        assert_ne!(changed, payload, "mutation {mutation}");
        assert!(
            rehydrate_native_bundle_transport_payload(&changed).is_err(),
            "mutation {mutation}"
        );
    }
    assert!(rehydrate_native_bundle_transport_payload(&payload["bundle"]).is_err());
}

#[test]
fn formula_less_duplicate_obligation_ids_are_rejected_in_either_order() {
    for formula_first in [false, true] {
        let mut payload = native_bundle_transport_payload(&bundle()).unwrap();
        let obligations = payload["bundle"]["module"]["proof_obligations"]
            .as_array_mut()
            .unwrap();
        let mut duplicate = obligations[0].clone();
        // This is the exact serde representation of formula: None, so typed
        // roundtrip comparison alone cannot identify the duplicated identity.
        duplicate["formula"] = serde_json::Value::Null;
        if formula_first {
            obligations.push(duplicate);
        } else {
            obligations.insert(0, duplicate);
        }
        let error = rehydrate_native_bundle_transport_payload(&payload).unwrap_err();
        assert!(error.contains("module proof obligation id 0 is repeated"));
    }
}
