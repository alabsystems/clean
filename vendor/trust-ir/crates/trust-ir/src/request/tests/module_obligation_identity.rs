use super::*;

#[test]
fn native_bundle_refuses_duplicate_module_obligation_declarations() {
    let original = source_generation_authority_bundle();
    original.validate().expect("unique original declarations");
    for conflicting in [false, true] {
        let mut bundle = original.clone();
        let mut duplicate = bundle.module.proof_obligations[0].clone();
        if conflicting {
            duplicate.formula = Some(ProofFormula::smtlib2("false", "Bool"));
        }
        bundle.module.proof_obligations.push(duplicate);
        refresh_native_bundle_module_identity(&mut bundle);
        assert_eq!(
            bundle.validate(),
            Err(vec![
                NativeVerificationBundleError::DuplicateModuleObligationId(ProofId::new(0))
            ]),
            "one ProofId must not name multiple declarations (conflicting={conflicting})",
        );
    }
}

#[test]
fn validated_native_view_refuses_duplicate_module_obligation_declarations() {
    let mut bundle = source_generation_authority_bundle();
    ValidatedNativeBundle::new(&bundle).expect("unique original declarations");
    bundle
        .module
        .proof_obligations
        .push(bundle.module.proof_obligations[0].clone());
    refresh_native_bundle_module_identity(&mut bundle);
    let expected = bundle.validate().unwrap_err();
    assert_eq!(ValidatedNativeBundle::new(&bundle).unwrap_err(), expected);
}

fn conflicting_contract_is_refused(suite: NativeVerifierSuite) {
    let mut bundle = discharge_native_bundle();
    bundle
        .requests
        .retain(|request| request.verifier_suite() == suite);
    bundle
        .validate()
        .expect("unique suite request is admissible");
    let id = bundle.requests[0].obligations()[0];
    let mut duplicate = bundle
        .module
        .proof_obligations
        .iter()
        .find(|row| row.id == id)
        .unwrap()
        .clone();
    duplicate.formula = Some(ProofFormula::smtlib2("false", "Bool"));
    bundle.module.proof_obligations.push(duplicate);
    refresh_native_bundle_module_identity(&mut bundle);
    assert_eq!(
        bundle.validate(),
        Err(vec![
            NativeVerificationBundleError::DuplicateModuleObligationId(id)
        ]),
        "{suite:?} admitted a second false contract for {id:?}",
    );
}

#[test]
fn duplicates_are_reported_in_physical_order_without_collapsing_occurrences() {
    let mut bundle = source_generation_authority_bundle();
    let first = bundle.module.proof_obligations[0].clone();
    let second = bundle.module.proof_obligations[1].clone();
    bundle
        .module
        .proof_obligations
        .extend([first.clone(), second.clone(), first.clone()]);
    refresh_native_bundle_module_identity(&mut bundle);
    let errors = bundle.validate().unwrap_err();
    let duplicates: Vec<_> = errors
        .iter()
        .filter_map(|error| match error {
            NativeVerificationBundleError::DuplicateModuleObligationId(id) => Some(*id),
            _ => None,
        })
        .collect();
    assert_eq!(duplicates, vec![first.id, second.id, first.id]);
}

#[test]
fn unrequested_duplicate_declarations_cannot_mint_live_source_authority() {
    let mut original = source_generation_authority_bundle();
    original
        .requests
        .retain(|request| request.verifier_suite() == NativeVerifierSuite::TrustMc);
    let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut original)
        .expect("unique original source");
    let mut bundle = original.clone(); // The clone has no live source marker.
    let duplicate = bundle.module.proof_obligations[0].clone();
    assert!(
        bundle
            .requests
            .iter()
            .all(|request| !request.obligations().contains(&duplicate.id))
    );
    bundle.module.proof_obligations.push(duplicate);
    refresh_native_bundle_module_identity(&mut bundle);
    let error = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).unwrap_err();
    assert_eq!(
        error,
        SourceGenerationAuthorityMintError::InvalidBundle(vec![
            NativeVerificationBundleError::DuplicateModuleObligationId(ProofId::new(0)),
        ])
    );
    assert!(authority.authorizes_bundle(&original));
}

#[test]
fn vc_request_refuses_a_second_contract_for_the_same_obligation() {
    conflicting_contract_is_refused(NativeVerifierSuite::TrustVc);
}

#[test]
fn mc_request_refuses_a_second_contract_for_the_same_obligation() {
    conflicting_contract_is_refused(NativeVerifierSuite::TrustMc);
}

#[test]
fn wp_request_refuses_a_second_contract_for_the_same_obligation() {
    conflicting_contract_is_refused(NativeVerifierSuite::TrustWp);
}

#[cfg(feature = "serde")]
#[test]
fn serialized_native_requests_cannot_hide_a_second_false_contract() {
    let mut bundle = discharge_native_bundle();
    let positive: NativeVerificationBundle =
        serde_json::from_str(&serde_json::to_string(&bundle).unwrap()).unwrap();
    positive
        .validate()
        .expect("unique transported declarations");
    let mut duplicate = bundle.module.proof_obligations[0].clone();
    let id = duplicate.id;
    duplicate.formula = Some(ProofFormula::smtlib2("false", "Bool"));
    bundle.module.proof_obligations.push(duplicate);
    refresh_native_bundle_module_identity(&mut bundle);
    let decoded: NativeVerificationBundle =
        serde_json::from_str(&serde_json::to_string(&bundle).unwrap()).unwrap();
    assert_eq!(
        decoded.module.proof_obligations,
        bundle.module.proof_obligations
    );
    let expected = vec![NativeVerificationBundleError::DuplicateModuleObligationId(
        id,
    )];
    assert_eq!(decoded.validate(), Err(expected.clone()));
    assert_eq!(ValidatedNativeBundle::new(&decoded).unwrap_err(), expected);
}
