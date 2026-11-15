use super::*;

#[test]
fn validated_view_borrows_the_exact_complete_input() {
    let bundle = source_generation_authority_bundle();
    let admitted = ValidatedNativeBundle::new(&bundle).expect("canonical admission");
    assert!(std::ptr::eq(admitted.bundle(), &bundle));
    assert_eq!(admitted.bundle().requests, bundle.requests);
    assert_eq!(admitted.bundle().evidence_bundles, bundle.evidence_bundles);
}

#[test]
fn validated_view_preserves_canonical_refusals() {
    let valid = source_generation_authority_bundle();
    let mut mutants = vec![valid.clone(); 4];
    mutants[0].schema_version = 0;
    mutants[1].trust_ir_module_digest = digest(0x32);
    mutants[2].requests.clear();
    mutants[3].lineage.roots.clear();
    mutants.push(native_bundle()); // Unreplayed input certificate, not authority.
    for bundle in mutants {
        let expected = bundle.validate().expect_err("mutant must refuse");
        let actual = ValidatedNativeBundle::new(&bundle).expect_err("view must refuse");
        assert_eq!(actual, expected);
    }
}

#[test]
fn validated_view_does_not_mint_source_generation_authority() {
    let mut bundle = source_generation_authority_bundle();
    let authority =
        SourceGenerationAuthority::mint_from_live_lowering(&mut bundle).expect("valid live source");
    let decoded = bundle.clone();
    let admitted = ValidatedNativeBundle::new(&decoded).expect("content admission");
    assert!(!authority.authorizes_bundle(admitted.bundle()));
    assert!(authority.authorizes_bundle(&bundle));
}

#[cfg(feature = "native-validation-observer")]
#[test]
fn validated_view_counts_real_entries_and_observer_unwinds() {
    use crate::request::validation_observer::ValidationObservation;
    let bundle = source_generation_authority_bundle();
    let outer = ValidationObservation::start();
    let admitted = ValidatedNativeBundle::new(&bundle).expect("canonical admission");
    assert_eq!(outer.calls(), 1);
    for _ in 0..4 {
        assert!(std::ptr::eq(admitted.bundle(), &bundle));
    }
    assert_eq!(outer.calls(), 1, "borrowing reuses the actual admission");
    let result = std::panic::catch_unwind(|| {
        let nested = ValidationObservation::start();
        bundle.validate().expect("nested validation");
        assert_eq!(nested.calls(), 1);
        panic!("test observer cleanup on unwind");
    });
    assert!(result.is_err());
    assert_eq!(outer.calls(), 2);
    let new = ValidationObservation::start();
    let mut invalid = bundle.clone();
    invalid.schema_version = 0;
    assert!(ValidatedNativeBundle::new(&invalid).is_err());
    assert_eq!(new.calls(), 1);
    assert_eq!(outer.calls(), 3);
    drop(outer); // Non-LIFO drop must not unregister `new`.
    bundle.validate().expect("remaining observer");
    assert_eq!(new.calls(), 2);
}
