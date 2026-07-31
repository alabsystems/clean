// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::spec::definition::SpecDefinition;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::test_utils::build_spec_with_stack;

fn assert_bridge_metadata(def: &SpecDefinition, name: &str, status: ProofStatus) {
    assert!(
        !def.is_axiom,
        "{name} should be a DerivedLemma, not an axiom"
    );
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "{name} should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status, status,
        "{name} has the wrong proof status"
    );
}

#[test]
fn test_raw_type_conversion_exists_and_applies_untyped_typing_conv() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("raw_type_conversion")
        .expect("raw_type_conversion should be registered");

    assert_bridge_metadata(def, "raw_type_conversion", ProofStatus::DerivedProved);

    // #2859: `Typing.conv` is now UNTYPED (`Typing e A -> DefEq A B -> Typing e B`),
    // so `raw_type_conversion` applies it DIRECTLY to the raw `is_def_eq` witness.
    // The former `raw_to_typed_def_eq` bridge is retired for this shim. The
    // soundness-critical invariant is unchanged: it must NOT reach the retired
    // direct `def_eq_to_eq` transport bridge.
    let value = def
        .value_src
        .as_ref()
        .expect("raw_type_conversion should have a proof term");
    assert!(
        value.contains("Typing.conv"),
        "raw_type_conversion proof should apply Typing.conv directly: {value}"
    );
    assert!(
        !value.contains("raw_to_typed_def_eq"),
        "raw_type_conversion no longer routes through raw_to_typed_def_eq \
         (Typing.conv is untyped, #2859): {value}"
    );
    assert!(
        !value.contains("def_eq_to_eq"),
        "raw_type_conversion should not use the retired direct def_eq_to_eq bridge: {value}"
    );

    let deps = def
        .dependencies
        .as_ref()
        .expect("raw_type_conversion should record dependencies");
    assert!(
        deps.contains("Typing.conv"),
        "raw_type_conversion dependencies should include Typing.conv: {deps:?}"
    );
    assert!(
        !deps.contains("raw_to_typed_def_eq"),
        "raw_type_conversion dependencies should no longer include raw_to_typed_def_eq: {deps:?}"
    );
    assert!(
        !deps.contains("def_eq_to_eq"),
        "raw_type_conversion dependencies should not include def_eq_to_eq: {deps:?}"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "raw_type_conversion should have no HelperAxiom leaves: {:?}",
        def.axiom_deps
    );
}

// test_raw_def_eq_preserves_typing_exists_and_uses_typed_lane_bridge removed:
// raw_def_eq_preserves_typing is RETIRED (#2859). Under untyped DefEq.beta, raw
// symmetric DefEq subject reduction is FALSE (subject-expansion counterexample);
// the only sound preservation is FORWARD over the directed whnf_to relation, which
// KernelWhnfPreservesTyping now uses via whnf_to_preserves_typing.

#[test]
fn test_raw_bridge_types_diverge_from_primary_definitions_after_typed_retarget() {
    let spec = build_spec_with_stack();

    let primary_tc = spec
        .definitions()
        .get("type_conversion")
        .expect("type_conversion should exist");
    let raw_tc = spec
        .definitions()
        .get("raw_type_conversion")
        .expect("raw_type_conversion should exist");
    assert_ne!(
        primary_tc.type_src, raw_tc.type_src,
        "primary and raw conversion surfaces should diverge after the typed-lane retarget"
    );
    assert!(
        primary_tc.type_src.contains("typing_is_def_eq"),
        "primary type_conversion should use typing_is_def_eq: {}",
        primary_tc.type_src
    );
    assert!(
        raw_tc.type_src.contains("is_def_eq"),
        "raw_type_conversion should keep the raw is_def_eq surface: {}",
        raw_tc.type_src
    );

    // raw_def_eq_preserves_typing is retired (#2859); the primary
    // def_eq_preserves_typing remains on the typed lane.
    let primary_dep = spec
        .definitions()
        .get("def_eq_preserves_typing")
        .expect("def_eq_preserves_typing should exist");
    assert!(
        primary_dep.type_src.contains("typing_is_def_eq"),
        "primary def_eq_preserves_typing should use typing_is_def_eq: {}",
        primary_dep.type_src
    );
}

#[test]
fn test_raw_bridge_speaks_is_def_eq() {
    let spec = build_spec_with_stack();

    let raw_tc = spec
        .definitions()
        .get("raw_type_conversion")
        .expect("raw_type_conversion should exist");
    assert!(
        raw_tc.type_src.contains("is_def_eq"),
        "raw_type_conversion should speak raw is_def_eq: {}",
        raw_tc.type_src
    );
    assert!(
        !raw_tc.type_src.contains("typing_is_def_eq"),
        "raw_type_conversion should not use the typed alias: {}",
        raw_tc.type_src
    );
}

#[test]
fn test_whnf_and_check_consumers_use_raw_bridge() {
    let spec = build_spec_with_stack();

    let whnf_pt = spec
        .definitions()
        .get("KernelWhnfPreservesTyping")
        .expect("KernelWhnfPreservesTyping should exist");
    let whnf_deps = whnf_pt
        .dependencies
        .as_ref()
        .expect("KernelWhnfPreservesTyping should record dependencies");
    // #2859: re-routed onto FORWARD directed subject reduction
    // (whnf_to_preserves_typing ∘ kernel_whnf_reduces_to_spec_whnf), not the
    // retired raw symmetric bridge.
    assert!(
        whnf_deps.contains("whnf_to_preserves_typing"),
        "KernelWhnfPreservesTyping should depend on whnf_to_preserves_typing: {whnf_deps:?}"
    );
    assert!(
        !whnf_deps.contains("def_eq_preserves_typing"),
        "KernelWhnfPreservesTyping should not depend on the primary: {whnf_deps:?}"
    );

    let check_local = spec
        .definitions()
        .get("kernel_check_returns_well_typed_from_infer")
        .expect("kernel_check_returns_well_typed_from_infer should exist");
    let check_deps = check_local
        .dependencies
        .as_ref()
        .expect("local check bridge should record dependencies");
    assert!(
        check_deps.contains("raw_type_conversion"),
        "local check bridge should depend on raw_type_conversion: {check_deps:?}"
    );
    assert!(
        !check_deps.contains("type_conversion"),
        "local check bridge should not depend on primary type_conversion: {check_deps:?}"
    );
}

#[test]
fn test_infer_sound_consumers_use_raw_bridge() {
    let spec = build_spec_with_stack();

    for (name, label) in [
        ("kernel_infer_app_sound", "app_sound"),
        ("kernel_infer_lam_sound", "lam_sound"),
        ("kernel_infer_pi_sound", "pi_sound"),
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should exist"));
        let deps = def
            .dependencies
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should record dependencies"));
        assert!(
            deps.contains("raw_type_conversion"),
            "{label} should depend on raw_type_conversion: {deps:?}"
        );
        assert!(
            !deps.contains("type_conversion"),
            "{label} should not depend on primary type_conversion: {deps:?}"
        );
    }
}

/// Systematic typed-lane isolation invariant: every implementation-soundness
/// wrapper that consumes a conversion theorem must reference the raw bridge
/// names in its proof term, never the primary typed-lane names. This prevents
/// regressions where a consumer silently reverts to the primary typed API
/// after a refactor.
///
/// Part of #2893: verification of the landed raw-to-typed bridge packet.
///
/// All implementation-soundness wrappers that use conversion: their proof
/// terms must contain `raw_type_conversion` or `raw_def_eq_preserves_typing`
/// and must NOT contain the bare primary names `type_conversion ` (with
/// trailing space to avoid matching `raw_type_conversion`) or
/// `def_eq_preserves_typing ` as standalone references.
#[test]
fn test_all_conversion_consumers_proof_terms_use_raw_bridge() {
    let spec = build_spec_with_stack();

    // These are all the implementation-soundness wrappers that consume
    // a conversion theorem, per the design doc. KernelWhnfPreservesTyping is
    // NO LONGER here: #2859 re-routed it onto FORWARD directed subject reduction
    // (whnf_to_preserves_typing), retiring its raw symmetric-conversion bridge.
    let conversion_consumers = [
        "kernel_check_returns_well_typed_from_infer",
        "kernel_infer_app_sound",
        "kernel_infer_lam_sound",
        "kernel_infer_pi_sound",
    ];

    for name in conversion_consumers {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should exist"));
        let value = def
            .value_src
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should have a proof term"));

        // Must use at least one raw bridge name
        let uses_raw =
            value.contains("raw_type_conversion") || value.contains("raw_def_eq_preserves_typing");
        assert!(
            uses_raw,
            "{name} proof term should reference a raw bridge name: {value}"
        );

        // Must NOT reference the primary typed names as standalone tokens.
        // We check that removing all "raw_" prefixes would still not leave
        // a bare "type_conversion" or "def_eq_preserves_typing" — meaning
        // those names only appear with the "raw_" prefix.
        let stripped = value
            .replace("raw_type_conversion", "RAW_TC_PLACEHOLDER")
            .replace("raw_def_eq_preserves_typing", "RAW_DEP_PLACEHOLDER");
        assert!(
            !stripped.contains("type_conversion"),
            "{name} proof term should not reference primary type_conversion: {value}"
        );
        assert!(
            !stripped.contains("def_eq_preserves_typing"),
            "{name} proof term should not reference primary def_eq_preserves_typing: {value}"
        );
    }
}

/// The raw kernel equality producers must stay on raw `is_def_eq`/`DefEq`
/// and never migrate to `typing_is_def_eq`/`TypedDefEq`. This is the
/// complement of the consumer isolation check above.
///
/// Note: some producers use the `is_def_eq` alias, others use the underlying
/// `DefEq` type directly. Both are raw. The invariant is that none of them
/// reference the typed lane (`typing_is_def_eq` or `TypedDefEq`).
#[test]
fn test_raw_producers_stay_on_raw_def_eq() {
    let spec = build_spec_with_stack();

    let raw_producers = [
        "KernelWhnfSound",
        "KernelDefEqSound",
        "kernel_whnf_returns_def_eq",
        "kernel_def_eq_reflects_spec",
    ];

    for name in raw_producers {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should exist"));
        // Must use raw equality: either `is_def_eq` alias or `DefEq` directly
        let uses_raw = def.type_src.contains("is_def_eq") || def.type_src.contains("DefEq");
        assert!(
            uses_raw,
            "{name} should return raw is_def_eq or DefEq: {}",
            def.type_src
        );
        // Must NOT use the typed lane
        assert!(
            !def.type_src.contains("typing_is_def_eq"),
            "{name} should NOT return typed typing_is_def_eq: {}",
            def.type_src
        );
        assert!(
            !def.type_src.contains("TypedDefEq"),
            "{name} should NOT return TypedDefEq: {}",
            def.type_src
        );
    }
}

/// The primary typed-lane definitions must all use `typing_is_def_eq` and
/// none of them should use bare `is_def_eq` in their type signatures.
#[test]
fn test_typed_lane_definitions_use_typing_is_def_eq() {
    let spec = build_spec_with_stack();

    // Typing.conv is NO LONGER a typed-lane def: #2859 untyped it to the literal
    // CIC conversion rule (forall e A B, Typing e A -> DefEq A B -> Typing e B),
    // which speaks raw DefEq, not typing_is_def_eq.
    let typed_lane_defs = [
        "type_conversion",
        "def_eq_preserves_typing",
        "TypePreservation",
    ];

    for name in typed_lane_defs {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert!(
            def.type_src.contains("typing_is_def_eq"),
            "{name} should use typing_is_def_eq: {}",
            def.type_src
        );
        // After stripping typing_is_def_eq, no bare is_def_eq should remain
        let stripped = def
            .type_src
            .replace("typing_is_def_eq", "TYPED_PLACEHOLDER");
        assert!(
            !stripped.contains("is_def_eq"),
            "{name} should not have bare is_def_eq alongside typing_is_def_eq: {}",
            def.type_src
        );
    }
}

/// The raw bridge shims keep raw public types but may internally use the typed
/// lane through `raw_to_typed_def_eq`. They must not reintroduce the direct
/// `def_eq_to_eq` transport bridge.
#[test]
fn test_raw_bridge_proof_terms_do_not_reference_def_eq_to_eq() {
    let spec = build_spec_with_stack();

    let name = "raw_type_conversion";
    let def = spec
        .definitions()
        .get(name)
        .unwrap_or_else(|| panic!("{name} should exist"));
    let value = def
        .value_src
        .as_ref()
        .unwrap_or_else(|| panic!("{name} should have a proof term"));
    assert!(
        !value.contains("def_eq_to_eq"),
        "{name} proof should not reference def_eq_to_eq: {value}"
    );
}
