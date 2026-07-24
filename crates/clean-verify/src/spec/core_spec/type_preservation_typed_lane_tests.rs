// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::test_utils::build_spec_with_stack;

#[test]
fn test_primary_conversion_surface_uses_typed_defeq() {
    let spec = build_spec_with_stack();

    // #2859 (Brick 7+8) made Typing.conv / Typing.rec's conv case UNTYPED: they now
    // consume the raw `DefEq A B` directly (church_rosser_whnf retirement track), NOT
    // the typed `typing_is_def_eq` alias. Typing is now a genuine `add_inductive`, so
    // Typing.conv is a kernel-generated CONSTRUCTOR and Typing.rec the generated
    // RECURSOR (neither is a value-less axiom); their `type_src` is the
    // "(constructor of Typing)" / "(recursor of Typing)" placeholder, so the
    // untypedness is checked against the kernel-ELABORATED type (same pattern as the
    // DefEq inductive-faithfulness tests).
    {
        let conv = spec
            .definitions()
            .get("Typing.conv")
            .expect("Typing.conv should exist");
        assert!(
            !conv.is_axiom,
            "Typing.conv should be a kernel-generated constructor, not an axiom"
        );
        let conv_ty = format!(
            "{:?}",
            conv.elaborated_type
                .as_ref()
                .expect("Typing.conv should record its elaborated type")
        );
        assert!(
            conv_ty.contains("DefEq") && !conv_ty.contains("typing_is_def_eq"),
            "Typing.conv should be the untyped raw-DefEq conversion (#2859): {conv_ty}"
        );
    }
    {
        let rec = spec
            .definitions()
            .get("Typing.rec")
            .expect("Typing.rec should exist");
        assert!(
            !rec.is_axiom,
            "Typing.rec should be a kernel-generated recursor, not an axiom"
        );
        let rec_ty = format!(
            "{:?}",
            rec.elaborated_type
                .as_ref()
                .expect("Typing.rec should record its elaborated type")
        );
        assert!(
            rec_ty.contains("DefEq") && !rec_ty.contains("typing_is_def_eq"),
            "Typing.rec's conv case should expose the untyped raw DefEq (#2859): {rec_ty}"
        );
    }

    // These public theorems still use typing_is_def_eq in their type signatures.
    for name in [
        "type_conversion",
        "def_eq_preserves_typing",
        "TypePreservation",
        "def_eq_typing_iff",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert!(
            def.type_src.contains("typing_is_def_eq"),
            "{name} should use typing_is_def_eq in its type: {}",
            def.type_src
        );
    }
}

#[test]
fn test_def_eq_typing_iff_uses_typed_recursor() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("def_eq_typing_iff")
        .expect("def_eq_typing_iff should exist");
    let value = def
        .value_src
        .as_ref()
        .expect("def_eq_typing_iff should have a proof term");

    assert!(
        value.contains("TypedDefEq.rec"),
        "def_eq_typing_iff should recurse over TypedDefEq: {value}"
    );
    assert!(
        !value.contains("DefEq.rec_beta_typed"),
        "def_eq_typing_iff should no longer mention the deleted helper axiom: {value}"
    );
}

#[test]
fn test_defeq_rec_beta_typed_removed() {
    let spec = build_spec_with_stack();
    assert!(
        !spec.definitions().contains_key("DefEq.rec_beta_typed"),
        "DefEq.rec_beta_typed should be removed after the typed-lane retarget"
    );
}

#[test]
fn test_raw_bridge_stays_raw_after_primary_retargeting() {
    let spec = build_spec_with_stack();

    // #2859: raw_def_eq_preserves_typing is RETIRED (symmetric raw subject
    // reduction is unsound under untyped DefEq.beta), so only the surviving
    // raw_type_conversion bridge is checked for staying on the raw is_def_eq
    // surface.
    let name = "raw_type_conversion";
    let def = spec
        .definitions()
        .get(name)
        .unwrap_or_else(|| panic!("{name} should exist"));
    assert!(
        def.type_src.contains("is_def_eq"),
        "{name} should keep the raw is_def_eq surface: {}",
        def.type_src
    );
    assert!(
        !def.type_src.contains("typing_is_def_eq"),
        "{name} should not migrate to the typed alias: {}",
        def.type_src
    );
}
