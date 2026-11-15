// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Native checks for the actual generic SET declarations, not source binding.

use crate::spec::Specification;
use clean_kernel::Name;

const ROOTS: &[&str] = &[
    "ir_byte_field_option_none_some_false_v1",
    "ir_byte_field_option_some_injective_v1",
    "ir_byte_field_spine_set_typed_v1",
];
const ROOT: &str = "ir_byte_field_spine_set_typed_v1";
const SPINE: &str =
    "IRScalar.vcons IRScalar.unit_ (IRScalar.vcons (IRScalar.bool_ Bool.false) IRScalar.vnil)";
const TYPES: &str = "IRList.cons IRTy IRTy.unit_ (IRList.cons IRTy IRTy.bool_ (IRList.nil IRTy))";

fn specification() -> Specification {
    crate::eval_ir::build_byte_prelude_spec_v1_with_stack()
        .expect("actual registered Byte SET vocabulary")
}

fn checked(spec: &Specification, name: &str) {
    let def = spec.get_definition(name).expect("value-bearing proof root");
    assert!(!def.is_axiom && def.elaborated_value.is_some());
    spec.verify_definition(name)
        .expect("actual Clean kernel check");
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn add(spec: &mut Specification, name: &str, source: &str) {
    spec.add_recursive_def(
        source,
        "Generic typed-spine SET instantiated with computed inputs",
    )
    .unwrap_or_else(|error| panic!("{source}: {error}"));
    checked(spec, name);
}

fn witness(index: &str, ty: &str, replacement: &str, name: &str) -> String {
    format!(
        "def {name} (ctx : IRByteContextV1) :\n\
         Eq Bool (ir_byte_match_fields_v1\n\
           (ir_byte_value_match_v1 ctx (ir_vals_set ({SPINE}) ({index}) ({replacement}))) ({TYPES})) Bool.true :=\n\
         {ROOT} ctx ({SPINE}) ({TYPES}) ({index}) ({ty}) ({replacement})\n\
           (Eq.refl Bool Bool.true)\n\
           (Eq.refl (IROption IRTy) (IROption.some IRTy ({ty})))\n\
           (Eq.refl Bool Bool.true)"
    )
}

fn rejected(spec: &mut Specification, name: &str, source: &str) {
    let error = spec
        .add_recursive_def(source, "Unchanged-proof incorrect SET admission conclusion")
        .expect_err("wrong conclusion must be rejected");
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

#[test]
fn byte_field_spine_set_generic_laws_are_checked_and_axiom_free() {
    crate::test_utils::run_with_stack(|| {
        let spec = specification();
        for root in ROOTS {
            checked(&spec, root);
        }
    });
}

#[test]
fn byte_field_spine_set_has_inhabited_head_and_successor_applications() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for (index, ty, replacement, name) in [
            (
                "Nat.zero",
                "IRTy.unit_",
                "IRScalar.unit_",
                "field_spine_set_head",
            ),
            (
                "Nat.succ Nat.zero",
                "IRTy.bool_",
                "IRScalar.bool_ Bool.true",
                "field_spine_set_tail",
            ),
        ] {
            add(&mut spec, name, &witness(index, ty, replacement, name));
        }
    });
}

#[test]
fn byte_field_spine_set_unchanged_proof_refuses_false_admission_conclusion() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let source = witness(
            "Nat.succ Nat.zero",
            "IRTy.bool_",
            "IRScalar.bool_ Bool.true",
            "field_spine_set_positive",
        );
        add(&mut spec, "field_spine_set_positive", &source);
        let wrong = source
            .replacen("field_spine_set_positive", "field_spine_set_wrong", 1)
            .replacen(") Bool.true :=\n", ") Bool.false :=\n", 1);
        assert_ne!(source, wrong);
        assert_eq!(
            source.split_once(":=\n").unwrap().1,
            wrong.split_once(":=\n").unwrap().1
        );
        rejected(&mut spec, "field_spine_set_wrong", &wrong);
    });
}
