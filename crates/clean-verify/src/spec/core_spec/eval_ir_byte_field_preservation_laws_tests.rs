// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual-kernel applications of the mechanically transferred insertion proofs.
//! Catalogs and closed values are model fixtures, not captured Rust bodies.

use crate::spec::Specification;
use clean_kernel::Name;

const ROOTS: &[&str] = &[
    "ir_byte_field_enum_spine_set_succ_invariant_v1",
    "ir_byte_field_types_set_writable_invariant_v1",
    "ir_byte_field_aggregate_spine_equation_v1",
    "ir_byte_field_aggregate_selected_spine_equation_v1",
    "ir_byte_field_inserted_value_admission_v1",
    "ir_byte_field_selected_insert_from_inputs_v1",
];

const CTX: &str = r"def field_preserve_ctx_v1 : IRByteContextV1 :=
  IRByteContextV1.mke
    (IRModule.mk (IRList.nil IRFunc) (IRList.nil IRGlobal))
    (IRList.cons IRByteLayoutV1
      (IRByteLayoutV1.mk (IRTy.struct_ 9) 16 8
        (IRList.cons IRTy IRTy.unit_ (IRList.cons IRTy IRTy.bool_ (IRList.nil IRTy)))
        (IRList.nil Nat))
      (IRList.nil IRByteLayoutV1))
    (IRList.nil IRByteSignatureV1) (IRList.nil IRByteFunctionV1)
    (IRList.nil IRByteSiteV1)
    (IRList.cons IRByteEnumV1
      (IRByteEnumV1.mk 10 (IRTy.uint_ 64)
        (IRList.cons IRByteEnumVariantV1
          (IRByteEnumVariantV1.mk 2
            (IRList.cons IRTy IRTy.unit_ (IRList.cons IRTy IRTy.bool_ (IRList.nil IRTy))))
          (IRList.nil IRByteEnumVariantV1)))
      (IRList.nil IRByteEnumV1))";

const STRUCT_SPINE: &str = r"def field_preserve_struct_spine_v1 : IRScalar :=
  IRScalar.vcons IRScalar.unit_ (IRScalar.vcons (IRScalar.bool_ Bool.false) IRScalar.vnil)";

const STRUCT_TYPES: &str = r"def field_preserve_struct_types_v1 : IRList IRTy :=
  IRList.cons IRTy IRTy.unit_ (IRList.cons IRTy IRTy.bool_ (IRList.nil IRTy))";

const ENUM_SPINE: &str = r"def field_preserve_enum_spine_v1 : IRScalar :=
  IRScalar.vcons (IRScalar.int_ 2)
    (IRScalar.vcons IRScalar.unit_ (IRScalar.vcons (IRScalar.bool_ Bool.false) IRScalar.vnil))";

const ENUM_TYPES: &str = r"def field_preserve_enum_types_v1 : IRList IRTy :=
  IRList.cons IRTy (IRTy.uint_ 64)
    (IRList.cons IRTy IRTy.unit_ (IRList.cons IRTy IRTy.bool_ (IRList.nil IRTy)))";

const STRUCT_INSERT: &str = r"def field_preserve_closed_struct_insert_v1 :
  Eq IRStepResult
    (ir_byte_insert_typed_v1 field_preserve_ctx_v1 (IRTy.struct_ 9) IRTy.bool_
      (IRScalar.aggv field_preserve_struct_spine_v1) 1 (IRScalar.bool_ Bool.true))
    (IRStepResult.value
      (IRScalar.aggv
        (IRScalar.vcons IRScalar.unit_ (IRScalar.vcons (IRScalar.bool_ Bool.true) IRScalar.vnil)))) :=
  ir_byte_field_selected_insert_from_inputs_v1
    field_preserve_ctx_v1 (IRTy.struct_ 9) IRTy.bool_ IRTy.bool_ field_preserve_struct_spine_v1 1 field_preserve_struct_types_v1 (IRScalar.bool_ Bool.true)
    (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true)
    (Eq.refl (IROption (IRList IRTy)) (IROption.some (IRList IRTy) field_preserve_struct_types_v1))
    (Eq.refl (IROption IRTy) (IROption.some IRTy IRTy.bool_))
    (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true)";

const ENUM_INSERT: &str = r"def field_preserve_closed_enum_insert_v1 :
  Eq IRStepResult
    (ir_byte_insert_typed_v1 field_preserve_ctx_v1 (IRTy.enum_ 10) IRTy.bool_
      (IRScalar.aggv field_preserve_enum_spine_v1) 2 (IRScalar.bool_ Bool.true))
    (IRStepResult.value
      (IRScalar.aggv
        (IRScalar.vcons (IRScalar.int_ 2)
          (IRScalar.vcons IRScalar.unit_ (IRScalar.vcons (IRScalar.bool_ Bool.true) IRScalar.vnil))))) :=
  ir_byte_field_selected_insert_from_inputs_v1
    field_preserve_ctx_v1 (IRTy.enum_ 10) IRTy.bool_ IRTy.bool_ field_preserve_enum_spine_v1 2 field_preserve_enum_types_v1 (IRScalar.bool_ Bool.true)
    (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true)
    (Eq.refl (IROption (IRList IRTy)) (IROption.some (IRList IRTy) field_preserve_enum_types_v1))
    (Eq.refl (IROption IRTy) (IROption.some IRTy IRTy.bool_))
    (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true) (Eq.refl Bool Bool.true)";

fn specification() -> Specification {
    crate::eval_ir::build_byte_prelude_spec_v1_with_stack()
        .expect("actual registered Byte insertion-preservation vocabulary")
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

fn add(spec: &mut Specification, source: &str) {
    spec.add_recursive_def(
        source,
        "Closed structural insertion fixture, not source authentication",
    )
    .unwrap_or_else(|error| panic!("{source}: {error}"));
    checked(spec, source.split_whitespace().nth(1).unwrap());
}

fn fixtures(spec: &mut Specification) {
    for source in [CTX, STRUCT_SPINE, STRUCT_TYPES, ENUM_SPINE, ENUM_TYPES] {
        add(spec, source);
    }
}

fn rejected(spec: &mut Specification, name: &str, source: &str) {
    let error = spec
        .add_recursive_def(source, "Unchanged-proof wrong nominal replacement type")
        .expect_err("wrong conclusion must not pass");
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

#[test]
fn byte_field_insert_preservation_generic_laws_are_checked_and_axiom_free() {
    crate::test_utils::run_with_stack(|| {
        let spec = specification();
        for root in ROOTS {
            checked(&spec, root);
        }
    });
}

#[test]
fn byte_field_insert_preservation_has_inhabited_struct_and_active_enum_applications() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        fixtures(&mut spec);
        add(&mut spec, STRUCT_INSERT);
        add(&mut spec, ENUM_INSERT);
    });
}

#[test]
fn byte_field_insert_preservation_unchanged_proofs_refuse_wrong_replacement_types() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        fixtures(&mut spec);
        for (source, positive, wrong, aggregate) in [
            (
                STRUCT_INSERT,
                "field_preserve_closed_struct_insert_v1",
                "field_preserve_wrong_struct_insert_v1",
                "(IRTy.struct_ 9)",
            ),
            (
                ENUM_INSERT,
                "field_preserve_closed_enum_insert_v1",
                "field_preserve_wrong_enum_insert_v1",
                "(IRTy.enum_ 10)",
            ),
        ] {
            add(&mut spec, source);
            let old =
                format!("(ir_byte_insert_typed_v1 field_preserve_ctx_v1 {aggregate} IRTy.bool_\n");
            let new =
                format!("(ir_byte_insert_typed_v1 field_preserve_ctx_v1 {aggregate} IRTy.unit_\n");
            assert_eq!(source.matches(&old).count(), 1);
            let mutated = source.replacen(positive, wrong, 1).replacen(&old, &new, 1);
            assert_eq!(
                source.split_once(":=\n").unwrap().1,
                mutated.split_once(":=\n").unwrap().1
            );
            rejected(&mut spec, wrong, &mutated);
        }
    });
}
