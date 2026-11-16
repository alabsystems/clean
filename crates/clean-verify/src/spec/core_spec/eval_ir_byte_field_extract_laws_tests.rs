// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Closed extraction applications using five computed input premises.
//! These catalogs and values are model fixtures, not a captured Rust body or heap.

use crate::spec::Specification;
use clean_kernel::Name;

const ROOT: &str = "ir_byte_field_selected_extract_from_inputs_v1";

const CTX: &str = r"def field_extract_ctx_v1 : IRByteContextV1 :=
  IRByteContextV1.mke
    (IRModule.mk (@IRList.nil IRFunc) (@IRList.nil IRGlobal))
    (@IRList.cons IRByteLayoutV1
      (IRByteLayoutV1.mk (IRTy.struct_ 9) 16 8
        (@IRList.cons IRTy IRTy.unit_ (@IRList.cons IRTy IRTy.bool_ (@IRList.nil IRTy)))
        (@IRList.nil Nat))
      (@IRList.nil IRByteLayoutV1))
    (@IRList.nil IRByteSignatureV1) (@IRList.nil IRByteFunctionV1)
    (@IRList.nil IRByteSiteV1)
    (@IRList.cons IRByteEnumV1
      (IRByteEnumV1.mk 10 (IRTy.uint_ 64)
        (@IRList.cons IRByteEnumVariantV1
          (IRByteEnumVariantV1.mk 2
            (@IRList.cons IRTy IRTy.unit_ (@IRList.cons IRTy IRTy.bool_ (@IRList.nil IRTy))))
          (@IRList.nil IRByteEnumVariantV1)))
      (@IRList.nil IRByteEnumV1))";

const STRUCT_SPINE: &str = r"def field_extract_struct_spine_v1 : IRScalar :=
  IRScalar.vcons IRScalar.unit_ (IRScalar.vcons (IRScalar.bool_ Bool.false) IRScalar.vnil)";

const STRUCT_TYPES: &str = r"def field_extract_struct_types_v1 : IRList IRTy :=
  @IRList.cons IRTy IRTy.unit_ (@IRList.cons IRTy IRTy.bool_ (@IRList.nil IRTy))";

const ENUM_SPINE: &str = r"def field_extract_enum_spine_v1 : IRScalar :=
  IRScalar.vcons (IRScalar.int_ 2)
    (IRScalar.vcons IRScalar.unit_ (IRScalar.vcons (IRScalar.bool_ Bool.false) IRScalar.vnil))";

const ENUM_TYPES: &str = r"def field_extract_enum_types_v1 : IRList IRTy :=
  @IRList.cons IRTy (IRTy.uint_ 64)
    (@IRList.cons IRTy IRTy.unit_ (@IRList.cons IRTy IRTy.bool_ (@IRList.nil IRTy)))";

const STRUCT_EXTRACT: &str = r"def field_extract_closed_struct_v1 :
  @Eq IRStepResult
    (ir_byte_extract_typed_v1 field_extract_ctx_v1 (IRTy.struct_ 9) IRTy.bool_
      (IRScalar.aggv field_extract_struct_spine_v1) 1)
    (IRStepResult.value (IRScalar.bool_ Bool.false)) :=
  ir_byte_field_selected_extract_from_inputs_v1
    field_extract_ctx_v1 (IRTy.struct_ 9) IRTy.bool_ IRTy.bool_ field_extract_struct_spine_v1 1 field_extract_struct_types_v1 (IRScalar.bool_ Bool.false)
    (@Eq.refl Bool Bool.true)
    (@Eq.refl (IROption (IRList IRTy)) (@IROption.some (IRList IRTy) field_extract_struct_types_v1))
    (@Eq.refl (IROption IRTy) (@IROption.some IRTy IRTy.bool_))
    (@Eq.refl Bool Bool.true)
    (@Eq.refl (IROption IRScalar) (@IROption.some IRScalar (IRScalar.bool_ Bool.false)))";

const ENUM_EXTRACT: &str = r"def field_extract_closed_enum_v1 :
  @Eq IRStepResult
    (ir_byte_extract_typed_v1 field_extract_ctx_v1 (IRTy.enum_ 10) IRTy.bool_
      (IRScalar.aggv field_extract_enum_spine_v1) 2)
    (IRStepResult.value (IRScalar.bool_ Bool.false)) :=
  ir_byte_field_selected_extract_from_inputs_v1
    field_extract_ctx_v1 (IRTy.enum_ 10) IRTy.bool_ IRTy.bool_ field_extract_enum_spine_v1 2 field_extract_enum_types_v1 (IRScalar.bool_ Bool.false)
    (@Eq.refl Bool Bool.true)
    (@Eq.refl (IROption (IRList IRTy)) (@IROption.some (IRList IRTy) field_extract_enum_types_v1))
    (@Eq.refl (IROption IRTy) (@IROption.some IRTy IRTy.bool_))
    (@Eq.refl Bool Bool.true)
    (@Eq.refl (IROption IRScalar) (@IROption.some IRScalar (IRScalar.bool_ Bool.false)))";

fn specification() -> Specification {
    crate::eval_ir::build_byte_prelude_spec_v1_with_stack()
        .expect("actual registered Byte extraction/type-equality vocabulary")
}

fn checked(spec: &Specification, name: &str) {
    let def = spec.get_definition(name).expect("value-bearing proof root");
    assert!(!def.is_axiom && def.elaborated_value.is_some());
    spec.verify_definition(name)
        .expect("actual Clean kernel check");
    let name = Name::from_string(name);
    // Both dependency closures must be empty, not merely within an allowlist.
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn add(spec: &mut Specification, source: &str) {
    spec.add_recursive_def(
        source,
        "Closed model fixture with computed inputs, not Rust source binding",
    )
    .unwrap_or_else(|error| panic!("{source}: {error}"));
    checked(spec, source.split_whitespace().nth(1).unwrap());
}

fn rejected(spec: &mut Specification, name: &str, source: &str) {
    let error = spec
        .add_recursive_def(source, "Unchanged-proof incorrect conclusion control")
        .expect_err("wrong conclusion must be rejected");
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

fn fixtures(spec: &mut Specification) {
    for source in [CTX, STRUCT_SPINE, STRUCT_TYPES, ENUM_SPINE, ENUM_TYPES] {
        add(spec, source);
    }
}

#[test]
fn byte_field_extract_input_law_is_checked_and_axiom_free() {
    crate::test_utils::run_with_stack(|| checked(&specification(), ROOT));
}

#[test]
fn byte_field_extract_has_inhabited_struct_and_active_enum_applications() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        fixtures(&mut spec);
        add(&mut spec, STRUCT_EXTRACT);
        add(&mut spec, ENUM_EXTRACT);
    });
}

#[test]
fn byte_field_extract_unchanged_proofs_refuse_wrong_nominal_result_types() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        fixtures(&mut spec);
        for (source, positive, wrong, aggregate) in [
            (
                STRUCT_EXTRACT,
                "field_extract_closed_struct_v1",
                "field_extract_wrong_struct_v1",
                "(IRTy.struct_ 9)",
            ),
            (
                ENUM_EXTRACT,
                "field_extract_closed_enum_v1",
                "field_extract_wrong_enum_v1",
                "(IRTy.enum_ 10)",
            ),
        ] {
            add(&mut spec, source);
            let old =
                format!("(ir_byte_extract_typed_v1 field_extract_ctx_v1 {aggregate} IRTy.bool_\n");
            let new =
                format!("(ir_byte_extract_typed_v1 field_extract_ctx_v1 {aggregate} IRTy.unit_\n");
            assert_eq!(source.matches(&old).count(), 1);
            assert_eq!(source.matches(&format!("def {positive} :")).count(), 1);
            let mutated = source.replacen(positive, wrong, 1).replacen(&old, &new, 1);
            assert_ne!(source, mutated);
            assert_eq!(
                source.split_once(":=\n").unwrap().1,
                mutated.split_once(":=\n").unwrap().1,
            );
            rejected(&mut spec, wrong, &mutated);
        }
    });
}
