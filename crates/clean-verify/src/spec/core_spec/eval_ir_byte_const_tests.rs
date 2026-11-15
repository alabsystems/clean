// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete contextual Const witnesses. Schemas are explicit model inputs,
//! not reflected Rust layouts or an authenticated production source capture.

use crate::spec::Specification;
use clean_kernel::Name;

const ROOTS: &[&str] = &[
    "ir_byte_const_checked_input_v1",
    "ir_byte_const_fields_nil_v1",
    "ir_byte_const_fields_cons_v1",
    "ir_byte_const_zero_pointer_v1",
    "ir_byte_const_zero_fatstr_v1",
    "ir_byte_const_zero_fatslice_v1",
    "ir_byte_const_zero_fatdyn_v1",
    "ir_byte_const_zero_containerlen_v1",
    "ir_byte_const_zero_containervtable_v1",
];
const BAD: &str = "IRStepResult.fault (IROutcome.type_error IRFault.bad_field)";
const NOT_INT: &str = "IRStepResult.fault (IROutcome.type_error IRFault.not_int)";
const ZERO_FAT: &str =
    "IRConst.aggv (IRConst.vcons (IRConst.int_ 0) (IRConst.vcons (IRConst.int_ 0) IRConst.vnil))";
const PROGRAM: &str = "IRModule.mk (IRList.nil IRFunc) (IRList.nil IRGlobal)";

fn specification() -> Specification {
    crate::eval_ir::build_byte_prelude_spec_v1_with_stack().expect("public Byte vocabulary")
}

fn checked(spec: &Specification, name: &str) {
    let definition = spec.get_definition(name).expect("value-bearing root");
    assert!(!definition.is_axiom && definition.elaborated_value.is_some());
    spec.verify_definition(name).expect("actual kernel check");
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn add(spec: &mut Specification, source: &str) {
    spec.add_recursive_def(source, "Complete contextual Const model witness")
        .unwrap_or_else(|error| panic!("{source}: {error}"));
    checked(spec, source.split_whitespace().nth(1).unwrap());
}

fn equality(spec: &mut Specification, name: &str, ty: &str, actual: &str, expected: &str) {
    add(
        spec,
        &format!("def {name} : Eq ({ty}) ({actual}) ({expected}) := Eq.refl ({ty}) ({expected})"),
    );
}

fn result(
    spec: &mut Specification,
    name: &str,
    ctx: &str,
    ty: &str,
    constant: &str,
    expected: &str,
) {
    equality(
        spec,
        name,
        "IRStepResult",
        &format!("ir_byte_const_context_eval_v1 {ctx} ({ty}) ({constant})"),
        expected,
    );
}

fn list(ty: &str, values: &[&str]) -> String {
    values
        .iter()
        .rev()
        .fold(format!("IRList.nil {ty}"), |tail, value| {
            format!("IRList.cons {ty} ({value}) ({tail})")
        })
}

fn aggregate(ty: &str, values: &[&str]) -> String {
    let spine = values
        .iter()
        .rev()
        .fold(format!("{ty}.vnil"), |tail, value| {
            format!("{ty}.vcons ({value}) ({tail})")
        });
    format!("{ty}.aggv ({spine})")
}

fn layout(id: u64, fields: &[&str]) -> String {
    format!(
        "IRByteLayoutV1.mk (IRTy.struct_ {id}) 32 8 ({}) (IRList.nil Nat)",
        list("IRTy", fields)
    )
}

fn schema(id: u64, tag: u64, fields: &[&str]) -> String {
    format!(
        "IRByteEnumV1.mk {id} (IRTy.uint_ 8) ({})",
        list(
            "IRByteEnumVariantV1",
            &[&format!(
                "IRByteEnumVariantV1.mk {tag} ({})",
                list("IRTy", fields)
            )]
        )
    )
}

fn context(layouts: &[&str], enums: &[&str], functions: &[&str]) -> String {
    format!("(IRByteContextV1.mke ({PROGRAM}) ({}) (IRList.nil IRByteSignatureV1) ({}) (IRList.nil IRByteSiteV1) ({}))", list("IRByteLayoutV1", layouts), list("IRByteFunctionV1", functions), list("IRByteEnumV1", enums))
}

fn rejected(spec: &mut Specification, name: &str, source: &str) {
    let error = spec
        .add_recursive_def(source, "Unchanged-proof wrong Const endpoint")
        .expect_err("wrong endpoint must not pass");
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

#[test]
fn byte_const_context_nested_struct_enum_seeds_convert_at_each_field_type() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let inner = schema(7, 19, &["IRTy.ptr_", "IRTy.fatstr_", "IRTy.usize_ 64"]);
        let outer = layout(9, &["IRTy.enum_ 7", "IRTy.bool_"]);
        let ctx = context(&[&outer], &[&inner], &[]);
        let seed = aggregate(
            "IRConst",
            &[
                "IRConst.int_ 19",
                "IRConst.int_ 0",
                ZERO_FAT,
                "IRConst.int_ 7",
            ],
        );
        let converted = aggregate(
            "IRScalar",
            &[
                "IRScalar.int_ 19",
                "IRScalar.nullptr_",
                "IRScalar.fat_ 0 0",
                "IRScalar.int_ 7",
            ],
        );
        result(
            &mut spec,
            "const_nested_seed",
            &ctx,
            "IRTy.struct_ 9",
            &aggregate("IRConst", &[&seed, "IRConst.bool_ Bool.true"]),
            &format!(
                "IRStepResult.value ({})",
                aggregate("IRScalar", &[&converted, "IRScalar.bool_ Bool.true"])
            ),
        );
        equality(
            &mut spec,
            "const_no_opaque_spine",
            "Bool",
            &format!("ir_byte_value_matches_v1 {ctx} (IRTy.enum_ 7) (ir_const_value ({seed}))"),
            "Bool.false",
        );
        // Reverse the nesting and put the struct and enum in the same ID
        // namespace numerically. Their families remain distinct.
        let structure = layout(7, &["IRTy.ptr_", "IRTy.containervtable_"]);
        let enumeration = schema(7, 3, &["IRTy.struct_ 7"]);
        let ctx = context(&[&structure], &[&enumeration], &[]);
        result(
            &mut spec,
            "const_reverse_nested",
            &ctx,
            "IRTy.enum_ 7",
            &aggregate(
                "IRConst",
                &[
                    "IRConst.int_ 3",
                    &aggregate("IRConst", &["IRConst.int_ 0", ZERO_FAT]),
                ],
            ),
            &format!(
                "IRStepResult.value ({})",
                aggregate(
                    "IRScalar",
                    &[
                        "IRScalar.int_ 3",
                        &aggregate("IRScalar", &["IRScalar.nullptr_", "IRScalar.fat_ 0 0"])
                    ]
                )
            ),
        );
    });
}

#[test]
fn byte_const_context_exact_null_and_fat_seeds_do_not_fabricate_addresses() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let ctx = context(&[], &[], &[]);
        result(
            &mut spec,
            "const_null_seed",
            &ctx,
            "IRTy.ptr_",
            "IRConst.int_ 0",
            "IRStepResult.value IRScalar.nullptr_",
        );
        result(
            &mut spec,
            "const_nonzero_ptr",
            &ctx,
            "IRTy.ptr_",
            "IRConst.int_ 16",
            BAD,
        );
        for (case, ty) in [
            "IRTy.ref_ IRTy.unit_",
            "IRTy.refmut_ IRTy.unit_",
            "IRTy.rawconst_ IRTy.unit_",
            "IRTy.rawmut_ IRTy.unit_",
            "IRTy.rc_ IRTy.unit_",
        ]
        .iter()
        .enumerate()
        {
            result(
                &mut spec,
                &format!("const_no_typed_ref_seed_{case}"),
                &ctx,
                ty,
                "IRConst.int_ 0",
                NOT_INT,
            );
        }
        for (case, (ty, metadata_ty, zero)) in [
            ("IRTy.fatstr_", "IRTy.uint_ 64", "IRScalar.int_ 0"),
            (
                "IRTy.fatslice_ (IRTy.uint_ 8)",
                "IRTy.uint_ 64",
                "IRScalar.int_ 0",
            ),
            ("IRTy.fatdyn_ 41", "IRTy.ptr_", "IRScalar.nullptr_"),
            ("IRTy.containerlen_", "IRTy.uint_ 64", "IRScalar.int_ 0"),
            ("IRTy.containervtable_", "IRTy.ptr_", "IRScalar.nullptr_"),
        ]
        .iter()
        .enumerate()
        {
            result(
                &mut spec,
                &format!("const_fat_zero_{case}"),
                &ctx,
                ty,
                ZERO_FAT,
                "IRStepResult.value (IRScalar.fat_ 0 0)",
            );
            equality(
                &mut spec,
                &format!("const_fat_metadata_{case}"),
                "IRStepResult",
                &format!(
                    "ir_byte_ptrmetadata_eval_v1 {ctx} ({ty}) ({metadata_ty}) (IRScalar.fat_ 0 0)"
                ),
                &format!("IRStepResult.value ({zero})"),
            );
            for (bad, constant) in [
                aggregate("IRConst", &["IRConst.int_ 16", "IRConst.int_ 0"]),
                aggregate("IRConst", &["IRConst.int_ 0", "IRConst.int_ 3"]),
                aggregate("IRConst", &["IRConst.int_ 0"]),
                aggregate(
                    "IRConst",
                    &["IRConst.int_ 0", "IRConst.int_ 0", "IRConst.int_ 0"],
                ),
                aggregate("IRConst", &["IRConst.bool_ Bool.false", "IRConst.int_ 0"]),
                aggregate("IRConst", &["IRConst.int_ 0", "IRConst.null_"]),
            ]
            .iter()
            .enumerate()
            {
                result(
                    &mut spec,
                    &format!("const_bad_fat_{case}_{bad}"),
                    &ctx,
                    ty,
                    constant,
                    BAD,
                );
            }
        }
    });
}

#[test]
fn byte_const_context_checks_complete_spines_and_unwrapped_selected_tags() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let enumeration = schema(7, 19, &["IRTy.bool_"]);
        let ctx = context(&[], &[&enumeration], &[]);
        for (case, values) in [
            vec!["IRConst.int_ 19"],
            vec![
                "IRConst.int_ 19",
                "IRConst.bool_ Bool.true",
                "IRConst.bool_ Bool.false",
            ],
            vec!["IRConst.int_ 0", "IRConst.bool_ Bool.true"],
            vec!["IRConst.int_ 275", "IRConst.bool_ Bool.true"],
            vec!["IRConst.bool_ Bool.true", "IRConst.bool_ Bool.true"],
            vec!["IRConst.int_ 19", "IRConst.int_ 1"],
            vec!["IRConst.int_ 19", "IRConst.undef_"],
            vec!["IRConst.int_ 19", "IRConst.phantomdata"],
        ]
        .iter()
        .enumerate()
        {
            let expected = if case == 5 { NOT_INT } else { BAD };
            result(
                &mut spec,
                &format!("const_bad_enum_{case}"),
                &ctx,
                "IRTy.enum_ 7",
                &aggregate("IRConst", values),
                expected,
            );
        }
        for (case, constant) in [
            "IRConst.vnil",
            "IRConst.vcons (IRConst.int_ 19) IRConst.vnil",
            "IRConst.aggv (IRConst.int_ 19)",
        ]
        .iter()
        .enumerate()
        {
            result(
                &mut spec,
                &format!("const_junk_{case}"),
                &ctx,
                "IRTy.enum_ 7",
                constant,
                BAD,
            );
        }
        let old = format!("(IRByteContextV1.mk ({PROGRAM}) (IRList.nil IRByteLayoutV1) (IRList.nil IRByteSignatureV1) (IRList.nil IRByteFunctionV1) (IRList.nil IRByteSiteV1))");
        result(
            &mut spec,
            "const_old_enum_refused",
            &old,
            "IRTy.enum_ 7",
            &aggregate("IRConst", &["IRConst.int_ 19", "IRConst.bool_ Bool.true"]),
            BAD,
        );
        let duplicate = context(&[], &[&enumeration, &enumeration], &[]);
        result(
            &mut spec,
            "const_duplicate_enum_refused",
            &duplicate,
            "IRTy.enum_ 7",
            &aggregate("IRConst", &["IRConst.int_ 19", "IRConst.bool_ Bool.true"]),
            BAD,
        );
    });
}

#[test]
fn byte_const_context_recursive_schema_and_scalar_bit_patterns_stay_bounded() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let recursive =
            format!("IRByteEnumV1.mk 7 (IRTy.uint_ 8) ({})", list("IRByteEnumVariantV1", &[
            "IRByteEnumVariantV1.mk 3 (IRList.nil IRTy)",
            "IRByteEnumVariantV1.mk 19 (IRList.cons IRTy (IRTy.enum_ 7) (IRList.nil IRTy))",
        ]));
        let ctx = context(&[], &[&recursive], &[]);
        let leaf = aggregate("IRConst", &["IRConst.int_ 3"]);
        let nested = aggregate("IRConst", &["IRConst.int_ 19", &leaf]);
        result(
            &mut spec,
            "const_finite_recursive_schema",
            &ctx,
            "IRTy.enum_ 7",
            &nested,
            &format!(
                "IRStepResult.value ({})",
                aggregate(
                    "IRScalar",
                    &[
                        "IRScalar.int_ 19",
                        &aggregate("IRScalar", &["IRScalar.int_ 3"])
                    ]
                )
            ),
        );
        let fields = layout(9, &["IRTy.uint_ 8", "IRTy.usize_ 64", "IRTy.unit_"]);
        let ctx = context(&[&fields], &[], &[]);
        result(
            &mut spec,
            "const_fields_wrap_individually",
            &ctx,
            "IRTy.struct_ 9",
            &aggregate(
                "IRConst",
                &["IRConst.int_ 259", "IRConst.int_ 7", "IRConst.phantomdata"],
            ),
            &format!(
                "IRStepResult.value ({})",
                aggregate(
                    "IRScalar",
                    &["IRScalar.int_ 3", "IRScalar.int_ 7", "IRScalar.unit_"]
                )
            ),
        );
        result(
            &mut spec,
            "const_poison_root",
            &ctx,
            "IRTy.unit_",
            "IRConst.undef_",
            BAD,
        );
        result(
            &mut spec,
            "const_phantom_not_bool",
            &ctx,
            "IRTy.bool_",
            "IRConst.phantomdata",
            BAD,
        );
        result(
            &mut spec,
            "const_unknown_structure",
            &ctx,
            "IRTy.struct_ 88",
            &aggregate("IRConst", &[]),
            BAD,
        );
    });
}

#[path = "eval_ir_byte_const_tests/cases.rs"]
mod cases;
