// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Inhabited complete SSA construction and fetched-dispatch model witnesses.
//! Hand-built catalogs/modules test the operational shapes preserved in the
//! historical Name/Expr capture. They do not replace a production body, prove
//! a captured callee, authenticate operand reflection, or decode Rust memory.

use crate::spec::Specification;
use clean_kernel::Name;

const ROOTS: &[&str] = &[
    "ir_byte_field_checked_input_v1",
    "ir_byte_field_selected_extract_v1",
    "ir_byte_field_selected_insert_v1",
    "ir_byte_field_extract_old_refused_v1",
    "ir_byte_field_insert_old_refused_v1",
    "ir_byte_field_enum_tag_write_refused_v1",
    "ir_byte_field_extract_mkt_v1",
    "ir_byte_field_insert_mkt_v1",
    "ir_byte_field_extract_metadata_refused_v1",
    "ir_byte_field_insert_metadata_refused_v1",
    "ir_byte_field_bind_world_v1",
    "ir_byte_field_scalar_world_v1",
    "ir_byte_field_fault_world_v1",
    "ir_byte_step_field_extract_v1",
    "ir_byte_step_field_insert_v1",
];
const BAD: &str = "IRStepResult.fault (IROutcome.type_error IRFault.bad_field)";
const BOUNDS: &str = "IRStepResult.fault (IROutcome.ub IRFault.bad_field)";
const ABSENT: &str = "IRStepResult.fault (IROutcome.unmodelled IRFault.width_bounded)";
const PROGRAM: &str = "IRModule.mk (@IRList.nil IRFunc) (@IRList.nil IRGlobal)";
const TRUE: &str = "(@Eq.refl Bool Bool.true)";

fn specification() -> Specification {
    crate::eval_ir::build_byte_prelude_spec_v1_with_stack().expect("public Byte field vocabulary")
}

fn checked(spec: &Specification, name: &str) {
    let def = spec.get_definition(name).expect("value-bearing root");
    assert!(!def.is_axiom && def.elaborated_value.is_some());
    spec.verify_definition(name).expect("actual kernel check");
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn add(spec: &mut Specification, source: &str) {
    spec.add_recursive_def(source, "Explicit complete SSA field model witness")
        .unwrap_or_else(|error| panic!("{source}: {error}"));
    checked(spec, source.split_whitespace().nth(1).unwrap());
}

fn equality(spec: &mut Specification, name: &str, ty: &str, actual: &str, expected: &str) {
    add(
        spec,
        &format!("def {name} : @Eq ({ty}) ({actual}) ({expected}) := @Eq.refl ({ty}) ({expected})"),
    );
}

fn result(spec: &mut Specification, name: &str, actual: &str, expected: &str) {
    equality(spec, name, "IRStepResult", actual, expected);
}

fn rejected(spec: &mut Specification, name: &str, source: &str) {
    let error = spec
        .add_recursive_def(source, "Unchanged-proof wrong field conclusion")
        .expect_err("wrong conclusion must not pass");
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

fn list(ty: &str, values: &[&str]) -> String {
    values
        .iter()
        .rev()
        .fold(format!("@IRList.nil {ty}"), |tail, value| {
            format!("@IRList.cons {ty} ({value}) ({tail})")
        })
}

fn spine(ty: &str, values: &[&str]) -> String {
    values
        .iter()
        .rev()
        .fold(format!("{ty}.vnil"), |tail, value| {
            format!("{ty}.vcons ({value}) ({tail})")
        })
}

fn aggregate(ty: &str, values: &[&str]) -> String {
    format!("{ty}.aggv ({})", spine(ty, values))
}

fn layout(id: u64, fields: &[&str]) -> String {
    format!(
        "IRByteLayoutV1.mk (IRTy.struct_ {id}) 32 8 ({}) (@IRList.nil Nat)",
        list("IRTy", fields)
    )
}

fn schema(id: u64, variants: &[(u64, &[&str])]) -> String {
    let variants: Vec<_> = variants
        .iter()
        .map(|(tag, fields)| format!("IRByteEnumVariantV1.mk {tag} ({})", list("IRTy", fields)))
        .collect();
    format!(
        "IRByteEnumV1.mk {id} (IRTy.uint_ 64) ({})",
        list(
            "IRByteEnumVariantV1",
            &variants.iter().map(String::as_str).collect::<Vec<_>>()
        )
    )
}

fn rows(values: &[(u64, &str)]) -> String {
    let values: Vec<_> = values
        .iter()
        .map(|(id, ty)| format!("IRByteOperandV1.mk {id} ({ty})"))
        .collect();
    list(
        "IRByteOperandV1",
        &values.iter().map(String::as_str).collect::<Vec<_>>(),
    )
}

fn site(pc: u64, ty: &str, operands: &[(u64, &str)]) -> String {
    format!(
        "IRByteSiteV1.mkt 41 0 {pc} 0 1 ({}) ({})",
        list("IRTy", &[ty]),
        rows(operands)
    )
}

fn context(layouts: &[&str], enums: &[&str], sites: &[&str]) -> String {
    format!("(IRByteContextV1.mke ({PROGRAM}) ({}) (@IRList.nil IRByteSignatureV1) (@IRList.nil IRByteFunctionV1) ({}) ({}))", list("IRByteLayoutV1", layouts), list("IRByteSiteV1", sites), list("IRByteEnumV1", enums))
}

#[test]
fn byte_field_nominal_laws_have_inhabited_applications_and_same_proof_controls() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for root in ROOTS {
            checked(&spec, root);
        }
        let fields = list("IRTy", &["IRTy.fatstr_", "IRTy.uint_ 64"]);
        let sp = spine("IRScalar", &["IRScalar.fat_ 16 3", "IRScalar.int_ 5"]);
        let structure = layout(9, &["IRTy.fatstr_", "IRTy.uint_ 64"]);
        let typed = site(0, "IRTy.fatstr_", &[(0, "IRTy.struct_ 9")]);
        let ctx = context(&[&structure], &[], &[&typed]);
        add(
            &mut spec,
            &format!("def field_law_ctx : IRByteContextV1 := {ctx}"),
        );
        let extract = format!("def field_derived_extract : @Eq IRStepResult\n  (ir_byte_extract_typed_v1 field_law_ctx (IRTy.struct_ 9) IRTy.fatstr_ (IRScalar.aggv ({sp})) 0)\n  (IRStepResult.value (IRScalar.fat_ 16 3)) :=\n  ir_byte_field_selected_extract_v1 field_law_ctx (IRTy.struct_ 9) IRTy.fatstr_ IRTy.fatstr_ ({sp}) 0 ({fields}) (IRScalar.fat_ 16 3) {TRUE}\n    (@Eq.refl (IROption (IRList IRTy)) (@IROption.some (IRList IRTy) ({fields})))\n    (@Eq.refl (IROption IRTy) (@IROption.some IRTy IRTy.fatstr_)) {TRUE}\n    (@Eq.refl (IROption IRScalar) (@IROption.some IRScalar (IRScalar.fat_ 16 3))) {TRUE}");
        add(&mut spec, &extract);
        let wrong = extract
            .replacen("field_derived_extract", "field_wrong_nominal", 1)
            .replacen(
                "(IRTy.struct_ 9) IRTy.fatstr_",
                "(IRTy.struct_ 9) IRTy.containerlen_",
                1,
            );
        assert_eq!(
            extract.split_once(":=").unwrap().1,
            wrong.split_once(":=").unwrap().1
        );
        rejected(&mut spec, "field_wrong_nominal", &wrong);
        let updated = aggregate("IRScalar", &["IRScalar.fat_ 16 3", "IRScalar.int_ 11"]);
        let insert = format!("def field_derived_insert : @Eq IRStepResult\n  (ir_byte_insert_typed_v1 field_law_ctx (IRTy.struct_ 9) (IRTy.uint_ 64) (IRScalar.aggv ({sp})) 1 (IRScalar.int_ 11))\n  (IRStepResult.value ({updated})) :=\n  ir_byte_field_selected_insert_v1 field_law_ctx (IRTy.struct_ 9) (IRTy.uint_ 64) (IRTy.uint_ 64) ({sp}) 1 ({fields}) (IRScalar.int_ 11) {TRUE} {TRUE}\n    (@Eq.refl (IROption (IRList IRTy)) (@IROption.some (IRList IRTy) ({fields})))\n    (@Eq.refl (IROption IRTy) (@IROption.some IRTy (IRTy.uint_ 64))) {TRUE} {TRUE} {TRUE} {TRUE}");
        add(&mut spec, &insert);
        let wrong = insert
            .replacen("field_derived_insert", "field_wrong_updated", 1)
            .replacen(
                &format!("(IRStepResult.value ({updated}))"),
                &format!(
                    "(IRStepResult.value ({}))",
                    aggregate("IRScalar", &["IRScalar.fat_ 16 3", "IRScalar.int_ 12"])
                ),
                1,
            );
        assert_eq!(
            insert.split_once(":=").unwrap().1,
            wrong.split_once(":=").unwrap().1
        );
        rejected(&mut spec, "field_wrong_updated", &wrong);
        let insert_rows = rows(&[(0, "IRTy.struct_ 9"), (1, "IRTy.uint_ 64")]);
        let insert_site = site(
            0,
            "IRTy.struct_ 9",
            &[(0, "IRTy.struct_ 9"), (1, "IRTy.uint_ 64")],
        );
        let insert_ctx = context(&[&structure], &[], &[&insert_site]);
        add(&mut spec, &format!("def field_derived_insert_site : @Eq IRStepResult\n  (ir_byte_insert_field_v1 {insert_ctx} ({insert_site}) (IRTy.struct_ 9) 0 (IRScalar.aggv ({sp})) 1 1 (IRScalar.int_ 11))\n  (ir_byte_insert_typed_v1 {insert_ctx} (IRTy.struct_ 9) (IRTy.uint_ 64) (IRScalar.aggv ({sp})) 1 (IRScalar.int_ 11)) :=\n  ir_byte_field_insert_mkt_v1 {insert_ctx} 41 0 0 0 1 ({}) ({insert_rows}) (IRTy.struct_ 9) (IRTy.struct_ 9) 0 (IRScalar.aggv ({sp})) 1 1 (IRTy.uint_ 64) (IRScalar.int_ 11) {TRUE}\n    (@Eq.refl (IROption IRTy) (@IROption.some IRTy (IRTy.struct_ 9))) {TRUE}\n    (@Eq.refl (IROption IRTy) (@IROption.some IRTy (IRTy.uint_ 64)))", list("IRTy", &["IRTy.struct_ 9"])));
        add(&mut spec, &format!("def field_derived_site : @Eq IRStepResult\n  (ir_byte_extract_field_v1 field_law_ctx ({typed}) IRTy.fatstr_ 0 (IRScalar.aggv ({sp})) 0)\n  (ir_byte_extract_typed_v1 field_law_ctx (IRTy.struct_ 9) IRTy.fatstr_ (IRScalar.aggv ({sp})) 0) :=\n  ir_byte_field_extract_mkt_v1 field_law_ctx 41 0 0 0 1 ({}) ({}) IRTy.fatstr_ (IRTy.struct_ 9) 0 (IRScalar.aggv ({sp})) 0 {TRUE} (@Eq.refl (IROption IRTy) (@IROption.some IRTy (IRTy.struct_ 9)))", list("IRTy", &["IRTy.fatstr_"]), rows(&[(0, "IRTy.struct_ 9")])));
    });
}

#[test]
fn byte_field_struct_nominal_operand_result_and_replacement_types_are_exact() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let structure = layout(9, &["IRTy.fatstr_", "IRTy.uint_ 64"]);
        let value = aggregate("IRScalar", &["IRScalar.fat_ 16 3", "IRScalar.int_ 5"]);
        let extract_site = site(0, "IRTy.fatstr_", &[(0, "IRTy.struct_ 9")]);
        let ctx = context(&[&structure], &[], &[&extract_site]);
        result(
            &mut spec,
            "field_struct_extract",
            &format!("ir_byte_extract_field_v1 {ctx} ({extract_site}) IRTy.fatstr_ 0 ({value}) 0"),
            "IRStepResult.value (IRScalar.fat_ 16 3)",
        );
        for (case, (result_ty, replacement_ty, expected)) in [
            (
                "IRTy.struct_ 9",
                "IRTy.fatstr_",
                format!(
                    "IRStepResult.value ({})",
                    aggregate("IRScalar", &["IRScalar.fat_ 32 7", "IRScalar.int_ 5"])
                ),
            ),
            ("IRTy.struct_ 9", "IRTy.containerlen_", BAD.to_owned()),
            ("IRTy.struct_ 10", "IRTy.fatstr_", BAD.to_owned()),
        ]
        .iter()
        .enumerate()
        {
            let typed = site(0, result_ty, &[(0, "IRTy.struct_ 9"), (1, replacement_ty)]);
            let ctx = context(&[&structure], &[], &[&typed]);
            result(&mut spec, &format!("field_struct_insert_{case}"), &format!("ir_byte_insert_field_v1 {ctx} ({typed}) ({result_ty}) 0 ({value}) 0 1 (IRScalar.fat_ 32 7)"), expected);
        }
        for (case, nominal) in [
            "IRTy.containerlen_",
            "IRTy.fatslice_ (IRTy.uint_ 8)",
            "IRTy.fatdyn_ 41",
            "IRTy.containervtable_",
        ]
        .iter()
        .enumerate()
        {
            let typed = site(0, nominal, &[(0, "IRTy.struct_ 9")]);
            let ctx = context(&[&structure], &[], &[&typed]);
            result(
                &mut spec,
                &format!("field_wrong_fat_{case}"),
                &format!("ir_byte_extract_field_v1 {ctx} ({typed}) ({nominal}) 0 ({value}) 0"),
                BAD,
            );
        }
        let wrong_results = site(0, "IRTy.containerlen_", &[(0, "IRTy.struct_ 9")]);
        result(
            &mut spec,
            "field_wrong_result_catalog",
            &format!(
                "ir_byte_extract_field_v1 {} ({wrong_results}) IRTy.fatstr_ 0 ({value}) 0",
                context(&[&structure], &[], &[&wrong_results])
            ),
            BAD,
        );
        result(&mut spec, "field_thin_reference_is_not_aggregate", &format!("ir_byte_extract_typed_v1 {ctx} (IRTy.ref_ (IRTy.struct_ 9)) IRTy.fatstr_ (IRScalar.ptr_ 16) 0"), "IRStepResult.fault (IROutcome.type_error IRFault.not_agg)");
    });
}

#[test]
fn byte_field_enum_active_lanes_and_tag_read_only_use_canonical_words() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let enumeration = schema(
            7,
            &[
                (19, &["IRTy.fatstr_"]),
                (27, &["IRTy.bool_", "IRTy.uint_ 64"]),
            ],
        );
        let ctx = context(&[], &[&enumeration], &[]);
        let active = aggregate("IRScalar", &["IRScalar.int_ 19", "IRScalar.fat_ 16 3"]);
        for (case, (ty, field, expected)) in [
            ("IRTy.uint_ 64", 0, "IRStepResult.value (IRScalar.int_ 19)"),
            ("IRTy.fatstr_", 1, "IRStepResult.value (IRScalar.fat_ 16 3)"),
            ("IRTy.bool_", 1, BOUNDS),
            ("IRTy.bool_", 0, BAD),
            ("IRTy.uint_ 64", 2, BOUNDS),
        ]
        .iter()
        .enumerate()
        {
            result(
                &mut spec,
                &format!("field_enum_extract_{case}"),
                &format!("ir_byte_extract_typed_v1 {ctx} (IRTy.enum_ 7) ({ty}) ({active}) {field}"),
                expected,
            );
        }
        result(&mut spec, "field_enum_retag_refused", &format!("ir_byte_insert_typed_v1 {ctx} (IRTy.enum_ 7) (IRTy.uint_ 64) ({active}) 0 (IRScalar.int_ 27)"), BOUNDS);
        result(&mut spec, "field_enum_other_variant_payload_refused", &format!("ir_byte_insert_typed_v1 {ctx} (IRTy.enum_ 7) IRTy.bool_ ({active}) 1 (IRScalar.bool_ Bool.true)"), BOUNDS);
        let updated = aggregate("IRScalar", &["IRScalar.int_ 19", "IRScalar.fat_ 32 7"]);
        result(&mut spec, "field_enum_payload_update", &format!("ir_byte_insert_typed_v1 {ctx} (IRTy.enum_ 7) IRTy.fatstr_ ({active}) 1 (IRScalar.fat_ 32 7)"), &format!("IRStepResult.value ({updated})"));
        let signed = format!(
            "IRByteEnumV1.mk 7 (IRTy.int_ 8) ({})",
            list(
                "IRByteEnumVariantV1",
                &[&format!(
                    "IRByteEnumVariantV1.mk 255 ({})",
                    list("IRTy", &["IRTy.bool_"])
                )]
            )
        );
        let signed_ctx = context(&[], &[&signed], &[]);
        for (case, (tag, expected)) in [(255, "IRStepResult.value (IRScalar.int_ 255)"), (511, BAD)]
            .iter()
            .enumerate()
        {
            let signed_value = aggregate(
                "IRScalar",
                &[&format!("IRScalar.int_ {tag}"), "IRScalar.bool_ Bool.true"],
            );
            result(&mut spec, &format!("field_signed_raw_word_{case}"), &format!("ir_byte_extract_typed_v1 {signed_ctx} (IRTy.enum_ 7) (IRTy.int_ 8) ({signed_value}) 0"), expected);
        }
        for (case, tag) in [0, 275].iter().enumerate() {
            let bad = aggregate(
                "IRScalar",
                &[&format!("IRScalar.int_ {tag}"), "IRScalar.fat_ 16 3"],
            );
            result(
                &mut spec,
                &format!("field_enum_raw_tag_{case}"),
                &format!("ir_byte_extract_typed_v1 {ctx} (IRTy.enum_ 7) IRTy.fatstr_ ({bad}) 1"),
                BAD,
            );
        }
        add(&mut spec, &format!("def field_derived_tag_refusal : @Eq IRStepResult (ir_byte_insert_typed_v1 {ctx} (IRTy.enum_ 7) (IRTy.uint_ 64) ({active}) 0 (IRScalar.int_ 27)) ({BOUNDS}) := ir_byte_field_enum_tag_write_refused_v1 {ctx} 7 (IRTy.uint_ 64) ({}) (IRScalar.int_ 27) {TRUE}", spine("IRScalar", &["IRScalar.int_ 19", "IRScalar.fat_ 16 3"])));
    });
}

#[test]
fn byte_field_complete_guards_refuse_partial_spines_cycles_and_duplicate_schemas() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let structure = layout(9, &["IRTy.uint_ 64", "IRTy.bool_"]);
        let ctx = context(&[&structure], &[], &[]);
        for (case, values) in [
            vec!["IRScalar.int_ 1"],
            vec!["IRScalar.int_ 1", "IRScalar.undef_"],
            vec!["IRScalar.int_ 1", "IRScalar.int_ 0"],
            vec![
                "IRScalar.int_ 1",
                "IRScalar.bool_ Bool.true",
                "IRScalar.unit_",
            ],
        ]
        .iter()
        .enumerate()
        {
            let value = aggregate("IRScalar", values);
            result(
                &mut spec,
                &format!("field_incomplete_read_{case}"),
                &format!(
                    "ir_byte_extract_typed_v1 {ctx} (IRTy.struct_ 9) (IRTy.uint_ 64) ({value}) 0"
                ),
                BAD,
            );
            result(&mut spec, &format!("field_incomplete_update_{case}"), &format!("ir_byte_insert_typed_v1 {ctx} (IRTy.struct_ 9) (IRTy.uint_ 64) ({value}) 0 (IRScalar.int_ 2)"), BAD);
        }
        let complete = aggregate("IRScalar", &["IRScalar.int_ 1", "IRScalar.bool_ Bool.true"]);
        let duplicate = context(&[&structure, &structure], &[], &[]);
        result(&mut spec, "field_duplicate_layout_refused", &format!("ir_byte_extract_typed_v1 {duplicate} (IRTy.struct_ 9) (IRTy.uint_ 64) ({complete}) 0"), BAD);
        for (case, enumeration) in [
            schema(7, &[(19, &["IRTy.bool_"]), (19, &["IRTy.uint_ 64"])]),
            schema(7, &[]),
        ]
        .iter()
        .enumerate()
        {
            let ctx = context(&[&structure], &[enumeration], &[]);
            result(&mut spec, &format!("field_bad_enum_catalog_{case}"), &format!("ir_byte_extract_typed_v1 {ctx} (IRTy.struct_ 9) (IRTy.uint_ 64) ({complete}) 0"), BAD);
        }
        let self_layout = layout(10, &["IRTy.struct_ 10"]);
        let enumeration = schema(7, &[(19, &["IRTy.bool_"])]);
        let duplicate_enums = context(&[&structure], &[&enumeration, &enumeration], &[]);
        result(&mut spec, "field_duplicate_enum_id_refused", &format!("ir_byte_extract_typed_v1 {duplicate_enums} (IRTy.struct_ 9) (IRTy.uint_ 64) ({complete}) 0"), BAD);
        let cyclic = context(&[&self_layout], &[], &[]);
        let finite = aggregate("IRScalar", &[&aggregate("IRScalar", &[])]);
        result(&mut spec, "field_cycle_finite_value_refused", &format!("ir_byte_extract_typed_v1 {cyclic} (IRTy.struct_ 10) (IRTy.struct_ 10) ({finite}) 0"), BAD);
        result(&mut spec, "field_bad_spine_refused", &format!("ir_byte_extract_typed_v1 {ctx} (IRTy.struct_ 9) (IRTy.uint_ 64) (IRScalar.aggv (IRScalar.int_ 1)) 0"), BAD);
        result(&mut spec, "field_bad_replacement_refused", &format!("ir_byte_insert_typed_v1 {ctx} (IRTy.struct_ 9) (IRTy.uint_ 64) ({complete}) 0 IRScalar.undef_"), BAD);
        result(&mut spec, "field_out_of_bounds_refused", &format!("ir_byte_insert_typed_v1 {ctx} (IRTy.struct_ 9) (IRTy.uint_ 64) ({complete}) 2 (IRScalar.int_ 2)"), BOUNDS);
    });
}

#[test]
fn byte_field_site_metadata_is_opt_in_unique_complete_and_single_result() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let structure = layout(9, &["IRTy.uint_ 64"]);
        let value = aggregate("IRScalar", &["IRScalar.int_ 5"]);
        let old =
            "IRByteSiteV1.mk 41 0 0 0 1 (@IRList.cons IRTy (IRTy.uint_ 64) (@IRList.nil IRTy))";
        let ctx = context(&[&structure], &[], &[old]);
        add(&mut spec, &format!("def field_derived_old_extract : @Eq IRStepResult (ir_byte_extract_field_v1 {ctx} ({old}) (IRTy.uint_ 64) 0 ({value}) 0) ({ABSENT}) := ir_byte_field_extract_old_refused_v1 {ctx} 41 0 0 0 1 ({}) (IRTy.uint_ 64) 0 ({value}) 0", list("IRTy", &["IRTy.uint_ 64"])));
        add(&mut spec, &format!("def field_derived_old_insert : @Eq IRStepResult (ir_byte_insert_field_v1 {ctx} ({old}) (IRTy.struct_ 9) 0 ({value}) 0 1 (IRScalar.int_ 7)) ({ABSENT}) := ir_byte_field_insert_old_refused_v1 {ctx} 41 0 0 0 1 ({}) (IRTy.struct_ 9) 0 ({value}) 0 1 (IRScalar.int_ 7)", list("IRTy", &["IRTy.uint_ 64"])));
        result(
            &mut spec,
            "field_old_extract_refused",
            &format!("ir_byte_extract_field_v1 {ctx} ({old}) (IRTy.uint_ 64) 0 ({value}) 0"),
            ABSENT,
        );
        result(&mut spec, "field_old_insert_refused", &format!("ir_byte_insert_field_v1 {ctx} ({old}) (IRTy.struct_ 9) 0 ({value}) 0 1 (IRScalar.int_ 7)"), ABSENT);
        for (case, operands) in [
            rows(&[]),
            rows(&[(0, "IRTy.struct_ 9"), (0, "IRTy.struct_ 9")]),
            rows(&[
                (0, "IRTy.struct_ 9"),
                (1, "IRTy.uint_ 64"),
                (0, "IRTy.struct_ 10"),
            ]),
        ]
        .iter()
        .enumerate()
        {
            let typed = format!(
                "IRByteSiteV1.mkt 41 0 0 0 1 ({}) ({operands})",
                list("IRTy", &["IRTy.uint_ 64"])
            );
            let ctx = context(&[&structure], &[], &[&typed]);
            result(
                &mut spec,
                &format!("field_bad_operands_{case}"),
                &format!("ir_byte_extract_field_v1 {ctx} ({typed}) (IRTy.uint_ 64) 0 ({value}) 0"),
                BAD,
            );
        }
        let typed = site(0, "IRTy.uint_ 64", &[(0, "IRTy.struct_ 9")]);
        for (case, result_types) in [
            list("IRTy", &[]),
            list("IRTy", &["IRTy.uint_ 64", "IRTy.uint_ 64"]),
        ]
        .iter()
        .enumerate()
        {
            let bad_site = format!(
                "IRByteSiteV1.mkt 41 0 0 0 1 ({result_types}) ({})",
                rows(&[(0, "IRTy.struct_ 9")])
            );
            result(
                &mut spec,
                &format!("field_result_arity_{case}"),
                &format!(
                    "ir_byte_extract_field_v1 {} ({bad_site}) (IRTy.uint_ 64) 0 ({value}) 0",
                    context(&[&structure], &[], &[&bad_site])
                ),
                BAD,
            );
        }
        let duplicate = context(&[&structure], &[], &[&typed, old]);
        result(
            &mut spec,
            "field_duplicate_site_refused",
            &format!(
                "ir_byte_extract_field_v1 {duplicate} ({typed}) (IRTy.uint_ 64) 0 ({value}) 0"
            ),
            BAD,
        );
        let insert = site(0, "IRTy.struct_ 9", &[(0, "IRTy.struct_ 9")]);
        add(&mut spec, &format!("def field_derived_duplicate_extract : @Eq IRStepResult (ir_byte_extract_field_v1 {duplicate} ({typed}) (IRTy.uint_ 64) 0 ({value}) 0) ({BAD}) := ir_byte_field_extract_metadata_refused_v1 {duplicate} 41 0 0 0 1 ({}) ({}) (IRTy.uint_ 64) (IRTy.struct_ 9) 0 ({value}) 0 (@Eq.refl Bool Bool.false)", list("IRTy", &["IRTy.uint_ 64"]), rows(&[(0, "IRTy.struct_ 9")])));
        add(&mut spec, &format!("def field_derived_duplicate_insert : @Eq IRStepResult (ir_byte_insert_field_v1 {duplicate} ({typed}) (IRTy.uint_ 64) 0 ({value}) 0 1 (IRScalar.int_ 7)) ({BAD}) := ir_byte_field_insert_metadata_refused_v1 {duplicate} 41 0 0 0 1 ({}) ({}) (IRTy.uint_ 64) (IRTy.struct_ 9) 0 ({value}) 0 1 (IRScalar.int_ 7) (@Eq.refl Bool Bool.false)", list("IRTy", &["IRTy.uint_ 64"]), rows(&[(0, "IRTy.struct_ 9")])));
        result(&mut spec, "field_missing_replacement_row", &format!("ir_byte_insert_field_v1 {} ({insert}) (IRTy.struct_ 9) 0 ({value}) 0 1 (IRScalar.int_ 7)", context(&[&structure], &[], &[&insert])), BAD);
    });
}

#[path = "eval_ir_byte_field_tests/cases.rs"]
mod cases;
