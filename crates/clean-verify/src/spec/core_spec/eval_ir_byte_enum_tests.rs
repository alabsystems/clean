// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructed SSA-schema witnesses and semantic refusals. These are not a
//! captured Name/Expr program, a Rust enum-layout claim, or provider fidelity.

use crate::spec::Specification;
use clean_kernel::Name;

const ROOTS: &[&str] = &[
    "ir_byte_enum_selected_fields_v1",
    "ir_byte_enum_ssa_selected_v1",
    "ir_byte_enum_ssa_input_v1",
    "ir_byte_enum_ssa_tag_v1",
    "ir_byte_enum_ssa_payload_v1",
    "ir_byte_enum_empty_extension_v1",
    "ir_byte_enum_empty_context_refused_v1",
    "ir_byte_enum_raw_lane_refused_v1",
    "ir_byte_enum_raw_decode_refused_v1",
    "ir_byte_enum_raw_load_refused_v1",
    "ir_byte_enum_raw_store_refused_v1",
];
const MODULE: &str = "(IRModule.mk (@IRList.nil IRFunc) (@IRList.nil IRGlobal))";
const TRUE: &str = "(@Eq.refl Bool Bool.true)";

fn specification() -> Specification {
    crate::eval_ir::build_byte_prelude_spec_v1_with_stack().expect("public ByteV1 vocabulary")
}

fn checked(spec: &Specification, name: &str) {
    let def = spec
        .get_definition(name)
        .expect("installed value-bearing root");
    assert!(!def.is_axiom && def.elaborated_value.is_some());
    spec.verify_definition(name).expect("kernel-checked body");
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn add(spec: &mut Specification, source: &str) {
    spec.add_recursive_def(source, "Constructed SSA enum model regression")
        .unwrap_or_else(|error| panic!("{source}: {error}"));
    checked(spec, source.split_whitespace().nth(1).unwrap());
}

fn equality(spec: &mut Specification, name: &str, ty: &str, actual: &str, expected: &str) {
    add(
        spec,
        &format!("def {name} : @Eq ({ty}) ({actual}) ({expected}) := @Eq.refl ({ty}) ({expected})"),
    );
}

fn reject(spec: &mut Specification, name: &str, source: &str) {
    let error = spec
        .add_recursive_def(source, "Unchanged-proof wrong enum conclusion")
        .expect_err("wrong endpoint must be rejected");
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

fn list(ty: &str, values: &[&str]) -> String {
    values
        .iter()
        .rev()
        .fold(format!("(@IRList.nil {ty})"), |tail, value| {
            format!("(@IRList.cons {ty} ({value}) {tail})")
        })
}

fn variant(tag: &str, fields: &[&str]) -> String {
    format!("(IRByteEnumVariantV1.mk {tag} {})", list("IRTy", fields))
}

fn schema(id: usize, ty: &str, variants: &[&str]) -> String {
    format!(
        "(IRByteEnumV1.mk {id} ({ty}) {})",
        list("IRByteEnumVariantV1", variants)
    )
}

fn context(enums: &[&str], layouts: &[&str], functions: &[&str]) -> String {
    format!("(IRByteContextV1.mke {MODULE} {} (@IRList.nil IRByteSignatureV1) {} (@IRList.nil IRByteSiteV1) {})",
        list("IRByteLayoutV1", layouts), list("IRByteFunctionV1", functions), list("IRByteEnumV1", enums))
}

fn spine(values: &[&str]) -> String {
    values
        .iter()
        .rev()
        .fold("IRScalar.vnil".into(), |tail, value| {
            format!("(IRScalar.vcons ({value}) {tail})")
        })
}

fn aggregate(values: &[&str]) -> String {
    format!("(IRScalar.aggv {})", spine(values))
}

fn admits(spec: &mut Specification, name: &str, ctx: &str, ty: &str, value: &str, expected: bool) {
    equality(
        spec,
        name,
        "Bool",
        &format!("ir_byte_value_matches_v1 {ctx} ({ty}) ({value})"),
        if expected { "Bool.true" } else { "Bool.false" },
    );
}

#[test]
fn byte_enum_sparse_signed_and_wide_tags_use_canonical_words_not_ordinals() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let a = variant("3", &[]);
        let b = variant("19", &["IRTy.bool_"]);
        let s = schema(7, "IRTy.uint_ 8", &[&a, &b]);
        let ctx = context(&[&s], &[], &[]);
        for (i, (lanes, expected)) in [
            (vec!["IRScalar.int_ 3"], true),
            (vec!["IRScalar.int_ 19", "IRScalar.bool_ Bool.true"], true),
            (vec!["IRScalar.int_ 0"], false),
            (vec!["IRScalar.int_ 1", "IRScalar.bool_ Bool.true"], false),
            (vec!["IRScalar.int_ 7"], false),
        ]
        .iter()
        .enumerate()
        {
            admits(
                &mut spec,
                &format!("enum_sparse_{i}"),
                &ctx,
                "IRTy.enum_ 7",
                &aggregate(lanes),
                *expected,
            );
        }
        // -5 is the canonical signed 8-bit pattern 251, not variant index 0.
        let signed = schema(9, "IRTy.int_ 8", &[&variant("251", &[])]);
        admits(
            &mut spec,
            "enum_signed_pattern",
            &context(&[&signed], &[], &[]),
            "IRTy.enum_ 9",
            &aggregate(&["IRScalar.int_ 251"]),
            true,
        );
        // Wider explicit reprs are valid; do not force inferred minimal width.
        for (i, ty) in [
            "IRTy.int_ 8",
            "IRTy.uint_ 16",
            "IRTy.int_ 32",
            "IRTy.uint_ 64",
            "IRTy.int_ 128",
            "IRTy.uint_ 128",
        ]
        .iter()
        .enumerate()
        {
            let s = schema(2, ty, &[&variant("3", &[])]);
            admits(
                &mut spec,
                &format!("enum_explicit_width_{i}"),
                &context(&[&s], &[], &[]),
                "IRTy.enum_ 2",
                &aggregate(&["IRScalar.int_ 3"]),
                true,
            );
        }
        for (i, (ty, word, expected)) in [
            ("IRTy.int_ 8", "255", true),
            ("IRTy.uint_ 8", "256", false),
            ("IRTy.uint_ 7", "3", false),
            ("IRTy.uint_ 256", "3", false),
            ("IRTy.usize_ 64", "3", false),
            ("IRTy.bool_", "1", false),
            (
                "IRTy.int_ 128",
                "340282366920938463463374607431768211455",
                true,
            ),
            (
                "IRTy.int_ 128",
                "340282366920938463463374607431768211456",
                false,
            ),
            (
                "IRTy.uint_ 128",
                "170141183460469231731687303715884105727",
                true,
            ),
            (
                "IRTy.uint_ 128",
                "170141183460469231731687303715884105728",
                false,
            ),
        ]
        .iter()
        .enumerate()
        {
            equality(
                &mut spec,
                &format!("enum_word_bound_{i}"),
                "Bool",
                &format!("ir_byte_enum_tag_fits_v1 ({ty}) {word}"),
                if *expected { "Bool.true" } else { "Bool.false" },
            );
            let s = schema(2, ty, &[&variant(word, &[])]);
            admits(
                &mut spec,
                &format!("enum_word_bound_admission_{i}"),
                &context(&[&s], &[], &[]),
                "IRTy.enum_ 2",
                &aggregate(&[&format!("IRScalar.int_ {word}")]),
                *expected,
            );
        }
    });
}

#[test]
fn byte_enum_catalog_rejects_duplicate_ids_tags_empty_and_unknown_schemas() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let a = variant("3", &[]);
        let b = variant("19", &[]);
        let good = schema(7, "IRTy.uint_ 8", &[&a, &b]);
        let other = schema(9, "IRTy.uint_ 8", &[&a]);
        let duplicate = schema(7, "IRTy.uint_ 8", &[&b]);
        let tag_duplicate = schema(7, "IRTy.uint_ 8", &[&a, &b, &a]);
        let empty = schema(7, "IRTy.uint_ 8", &[]);
        let bad_width = schema(7, "IRTy.uint_ 7", &[&a]);
        let too_large = schema(7, "IRTy.uint_ 8", &[&variant("256", &[])]);
        let contexts = [
            context(&[], &[], &[]),
            context(&[&other], &[], &[]),
            context(&[&good, &other, &duplicate], &[], &[]),
            context(&[&tag_duplicate], &[], &[]),
            context(&[&empty], &[], &[]),
            context(&[&bad_width], &[], &[]),
            context(&[&too_large], &[], &[]),
            // Invalid data elsewhere in the enum catalog fails enum admission.
            context(&[&good, &schema(11, "IRTy.uint_ 8", &[])], &[], &[]),
        ];
        for (i, ctx) in contexts.iter().enumerate() {
            admits(
                &mut spec,
                &format!("enum_bad_catalog_{i}"),
                ctx,
                "IRTy.enum_ 7",
                &aggregate(&["IRScalar.int_ 3"]),
                false,
            );
            admits(
                &mut spec,
                &format!("enum_catalog_not_scalar_guard_{i}"),
                ctx,
                "IRTy.bool_",
                "IRScalar.bool_ Bool.true",
                true,
            );
        }
        equality(
            &mut spec,
            "enum_good_catalog",
            "Bool",
            &format!(
                "ir_byte_enum_catalog_valid_v1 {}",
                list("IRByteEnumV1", &[&good, &other])
            ),
            "Bool.true",
        );
    });
}

#[test]
fn byte_enum_complete_spines_enforce_kinds_arity_and_nominal_function_types() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let s = schema(
            7,
            "IRTy.uint_ 8",
            &[&variant("19", &["IRTy.bool_", "IRTy.func_ 3"])],
        );
        let ctx = context(
            &[&s],
            &[],
            &[
                "IRByteFunctionV1.mk 40 3 4096 0 Bool.false",
                "IRByteFunctionV1.mk 41 4 8192 0 Bool.false",
            ],
        );
        let good = aggregate(&[
            "IRScalar.int_ 19",
            "IRScalar.bool_ Bool.true",
            "IRScalar.fnptr_ 40",
        ]);
        admits(
            &mut spec,
            "enum_complete_payload",
            &ctx,
            "IRTy.enum_ 7",
            &good,
            true,
        );
        for (i, value) in [
            "IRScalar.undef_".into(),
            "IRScalar.int_ 19".into(),
            "IRScalar.vnil".into(),
            spine(&[
                "IRScalar.int_ 19",
                "IRScalar.bool_ Bool.true",
                "IRScalar.fnptr_ 40",
            ]),
            "IRScalar.aggv (IRScalar.int_ 19)".into(),
            aggregate(&[]),
            aggregate(&[
                "IRScalar.bool_ Bool.true",
                "IRScalar.bool_ Bool.true",
                "IRScalar.fnptr_ 40",
            ]),
            aggregate(&[
                "IRScalar.ptr_ 19",
                "IRScalar.bool_ Bool.true",
                "IRScalar.fnptr_ 40",
            ]),
            aggregate(&[
                "IRScalar.undef_",
                "IRScalar.bool_ Bool.true",
                "IRScalar.fnptr_ 40",
            ]),
            aggregate(&["IRScalar.int_ 19", "IRScalar.int_ 1", "IRScalar.fnptr_ 40"]),
            aggregate(&[
                "IRScalar.int_ 19",
                "IRScalar.bool_ Bool.true",
                "IRScalar.fnptr_ 41",
            ]),
            aggregate(&[
                "IRScalar.int_ 19",
                "IRScalar.bool_ Bool.true",
                "IRScalar.ptr_ 4096",
            ]),
            aggregate(&["IRScalar.int_ 19", "IRScalar.bool_ Bool.true"]),
            aggregate(&[
                "IRScalar.int_ 19",
                "IRScalar.bool_ Bool.true",
                "IRScalar.fnptr_ 40",
                "IRScalar.unit_",
            ]),
            "IRScalar.aggv (IRScalar.vcons (IRScalar.int_ 19) (IRScalar.int_ 1))".into(),
        ]
        .iter()
        .enumerate()
        {
            admits(
                &mut spec,
                &format!("enum_malformed_{i}"),
                &ctx,
                "IRTy.enum_ 7",
                value,
                false,
            );
        }
    });
}

#[test]
fn byte_enum_nested_struct_enum_values_use_existing_structural_recursion() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        // Same numeric struct/enum ID is intentional: these are distinct namespaces.
        let layout = format!(
            "IRByteLayoutV1.mk (IRTy.struct_ 7) 16 8 {} {}",
            list("IRTy", &["IRTy.enum_ 7", "IRTy.bool_"]),
            list("Nat", &["0", "8"])
        );
        let leaf = schema(7, "IRTy.int_ 8", &[&variant("251", &["IRTy.uint_ 8"])]);
        let outer = schema(
            9,
            "IRTy.uint_ 16",
            &[&variant("19", &["IRTy.struct_ 7", "IRTy.enum_ 7"])],
        );
        let ctx = context(&[&leaf, &outer], &[&layout], &[]);
        let value = aggregate(&["IRScalar.int_ 251", "IRScalar.int_ 8"]);
        let product = aggregate(&[&value, "IRScalar.bool_ Bool.false"]);
        let nested = aggregate(&["IRScalar.int_ 19", &product, &value]);
        admits(
            &mut spec,
            "enum_struct_contains_enum",
            &ctx,
            "IRTy.struct_ 7",
            &product,
            true,
        );
        admits(
            &mut spec,
            "enum_contains_struct_and_enum",
            &ctx,
            "IRTy.enum_ 9",
            &nested,
            true,
        );
        let bad_leaf = aggregate(&["IRScalar.int_ 251", "IRScalar.int_ 256"]);
        let bad_product = aggregate(&[&bad_leaf, "IRScalar.bool_ Bool.false"]);
        admits(
            &mut spec,
            "enum_deep_wrong_payload",
            &ctx,
            "IRTy.enum_ 9",
            &aggregate(&["IRScalar.int_ 19", &bad_product, &value]),
            false,
        );
        admits(
            &mut spec,
            "enum_deep_wrong_schema",
            &ctx,
            "IRTy.enum_ 7",
            &nested,
            false,
        );
        // A cyclic schema is finite input, not a recursive type traversal; a
        // finite nonmatching value is refused without inventing a depth bound.
        let cycle = schema(12, "IRTy.uint_ 8", &[&variant("3", &["IRTy.enum_ 12"])]);
        admits(
            &mut spec,
            "enum_schema_cycle_finite_value",
            &context(&[&cycle], &[], &[]),
            "IRTy.enum_ 12",
            &aggregate(&["IRScalar.int_ 3", "IRScalar.unit_"]),
            false,
        );
    });
}

#[test]
fn byte_enum_old_context_and_non_enum_semantics_remain_conservative() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let layout = format!(
            "IRByteLayoutV1.mk (IRTy.struct_ 7) 1 1 {} {}",
            list("IRTy", &["IRTy.bool_"]),
            list("Nat", &["0"])
        );
        let old = format!("IRByteContextV1.mk {MODULE} {} (@IRList.nil IRByteSignatureV1) (@IRList.nil IRByteFunctionV1) (@IRList.nil IRByteSiteV1)", list("IRByteLayoutV1", &[&layout]));
        let empty = context(&[], &[&layout], &[]);
        let invalid = schema(7, "IRTy.uint_ 8", &[]);
        let bad_catalog = context(&[&invalid, &invalid], &[&layout], &[]);
        for (i, ctx) in [format!("({old})"), empty, bad_catalog].iter().enumerate() {
            admits(
                &mut spec,
                &format!("enum_old_struct_{i}"),
                ctx,
                "IRTy.struct_ 7",
                &aggregate(&["IRScalar.bool_ Bool.true"]),
                true,
            );
            admits(
                &mut spec,
                &format!("enum_old_integer_{i}"),
                ctx,
                "IRTy.usize_ 64",
                "IRScalar.int_ 17",
                true,
            );
            admits(
                &mut spec,
                &format!("enum_old_refusal_{i}"),
                ctx,
                "IRTy.enum_ 7",
                &aggregate(&["IRScalar.int_ 0"]),
                false,
            );
        }
        add(&mut spec, &format!("def enum_old_arbitrary (v : IRScalar) : @Eq Bool (ir_byte_value_matches_v1 ({old}) (IRTy.enum_ 7) v) Bool.false :=
ir_byte_enum_empty_context_refused_v1 {MODULE} {} (@IRList.nil IRByteSignatureV1) (@IRList.nil IRByteFunctionV1) (@IRList.nil IRByteSiteV1) 7 v", list("IRByteLayoutV1", &[&layout])));
    });
}

#[test]
fn byte_enum_public_laws_have_empty_closures_and_wrong_conclusions_are_rejected() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for root in ROOTS {
            checked(&spec, root);
        }
        let v = variant("19", &["IRTy.bool_"]);
        let s = schema(7, "IRTy.uint_ 8", &[&v]);
        let ctx = context(&[&s], &[], &[]);
        let payload = spine(&["IRScalar.bool_ Bool.true"]);
        let value = aggregate(&["IRScalar.int_ 19", "IRScalar.bool_ Bool.true"]);
        let inputs = format!(
            "{ctx} 7 {s} {v} 19 {payload} {TRUE}
  (@Eq.refl (IROption IRByteEnumV1) (@IROption.some IRByteEnumV1 {s}))
  (@Eq.refl (IROption IRByteEnumVariantV1) (@IROption.some IRByteEnumVariantV1 {v}))"
        );
        let proof = format!("ir_byte_enum_ssa_input_v1 {inputs} {TRUE} {TRUE}");
        add(&mut spec, &format!("def enum_derived_admission : @Eq Bool (ir_byte_value_matches_v1 {ctx} (IRTy.enum_ 7) {value}) Bool.true := {proof}"));
        for (i, bad) in [
            aggregate(&["IRScalar.int_ 0", "IRScalar.bool_ Bool.true"]),
            aggregate(&["IRScalar.int_ 19", "IRScalar.int_ 1"]),
            aggregate(&["IRScalar.int_ 19"]),
        ]
        .iter()
        .enumerate()
        {
            let name = format!("enum_wrong_endpoint_{i}");
            reject(&mut spec, &name, &format!("def {name} : @Eq Bool (ir_byte_value_matches_v1 {ctx} (IRTy.enum_ 7) {bad}) Bool.true := {proof}"));
        }
        // The exact selected type list is nominal, even when scalar carriers
        // happen to be compatible at two different types.
        let v = variant("3", &["IRTy.fatstr_"]);
        let s = schema(8, "IRTy.uint_ 8", &[&v]);
        let ctx = context(&[&s], &[], &[]);
        let payload = spine(&["IRScalar.fat_ 16 3"]);
        let selected_proof = format!(
            "ir_byte_enum_selected_fields_v1 {ctx} 8 {s} {v} 3 {payload} {TRUE}
  (@Eq.refl (IROption IRByteEnumV1) (@IROption.some IRByteEnumV1 {s}))
  (@Eq.refl (IROption IRByteEnumVariantV1) (@IROption.some IRByteEnumVariantV1 {v}))"
        );
        for (name, field, positive) in [
            ("enum_selected_nominal", "IRTy.fatstr_", true),
            ("enum_wrong_nominal", "IRTy.containerlen_", false),
        ] {
            let source = format!(
                "def {name} : @Eq (IROption (IRList IRTy))
  (ir_byte_enum_spine_types_v1 {ctx} 8 (IRScalar.vcons (IRScalar.int_ 3) {payload}))
  (@IROption.some (IRList IRTy) {}) := {selected_proof}",
                list("IRTy", &["IRTy.uint_ 8", field])
            );
            if positive {
                add(&mut spec, &source);
            } else {
                reject(&mut spec, name, &source);
            }
        }
    });
}

#[test]
fn byte_enum_valid_ssa_schemas_do_not_admit_raw_aggregate_memory_operations() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let s = schema(7, "IRTy.uint_ 8", &[&variant("3", &[])]);
        let layouts = [
            "IRByteLayoutV1.mk (IRTy.enum_ 7) 8 8 (@IRList.nil IRTy) (@IRList.nil Nat)",
            "IRByteLayoutV1.mk (IRTy.struct_ 7) 8 8 (@IRList.nil IRTy) (@IRList.nil Nat)",
        ];
        let ctx = context(&[&s], &layouts, &[]);
        // Initialized, aligned, accessible memory does not turn a schema into a decoder.
        let mem = "IRByteMemoryV1.mk (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 8 0 Bool.true) (@IRList.nil IRByteAllocationV1)) (fun (_ : Nat) => @IROption.some Nat 0) 32";
        let fault = format!(
            "IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded) ({mem})"
        );
        for (i, ty) in ["IRTy.enum_ 7", "IRTy.struct_ 7"].iter().enumerate() {
            equality(
                &mut spec,
                &format!("enum_raw_decode_{i}"),
                "IROption IRScalar",
                &format!("ir_byte_decode_word_v1 {ctx} ({ty}) 3"),
                "@IROption.none IRScalar",
            );
            for (j, volatile) in ["Bool.false", "Bool.true"].iter().enumerate() {
                equality(
                    &mut spec,
                    &format!("enum_raw_load_{i}_{j}"),
                    "IRByteMemoryResultV1",
                    &format!(
                        "ir_byte_load_v1 {ctx} ({ty}) (IRScalar.ptr_ 16) 8 {volatile} ({mem})"
                    ),
                    &fault,
                );
                equality(
                    &mut spec,
                    &format!("enum_raw_store_{i}_{j}"),
                    "IRByteMemoryResultV1",
                    &format!(
                        "ir_byte_store_v1 {ctx} ({ty}) (IRScalar.ptr_ 16) {} 8 {volatile} ({mem})",
                        aggregate(&["IRScalar.int_ 3"])
                    ),
                    &fault,
                );
            }
        }
    });
}

#[test]
fn byte_enum_import_is_one_ssa_result_and_preserves_returned_world_on_fault() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let s = schema(7, "IRTy.uint_ 8", &[&variant("19", &["IRTy.bool_"])]);
        let ctx = context(&[&s], &[], &[]);
        let current = "(IRFrame.mk 9 7 2 (@IRList.nil IRBinding) (@IRList.nil Nat))";
        let frames = list("IRFrame", &[current]);
        let machine = format!("(IRMachine.mk {frames} (@IRList.nil IRMemSlot) 1)");
        let owners = list("Nat", &["1"]);
        let old_memory = "(IRByteMemoryV1.mk (@IRList.nil IRByteAllocationV1) (fun (_ : Nat) => @IROption.none Nat) 16)";
        let new_memory = "(IRByteMemoryV1.mk (@IRList.nil IRByteAllocationV1) (fun (_ : Nat) => @IROption.some Nat 7) 32)";
        let old_world = format!("(@IRByteWorldV1.mk Nat {old_memory} 4 {owners} 2)");
        let new_world = format!("(@IRByteWorldV1.mk Nat {new_memory} 5 {owners} 2)");
        let destinations = list("Nat", &["99"]);
        let types = list("IRTy", &["IRTy.enum_ 7"]);
        let value = aggregate(&["IRScalar.int_ 19", "IRScalar.bool_ Bool.true"]);
        let values = list("IRScalar", &[&value]);
        let next = format!(
            "IRMachine.mk {} (@IRList.nil IRMemSlot) 1",
            list(
                "IRFrame",
                &[&format!(
                    "ir_frame_advance (ir_frame_set_many {current} {destinations} {values})"
                )]
            )
        );
        let actual = |vs: &str| {
            format!("ir_byte_import_result_v1 Nat {ctx} {machine} {old_world} {destinations} {types} (@IRByteImportResultV1.mk Nat (IROutcome.ret {vs}) {new_memory} 5)")
        };
        equality(
            &mut spec,
            "enum_import_one_result",
            "IRByteConfigV1 Nat",
            &actual(&values),
            &format!("@IRByteConfigV1.running Nat ({next}) {new_world}"),
        );
        for (i, bad) in [
            list(
                "IRScalar",
                &["IRScalar.int_ 19", "IRScalar.bool_ Bool.true"],
            ),
            list(
                "IRScalar",
                &[&aggregate(&["IRScalar.int_ 0", "IRScalar.bool_ Bool.true"])],
            ),
            list("IRScalar", &[]),
        ]
        .iter()
        .enumerate()
        {
            equality(&mut spec, &format!("enum_import_fault_{i}"), "IRByteConfigV1 Nat", &actual(bad), &format!("@IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.bad_field) {new_world}"));
        }
        // C/Fast admit this helper-level import; unsupported calling convention
        // 2 still fails before the provider runs. No whole-module claim here.
        let provider = format!("fun (_ : Nat) (_ : IRList IRScalar) (_ : IRByteMemoryV1) (_ : Nat) => @IRByteImportResultV1.mk Nat (IROutcome.ret {values}) {new_memory} 5");
        for cc in 0..=2 {
            let binding = format!("IRByteFunctionV1.mk 55 4 4096 {cc} Bool.true");
            let site = format!("IRByteSiteV1.mk 9 7 2 0 {cc} {types}");
            let signature = format!("IRByteSignatureV1.mk 4 (@IRList.nil IRTy) {types} Bool.false");
            equality(&mut spec, &format!("enum_import_cc_{cc}"), "IRByteConfigV1 Nat", &format!("ir_byte_call_known_v1 Nat {ctx} ({provider}) {machine} {old_world} {destinations} ({site}) ({binding}) ({signature}) (@IRList.nil IRScalar)"),
                &if cc < 2 { format!("@IRByteConfigV1.running Nat ({next}) {new_world}") } else { format!("@IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.not_fnptr) {old_world}") });
        }
    });
}
