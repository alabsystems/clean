// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked ByteV1 value transport, not allocation, source, ABI or vtable authority.
//! Fat values share two words; their distinct kinds live in the declared IRTy.

use crate::spec::Specification;
use clean_kernel::Name;

const KINDS: [(&str, &str); 5] = [
    ("IRTy.fatstr_", "IRTy.uint_ 64"),
    ("IRTy.fatslice_ (IRTy.uint_ 8)", "IRTy.uint_ 64"),
    ("IRTy.fatdyn_ 7", "IRTy.ptr_"),
    ("IRTy.containerlen_", "IRTy.uint_ 64"),
    ("IRTy.containervtable_", "IRTy.ptr_"),
];
const BAD: &str = "IRStepResult.fault (IROutcome.type_error IRFault.bad_field)";
const MAX: &str = "18446744073709551615";
const LIMIT: &str = "18446744073709551616";

fn specification() -> Specification {
    crate::eval_ir::build_byte_prelude_spec_v1_with_stack().expect("public ByteV1 vocabulary")
}

fn add(spec: &mut Specification, source: &str) {
    spec.add_recursive_def(source, "Nominal fat-pointer ByteV1 regression")
        .unwrap_or_else(|error| panic!("{source}: {error}"));
    let name = source.split_whitespace().nth(1).unwrap();
    spec.verify_definition(name).expect("kernel-checked value");
    let name = Name::from_string(name);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn equality(spec: &mut Specification, name: &str, ty: &str, actual: &str, expected: &str) {
    add(
        spec,
        &format!(
            "def {name} (ctx : IRByteContextV1) :
  Eq ({ty}) ({actual}) ({expected}) := Eq.refl ({ty}) ({expected})"
        ),
    );
}

fn refuse_claim(spec: &mut Specification, name: &str, source: &str) {
    let error = spec
        .add_recursive_def(source, "Deliberately false fat-pointer claim")
        .expect_err("wrong endpoint must be rejected");
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

fn pointer(word: &str) -> String {
    if word == "0" {
        "IRScalar.nullptr_".into()
    } else {
        format!("IRScalar.ptr_ {word}")
    }
}

fn metadata(ty: &str, word: &str) -> String {
    if ty == "IRTy.ptr_" {
        pointer(word)
    } else {
        format!("IRScalar.int_ {word}")
    }
}

#[test]
fn byte_fat_nominal_kinds_metadata_and_word_bounds_are_checked() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let types = KINDS
            .iter()
            .map(|(ty, _)| *ty)
            .chain([
                "IRTy.fatslice_ (IRTy.uint_ 16)",
                "IRTy.fatdyn_ 8",
                "IRTy.fatptr_ (IRTy.uint_ 8)",
                "IRTy.uint_ 128",
            ])
            .collect::<Vec<_>>();
        for (i, a) in types.iter().enumerate() {
            for (j, b) in types.iter().enumerate() {
                equality(
                    &mut spec,
                    &format!("byte_fat_kind_{i}_{j}"),
                    "Bool",
                    &format!("ir_byte_ty_eq_v1 ({a}) ({b})"),
                    if i == j { "Bool.true" } else { "Bool.false" },
                );
            }
        }
        for (i, (ty, mt)) in KINDS.iter().enumerate() {
            equality(
                &mut spec,
                &format!("byte_fat_metadata_kind_{i}"),
                "IROption IRTy",
                &format!("ir_byte_fat_metadata_ty_v1 ({ty})"),
                &format!("IROption.some IRTy ({mt})"),
            );
            for (j, (data, meta, expected)) in [
                ("0", "0", "Bool.true"),
                (MAX, MAX, "Bool.true"),
                (LIMIT, "0", "Bool.false"),
                ("0", LIMIT, "Bool.false"),
            ]
            .into_iter()
            .enumerate()
            {
                equality(
                    &mut spec,
                    &format!("byte_fat_words_{i}_{j}"),
                    "Bool",
                    &format!("ir_byte_fat_value_matches_v1 ({ty}) {data} {meta}"),
                    expected,
                );
                equality(
                    &mut spec,
                    &format!("byte_fat_typed_words_{i}_{j}"),
                    "Bool",
                    &format!("ir_byte_value_matches_v1 ctx ({ty}) (IRScalar.fat_ {data} {meta})"),
                    expected,
                );
            }
        }
        equality(
            &mut spec,
            "byte_fat_legacy_has_no_kind",
            "IROption IRTy",
            "ir_byte_fat_metadata_ty_v1 (IRTy.fatptr_ (IRTy.uint_ 8))",
            "IROption.none IRTy",
        );
    });
}

#[test]
fn byte_fat_five_kinds_project_and_reconstruct_zero_ordinary_and_max_words() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for (i, (ty, mt)) in KINDS.iter().enumerate() {
            for (j, (data, meta)) in [("0", "0"), ("16", "5"), (MAX, MAX)]
                .into_iter()
                .enumerate()
            {
                let fat = format!("IRScalar.fat_ {data} {meta}");
                let d = pointer(data);
                let m = metadata(mt, meta);
                for (op, actual, value) in [
                    (
                        "data",
                        format!("ir_byte_ptrdata_eval_v1 ctx ({ty}) ({fat})"),
                        d.clone(),
                    ),
                    (
                        "metadata",
                        format!("ir_byte_ptrmetadata_eval_v1 ctx ({ty}) ({mt}) ({fat})"),
                        m.clone(),
                    ),
                    (
                        "parts",
                        format!("ir_byte_ptrfromparts_eval_v1 ctx ({ty}) ({mt}) ({d}) ({m})"),
                        fat,
                    ),
                ] {
                    equality(
                        &mut spec,
                        &format!("byte_fat_{op}_{i}_{j}"),
                        "IRStepResult",
                        &actual,
                        &format!("IRStepResult.value ({value})"),
                    );
                }
            }
        }
        // ContainerLen data points at the header, not at header+16 or the str tail.
        refuse_claim(
            &mut spec,
            "byte_fat_container_is_not_tail",
            "def byte_fat_container_is_not_tail (ctx : IRByteContextV1) :
  Eq IRStepResult (ir_byte_ptrdata_eval_v1 ctx IRTy.containerlen_ (IRScalar.fat_ 16 5))
    (IRStepResult.value (IRScalar.ptr_ 32)) :=
  Eq.refl IRStepResult (IRStepResult.value (IRScalar.ptr_ 32))",
        );
        refuse_claim(
            &mut spec,
            "byte_fat_zero_is_not_ptr_zero",
            "def byte_fat_zero_is_not_ptr_zero (ctx : IRByteContextV1) :
  Eq IRStepResult (ir_byte_ptrdata_eval_v1 ctx IRTy.containerlen_ (IRScalar.fat_ 0 5))
    (IRStepResult.value (IRScalar.ptr_ 0)) :=
  Eq.refl IRStepResult (IRStepResult.value (IRScalar.ptr_ 0))",
        );
    });
}

#[test]
fn byte_fat_rejects_wrong_metadata_types_and_noncanonical_operands() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for (i, (ty, mt)) in KINDS.iter().enumerate() {
            for (j, value) in [
                "IRScalar.ptr_ 16",
                "IRScalar.int_ 16",
                "IRScalar.nullptr_",
                "IRScalar.undef_",
                "IRScalar.fnptr_ 0",
                "IRScalar.fat_ 18446744073709551616 0",
                "IRScalar.fat_ 0 18446744073709551616",
            ]
            .into_iter()
            .enumerate()
            {
                equality(
                    &mut spec,
                    &format!("byte_fat_bad_data_{i}_{j}"),
                    "IRStepResult",
                    &format!("ir_byte_ptrdata_eval_v1 ctx ({ty}) ({value})"),
                    BAD,
                );
                equality(
                    &mut spec,
                    &format!("byte_fat_bad_meta_{i}_{j}"),
                    "IRStepResult",
                    &format!("ir_byte_ptrmetadata_eval_v1 ctx ({ty}) ({mt}) ({value})"),
                    BAD,
                );
            }
            for (j, wrong) in [
                if *mt == "IRTy.ptr_" {
                    "IRTy.uint_ 64"
                } else {
                    "IRTy.ptr_"
                },
                "IRTy.usize_ 64",
                "IRTy.unit_",
                "IRTy.func_ 0",
            ]
            .into_iter()
            .enumerate()
            {
                equality(
                    &mut spec,
                    &format!("byte_fat_meta_type_{i}_{j}"),
                    "IRStepResult",
                    &format!(
                        "ir_byte_ptrmetadata_eval_v1 ctx ({ty}) ({wrong}) (IRScalar.fat_ 16 5)"
                    ),
                    BAD,
                );
                equality(
                    &mut spec,
                    &format!("byte_fat_parts_type_{i}_{j}"),
                    "IRStepResult",
                    &format!(
                        "ir_byte_ptrfromparts_eval_v1 ctx ({ty}) ({wrong}) (IRScalar.ptr_ 16) ({})",
                        metadata(mt, "5")
                    ),
                    BAD,
                );
            }
            for (j, bad_data) in [
                "IRScalar.ptr_ 0",
                "IRScalar.ptr_ 18446744073709551616",
                "IRScalar.int_ 16",
                "IRScalar.fnptr_ 0",
            ]
            .into_iter()
            .enumerate()
            {
                equality(
                    &mut spec,
                    &format!("byte_fat_parts_data_{i}_{j}"),
                    "IRStepResult",
                    &format!(
                        "ir_byte_ptrfromparts_eval_v1 ctx ({ty}) ({mt}) ({bad_data}) ({})",
                        metadata(mt, "5")
                    ),
                    BAD,
                );
            }
            let wrong_sort = if *mt == "IRTy.ptr_" {
                "IRScalar.int_ 5"
            } else {
                "IRScalar.ptr_ 5"
            };
            for (j, bad_meta) in [
                wrong_sort,
                "IRScalar.fnptr_ 0",
                "IRScalar.ptr_ 0",
                "IRScalar.int_ 18446744073709551616",
                "IRScalar.ptr_ 18446744073709551616",
            ]
            .into_iter()
            .enumerate()
            {
                equality(
                    &mut spec,
                    &format!("byte_fat_parts_meta_{i}_{j}"),
                    "IRStepResult",
                    &format!(
                        "ir_byte_ptrfromparts_eval_v1 ctx ({ty}) ({mt}) (IRScalar.ptr_ 16) ({bad_meta})"
                    ),
                    BAD,
                );
            }
        }
    });
}

#[test]
fn byte_fat_thin_controls_and_legacy_family_refusals_are_explicit() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for (i, ty) in [
            "IRTy.ptr_",
            "IRTy.ref_ (IRTy.uint_ 8)",
            "IRTy.refmut_ (IRTy.uint_ 8)",
            "IRTy.rawconst_ (IRTy.uint_ 8)",
            "IRTy.rawmut_ (IRTy.uint_ 8)",
            "IRTy.rc_ (IRTy.uint_ 8)",
        ]
        .into_iter()
        .enumerate()
        {
            for (j, value) in ["IRScalar.nullptr_", "IRScalar.ptr_ 16"]
                .into_iter()
                .enumerate()
            {
                equality(
                    &mut spec,
                    &format!("byte_fat_thin_data_{i}_{j}"),
                    "IRStepResult",
                    &format!("ir_byte_ptrdata_eval_v1 ctx ({ty}) ({value})"),
                    &format!("IRStepResult.value ({value})"),
                );
                equality(
                    &mut spec,
                    &format!("byte_fat_thin_meta_{i}_{j}"),
                    "IRStepResult",
                    &format!("ir_byte_ptrmetadata_eval_v1 ctx ({ty}) IRTy.unit_ ({value})"),
                    "IRStepResult.value IRScalar.unit_",
                );
                equality(
                    &mut spec,
                    &format!("byte_fat_thin_parts_{i}_{j}"),
                    "IRStepResult",
                    &format!(
                        "ir_byte_ptrfromparts_eval_v1 ctx ({ty}) IRTy.unit_ ({value}) IRScalar.unit_"
                    ),
                    &format!("IRStepResult.value ({value})"),
                );
            }
        }
        for (i, ty) in [
            "IRTy.fatptr_ (IRTy.uint_ 8)",
            "IRTy.uint_ 64",
            "IRTy.func_ 0",
        ]
        .into_iter()
        .enumerate()
        {
            for (j, expression) in [
                format!("ir_byte_ptrdata_eval_v1 ctx ({ty}) value"),
                format!("ir_byte_ptrmetadata_eval_v1 ctx ({ty}) (IRTy.uint_ 64) value"),
                format!("ir_byte_ptrfromparts_eval_v1 ctx ({ty}) (IRTy.uint_ 64) value value"),
            ]
            .into_iter()
            .enumerate()
            {
                add(
                    &mut spec,
                    &format!(
                        "def byte_fat_unknown_{i}_{j} (ctx : IRByteContextV1) (value : IRScalar) :
  Eq IRStepResult ({expression}) ir_width_fault := Eq.refl IRStepResult ir_width_fault"
                    ),
                );
            }
        }
        for (i, expression) in [
            "ir_byte_ptrdata_eval_v1 ctx IRTy.ptr_ (IRScalar.ptr_ 0)",
            "ir_byte_ptrmetadata_eval_v1 ctx IRTy.ptr_ (IRTy.uint_ 64) (IRScalar.ptr_ 16)",
            "ir_byte_ptrfromparts_eval_v1 ctx IRTy.ptr_ IRTy.unit_ (IRScalar.ptr_ 16) (IRScalar.int_ 0)",
        ].into_iter().enumerate() {
            equality(&mut spec, &format!("byte_fat_thin_bad_{i}"), "IRStepResult", expression, BAD);
        }
    });
}

#[path = "eval_ir_byte_fat_tests/fetched.rs"]
mod fetched_tests;

#[path = "eval_ir_byte_fat_tests/laws.rs"]
mod law_tests;

#[path = "eval_ir_byte_fat_tests/nested.rs"]
mod nested_tests;

#[test]
fn byte_fat_memory_and_casts_remain_refused_without_granting_access() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for (i, ty) in KINDS
            .iter()
            .map(|(ty, _)| *ty)
            .chain(["IRTy.fatptr_ (IRTy.uint_ 8)"])
            .enumerate()
        {
            for (j, expression) in [
                format!("ir_byte_load_v1 ctx ({ty}) (IRScalar.ptr_ 16) 8 Bool.false mem"),
                format!("ir_byte_store_v1 ctx ({ty}) (IRScalar.ptr_ 16) (IRScalar.fat_ 16 5) 8 Bool.false mem"),
            ].into_iter().enumerate() {
                add(&mut spec, &format!("def byte_fat_memory_refused_{i}_{j}
  (ctx : IRByteContextV1) (mem : IRByteMemoryV1) : Eq IRByteMemoryResultV1 ({expression})
  (IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded) mem) :=
  Eq.refl IRByteMemoryResultV1 (IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded) mem)"));
            }
            for (j, op) in ["bitcast", "ptrtoptr", "transmute"].into_iter().enumerate() {
                equality(
                    &mut spec,
                    &format!("byte_fat_cast_refused_{i}_{j}"),
                    "IRStepResult",
                    &format!(
                        "ir_byte_cast_eval_v1 ctx IRCastOp.{op} ({ty}) ({ty}) (IRScalar.fat_ 16 5)"
                    ),
                    "ir_width_fault",
                );
            }
        }
        equality(
            &mut spec,
            "byte_fat_empty_memory_has_no_access",
            "Bool",
            "ir_byte_accessible_v1 (IRList.nil IRByteAllocationV1) 16 8 8",
            "Bool.false",
        );
    });
}
