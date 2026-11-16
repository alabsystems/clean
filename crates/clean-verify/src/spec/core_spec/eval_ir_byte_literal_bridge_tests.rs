// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Joint semantic-model tests, not a Rust Name/Arc/Expr representation bridge.
//! Every successful observer claim below starts from actual input bytes/access;
//! no hypothesis supplies the desired decoded result or literal return equation.

use std::collections::BTreeSet;
use std::sync::OnceLock;

use clean_kernel::{ConstantInfo, Name};

use crate::spec::definition::SpecDefinition;
use crate::spec::Specification;

const DRIVER_ROOTS: [&str; 5] = [
    "ir_drive_v1",
    "ir_drive_zero_v1",
    "ir_drive_succ_v1",
    "ir_drive_halted_v1",
    "ir_drive_add_v1",
];
const LITERAL_ROOTS: [&str; 4] = [
    "literal_builtin_nat_name",
    "literal_builtin_string_name",
    "literal_nat_type",
    "literal_string_type",
];
const NEW_ROOTS: [&str; 15] = [
    "ir_byte_run_v1",
    "ir_byte_step_v1",
    "ir_byte_builtin_name_atom_v1",
    "ir_byte_builtin_literal_type_v1",
    "ir_byte_literal_type_result_v1",
    "ir_byte_literal_type_v1",
    "ir_byte_literal_nat_input_v1",
    "ir_byte_literal_string_input_v1",
    "ir_byte_literal_infers_v1",
    "ir_byte_literal_typing_v1",
    "ir_byte_literal_infers_sound_v1",
    "ir_byte_literal_nat_infers_input_v1",
    "ir_byte_literal_string_infers_input_v1",
    "ir_byte_literal_nat_typing_input_v1",
    "ir_byte_literal_string_typing_input_v1",
];
const WORDS: [(&str, &[u16]); 2] = [
    ("nat", &[78, 97, 116]),
    ("string", &[83, 116, 114, 105, 110, 103]),
];
const RESULT: &str = "IROption KExpr";

fn audit(spec: &Specification, root: &str) {
    let definition = spec.get_definition(root).expect("registered root");
    assert!(!definition.is_axiom && definition.elaborated_value.is_some());
    spec.verify_definition(root)
        .unwrap_or_else(|error| panic!("{root}: {error}"));
    let name = Name::from_string(root);
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty(), "{root}");
    assert!(
        spec.env().trust_marker_deps(&name).unwrap().is_empty(),
        "{root}"
    );
}

fn same_definition(before: &SpecDefinition, after: &SpecDefinition) {
    let SpecDefinition {
        name,
        type_src,
        value_src,
        is_axiom,
        category,
        proof_status,
        description,
        elaborated_type,
        elaborated_value,
        dependencies,
        axiom_deps,
    } = before;
    assert_eq!(
        (
            name,
            type_src,
            value_src,
            is_axiom,
            category,
            proof_status,
            description,
            elaborated_type,
            elaborated_value,
            dependencies,
            axiom_deps,
        ),
        (
            &after.name,
            &after.type_src,
            &after.value_src,
            &after.is_axiom,
            &after.category,
            &after.proof_status,
            &after.description,
            &after.elaborated_type,
            &after.elaborated_value,
            &after.dependencies,
            &after.axiom_deps,
        ),
        "existing Full definition changed: {name}"
    );
}

fn same_constant(before: &ConstantInfo, after: &ConstantInfo) {
    let ConstantInfo {
        name,
        level_params,
        type_,
        value,
        is_reducible,
        reducibility,
        kind,
    } = before;
    assert_eq!(
        (
            name,
            level_params,
            type_,
            value,
            is_reducible,
            reducibility,
            kind
        ),
        (
            &after.name,
            &after.level_params,
            &after.type_,
            &after.value,
            &after.is_reducible,
            &after.reducibility,
            &after.kind,
        ),
        "existing Full kernel constant changed: {name}"
    );
}

fn joint() -> &'static Specification {
    static JOINT: OnceLock<Result<Specification, String>> = OnceLock::new();
    JOINT
        .get_or_init(|| {
            let before = crate::test_utils::shared_spec();
            for name in [
                "Nat.le_add_left",
                "Nat.add_sub_cancel",
                "Nat.ulpRound.le_of_add_le_add_right",
                "Nat.div",
                "Nat.mod",
                "Nat.div_add_mod",
                "Nat.mod_lt",
                "Nat.add_left_cancel",
                "Nat.right_distrib",
            ] {
                let key = Name::from_string(name);
                let constant = before.env().get_const(&key);
                eprintln!(
                    "Full-before-Byte {name}: spec={}, constant={}, value={}, axioms={:?}, markers={:?}",
                    before.get_definition(name).is_some(),
                    constant.is_some(),
                    constant.is_some_and(|c| c.value.is_some()),
                    before.env().axiom_deps(&key),
                    before.env().trust_marker_deps(&key),
                );
                if constant.is_some() {
                    assert!(before.env().axiom_deps(&key).is_some());
                    assert!(before.env().trust_marker_deps(&key).is_some());
                }
            }
            for root in DRIVER_ROOTS.into_iter().chain(LITERAL_ROOTS) {
                audit(before, root);
            }
            // Full is built once; its immutable expression DAG is shared by this clone.
            // This exercises the production append method used by the new constructor.
            let mut after = before.clone();
            after
                .add_eval_ir_byte_literal_model_v1()
                .map_err(|error| format!("completed Full -> Byte/literal installation: {error}"))?;
            for (name, definition) in before.definitions() {
                same_definition(
                    definition,
                    after.get_definition(name).expect("Full definition retained"),
                );
            }
            for constant in before.env().constants() {
                same_constant(
                    constant,
                    after
                        .env()
                        .get_const(&constant.name)
                        .expect("Full kernel constant retained"),
                );
            }
            let added = after
                .definitions()
                .iter()
                .filter(|(name, _)| !before.definitions().contains_key(*name))
                .map(|(name, _)| name.clone())
                .collect::<BTreeSet<_>>();
            assert!(added.len() > NEW_ROOTS.len(), "nonvacuous complete Byte installation");
            for root in NEW_ROOTS {
                assert!(added.contains(root), "missing new root: {root}");
                audit(&after, root);
            }
            let mut checked = 0;
            for root in &added {
                if after.get_definition(root).unwrap().elaborated_value.is_some() {
                    audit(&after, root);
                    checked += 1;
                }
            }
            assert!(checked >= NEW_ROOTS.len());
            eprintln!(
                "Full -> Byte/literal census: before={} after={} added={} checked-valued={checked}",
                before.definitions().len(),
                after.definitions().len(),
                added.len(),
            );
            Ok(after)
        })
        .as_ref()
        .unwrap_or_else(|error| panic!("{error}"))
}

fn add(spec: &mut Specification, source: &str) {
    spec.add_recursive_def(source, "Joint Byte/literal input-derived model witness")
        .unwrap_or_else(|error| panic!("{source}: {error}"));
    audit(spec, source.split_whitespace().nth(1).unwrap());
}

fn result(kind: &str) -> String {
    format!("@IROption.some KExpr literal_{kind}_type")
}

fn equality(spec: &mut Specification, name: &str, actual: &str, expected: &str) {
    add(
        spec,
        &format!(
            "def {name} : Eq ({RESULT}) ({actual}) ({expected}) :=
              @Eq.refl ({RESULT}) ({expected})"
        ),
    );
}

fn fixture(spec: &mut Specification, name: &str, word: &[u16]) {
    let bytes = word.iter().enumerate().rev().fold(
        "@IROption.none Nat".to_string(),
        |tail, (index, byte)| {
            format!(
                "@Bool.rec (fun (_ : Bool) => IROption Nat) ({tail})
                  (@IROption.some Nat {byte}) (ir_nat_eqb address {})",
                65 + index
            )
        },
    );
    add(
        spec,
        &format!(
            "def {name} : IRByteMemoryV1 := IRByteMemoryV1.mk
              (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 64 16 7 Bool.true)
                (@IRList.nil IRByteAllocationV1)) (fun (address : Nat) => {bytes}) 1024"
        ),
    );
}

#[test]
fn byte_literal_joint_preserves_full_and_checks_every_new_valued_root() {
    crate::test_utils::run_with_stack(|| {
        let spec = joint();
        for root in DRIVER_ROOTS
            .into_iter()
            .chain(LITERAL_ROOTS)
            .chain(NEW_ROOTS)
        {
            audit(spec, root);
        }
    });
}

#[test]
fn byte_literal_joint_maps_atoms_to_existing_builtin_aliases_without_numeric_tags() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = joint().clone();
        for (kind, _) in WORDS {
            add(
                &mut spec,
                &format!(
                    "def joint_atom_{kind} :
                      Eq KExpr (ir_byte_builtin_literal_type_v1 IRBuiltinNameAtomV1.{kind}_)
                        literal_{kind}_type := @Eq.refl KExpr literal_{kind}_type"
                ),
            );
            equality(
                &mut spec,
                &format!("joint_option_{kind}"),
                &format!("ir_byte_literal_type_result_v1 (@IROption.some IRBuiltinNameAtomV1 IRBuiltinNameAtomV1.{kind}_ )"),
                &result(kind),
            );
        }
        equality(
            &mut spec,
            "joint_none_stays_none",
            "ir_byte_literal_type_result_v1 (@IROption.none IRBuiltinNameAtomV1)",
            "@IROption.none KExpr",
        );
    });
}

#[test]
fn byte_literal_joint_input_laws_derive_both_model_results_from_bytes() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = joint().clone();
        for (kind, word) in WORDS {
            let length = word.len();
            let mut address = "data".to_string();
            let mut premises = String::new();
            let mut arguments = String::new();
            let mut inhabited = String::new();
            for (index, byte) in word.iter().enumerate() {
                premises.push_str(&format!(
                    " (byte{index} : Eq (IROption Nat) (bytes ({address}))
                      (@IROption.some Nat {byte}))"
                ));
                arguments.push_str(&format!(" byte{index}"));
                inhabited.push_str(&format!(
                    " (@Eq.refl (IROption Nat) (@IROption.some Nat {byte}))"
                ));
                address = format!("Nat.succ ({address})");
            }
            let expected = result(kind);
            add(
                &mut spec,
                &format!(
                    "def joint_general_{kind}
                      (allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat)
                      (next data : Nat) (bounded : Nat.lt data ir_byte_limit_v1)
                      (access : Eq Bool (ir_byte_accessible_v1 allocs data {length} 1) Bool.true)
                      {premises} : Eq ({RESULT}) (ir_byte_literal_type_v1
                        (IRByteMemoryV1.mk allocs bytes next) IRTy.fatstr_
                        (IRScalar.fat_ data {length})) ({expected}) :=
                      ir_byte_literal_{kind}_input_v1 allocs bytes next data bounded access {arguments}"
                ),
            );
            let memory = format!("joint_input_memory_{kind}");
            fixture(&mut spec, &memory, word);
            add(
                &mut spec,
                &format!(
                    "def joint_inhabited_{kind} : Eq ({RESULT})
                      (ir_byte_literal_type_v1 {memory} IRTy.fatstr_ (IRScalar.fat_ 65 {length}))
                      ({expected}) := ir_byte_literal_{kind}_input_v1
                        (ir_byte_mem_allocs_v1 {memory}) (ir_byte_mem_bytes_v1 {memory}) 1024 65
                        (Nat.le_add_right 66 {}) (@Eq.refl Bool Bool.true) {inhabited}",
                    (1_u128 << 64) - 66
                ),
            );
        }
    });
}

#[test]
fn byte_literal_joint_wrong_nominal_kinds_and_corrupt_bytes_do_not_map() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = joint().clone();
        for (kind, word) in WORDS {
            let memory = format!("joint_refusal_memory_{kind}");
            fixture(&mut spec, &memory, word);
            for (index, ty) in [
                "IRTy.containerlen_",
                "IRTy.fatslice_ (IRTy.uint_ 8)",
                "IRTy.ptr_",
            ]
            .into_iter()
            .enumerate()
            {
                equality(
                    &mut spec,
                    &format!("joint_wrong_kind_{kind}_{index}"),
                    &format!(
                        "ir_byte_literal_type_v1 {memory} ({ty}) (IRScalar.fat_ 65 {})",
                        word.len()
                    ),
                    "@IROption.none KExpr",
                );
            }
            let mut wrong = word.to_vec();
            wrong[0] += 1;
            let memory = format!("joint_corrupt_memory_{kind}");
            fixture(&mut spec, &memory, &wrong);
            equality(
                &mut spec,
                &format!("joint_bad_bytes_{kind}"),
                &format!(
                    "ir_byte_literal_type_v1 {memory} IRTy.fatstr_ (IRScalar.fat_ 65 {})",
                    word.len()
                ),
                "@IROption.none KExpr",
            );
        }
    });
}

#[test]
fn byte_literal_joint_swapped_model_types_are_semantic_proof_failures() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = joint().clone();
        for (index, (kind, word)) in WORDS.iter().enumerate() {
            let memory = format!("joint_wrong_endpoint_memory_{kind}");
            fixture(&mut spec, &memory, word);
            let name = format!("joint_wrong_endpoint_{kind}");
            let wrong = result(WORDS[1 - index].0);
            let source = format!(
                "def {name} : Eq ({RESULT}) (ir_byte_literal_type_v1 {memory}
                  IRTy.fatstr_ (IRScalar.fat_ 65 {})) ({wrong}) := @Eq.refl ({RESULT}) ({wrong})",
                word.len()
            );
            let error = spec
                .add_recursive_def(&source, "Deliberately false mapped literal type")
                .expect_err("distinct model builtin names cannot exchange results");
            crate::test_utils::assert_type_mismatch_rejection(&error, &name);
            assert!(spec.get_definition(&name).is_none());
        }
    });
}

#[test]
fn byte_literal_joint_initialized_bytes_derive_inference_and_typing() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = joint().clone();
        for (kind, word) in WORDS {
            let length = word.len();
            let memory = format!("joint_typed_memory_{kind}");
            fixture(&mut spec, &memory, word);
            let mut address = "data".to_string();
            let mut premises = String::new();
            let mut arguments = String::new();
            let mut inhabited = String::new();
            for (index, byte) in word.iter().enumerate() {
                premises.push_str(&format!(
                    " (byte{index} : Eq (IROption Nat) (bytes ({address}))
                      (@IROption.some Nat {byte}))"
                ));
                arguments.push_str(&format!(" byte{index}"));
                inhabited.push_str(&format!(
                    " (@Eq.refl (IROption Nat) (@IROption.some Nat {byte}))"
                ));
                address = format!("Nat.succ ({address})");
            }
            for judgment in ["infers", "typing"] {
                add(
                    &mut spec,
                    &format!(
                        "def joint_general_{kind}_{judgment}
                          (tenv : KDeclEnv) (G : ListType KExpr) (payload : Nat)
                          (allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat)
                          (next data : Nat) (bounded : Nat.lt data ir_byte_limit_v1)
                          (access : Eq Bool (ir_byte_accessible_v1 allocs data {length} 1) Bool.true)
                          {premises} : ir_byte_literal_{judgment}_v1 tenv G (literal_{kind} payload)
                            (ir_byte_literal_type_v1 (IRByteMemoryV1.mk allocs bytes next)
                              IRTy.fatstr_ (IRScalar.fat_ data {length})) :=
                          ir_byte_literal_{kind}_{judgment}_input_v1 tenv G payload
                            allocs bytes next data bounded access {arguments}"
                    ),
                );
                // Inhabit every memory premise. Payload, environment and context
                // remain arbitrary: the two string identities are not conflated.
                add(
                    &mut spec,
                    &format!(
                        "def joint_inhabited_{kind}_{judgment}
                          (tenv : KDeclEnv) (G : ListType KExpr) (payload : Nat) :
                          ir_byte_literal_{judgment}_v1 tenv G (literal_{kind} payload)
                            (ir_byte_literal_type_v1 {memory} IRTy.fatstr_
                              (IRScalar.fat_ 65 {length})) :=
                          ir_byte_literal_{kind}_{judgment}_input_v1 tenv G payload
                            (ir_byte_mem_allocs_v1 {memory}) (ir_byte_mem_bytes_v1 {memory}) 1024 65
                            (Nat.le_add_right 66 {}) (@Eq.refl Bool Bool.true) {inhabited}",
                        (1_u128 << 64) - 66
                    ),
                );
            }
        }
    });
}

fn semantic_refusal(spec: &mut Specification, name: &str, source: &str) {
    let error = spec
        .add_recursive_def(
            source,
            "Deliberately invalid byte/literal inference witness",
        )
        .expect_err("invalid observation cannot establish modeled inference");
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

#[test]
fn byte_literal_joint_failed_observations_cannot_be_typed_as_success() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = joint().clone();
        for (judgment, relation) in [("infers", "KernelInfers"), ("typing", "TypingCtxConv")] {
            // This identity type-checks only when failure is really Empty. It
            // does not try to inhabit failure or assume it away in a positive law.
            add(
                &mut spec,
                &format!(
                    "def joint_{judgment}_none_is_empty
                      (tenv : KDeclEnv) (G : ListType KExpr) (input : KExpr)
                      (h : ir_byte_literal_{judgment}_v1 tenv G input (@IROption.none KExpr)) :
                      Empty := h"
                ),
            );
            for (kind, word) in WORDS {
                let memory = format!("joint_failed_{judgment}_{kind}");
                fixture(&mut spec, &memory, word);
                let mut corrupt = word.to_vec();
                corrupt[0] += 1;
                let bad_memory = format!("{memory}_corrupt");
                fixture(&mut spec, &bad_memory, &corrupt);
                for (reason, selected_memory, ty) in [
                    ("nominal", memory.as_str(), "IRTy.containerlen_"),
                    ("bytes", bad_memory.as_str(), "IRTy.fatstr_"),
                ] {
                    let name = format!("joint_reject_{judgment}_{kind}_{reason}");
                    semantic_refusal(
                        &mut spec,
                        &name,
                        &format!(
                            "def {name} (tenv : KDeclEnv) (G : ListType KExpr) (payload : Nat) :
                              ir_byte_literal_{judgment}_v1 tenv G (literal_{kind} payload)
                                (ir_byte_literal_type_v1 {selected_memory} {ty}
                                  (IRScalar.fat_ 65 {})) := @{relation}.lit_{kind} tenv G payload",
                            word.len()
                        ),
                    );
                }
            }
        }
    });
}

#[test]
fn byte_literal_joint_exact_inference_rejects_the_other_literal_kind() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = joint().clone();
        for (index, (kind, word)) in WORDS.iter().enumerate() {
            let other = WORDS[1 - index].0;
            let memory = format!("joint_infers_wrong_kind_memory_{kind}");
            fixture(&mut spec, &memory, word);
            let name = format!("joint_infers_wrong_kind_{kind}");
            // Exact algorithmic results, not a claim that arbitrary environments
            // cannot relate the two types using declarative conversion.
            semantic_refusal(
                &mut spec,
                &name,
                &format!(
                    "def {name} (tenv : KDeclEnv) (G : ListType KExpr) (payload : Nat) :
                      ir_byte_literal_infers_v1 tenv G (literal_{other} payload)
                        (ir_byte_literal_type_v1 {memory} IRTy.fatstr_
                          (IRScalar.fat_ 65 {})) := @KernelInfers.lit_{other} tenv G payload",
                    word.len()
                ),
            );
        }
    });
}
