// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual module fetch/step/run paths, with explicit untrusted model catalogs.

use super::{
    add, aggregate, checked, context, equality, layout, list, rejected, result, rows, schema, site,
    specification, ROOTS, TRUE,
};

const NO_PROVIDER: &str = "def field_no_provider : IRByteProvidersV1 Nat := fun (_ : Nat) (_ : IRList IRScalar) (memory : IRByteMemoryV1) (host : Nat) => @IRByteImportResultV1.mk Nat (IROutcome.stuck IRFault.no_func) memory host";

fn program(
    params: &[&str],
    returns: &[&str],
    nodes: &[String],
    sites: &[String],
    layouts: &[&str],
    enums: &[&str],
) -> (String, String, String) {
    let ids: Vec<_> = (0..params.len()).map(|id| id.to_string()).collect();
    let ids = list("Nat", &ids.iter().map(String::as_str).collect::<Vec<_>>());
    let block = format!(
        "IRBlock.mk 0 ({ids}) ({})",
        list(
            "IRNode",
            &nodes.iter().map(String::as_str).collect::<Vec<_>>()
        )
    );
    let function = format!("IRFunc.mk 41 ({ids}) 0 ({})", list("IRBlock", &[&block]));
    let module = format!(
        "IRModule.mk ({}) (@IRList.nil IRGlobal)",
        list("IRFunc", &[&function])
    );
    let ctx = format!(
        "IRByteContextV1.mke ({module}) ({}) ({}) ({}) ({}) ({})",
        list("IRByteLayoutV1", layouts),
        list(
            "IRByteSignatureV1",
            &[&format!(
                "IRByteSignatureV1.mk 41 ({}) ({}) Bool.false",
                list("IRTy", params),
                list("IRTy", returns)
            )]
        ),
        list(
            "IRByteFunctionV1",
            &["IRByteFunctionV1.mk 41 41 160 1 Bool.false"]
        ),
        list(
            "IRByteSiteV1",
            &sites.iter().map(String::as_str).collect::<Vec<_>>()
        ),
        list("IRByteEnumV1", enums)
    );
    (ctx, function, block)
}

fn node(instruction: &str, id: u64) -> String {
    format!(
        "IRNode.mk ({instruction}) ({})",
        list("Nat", &[&id.to_string()])
    )
}

fn ret(id: u64) -> String {
    format!(
        "IRNode.mk (IRInst.ret ({})) (@IRList.nil Nat)",
        list("Nat", &[&id.to_string()])
    )
}

fn old_site(pc: u64, types: &[&str]) -> String {
    format!("IRByteSiteV1.mk 41 0 {pc} 0 1 ({})", list("IRTy", types))
}

#[test]
fn byte_field_fetched_seed_updates_return_complete_nested_values_and_retire_owner() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        add(&mut spec, NO_PROVIDER);
        // A Name-shaped outer struct containing a complete tag-selected enum.
        // Only the operation chain is exercised; no captured load/call is
        // replaced with this function, and no producer identity is asserted.
        let enumeration = schema(7, &[(19, &["IRTy.fatstr_"])]);
        let structure = layout(9, &["IRTy.enum_ 7", "IRTy.uint_ 64"]);
        let seed_enum = aggregate(
            "IRConst",
            &[
                "IRConst.int_ 19",
                &aggregate("IRConst", &["IRConst.int_ 0", "IRConst.int_ 0"]),
            ],
        );
        let seed = aggregate("IRConst", &[&seed_enum, "IRConst.int_ 0"]);
        let value_enum = aggregate("IRScalar", &["IRScalar.int_ 19", "IRScalar.fat_ 16 3"]);
        let expected = aggregate("IRScalar", &[&value_enum, "IRScalar.int_ 11"]);
        let instructions = vec![
            node(&format!("IRInst.const_ (IRTy.struct_ 9) ({seed})"), 99),
            node("IRInst.insertfield (IRTy.struct_ 9) 99 0 0", 100),
            node("IRInst.insertfield (IRTy.struct_ 9) 100 1 1", 101),
            ret(101),
        ];
        let sites = vec![
            old_site(0, &["IRTy.struct_ 9"]),
            site(
                1,
                "IRTy.struct_ 9",
                &[(99, "IRTy.struct_ 9"), (0, "IRTy.enum_ 7")],
            ),
            site(
                2,
                "IRTy.struct_ 9",
                &[(100, "IRTy.struct_ 9"), (1, "IRTy.uint_ 64")],
            ),
            old_site(3, &[]),
        ];
        let (ctx, _, _) = program(
            &["IRTy.enum_ 7", "IRTy.uint_ 64"],
            &["IRTy.struct_ 9"],
            &instructions,
            &sites,
            &[&structure],
            &[&enumeration],
        );
        add(
            &mut spec,
            &format!("def field_construct_ctx : IRByteContextV1 := {ctx}"),
        );
        let initial = format!(
            "ir_byte_init_v1 Nat field_construct_ctx 41 ({}) (ir_byte_memory_empty_v1 64) 73",
            list("IRScalar", &[&value_enum, "IRScalar.int_ 11"])
        );
        let final_world = "@IRByteWorldV1.mk Nat (ir_byte_retire_v1 1 (ir_byte_memory_empty_v1 64)) 73 (@IRList.nil Nat) 2";
        let endpoint = format!(
            "@IRByteConfigV1.halted Nat (IROutcome.ret ({})) ({final_world})",
            list("IRScalar", &[&expected])
        );
        let positive = format!("def field_derived_fetched_constructor : @Eq (IRByteConfigV1 Nat)\n  (ir_byte_run_v1 Nat field_construct_ctx field_no_provider 4 ({initial}))\n  ({endpoint}) := @Eq.refl (IRByteConfigV1 Nat) ({endpoint})");
        add(&mut spec, &positive);
        let wrong = positive.replacen("field_derived_fetched_constructor", "field_wrong_return_owner", 1)
            .replacen(&format!("({endpoint}) :="), &format!("(@IRByteConfigV1.halted Nat (IROutcome.ret ({})) (@IRByteWorldV1.mk Nat (ir_byte_memory_empty_v1 64) 73 ({}) 2)) :=", list("IRScalar", &[&expected]), list("Nat", &["1"])), 1);
        assert_eq!(
            positive.split_once(":=").unwrap().1,
            wrong.split_once(":=").unwrap().1
        );
        rejected(&mut spec, "field_wrong_return_owner", &wrong);
        // Construction keeps the owner until the actual return step. The
        // independent step-rule applications below use inhabited worlds too.
        let values = list("IRScalar", &[&value_enum, "IRScalar.int_ 11"]);
        let before = format!("ir_byte_run_v1 Nat field_construct_ctx field_no_provider 1 (ir_byte_init_v1 Nat field_construct_ctx 41 ({values}) (ir_byte_memory_empty_v1 64) 73)");
        equality(
            &mut spec,
            "field_construct_pre_return_owners",
            "IRList Nat",
            &format!("ir_byte_world_owners_v1 Nat (ir_byte_final_world_v1 Nat ({before}))"),
            &list("Nat", &["1"]),
        );
        equality(&mut spec, "field_construct_return_owners", "IRList Nat", &format!("ir_byte_world_owners_v1 Nat (ir_byte_final_world_v1 Nat (ir_byte_run_v1 Nat field_construct_ctx field_no_provider 4 ({initial})))"), "@IRList.nil Nat");
    });
}

#[test]
fn byte_field_fetched_enum_seed_payload_updates_use_tag_at_zero() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        add(&mut spec, NO_PROVIDER);
        let pointer = layout(8, &["IRTy.ptr_"]);
        let text = layout(11, &["IRTy.fatstr_"]);
        // Historical NameInner uses repr(u64), with payload fields one/two;
        // these explicit model inputs retain that convention, not toy u8.
        let enumeration = schema(7, &[(0, &[]), (1, &["IRTy.struct_ 8", "IRTy.struct_ 11"])]);
        let seed = aggregate(
            "IRConst",
            &[
                "IRConst.int_ 1",
                &aggregate("IRConst", &["IRConst.int_ 0"]),
                &aggregate(
                    "IRConst",
                    &[&aggregate("IRConst", &["IRConst.int_ 0", "IRConst.int_ 0"])],
                ),
            ],
        );
        let prefix = aggregate("IRScalar", &["IRScalar.ptr_ 128"]);
        let text_value = aggregate("IRScalar", &["IRScalar.fat_ 144 3"]);
        let expected = aggregate("IRScalar", &["IRScalar.int_ 1", &prefix, &text_value]);
        let nodes = vec![
            node(&format!("IRInst.const_ (IRTy.enum_ 7) ({seed})"), 99),
            node("IRInst.insertfield (IRTy.enum_ 7) 99 1 0", 100),
            node("IRInst.insertfield (IRTy.enum_ 7) 100 2 1", 101),
            ret(101),
        ];
        let sites = vec![
            old_site(0, &["IRTy.enum_ 7"]),
            site(
                1,
                "IRTy.enum_ 7",
                &[(99, "IRTy.enum_ 7"), (0, "IRTy.struct_ 8")],
            ),
            site(
                2,
                "IRTy.enum_ 7",
                &[(100, "IRTy.enum_ 7"), (1, "IRTy.struct_ 11")],
            ),
            old_site(3, &[]),
        ];
        let (ctx, _, _) = program(
            &["IRTy.struct_ 8", "IRTy.struct_ 11"],
            &["IRTy.enum_ 7"],
            &nodes,
            &sites,
            &[&pointer, &text],
            &[&enumeration],
        );
        add(
            &mut spec,
            &format!("def field_enum_construct_ctx : IRByteContextV1 := {ctx}"),
        );
        let actual = format!("ir_byte_run_v1 Nat field_enum_construct_ctx field_no_provider 4 (ir_byte_init_v1 Nat field_enum_construct_ctx 41 ({}) (ir_byte_memory_empty_v1 64) 73)", list("IRScalar", &[&prefix, &text_value]));
        let endpoint = format!("@IRByteConfigV1.halted Nat (IROutcome.ret ({})) (@IRByteWorldV1.mk Nat (ir_byte_retire_v1 1 (ir_byte_memory_empty_v1 64)) 73 (@IRList.nil Nat) 2)", list("IRScalar", &[&expected]));
        equality(
            &mut spec,
            "field_enum_construct_complete_return",
            "IRByteConfigV1 Nat",
            &actual,
            &endpoint,
        );
    });
}

#[test]
fn byte_field_fetched_step_rules_world_and_faults_have_constructed_applications() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        add(&mut spec, NO_PROVIDER);
        let structure = layout(9, &["IRTy.fatstr_"]);
        let value = aggregate("IRScalar", &["IRScalar.fat_ 16 3"]);
        for (case, (instruction, result_ty, operands, extra, name)) in [
            (
                "IRInst.extractfield IRTy.fatstr_ 0 0",
                "IRTy.fatstr_",
                vec![(0, "IRTy.struct_ 9")],
                "",
                "extract",
            ),
            (
                "IRInst.insertfield (IRTy.struct_ 9) 0 0 1",
                "IRTy.struct_ 9",
                vec![(0, "IRTy.struct_ 9"), (1, "IRTy.fatstr_")],
                "1",
                "insert",
            ),
        ]
        .iter()
        .enumerate()
        {
            let typed = site(0, result_ty, operands);
            let nodes = vec![node(instruction, 99)];
            let (ctx, function, block) = program(
                &["IRTy.struct_ 9", "IRTy.fatstr_"],
                &[result_ty],
                &nodes,
                std::slice::from_ref(&typed),
                &[&structure],
                &[],
            );
            let locals = list(
                "IRBinding",
                &[
                    &format!("IRBinding.mk 0 ({value})"),
                    "IRBinding.mk 1 (IRScalar.fat_ 32 7)",
                ],
            );
            let current = format!("IRFrame.mk 41 0 0 ({locals}) (@IRList.nil Nat)");
            let state = format!(
                "IRMachine.mk ({}) (@IRList.nil IRMemSlot) 0",
                list("IRFrame", &[&current])
            );
            let world = format!(
                "@IRByteWorldV1.mk Nat (ir_byte_memory_empty_v1 64) 73 ({}) 2",
                list("Nat", &["1"])
            );
            let r = if *name == "extract" {
                format!("ir_byte_extract_field_v1 ({ctx}) ({typed}) ({result_ty}) 0 (ir_getd ({state}) 0) 0")
            } else {
                format!("ir_byte_insert_field_v1 ({ctx}) ({typed}) ({result_ty}) 0 (ir_getd ({state}) 0) 0 1 (ir_getd ({state}) 1)")
            };
            let expected = format!(
                "ir_byte_scalar_result_v1 Nat ({ctx}) ({state}) ({world}) ({}) ({}) ({r})",
                list("Nat", &["99"]),
                list("IRTy", &[result_ty])
            );
            add(&mut spec, &format!("def field_derived_step_{case} : @Eq (IRByteConfigV1 Nat) (ir_byte_step_v1 Nat ({ctx}) field_no_provider (@IRByteConfigV1.running Nat ({state}) ({world}))) ({expected}) := ir_byte_step_field_{name}_v1 Nat ({ctx}) field_no_provider ({current}) (@IRList.nil IRFrame) (@IRList.nil IRMemSlot) 0 ({world}) ({function}) ({block}) ({typed}) ({result_ty}) 0 0 ({}) {TRUE}\n  (@Eq.refl (IROption IRFunc) (@IROption.some IRFunc ({function})))\n  (@Eq.refl (IROption IRBlock) (@IROption.some IRBlock ({block})))\n  (@Eq.refl (IROption IRByteSiteV1) (@IROption.some IRByteSiteV1 ({typed}))) {TRUE} {extra}\n  (@Eq.refl (IROption IRNode) (@IROption.some IRNode ({})))", list("Nat", &["99"]), nodes[0]));
            add(&mut spec, &format!("def field_derived_scalar_world_{case} : @Eq (IRByteWorldV1 Nat) (ir_byte_final_world_v1 Nat ({expected})) ({world}) := ir_byte_field_scalar_world_v1 Nat ({ctx}) ({state}) ({world}) ({}) ({}) ({r})", list("Nat", &["99"]), list("IRTy", &[result_ty])));
            let bad_site = old_site(0, &[result_ty]);
            let (bad_ctx, _, _) = program(
                &["IRTy.struct_ 9", "IRTy.fatstr_"],
                &[result_ty],
                &nodes,
                &[bad_site],
                &[&structure],
                &[],
            );
            equality(&mut spec, &format!("field_fetched_old_site_{case}"), "IRByteConfigV1 Nat", &format!("ir_byte_step_v1 Nat ({bad_ctx}) field_no_provider (@IRByteConfigV1.running Nat ({state}) ({world}))"), &format!("@IRByteConfigV1.halted Nat (IROutcome.unmodelled IRFault.width_bounded) ({world})"));
        }
        for root in ROOTS {
            checked(&spec, root);
        }
        // Each access type belongs to some variant, but NOT the active one.
        // This is a dynamic UB residue, not a malformed site/catalog case.
        let enumeration = schema(7, &[(19, &["IRTy.fatstr_"]), (27, &["IRTy.bool_"])]);
        let active = aggregate("IRScalar", &["IRScalar.int_ 19", "IRScalar.fat_ 16 3"]);
        for (case, (instruction, ty, operands)) in [
            (
                "IRInst.extractfield IRTy.bool_ 0 1",
                "IRTy.bool_",
                vec![(0, "IRTy.enum_ 7")],
            ),
            (
                "IRInst.insertfield (IRTy.enum_ 7) 0 1 1",
                "IRTy.enum_ 7",
                vec![(0, "IRTy.enum_ 7"), (1, "IRTy.bool_")],
            ),
        ]
        .iter()
        .enumerate()
        {
            let nodes = vec![node(instruction, 99)];
            let sites = vec![site(0, ty, operands)];
            let (ctx, _, _) = program(
                &["IRTy.enum_ 7", "IRTy.bool_"],
                &[ty],
                &nodes,
                &sites,
                &[],
                &[&enumeration],
            );
            let actual = format!("ir_byte_run_v1 Nat ({ctx}) field_no_provider 1 (ir_byte_init_v1 Nat ({ctx}) 41 ({}) (ir_byte_memory_empty_v1 64) 73)", list("IRScalar", &[&active, "IRScalar.bool_ Bool.true"]));
            equality(&mut spec, &format!("field_fetched_active_variant_ub_{case}"), "IRByteConfigV1 Nat", &actual, &format!("@IRByteConfigV1.halted Nat (IROutcome.ub IRFault.bad_field) (@IRByteWorldV1.mk Nat (ir_byte_memory_empty_v1 64) 73 ({}) 2)", list("Nat", &["1"])));
        }
    });
}

#[test]
fn byte_field_fetched_const_rejects_same_shape_nominal_results_before_binding() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        add(&mut spec, NO_PROVIDER);
        let structure_a = layout(9, &["IRTy.bool_"]);
        let structure_b = layout(10, &["IRTy.bool_"]);
        let enum_a = schema(7, &[(19, &["IRTy.bool_"])]);
        let enum_b = schema(8, &[(19, &["IRTy.bool_"])]);
        for (case, (source_ty, site_ty, constant, value)) in [
            (
                "IRTy.fatstr_",
                "IRTy.containerlen_",
                aggregate("IRConst", &["IRConst.int_ 0", "IRConst.int_ 0"]),
                "IRScalar.fat_ 0 0".to_owned(),
            ),
            (
                "IRTy.struct_ 9",
                "IRTy.struct_ 10",
                aggregate("IRConst", &["IRConst.bool_ Bool.true"]),
                aggregate("IRScalar", &["IRScalar.bool_ Bool.true"]),
            ),
            (
                "IRTy.enum_ 7",
                "IRTy.enum_ 8",
                aggregate("IRConst", &["IRConst.int_ 19", "IRConst.bool_ Bool.true"]),
                aggregate(
                    "IRScalar",
                    &["IRScalar.int_ 19", "IRScalar.bool_ Bool.true"],
                ),
            ),
        ]
        .iter()
        .enumerate()
        {
            for (control, result_ty) in [("valid", *source_ty), ("wrong", *site_ty)] {
                let nodes = vec![node(
                    &format!("IRInst.const_ ({source_ty}) ({constant})"),
                    99,
                )];
                let sites = vec![old_site(0, &[result_ty])];
                let (ctx, _, _) = program(
                    &[],
                    &[result_ty],
                    &nodes,
                    &sites,
                    &[&structure_a, &structure_b],
                    &[&enum_a, &enum_b],
                );
                let ctx_name = format!("field_const_ctx_{case}_{control}");
                add(
                    &mut spec,
                    &format!("def {ctx_name} : IRByteContextV1 := {ctx}"),
                );
                // These BOTH pass: the refusal cannot be credited to a
                // representation sort mismatch or an uninhabited premise.
                equality(
                    &mut spec,
                    &format!("field_const_source_shape_{case}_{control}"),
                    "Bool",
                    &format!("ir_byte_value_matches_v1 {ctx_name} ({source_ty}) ({value})"),
                    "Bool.true",
                );
                equality(
                    &mut spec,
                    &format!("field_const_site_shape_{case}_{control}"),
                    "Bool",
                    &format!("ir_byte_value_matches_v1 {ctx_name} ({site_ty}) ({value})"),
                    "Bool.true",
                );
                result(
                    &mut spec,
                    &format!("field_const_conversion_{case}_{control}"),
                    &format!("ir_byte_const_context_eval_v1 {ctx_name} ({source_ty}) ({constant})"),
                    &format!("IRStepResult.value ({value})"),
                );
                let initial = format!("ir_byte_init_v1 Nat {ctx_name} 41 (@IRList.nil IRScalar) (ir_byte_memory_empty_v1 64) 73");
                let actual =
                    format!("ir_byte_run_v1 Nat {ctx_name} field_no_provider 1 ({initial})");
                if control == "wrong" {
                    equality(&mut spec, &format!("field_const_nominal_refusal_{case}"), "IRByteConfigV1 Nat", &actual, &format!("@IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.bad_field) (@IRByteWorldV1.mk Nat (ir_byte_memory_empty_v1 64) 73 ({}) 2)", list("Nat", &["1"])));
                } else {
                    equality(&mut spec, &format!("field_const_valid_carrier_{case}"), "IRScalar", &format!("@IRByteConfigV1.rec Nat (fun (_ : IRByteConfigV1 Nat) => IRScalar) (fun (state : IRMachine) (_ : IRByteWorldV1 Nat) => ir_getd state 99) (fun (_ : IROutcome) (_ : IRByteWorldV1 Nat) => IRScalar.undef_) ({actual})"), value);
                }
            }
        }
    });
}

#[test]
fn byte_field_fetched_admission_faults_preserve_exact_world_and_result_arity() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        add(&mut spec, NO_PROVIDER);
        let structure = layout(9, &["IRTy.fatstr_"]);
        let aggregate = aggregate("IRScalar", &["IRScalar.fat_ 16 3"]);
        let world = format!(
            "@IRByteWorldV1.mk Nat (ir_byte_memory_empty_v1 64) 73 ({}) 2",
            list("Nat", &["1"])
        );
        let locals = list(
            "IRBinding",
            &[
                &format!("IRBinding.mk 0 ({aggregate})"),
                "IRBinding.mk 1 (IRScalar.fat_ 32 7)",
            ],
        );
        let frame = format!("IRFrame.mk 41 0 0 ({locals}) (@IRList.nil Nat)");
        let state = format!(
            "IRMachine.mk ({}) (@IRList.nil IRMemSlot) 0",
            list("IRFrame", &[&frame])
        );
        let good = site(
            0,
            "IRTy.struct_ 9",
            &[(0, "IRTy.struct_ 9"), (1, "IRTy.fatstr_")],
        );
        for (case, (result_ids, operand_rows, duplicate_site)) in [
            (
                list("Nat", &[]),
                rows(&[(0, "IRTy.struct_ 9"), (1, "IRTy.fatstr_")]),
                false,
            ),
            (
                list("Nat", &["99", "99"]),
                rows(&[(0, "IRTy.struct_ 9"), (1, "IRTy.fatstr_")]),
                false,
            ),
            (
                list("Nat", &["99"]),
                rows(&[
                    (0, "IRTy.struct_ 9"),
                    (1, "IRTy.fatstr_"),
                    (0, "IRTy.struct_ 9"),
                ]),
                false,
            ),
            (list("Nat", &["99"]), rows(&[(0, "IRTy.struct_ 9")]), false),
            (
                list("Nat", &["99"]),
                rows(&[(0, "IRTy.struct_ 9"), (1, "IRTy.containerlen_")]),
                false,
            ),
            (
                list("Nat", &["99"]),
                rows(&[(0, "IRTy.struct_ 9"), (1, "IRTy.fatstr_")]),
                true,
            ),
        ]
        .iter()
        .enumerate()
        {
            let instruction = "IRInst.insertfield (IRTy.struct_ 9) 0 0 1";
            let nodes = vec![format!("IRNode.mk ({instruction}) ({result_ids})")];
            let typed = format!(
                "IRByteSiteV1.mkt 41 0 0 0 1 ({}) ({operand_rows})",
                list("IRTy", &["IRTy.struct_ 9"])
            );
            let sites = if *duplicate_site {
                vec![typed, good.clone()]
            } else {
                vec![typed]
            };
            let (ctx, _, _) = program(
                &["IRTy.struct_ 9", "IRTy.fatstr_"],
                &["IRTy.struct_ 9"],
                &nodes,
                &sites,
                &[&structure],
                &[],
            );
            let actual = format!("ir_byte_step_v1 Nat ({ctx}) field_no_provider (@IRByteConfigV1.running Nat ({state}) ({world}))");
            equality(
                &mut spec,
                &format!("field_fetched_admission_refusal_{case}"),
                "IRByteConfigV1 Nat",
                &actual,
                &format!(
                    "@IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.bad_field) ({world})"
                ),
            );
        }
        let ctx = context(&[&structure], &[], &[]);
        add(&mut spec, &format!("def field_derived_fault_world : @Eq (IRByteConfigV1 Nat)\n  (ir_byte_scalar_result_v1 Nat {ctx} ({state}) ({world}) ({}) ({}) (IRStepResult.fault (IROutcome.ub IRFault.bad_field)))\n  (@IRByteConfigV1.halted Nat (IROutcome.ub IRFault.bad_field) ({world})) := ir_byte_field_fault_world_v1 Nat {ctx} ({state}) ({world}) ({}) ({}) (IROutcome.ub IRFault.bad_field)", list("Nat", &["99"]), list("IRTy", &["IRTy.struct_ 9"]), list("Nat", &["99"]), list("IRTy", &["IRTy.struct_ 9"])));
    });
}
