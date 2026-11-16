// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Contextual constant laws and the actual fetched complete-world dispatcher.

use super::{
    add, aggregate, checked, context, equality, layout, list, rejected, result, schema,
    specification, BAD, ROOTS, ZERO_FAT,
};

#[test]
fn byte_const_context_function_seeds_require_actual_signature_and_code_address() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let function = "IRByteFunctionV1.mk 41 42 160 1 Bool.false";
        let structure = layout(9, &["IRTy.func_ 42"]);
        let ctx = context(&[&structure], &[], &[function]);
        result(
            &mut spec,
            "const_function_seed",
            &ctx,
            "IRTy.struct_ 9",
            &aggregate("IRConst", &["IRConst.func_ 41"]),
            &format!(
                "IRStepResult.value ({})",
                aggregate("IRScalar", &["IRScalar.fnptr_ 41"])
            ),
        );
        result(
            &mut spec,
            "const_function_wrong_signature",
            &ctx,
            "IRTy.func_ 41",
            "IRConst.func_ 41",
            BAD,
        );
        result(
            &mut spec,
            "const_function_absent",
            &ctx,
            "IRTy.func_ 42",
            "IRConst.func_ 99",
            BAD,
        );
        let zero = context(
            &[&structure],
            &[],
            &["IRByteFunctionV1.mk 41 42 0 1 Bool.false"],
        );
        result(
            &mut spec,
            "const_function_zero_address",
            &zero,
            "IRTy.func_ 42",
            "IRConst.func_ 41",
            BAD,
        );
    });
}

#[test]
fn byte_const_context_laws_have_bodies_and_wrong_endpoints_reject_same_proofs() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for root in ROOTS {
            checked(&spec, root);
        }
        let ctx = context(&[], &[], &[]);
        let positive = format!("def const_derived_null : @Eq IRStepResult\n  (ir_byte_const_context_eval_v1 {ctx} IRTy.ptr_ (IRConst.int_ 0))\n  (IRStepResult.value IRScalar.nullptr_) := ir_byte_const_zero_pointer_v1 {ctx}");
        add(&mut spec, &positive);
        let wrong = positive
            .replacen("const_derived_null", "const_wrong_null", 1)
            .replacen(
                "(IRStepResult.value IRScalar.nullptr_)",
                "(IRStepResult.value (IRScalar.int_ 0))",
                1,
            );
        assert_eq!(
            positive.split_once(":=").unwrap().1,
            wrong.split_once(":=").unwrap().1
        );
        rejected(&mut spec, "const_wrong_null", &wrong);
        let cons = format!("def const_derived_fields : @Eq IRStepResult\n  (ir_byte_const_fields_at_v1 (ir_byte_const_fold_v1 {ctx} (IRConst.vcons (IRConst.int_ 0) IRConst.vnil))\n    (@IRList.cons IRTy IRTy.ptr_ (@IRList.nil IRTy)))\n  (IRStepResult.value (IRScalar.vcons IRScalar.nullptr_ IRScalar.vnil)) :=\n  ir_byte_const_fields_cons_v1 {ctx} (IRConst.int_ 0) IRConst.vnil IRTy.ptr_ (@IRList.nil IRTy) IRScalar.nullptr_ IRScalar.vnil\n    (ir_byte_const_zero_pointer_v1 {ctx}) (ir_byte_const_fields_nil_v1 {ctx})");
        add(&mut spec, &cons);
        let wrong = cons
            .replacen("const_derived_fields", "const_wrong_fields", 1)
            .replacen(
                "IRScalar.vcons IRScalar.nullptr_ IRScalar.vnil",
                "IRScalar.vcons (IRScalar.int_ 0) IRScalar.vnil",
                1,
            );
        assert_eq!(
            cons.split_once(":=").unwrap().1,
            wrong.split_once(":=").unwrap().1
        );
        rejected(&mut spec, "const_wrong_fields", &wrong);
    });
}

#[test]
fn byte_const_context_actual_fetched_dispatch_returns_exact_value_and_world() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        let enumeration = schema(7, 19, &["IRTy.ptr_", "IRTy.fatstr_"]);
        let expected = aggregate(
            "IRScalar",
            &["IRScalar.int_ 19", "IRScalar.nullptr_", "IRScalar.fat_ 0 0"],
        );
        let mem = "ir_byte_memory_empty_v1 64";
        add(&mut spec, "def const_no_provider : IRByteProvidersV1 Nat := fun (_ : Nat) (_ : IRList IRScalar) (memory : IRByteMemoryV1) (host : Nat) => @IRByteImportResultV1.mk Nat (IROutcome.stuck IRFault.no_func) memory host");
        for (case, (tag, result_ty, succeeds)) in [
            (19, "IRTy.enum_ 7", true),
            (0, "IRTy.enum_ 7", false),
            (19, "IRTy.uint_ 64", false),
        ]
        .iter()
        .enumerate()
        {
            let seed = aggregate(
                "IRConst",
                &[&format!("IRConst.int_ {tag}"), "IRConst.int_ 0", ZERO_FAT],
            );
            let nodes = list(
                "IRNode",
                &[
                    &format!(
                        "IRNode.mk (IRInst.const_ (IRTy.enum_ 7) ({seed})) ({})",
                        list("Nat", &["99"])
                    ),
                    &format!(
                        "IRNode.mk (IRInst.ret ({})) (@IRList.nil Nat)",
                        list("Nat", &["99"])
                    ),
                ],
            );
            let blocks = list(
                "IRBlock",
                &[&format!("IRBlock.mk 0 (@IRList.nil Nat) ({nodes})")],
            );
            let program = format!(
                "IRModule.mk ({}) (@IRList.nil IRGlobal)",
                list(
                    "IRFunc",
                    &[&format!("IRFunc.mk 41 (@IRList.nil Nat) 0 ({blocks})")]
                )
            );
            let sites = list(
                "IRByteSiteV1",
                &[
                    &format!(
                        "IRByteSiteV1.mk 41 0 0 0 1 ({})",
                        list("IRTy", &[result_ty])
                    ),
                    "IRByteSiteV1.mk 41 0 1 0 1 (@IRList.nil IRTy)",
                ],
            );
            let ctx = format!("IRByteContextV1.mke ({program}) (@IRList.nil IRByteLayoutV1) ({}) ({}) ({sites}) ({})",
                list("IRByteSignatureV1", &[&format!("IRByteSignatureV1.mk 41 (@IRList.nil IRTy) ({}) Bool.false", list("IRTy", &["IRTy.enum_ 7"]))]),
                list("IRByteFunctionV1", &["IRByteFunctionV1.mk 41 41 160 1 Bool.false"]),
                list("IRByteEnumV1", &[&enumeration]));
            let ctx_name = format!("const_fetch_ctx_{case}");
            add(
                &mut spec,
                &format!("def {ctx_name} : IRByteContextV1 := {ctx}"),
            );
            let actual = format!("ir_byte_run_v1 Nat {ctx_name} const_no_provider 2 (ir_byte_init_v1 Nat {ctx_name} 41 (@IRList.nil IRScalar) ({mem}) 73)");
            let endpoint = if *succeeds {
                format!("@IRByteConfigV1.halted Nat (IROutcome.ret ({})) (@IRByteWorldV1.mk Nat (ir_byte_retire_v1 1 ({mem})) 73 (@IRList.nil Nat) 2)", list("IRScalar", &[&expected]))
            } else {
                format!("@IRByteConfigV1.halted Nat (IROutcome.type_error IRFault.bad_field) (@IRByteWorldV1.mk Nat ({mem}) 73 ({}) 2)", list("Nat", &["1"]))
            };
            equality(
                &mut spec,
                &format!("const_fetch_complete_{case}"),
                "IRByteConfigV1 Nat",
                &actual,
                &endpoint,
            );
        }
    });
}
