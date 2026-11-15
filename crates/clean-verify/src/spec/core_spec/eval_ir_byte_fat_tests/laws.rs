// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn bound(word: &str) -> String {
    let successor = word.parse::<u128>().unwrap() + 1;
    format!(
        "(Nat.le_add_right {successor} {})",
        (1_u128 << 64) - successor
    )
}

fn claim(op: &str, ty: &str, mt: &str, data: &str, meta: &str) -> (String, String) {
    let d = format!("ir_byte_pointer_value_v1 {data}");
    let m = if mt == "IRTy.ptr_" {
        format!("ir_byte_pointer_value_v1 {meta}")
    } else {
        format!("IRScalar.int_ {meta}")
    };
    let fat = format!("IRScalar.fat_ {data} {meta}");
    match op {
        "data" => (
            format!("ir_byte_ptrdata_eval_v1 ctx ({ty}) ({fat})"),
            format!("IRStepResult.value ({d})"),
        ),
        "metadata" => (
            format!("ir_byte_ptrmetadata_eval_v1 ctx ({ty}) ({mt}) ({fat})"),
            format!("IRStepResult.value ({m})"),
        ),
        "fromparts" => (
            format!("ir_byte_ptrfromparts_eval_v1 ctx ({ty}) ({mt}) ({d}) ({m})"),
            format!("IRStepResult.value ({fat})"),
        ),
        _ => panic!("unknown test operation"),
    }
}

#[test]
fn byte_fat_general_laws_are_audited_and_have_inhabited_bound_only_applications() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for (i, (prefix, generic_ty, binder, argument, concrete_argument)) in [
            ("fatstr", "IRTy.fatstr_", "", "", ""),
            (
                "fatslice",
                "IRTy.fatslice_ element",
                "(element : IRTy)",
                "element",
                "(IRTy.uint_ 8)",
            ),
            (
                "fatdyn",
                "IRTy.fatdyn_ traitId",
                "(traitId : Nat)",
                "traitId",
                "7",
            ),
            ("containerlen", "IRTy.containerlen_", "", "", ""),
            ("containervtable", "IRTy.containervtable_", "", "", ""),
        ]
        .into_iter()
        .enumerate()
        {
            let (concrete_ty, mt) = KINDS[i];
            for op in ["data", "metadata", "fromparts"] {
                let root = format!("ir_byte_{prefix}_{op}_v1");
                let definition = spec
                    .get_definition(&root)
                    .expect("registered general fat law");
                assert!(!definition.is_axiom && definition.elaborated_value.is_some());
                spec.verify_definition(&root)
                    .expect("general law checks independently");
                let name = Name::from_string(&root);
                assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
                assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());

                let (actual, expected) = claim(op, generic_ty, mt, "data", "metadata");
                add(
                    &mut spec,
                    &format!(
                        "def byte_fat_general_{prefix}_{op}
  (ctx : IRByteContextV1) {binder} (data metadata : Nat)
  (dataBound : Nat.lt data ir_byte_limit_v1)
  (metadataBound : Nat.lt metadata ir_byte_limit_v1) :
  Eq IRStepResult ({actual}) ({expected}) :=
  {root} ctx {argument} data metadata dataBound metadataBound"
                    ),
                );

                for (j, (data, meta)) in [("0", "0"), ("16", "5"), (MAX, MAX)]
                    .into_iter()
                    .enumerate()
                {
                    let (actual, expected) = claim(op, concrete_ty, mt, data, meta);
                    add(
                        &mut spec,
                        &format!(
                            "def byte_fat_inhabited_{prefix}_{op}_{j}
  (ctx : IRByteContextV1) : Eq IRStepResult ({actual}) ({expected}) :=
  {root} ctx {concrete_argument} {data} {meta} {} {}",
                            bound(data),
                            bound(meta)
                        ),
                    );
                }
            }
        }
        refuse_claim(
            &mut spec,
            "byte_fat_law_cannot_change_metadata",
            &format!(
                "def byte_fat_law_cannot_change_metadata (ctx : IRByteContextV1) :
  Eq IRStepResult (ir_byte_ptrfromparts_eval_v1 ctx IRTy.containerlen_ (IRTy.uint_ 64)
    (IRScalar.ptr_ 16) (IRScalar.int_ 5)) (IRStepResult.value (IRScalar.fat_ 16 6)) :=
  ir_byte_containerlen_fromparts_v1 ctx 16 5 {} {}",
                bound("16"),
                bound("5")
            ),
        );
    });
}
