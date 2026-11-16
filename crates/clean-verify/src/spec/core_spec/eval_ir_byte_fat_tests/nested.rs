// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authored nested representation fixture, not Rust source or ABI evidence.
//! Aggregate spines and fat carriers are untagged: nominal identity lives in
//! the declared type and exact context rows, not invented runtime tags.

use super::*;

fn list(ty: &str, values: &[String]) -> String {
    values
        .iter()
        .rev()
        .fold(format!("@IRList.nil {ty}"), |tail, value| {
            format!("@IRList.cons {ty} ({value}) ({tail})")
        })
}

fn aggregate(values: &[String]) -> String {
    let fields = values
        .iter()
        .rev()
        .fold("IRScalar.vnil".into(), |tail, value| {
            format!("IRScalar.vcons ({value}) ({tail})")
        });
    format!("IRScalar.aggv ({fields})")
}

fn layout(ty: &str, size: u64, align: u64, fields: &[&str], offsets: &[u64]) -> String {
    format!(
        "IRByteLayoutV1.mk ({ty}) {size} {align} ({}) ({})",
        list(
            "IRTy",
            &fields
                .iter()
                .map(|value| (*value).to_string())
                .collect::<Vec<_>>()
        ),
        list(
            "Nat",
            &offsets.iter().map(u64::to_string).collect::<Vec<_>>()
        ),
    )
}

fn context(rows: &[String]) -> String {
    format!(
        "IRByteContextV1.mk (IRModule.mk (@IRList.nil IRFunc) (@IRList.nil IRGlobal))
 ({}) (@IRList.nil IRByteSignatureV1) (@IRList.nil IRByteFunctionV1)
 (@IRList.nil IRByteSiteV1)",
        list("IRByteLayoutV1", rows)
    )
}

fn nested(data: &str, metadata: &str) -> String {
    let empty = aggregate(&[]);
    aggregate(&[
        aggregate(&[format!("IRScalar.fat_ {data} {metadata}")]),
        empty.clone(),
        empty,
    ])
}

#[test]
fn byte_fat_nested_struct_fields_keep_exact_layout_identity_and_check_every_carrier() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        // Arc-like 16/8 [0,16,16], transparent wrapper, then two DISTINCT empty
        // rows. The model has no Rust repr/ABI tag. Physical shape validity is
        // the reflector's obligation; this tests exact catalog lookup and
        // recursive SSA typing, not aggregate byte-memory admission.
        let rows = vec![
            layout(
                "IRTy.struct_ 41",
                16,
                8,
                &["IRTy.struct_ 7", "IRTy.struct_ 83", "IRTy.struct_ 97"],
                &[0, 16, 16],
            ),
            layout("IRTy.struct_ 7", 16, 8, &["IRTy.containerlen_"], &[0]),
            layout("IRTy.struct_ 83", 0, 1, &[], &[]),
            layout("IRTy.struct_ 97", 0, 1, &[], &[]),
            layout("IRTy.containerlen_", 16, 8, &[], &[]),
        ];
        add(
            &mut spec,
            &format!(
                "def byte_fat_nested_context : IRByteContextV1 := {}",
                context(&rows)
            ),
        );
        for (index, id) in [41, 7, 83, 97].into_iter().enumerate() {
            equality(
                &mut spec,
                &format!("byte_fat_nested_row_{index}"),
                "IROption IRByteLayoutV1",
                &format!("ir_byte_layout_v1 byte_fat_nested_context (IRTy.struct_ {id})"),
                &format!("@IROption.some IRByteLayoutV1 ({})", rows[index]),
            );
        }
        for (index, (a, b)) in [
            ("IRTy.struct_ 83", "IRTy.struct_ 97"),
            ("IRTy.containerlen_", "IRTy.fatstr_"),
            ("IRTy.containerlen_", "IRTy.fatslice_ (IRTy.uint_ 8)"),
        ]
        .into_iter()
        .enumerate()
        {
            equality(
                &mut spec,
                &format!("byte_fat_nested_nominal_{index}"),
                "Bool",
                &format!("ir_byte_ty_eq_v1 ({a}) ({b})"),
                "Bool.false",
            );
        }
        // Str cannot replace the actual row's ContainerLen declaration,
        // although both declarations accept the same physical fat carrier.
        refuse_claim(
            &mut spec,
            "byte_fat_nested_not_str_row",
            &format!(
                "def byte_fat_nested_not_str_row : @Eq (IRList IRTy)
 (ir_byte_layout_fields_v1 ({}))
 (@IRList.cons IRTy IRTy.fatstr_ (@IRList.nil IRTy)) :=
 @Eq.refl (IRList IRTy) (@IRList.cons IRTy IRTy.fatstr_ (@IRList.nil IRTy))",
                rows[1]
            ),
        );
        for (index, (data, meta)) in [("0", "0"), ("64", "5"), (MAX, MAX)]
            .into_iter()
            .enumerate()
        {
            equality(
                &mut spec,
                &format!("byte_fat_nested_valid_{index}"),
                "Bool",
                &format!(
                    "ir_byte_value_matches_v1 byte_fat_nested_context (IRTy.struct_ 41) ({})",
                    nested(data, meta)
                ),
                "Bool.true",
            );
        }
        let empty = aggregate(&[]);
        let good_inner = aggregate(&["IRScalar.fat_ 64 5".into()]);
        let malformed = vec![
            nested(LIMIT, "0"),
            nested("0", LIMIT),
            aggregate(&[
                aggregate(&["IRScalar.ptr_ 64".into()]),
                empty.clone(),
                empty.clone(),
            ]),
            aggregate(&[
                aggregate(&["IRScalar.int_ 64".into()]),
                empty.clone(),
                empty.clone(),
            ]),
            aggregate(&[
                aggregate(&["IRScalar.fnptr_ 7".into()]),
                empty.clone(),
                empty.clone(),
            ]),
            aggregate(&[
                good_inner.clone(),
                aggregate(&["IRScalar.int_ 0".into()]),
                empty.clone(),
            ]),
            aggregate(&[
                good_inner.clone(),
                empty.clone(),
                aggregate(&["IRScalar.nullptr_".into()]),
            ]),
            aggregate(&[good_inner.clone(), empty.clone()]),
            aggregate(&[
                good_inner.clone(),
                empty.clone(),
                empty.clone(),
                empty.clone(),
            ]),
            aggregate(&[aggregate(&[]), empty.clone(), empty.clone()]),
            aggregate(&[
                aggregate(&["IRScalar.fat_ 64 5".into(), "IRScalar.unit_".into()]),
                empty.clone(),
                empty.clone(),
            ]),
            "IRScalar.fat_ 64 5".into(),
        ];
        for (index, value) in malformed.into_iter().enumerate() {
            equality(
                &mut spec,
                &format!("byte_fat_nested_bad_value_{index}"),
                "Bool",
                &format!(
                    "ir_byte_value_matches_v1 byte_fat_nested_context (IRTy.struct_ 41) ({value})"
                ),
                "Bool.false",
            );
        }
        // Missing EACH nested struct row fails; no entry is invented from the
        // untagged runtime spine. Pure fat SSA typing does not itself require
        // a byte-memory layout lookup for the leaf.
        for missing in 0..4 {
            let incomplete = rows
                .iter()
                .enumerate()
                .filter(|(index, _)| *index != missing)
                .map(|(_, row)| row.clone())
                .collect::<Vec<_>>();
            equality(
                &mut spec,
                &format!("byte_fat_nested_missing_row_{missing}"),
                "Bool",
                &format!(
                    "ir_byte_value_matches_v1 ({}) (IRTy.struct_ 41) ({})",
                    context(&incomplete),
                    nested("64", "5")
                ),
                "Bool.false",
            );
        }
        for (index, wrong_field) in ["IRTy.bool_", "IRTy.fatptr_ (IRTy.uint_ 8)"]
            .into_iter()
            .enumerate()
        {
            let mut changed = rows.clone();
            changed[1] = layout("IRTy.struct_ 7", 16, 8, &[wrong_field], &[0]);
            equality(
                &mut spec,
                &format!("byte_fat_nested_wrong_field_{index}"),
                "Bool",
                &format!(
                    "ir_byte_value_matches_v1 ({}) (IRTy.struct_ 41) ({})",
                    context(&changed),
                    nested("64", "5")
                ),
                "Bool.false",
            );
        }
    });
}
