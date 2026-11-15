// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn sparse_unsorted_and_duplicate_definitions_match_the_entire_original_digest() {
    let mut m = module();
    run(&m, f());
    m.functions[0].blocks[1].params.push((v(40), Ty::I64));
    m.functions[0].blocks[1].body[0].results.push(v(40));
    m.functions[0].blocks[1].id = m.functions[0].blocks[0].id;
    run(&m, f());
}
#[test]
fn all_parameters_precede_all_results_and_dangling_summary_bindings_stay_dangling() {
    let mut m = module();
    let mut formula = ProofFormula::smtlib2("(= r 1)", "Bool");
    formula.bindings = [0, 1, 30, 40, 70, 80, 999, u32::MAX]
        .into_iter()
        .map(|id| {
            (
                format!("r{id}"),
                ClauseBinding {
                    sort: ClauseSort::BitVec(64),
                    place: ClausePlace::Value(v(id)),
                },
            )
        })
        .collect();
    m.functions[0].summary = Some(
        FunctionSummary::new()
            .requiring(formula.clone())
            .ensuring(formula),
    );
    m.functions[0].value_names = Some(vec![
        (v(40), "p".into()),
        (v(70), "r".into()),
        (v(999), "undefined".into()),
    ]);
    run(&m, f());
    let reference = FunctionCanonicalPlan::new(&m.functions[0]);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut out = Output::counter(&mut s, site()).unwrap();
    let mut plan = Plan::default();
    plan.build(&m.functions[0], &mut out).unwrap();
    for id in [0, 1, 30, 40, 70, 80, 999, u32::MAX] {
        assert_eq!(
            plan.map(v(id), &mut out).unwrap(),
            reference.map_value(v(id))
        );
        assert_eq!(
            plan.binding(v(id), &mut out).unwrap(),
            reference.map_binding_value(v(id))
        );
    }
    plan.retire(&mut out);
}
#[test]
fn trailing_empty_attributes_trim_but_interior_and_return_records_stay_exact() {
    let mut m = module();
    for tail in 0..4 {
        m.functions[0].attrs.params = vec![
            ParamAttrs::default(),
            ParamAttrs {
                nonnull: true,
                ..ParamAttrs::default()
            },
        ];
        m.functions[0]
            .attrs
            .params
            .extend((0..tail).map(|_| ParamAttrs::default()));
        m.functions[0].attrs.ret = ParamAttrs {
            noalias: true,
            ..ParamAttrs::default()
        };
        run(&m, f());
    }
}
#[test]
fn the_minimal_image_ignores_unrelated_tables_but_binds_every_body_change() {
    let m = module();
    let original = m.function_body_digest(f()).unwrap();
    let mut changed = m.clone();
    changed.name = "different module".into();
    changed.files = vec!["not-the-body.rs".into()];
    changed.types = vec![Ty::Error];
    changed.global_asm = vec!["not in minimal image".into()];
    changed.drop_glue = vec![DropGlueEntry {
        glue: FuncId::new(1),
        ty: Ty::Error,
    }];
    assert_eq!(original, changed.function_body_digest(f()).unwrap());
    run(&changed, f());
    changed.functions[0].blocks[0].body[0].inst = Inst::Copy {
        ty: Ty::Ptr,
        operand: v(999),
    };
    assert_ne!(original, changed.function_body_digest(f()).unwrap());
    run(&changed, f());
}
#[test]
fn licenses_and_display_paths_are_omitted_while_source_provenance_is_retained_even_for_nan() {
    let mut m = module();
    let base = m.function_body_digest(f()).unwrap();
    m.functions[0].body_gate = Some(crate::BodyGate::Gated {
        authority: "authority_λ".into(),
        evidence: Some(GateEvidence {
            obligation: ProofId::new(9),
            body_digest: ProofDigest::zero(),
        }),
    });
    m.functions[0].display_path = Some("display::path".into());
    assert_eq!(base, m.function_body_digest(f()).unwrap());
    run(&m, f());
    m.functions[0].proofs.push(ProofAnnotation::BoundedOutput {
        lo: f64::NAN,
        hi: 1.0,
    });
    m.functions[0].source_provenance = Some(SourceProvenance::new(
        ProofDigest::zero(),
        ProofDigest::zero(),
        vec![SourceLoopProvenance {
            source_loop_id: 3,
            hir_local_id: 7,
            header: BlockId::new(8),
            bindings: vec![SourceBindingProvenance {
                name: "x_λ".into(),
                hir_local_id: 9,
                place: SourcePlace::LoopParameter { index: 2 },
            }],
        }],
    ));
    run(&m, f());
    let digest = m.function_body_digest(f()).unwrap();
    m.functions[0].source_provenance.as_mut().unwrap().loops[0].bindings[0]
        .name
        .push('!');
    assert_ne!(digest, m.function_body_digest(f()).unwrap());
    run(&m, f());
}
#[test]
fn resolved_drop_rows_sort_deduplicate_and_ignore_unresolved_or_unused_rows() {
    let mut m = drops();
    run(&m, f());
    let base = m.function_body_digest(f()).unwrap();
    m.drop_glue.reverse();
    m.drop_glue.push(DropGlueEntry {
        glue: FuncId::new(7),
        ty: Ty::Bool,
    });
    assert_eq!(base, m.function_body_digest(f()).unwrap());
    run(&m, f());
    m.drop_glue.retain(|row| row.ty != Ty::I64);
    assert_ne!(base, m.function_body_digest(f()).unwrap());
    run(&m, f());
}
#[test]
fn ambiguous_type_and_shared_glue_refuse_with_complete_original_first_error_text() {
    for m in [ambiguous(), same_glue()] {
        let expected = m.function_body_digest(f()).unwrap_err();
        assert!(expected.contains("so the body has no identity to state"));
        run(&m, f());
    }
    let mut m = ambiguous();
    m.functions[0].blocks[0].body[0].inst = Inst::Drop {
        ty: Ty::handle("名é🦀", "runtime::名字"),
        ptr: v(40),
    };
    m.drop_glue.extend([
        DropGlueEntry {
            glue: FuncId::new(1),
            ty: Ty::handle("名é🦀", "runtime::名字"),
        },
        DropGlueEntry {
            glue: FuncId::new(2),
            ty: Ty::handle("名é🦀", "runtime::名字"),
        },
    ]);
    run(&m, f());
}
#[test]
fn missing_and_duplicate_ids_use_unique_id_semantics_including_off_index_rows() {
    let mut m = module();
    run(&m, FuncId::new(0));
    run(&m, f());
    let mut other = m.functions[0].clone();
    other.id = FuncId::new(0);
    m.functions.insert(0, other);
    run(&m, f());
    m.functions.push(m.functions[1].clone());
    run(&m, f());
    assert!(
        m.function_body_digest(f())
            .unwrap_err()
            .contains("missing or duplicated")
    );
}
#[test]
fn inline_error_precedes_inlining_and_dialect_attribute_types_are_not_skipped() {
    let mut m = module();
    m.functions[0].scopes = Some(vec![inlining()]);
    m.functions[0].blocks[0]
        .params
        .push((v(300), Ty::Tuple(vec![Ty::Ref(Box::new(Ty::Error))])));
    assert!(
        m.function_body_digest(f())
            .unwrap_err()
            .contains("producer-internal Ty::Error")
    );
    run(&m, f());
    m.functions[0].blocks[0].params.pop();
    run(&m, f());
    let op = crate::dialect::DialectInst::new("unknown", "opaque").with_attr(
        "t",
        crate::dialect::AttrValue::Ty(Ty::Tuple(vec![Ty::Error])),
    );
    m.functions[0].blocks[0]
        .body
        .insert(0, InstrNode::new(Inst::DialectOp(Box::new(op))));
    assert!(
        m.function_body_digest(f())
            .unwrap_err()
            .contains("producer-internal Ty::Error")
    );
    run(&m, f());
}
#[test]
fn huge_splat_count_full_raw_bytes_and_dialect_operand_records_are_never_expanded_or_normalized() {
    let mut m = module();
    m.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Const {
            ty: Ty::Array(TyId::new(999), u64::MAX),
            value: Constant::Splat {
                elem: Box::new(Constant::Int(-4)),
                len: u64::MAX,
            },
        })
        .with_result(v(111)),
    );
    let op = crate::dialect::DialectInst::new("unknown_λ", "raw")
        .with_operands([v(40), v(70), v(999)])
        .with_result_ty(Ty::handle("H", "runtime::H"))
        .with_attr(
            "bytes",
            crate::dialect::AttrValue::Bytes((0..4097).map(|n| (n % 251) as u8).collect()),
        )
        .with_attr(
            "f",
            crate::dialect::AttrValue::F64(f64::from_bits(0x7ff8_0000_0000_0017)),
        );
    m.functions[0].blocks[0].body.insert(
        1,
        InstrNode::new(Inst::DialectOp(Box::new(op))).with_result(v(112)),
    );
    run(&m, f());
}
