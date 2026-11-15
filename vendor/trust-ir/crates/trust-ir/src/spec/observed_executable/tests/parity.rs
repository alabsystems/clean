// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_absent_nonfunction_targets_and_both_modes_keep_the_original_scope() {
    assert!(run(&Module::new("")).0.is_empty());
    let mut m = fixture();
    assert!(run(&m).0.is_empty());
    for mode in [SpecEnforcementMode::DesignOnly, SpecEnforcementMode::Linked] {
        m.spec_modules[0].enforcement = mode;
        for target in [
            None,
            Some(SpecProjectionTarget::ExternalUnresolved),
            Some(SpecProjectionTarget::TemporalFieldPathsV1),
        ] {
            let a = &mut m.spec_modules[0].anchors[0];
            a.function = None;
            a.projection_target = target;
            assert!(run(&m).0.is_empty());
        }
    }
}
#[test]
fn exact_nonblank_container_machine_action_guards_skip_only_unowned_anchors() {
    for field in 0..4 {
        let mut m = compact();
        match field {
            0 => m.spec_modules[0].name = "\u{2003}\n".into(),
            1 => m.spec_modules[0].anchors[0].machine = "\u{3000}".into(),
            2 => m.spec_modules[0].anchors[0].action = " ".into(),
            _ => m.spec_modules[0].anchors[0].machine = "foreign".into(),
        }
        assert!(run(&m).0.is_empty());
    }
}
#[test]
fn missing_function_has_full_unsigned_identity_and_exact_quoted_raw_module_name() {
    let mut m = compact();
    m.name = "λ'\"\n\0".repeat(1000) + "TAIL";
    let out = run(&m).0;
    assert_eq!(out.len(), 1);
    assert_eq!(
        detail(&out[0]),
        format!("function id is not present in module {:?}", m.name)
    );
    assert!(
        matches!(&out[0],SpecLinkViolation::ExecutableTargetInvalid{function,target:"action",..} if *function==u32::MAX)
    );
}
#[test]
fn duplicate_count_is_complete_and_ambiguity_precedes_body_name_and_signature_checks() {
    let mut m = fixture();
    let mut duplicate = m.functions[0].clone();
    duplicate.blocks.clear();
    duplicate.name = "wrong".into();
    duplicate.ty = FuncTyId::new(u32::MAX);
    m.functions.extend([duplicate.clone(), duplicate]);
    let out = run(&m).0;
    assert_eq!(out.len(), 1);
    assert_eq!(detail(&out[0]), "function id is ambiguous (3 definitions)");
    m.spec_modules[0].anchors[0].projection_target =
        Some(SpecProjectionTarget::Function(FuncId::new(7)));
    let out = run(&m).0;
    assert_eq!(out.len(), 2);
    assert!(
        out.iter()
            .all(|row| detail(row) == "function id is ambiguous (3 definitions)")
    );
}
#[test]
fn sparse_out_of_order_and_direct_slot_lookup_keep_the_exact_original_function() {
    let mut m = fixture();
    m.functions.reverse();
    assert!(run(&m).0.is_empty());
    m.functions[0].id = FuncId::new(0);
    m.functions[1].id = FuncId::new(1);
    let a = &mut m.spec_modules[0].anchors[0];
    a.function = Some(FuncId::new(1));
    a.projection_target = Some(SpecProjectionTarget::Function(FuncId::new(0)));
    assert!(run(&m).0.is_empty());
}
#[test]
fn bodyless_refusal_precedes_name_or_signature_and_actions_do_not_require_a_signature() {
    let mut m = fixture();
    m.functions[1].blocks.clear();
    m.functions[1].name = "wrong".into();
    m.functions[1].ty = FuncTyId::new(u32::MAX);
    assert_eq!(detail(&run(&m).0[0]), "function is a bodyless declaration");
    m = fixture();
    m.functions[0].ty = FuncTyId::new(u32::MAX);
    assert!(run(&m).0.is_empty());
}
#[test]
fn action_and_projection_name_mismatches_keep_both_complete_debug_strings() {
    let mut m = fixture();
    m.functions[0].name = "linkedλ'\"\n".repeat(1000);
    m.functions[1].name = "linked projection".into();
    let a = &mut m.spec_modules[0].anchors[0];
    a.rust_symbol = "expected action".into();
    a.project = Some("expected projection".into());
    let out = run(&m).0;
    assert_eq!(out.len(), 2);
    assert_eq!(
        detail(&out[0]),
        format!(
            "rust_symbol {:?} does not match typed target {:?}",
            "expected action", m.functions[0].name
        )
    );
    assert_eq!(
        detail(&out[1]),
        "project \"expected projection\" does not match typed target \"linked projection\""
    );
}
#[test]
fn blank_expected_names_exempt_only_name_agreement_and_missing_project_is_empty() {
    let mut m = fixture();
    let a = &mut m.spec_modules[0].anchors[0];
    a.rust_symbol = "\u{2003}\t".into();
    a.project = None;
    assert!(run(&m).0.is_empty());
    m.func_types[0].is_vararg = true;
    assert_eq!(run(&m).0.len(), 1);
}
#[test]
fn missing_projection_signature_follows_body_and_name_resolution_with_exact_type_id() {
    let mut m = fixture();
    m.functions[1].ty = FuncTyId::new(u32::MAX);
    assert_eq!(
        detail(&run(&m).0[0]),
        "function references missing signature type #4294967295"
    );
}
#[test]
fn projection_requires_exact_one_immutable_reference_one_result_and_no_varargs() {
    for inner in types() {
        let mut m = fixture();
        m.func_types[0].returns = vec![inner.clone()];
        m.func_types[0].params = vec![Ty::Ref(Box::new(inner))];
        assert!(run(&m).0.is_empty());
    }
    for params in [
        vec![],
        vec![Ty::U8],
        vec![Ty::RefMut(Box::new(Ty::U8))],
        vec![Ty::PtrConst(Box::new(Ty::U8))],
        vec![Ty::Refine(TyId::new(0), PredId::new(0))],
        vec![Ty::Ref(Box::new(Ty::U8))],
        vec![Ty::Ref(Box::new(Ty::U8)), Ty::Ref(Box::new(Ty::U8))],
    ] {
        for returns in [vec![], vec![Ty::U8], vec![Ty::U8, Ty::U16]] {
            for vararg in [false, true] {
                let mut m = fixture();
                m.func_types[0] = FuncTy::unrecorded(params.clone(), returns.clone(), vararg);
                let valid = !vararg
                    && params.len() == 1
                    && returns.len() == 1
                    && matches!(params[0], Ty::Ref(_));
                assert_eq!(run(&m).0.len(), usize::from(!valid));
            }
        }
    }
}
#[test]
fn canonical_sort_and_dedup_keep_machine_action_role_detail_then_numeric_id_order() {
    let mut m = compact();
    let mut a = m.spec_modules[0].anchors[0].clone();
    a.action = "z".into();
    a.function = Some(FuncId::new(20));
    m.spec_modules[0].anchors.extend([a.clone(), a]);
    let mut n = m.spec_modules[0].clone();
    n.name = "A".into();
    for a in &mut n.anchors {
        a.machine = "A".into();
    }
    m.spec_modules.push(n);
    let out = run(&m).0;
    assert_eq!(out.len(), 4);
    assert!(
        matches!(&out[0],SpecLinkViolation::ExecutableTargetInvalid{machine,..} if machine=="A")
    );
}
#[test]
fn undeclared_action_still_receives_executable_checks_and_irrelevant_payloads_are_opaque() {
    let mut m = compact();
    m.spec_modules[0].actions.clear();
    assert_eq!(run(&m).0.len(), 1);
    let (_, before) = run(&m);
    m.spec_modules[0].anchors[0].span = "opaque".repeat(10000);
    m.functions[0].name = "unused".repeat(10000);
    m.types = types();
    let (_, after) = run(&m);
    assert_eq!(before.events, after.events);
}
