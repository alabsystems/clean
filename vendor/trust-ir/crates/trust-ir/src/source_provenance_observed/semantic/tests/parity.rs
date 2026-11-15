// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn exact_one_function_projection_matches_original_full_clone_retain_clear_digest() {
    let m = module();
    assert!(parity(&m, FuncId::new(151)).is_ok());
    assert!(parity(&m, FuncId::new(17)).is_ok());
}
#[test]
fn source_carriers_and_sibling_only_content_do_not_move_selected_body_identity() {
    let mut m = module();
    let expected = parity(&m, FuncId::new(151)).unwrap();
    m.functions[0].name = "totally_different_sibling".into();
    m.functions[0].blocks[0]
        .body
        .push(InstrNode::new(Inst::Unreachable));
    m.functions[0].source_provenance = Some(carrier(&"ignored_λ".repeat(5000)));
    m.functions[1].source_provenance = Some(carrier(&"also_ignored_λ".repeat(5000)));
    assert_eq!(parity(&m, FuncId::new(151)).unwrap(), expected);
    m.functions[1].source_provenance = None;
    assert_eq!(parity(&m, FuncId::new(151)).unwrap(), expected);
}
#[test]
fn all_retained_module_tables_name_and_selected_function_content_remain_bound() {
    let m = module();
    let expected = parity(&m, FuncId::new(151)).unwrap();
    let mut cases = Vec::new();
    let mut changed = m.clone();
    changed.name.push('x');
    cases.push(changed);
    let mut changed = m.clone();
    changed.types.push(Ty::U8);
    cases.push(changed);
    let mut changed = m.clone();
    changed.globals[0].name.push('x');
    cases.push(changed);
    let mut changed = m.clone();
    changed.globals[0].initializer = Some(crate::Constant::Int(4));
    cases.push(changed);
    let mut changed = m.clone();
    changed.functions[1].name.push('x');
    cases.push(changed);
    let mut changed = m.clone();
    changed.functions[1].blocks[0]
        .body
        .push(InstrNode::new(Inst::Unreachable));
    cases.push(changed);
    for changed in cases {
        assert_ne!(parity(&changed, FuncId::new(151)).unwrap(), expected);
    }
}
#[test]
fn original_v3_debug_path_projection_and_function_id_seal_are_preserved() {
    let mut m = module();
    let expected = parity(&m, FuncId::new(151)).unwrap();
    m.files[0].push_str("different_path");
    assert_eq!(parity(&m, FuncId::new(151)).unwrap(), expected);
    m.functions[0] = m.functions[1].clone();
    m.functions[0].id = FuncId::new(152);
    assert_ne!(parity(&m, FuncId::new(152)).unwrap(), expected);
}
#[test]
fn missing_and_duplicate_targets_preserve_exact_semantic_error_without_authority() {
    let mut m = module();
    for id in [0, u32::MAX] {
        assert_eq!(
            parity(&m, FuncId::new(id)),
            Err(format!(
                "source provenance target function #{id} is missing or duplicated"
            ))
        );
    }
    m.functions.push(m.functions[1].clone());
    assert_eq!(
        parity(&m, FuncId::new(151)),
        Err("source provenance target function #151 is missing or duplicated".into())
    );
}
#[test]
fn whole_module_both_identity_schemes_still_match_the_unchanged_ordinary_plan() {
    let m = module();
    for scheme in crate::IdentityScheme::ALL {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            crate::binary::observed_module_identity(&m, scheme, &mut session, site()).unwrap(),
            m.stable_digest_under(scheme)
        );
    }
}

#[test]
fn omitted_sibling_payload_is_not_traversed_but_retained_module_poison_still_refuses() {
    let mut m = module();
    let expected = parity(&m, FuncId::new(151)).unwrap();
    m.functions[0].blocks[0]
        .body
        .push(InstrNode::new(Inst::Undef { ty: Ty::Error }));
    assert_eq!(parity(&m, FuncId::new(151)).unwrap(), expected);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        m.stable_digest_observed(&mut session, site()),
        Err(ObservedValueError::UnsupportedValue)
    );
    m.types.push(Ty::Error);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        m.source_provenance_semantic_digest_observed(FuncId::new(151), &mut session, site()),
        Err(ObservedValueError::UnsupportedValue)
    );
}
