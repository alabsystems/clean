// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::tests_contract_gate_support::{
    mk_bool_backend_and_mapping, mk_bool_env, mk_eq_u, mk_qf_lia_backend_and_mapping,
    mk_qf_lia_env, mk_qf_uf_backend_and_mapping, mk_qf_uf_env, neg_false,
};
use super::super::tests_e2e::assert_proof_type_checks_to_false;
use super::support::evaluate_gate_case;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, LocalContext};

#[test]
fn test_2386_replacement_gate_qf_bool() {
    let env = mk_bool_env();
    let (mut backend, map, [h_p_id, h_not_p_id], not_p) = mk_bool_backend_and_mapping();
    let p_prop = Expr::const_(Name::from_string("P"), vec![]);

    let (proof_present, native_complete, unlimited, zero_trust) =
        evaluate_gate_case(&mut backend, &map, &neg_false());

    assert!(proof_present, "QF_BOOL: proof must be present");
    assert!(native_complete, "QF_BOOL: native quality must be complete");

    for (label, candidate) in [("unlimited", &unlimited), ("zero_trust", &zero_trust)] {
        if let Some(c) = candidate {
            let mut ctx = LocalContext::new();
            ctx.push_with_id(
                h_p_id,
                Name::from_string("hP"),
                p_prop.clone(),
                BinderInfo::Default,
            );
            ctx.push_with_id(
                h_not_p_id,
                Name::from_string("hNotP"),
                not_p.clone(),
                BinderInfo::Default,
            );
            assert_proof_type_checks_to_false(
                &env,
                ctx,
                c.refutation(),
                &format!("QF_BOOL {label}"),
            );
        }
    }

    if zero_trust.is_some() {
        assert!(
            unlimited.is_some(),
            "QF_BOOL: zero-trust accepted but unlimited rejected — inconsistent"
        );
    }
}

#[test]
fn test_2386_replacement_gate_qf_uf() {
    let env = mk_qf_uf_env();
    let (mut backend, map, [h_ab_id, h_bc_id, h_neq_ac_id], neq_ac) =
        mk_qf_uf_backend_and_mapping();
    let eq_ab = mk_eq_u("a", "b");
    let eq_bc = mk_eq_u("b", "c");

    let (proof_present, native_complete, unlimited, zero_trust) =
        evaluate_gate_case(&mut backend, &map, &neg_false());

    assert!(proof_present, "QF_UF: proof must be present");
    assert!(native_complete, "QF_UF: native quality must be complete");

    for (label, candidate) in [("unlimited", &unlimited), ("zero_trust", &zero_trust)] {
        if let Some(c) = candidate {
            let mut ctx = LocalContext::new();
            ctx.push_with_id(
                h_ab_id,
                Name::from_string("h_ab"),
                eq_ab.clone(),
                BinderInfo::Default,
            );
            ctx.push_with_id(
                h_bc_id,
                Name::from_string("h_bc"),
                eq_bc.clone(),
                BinderInfo::Default,
            );
            ctx.push_with_id(
                h_neq_ac_id,
                Name::from_string("h_neq_ac"),
                neq_ac.clone(),
                BinderInfo::Default,
            );
            assert_proof_type_checks_to_false(&env, ctx, c.refutation(), &format!("QF_UF {label}"));
        }
    }

    if zero_trust.is_some() {
        assert!(
            unlimited.is_some(),
            "QF_UF: zero-trust accepted but unlimited rejected — inconsistent"
        );
    }
}

#[test]
fn test_2386_replacement_gate_qf_lia() {
    let env = mk_qf_lia_env();
    let (mut backend, map, [h_x_neg_id, h_x_pos_id], lt_x_0, lt_0_x) =
        mk_qf_lia_backend_and_mapping();

    let (proof_present, _native_complete, unlimited, zero_trust) =
        evaluate_gate_case(&mut backend, &map, &neg_false());

    assert!(proof_present, "QF_LIA: proof must be present");

    for (label, candidate) in [("unlimited", &unlimited), ("zero_trust", &zero_trust)] {
        if let Some(c) = candidate {
            let mut ctx = LocalContext::new();
            ctx.push_with_id(
                h_x_neg_id,
                Name::from_string("h_x_neg"),
                lt_x_0.clone(),
                BinderInfo::Default,
            );
            ctx.push_with_id(
                h_x_pos_id,
                Name::from_string("h_x_pos"),
                lt_0_x.clone(),
                BinderInfo::Default,
            );
            assert_proof_type_checks_to_false(
                &env,
                ctx,
                c.refutation(),
                &format!("QF_LIA {label}"),
            );
        }
    }

    if zero_trust.is_some() {
        assert!(
            unlimited.is_some(),
            "QF_LIA: zero-trust accepted but unlimited rejected — inconsistent"
        );
    }
}
