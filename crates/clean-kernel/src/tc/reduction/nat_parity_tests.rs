// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::env::{Declaration, Environment, KernelTheory};

fn parity(input: Expr) -> Expr {
    app("Nat.div2Par", [input])
}

#[test]
fn actual_parity_recovers_word_boundaries_and_nested_inputs() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    for (input, expected) in [
        (65_536u128, 0u128),
        (65_537, 1),
        (4_294_967_294, 0),
        (4_294_967_295, 1),
        (18_446_744_073_709_551_614, 0),
        (18_446_744_073_709_551_615, 1),
        (u128::MAX - 1, 0),
        (u128::MAX, 1),
        (0, 0),
        (1, 1),
    ] {
        let term = parity(Expr::nat_lit_u128(input));
        let result = tc.reduce_certified_parity(&term);
        assert_eq!(result, Some(Expr::nat_lit_u128(expected)), "input={input}");
        assert!(tc.is_def_eq(&term, &Expr::nat_lit_u128(expected)));
        assert!(!tc.heartbeat_spent());
    }
    assert!(tc.unary_shift_alias_verified.get());
    let nested = parity(app("Nat.div2", [Expr::nat_lit(u64::MAX)]));
    assert_eq!(tc.reduce_certified_parity(&nested), Some(Expr::nat_lit(1)));
    assert!(tc.parity_reconstruction_verified.get());
}

#[test]
fn open_terms_wrong_levels_and_reentry_never_use_parity_recovery() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    assert!(tc.reduce_certified_parity(&parity(Expr::bvar(0))).is_none());
    let wrong_level = Expr::app(
        Expr::const_(Name::from_string("Nat.div2Par"), vec![Level::zero()]),
        Expr::nat_lit(65_537),
    );
    assert!(tc.reduce_certified_parity(&wrong_level).is_none());
    CHECKING_RECONSTRUCTION.with(|checking| {
        checking.set(true);
        assert!(tc
            .reduce_certified_parity(&parity(Expr::nat_lit(65_537)))
            .is_none());
        let (goal, proof) = reconstruction();
        assert!(!tc.certify_parity_equation(&goal, &proof));
        checking.set(false);
    });
    assert!(!tc.parity_reconstruction_verified.get());
}

#[test]
fn a_logical_foundation_cannot_license_arithmetic_reconstruction() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    let foundation = c("propext");
    let ty = tc
        .infer_type(&foundation)
        .expect("type of the canonical axiom");
    let (goal, proof) = reconstruction();
    let dependent_proof = Expr::app(Expr::lam(BinderInfo::Default, ty, proof), foundation);
    tc.check_type(&dependent_proof, &goal)
        .expect("same true arithmetic reconstruction");
    let audit = env.audit_certification(&goal, &dependent_proof);
    assert!(audit.is_certified());
    assert!(audit.foundations.contains(&Name::from_string("propext")));
    assert!(!tc.certify_parity_equation(&goal, &dependent_proof));
}

#[test]
fn same_proof_cannot_certify_a_changed_parity_result() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    let (goal, proof) = reconstruction();
    tc.check_type(&proof, &goal)
        .expect("actual constructed universal proof");
    assert!(tc.certify_parity_equation(&goal, &proof));
    let n = Expr::bvar(0);
    let half = app("Nat.div2", [n.clone()]);
    let wrong = app(
        "Nat.sub",
        [
            n.clone(),
            app(
                "Nat.add",
                [app("Nat.add", [half.clone(), half]), Expr::nat_lit(1)],
            ),
        ],
    );
    let wrong_goal = Expr::pi(BinderInfo::Default, nat(), eq(parity(n), wrong));
    assert!(!tc.certify_parity_equation(&wrong_goal, &proof));
}

#[test]
fn an_axiom_or_structurally_installed_proof_cannot_authorize_recovery() {
    for structural in [false, true] {
        let mut env = Environment::with_prelude();
        let (goal, proof) = reconstruction();
        let name = Name::from_string("Untrusted.parity_equation");
        if structural {
            env.add_decl_structural(Declaration::Theorem {
                name: name.clone(),
                level_params: vec![],
                type_: goal.clone(),
                value: proof,
            })
            .expect("structural fixture");
        } else {
            env.add_decl(Declaration::Axiom {
                name: name.clone(),
                level_params: vec![],
                type_: goal.clone(),
            })
            .expect("axiom fixture");
        }
        let tc = TypeChecker::new(&env);
        let apparent_proof = Expr::const_(name, vec![]);
        assert!(tc.check_type(&apparent_proof, &goal).is_ok());
        assert!(!tc.certify_parity_equation(&goal, &apparent_proof));
    }
}

#[test]
fn nested_audits_preserve_both_caller_and_ambient_exhaustion() {
    let env = Environment::with_prelude();
    let (goal, proof) = reconstruction();
    let mut tc = TypeChecker::new(&env);
    tc.set_heartbeat_limit(1);
    assert!(!tc.certify_parity_equation(&goal, &proof));
    assert!(tc.heartbeat_spent());
    assert!(!tc.parity_reconstruction_verified.get());

    let saved = crate::tc::declaration_budget_state();
    crate::tc::restore_declaration_budget_state(7, 1);
    let tc = TypeChecker::new(&env);
    assert!(!tc.certify_parity_equation(&goal, &proof));
    assert_eq!(crate::tc::declaration_budget_state(), (7, 0));
    assert!(!tc.parity_reconstruction_verified.get());
    crate::tc::restore_declaration_budget_state(saved.0, saved.1);
}

#[test]
fn theory_changes_forget_certified_parity_reconstruction() {
    let env = Environment::with_prelude();
    let mut tc = TypeChecker::new(&env);
    assert!(tc
        .reduce_certified_parity(&parity(Expr::nat_lit(65_537)))
        .is_some());
    assert!(tc.parity_reconstruction_verified.get());
    tc.set_kernel_theory(KernelTheory::LeanReference);
    assert!(!tc.parity_reconstruction_verified.get());
    assert!(tc
        .reduce_certified_parity(&parity(Expr::nat_lit(65_537)))
        .is_none());
}

#[test]
fn certified_parity_retains_the_reference_primitive_inventory() {
    let mut env = Environment::with_prelude();
    env.set_kernel_theory(KernelTheory::LeanReference);
    let tc = TypeChecker::new(&env);
    for head in [&names::NAT_SHIFT_RIGHT, &names::NAT_ADD, &names::NAT_SUB] {
        assert!(tc.hardwired_fold_admitted(head));
    }
    assert!(!tc.hardwired_fold_admitted(&names::NAT_PRED));
    assert_eq!(
        tc.reduce_certified_parity(&parity(Expr::nat_lit(u64::MAX))),
        Some(Expr::nat_lit(1)),
    );
    assert!(tc.parity_reconstruction_verified.get());
    assert!(tc.unary_shift_alias_verified.get());
    assert!(!tc.heartbeat_spent());
}
