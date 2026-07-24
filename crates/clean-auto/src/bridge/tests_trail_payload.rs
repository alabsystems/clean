// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused tests for stored theory payloads in the SMT proof trail (#2442).

use super::super::*;
use super::test_helpers::{make_eq, setup_env};
use crate::smt::TheoryLiteral;
use clean_kernel::name::Name;

fn mk_and(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), a.clone()),
        b.clone(),
    )
}

fn mk_not(expr: &Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), expr.clone())
}

fn make_nat_le(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.le"), vec![]), lhs),
        rhs,
    )
}

#[test]
fn test_trail_conflict_theories_exposes_stored_euf_payload() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    let term_a = bridge
        .translate_term(&a)
        .expect("lhs term should translate before proof reconstruction");
    let term_c = bridge
        .translate_term(&c)
        .expect("rhs term should translate before proof reconstruction");

    let eq_ab = make_eq(ty.clone(), a.clone(), b.clone());
    let eq_bc = make_eq(ty.clone(), b.clone(), c.clone());
    let eq_ac = make_eq(ty, a, c);
    let neq_ac = mk_not(&eq_ac);

    bridge
        .add_hypothesis_with_fvar(&mk_and(&eq_ab, &eq_bc), Some(FVarId::new(910)))
        .expect("conjunctive equality hypothesis should assert");
    bridge
        .add_hypothesis_with_fvar(&neq_ac, Some(FVarId::new(911)))
        .expect("negated equality hypothesis should assert");

    let result = bridge.prove(&eq_ac).expect("equality goal should solve");
    assert!(
        result.is_verified(),
        "trail-guided equality goal should reconstruct a native proof, got {result:?}"
    );

    let conflict_payloads = bridge.trail_conflict_theories();
    assert!(
        conflict_payloads.iter().any(|(theory, lits)| {
            *theory == "EUF" && lits.contains(&TheoryLiteral::Neq(term_a, term_c))
        }),
        "stored trail payload should expose the EUF disequality witness, got {conflict_payloads:?}"
    );
}

#[test]
fn test_trail_conflict_theories_exposes_stored_arithmetic_payload() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    let term_a = bridge
        .translate_term(&a)
        .expect("a should translate before arithmetic proof reconstruction");
    let term_b = bridge
        .translate_term(&b)
        .expect("b should translate before arithmetic proof reconstruction");
    let term_c = bridge
        .translate_term(&c)
        .expect("c should translate before arithmetic proof reconstruction");

    bridge
        .add_hypothesis_with_fvar(&make_nat_le(a.clone(), b.clone()), Some(FVarId::new(920)))
        .expect("left arithmetic hypothesis should assert");
    bridge
        .add_hypothesis_with_fvar(&make_nat_le(b.clone(), c.clone()), Some(FVarId::new(921)))
        .expect("right arithmetic hypothesis should assert");

    let result = bridge
        .prove(&make_nat_le(a, c))
        .expect("arithmetic goal should solve");
    assert!(
        result.is_verified(),
        "arithmetic trail reconstruction should build a native proof, got {result:?}"
    );

    let conflict_payloads = bridge.trail_conflict_theories();
    assert!(
        !conflict_payloads.is_empty(),
        "arithmetic proof should record arithmetic trail payloads"
    );
    assert!(
        conflict_payloads.iter().any(|(theory, lits)| {
            *theory == "LRA"
                && lits.iter().any(|lit| {
                    matches!(lit, TheoryLiteral::Le(lhs, rhs) | TheoryLiteral::Lt(lhs, rhs) if *lhs == term_c && *rhs == term_a)
                })
                && lits.iter().any(|lit| {
                    matches!(lit, TheoryLiteral::Le(lhs, rhs) | TheoryLiteral::Lt(lhs, rhs) if *lhs == term_a && *rhs == term_b)
                })
                && lits.iter().any(|lit| {
                    matches!(lit, TheoryLiteral::Le(lhs, rhs) | TheoryLiteral::Lt(lhs, rhs) if *lhs == term_b && *rhs == term_c)
                })
        }),
        "stored trail payload should expose the arithmetic conflict witness, got {conflict_payloads:?}"
    );
}
