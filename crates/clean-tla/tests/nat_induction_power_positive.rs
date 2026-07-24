// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Test for power_positive benchmark gap
//!
//! Copyright 2026 Andrew Yates
//! Licensed under Apache-2.0

use clean_tla::encoding::{TlaArithOp, TlaCmpOp, TlaExpr, TlaFormula};
use clean_tla::obligation::{TlaDeclare, TlaObligation};
use clean_tla::tactic::prove_tla_obligation_traced;

fn pow_expr(n: TlaExpr, k: TlaExpr) -> TlaExpr {
    TlaExpr::OpApply("pow".to_string(), vec![n, k])
}

#[test]
fn test_nat_induction_power_positive() {
    // Hypothesis: ∀n ∈ Nat. pow(n, 0) = 1
    let pow_base = TlaFormula::ForallIn(
        "n".to_string(),
        Box::new(TlaExpr::Nat),
        Box::new(TlaFormula::Eq(
            Box::new(pow_expr(TlaExpr::Var("n".to_string()), TlaExpr::Int(0))),
            Box::new(TlaExpr::Int(1)),
        )),
    );

    // Hypothesis: ∀n ∈ Nat. ∀k ∈ Nat. pow(n, k+1) = n * pow(n, k)
    let pow_step = TlaFormula::ForallIn(
        "n".to_string(),
        Box::new(TlaExpr::Nat),
        Box::new(TlaFormula::ForallIn(
            "k".to_string(),
            Box::new(TlaExpr::Nat),
            Box::new(TlaFormula::Eq(
                Box::new(pow_expr(
                    TlaExpr::Var("n".to_string()),
                    TlaExpr::Arith(
                        TlaArithOp::Add,
                        Box::new(TlaExpr::Var("k".to_string())),
                        Box::new(TlaExpr::Int(1)),
                    ),
                )),
                Box::new(TlaExpr::Arith(
                    TlaArithOp::Mul,
                    Box::new(TlaExpr::Var("n".to_string())),
                    Box::new(pow_expr(
                        TlaExpr::Var("n".to_string()),
                        TlaExpr::Var("k".to_string()),
                    )),
                )),
            )),
        )),
    );

    // Goal: ∀k ∈ Nat. pow(2, k) > 0
    let goal = TlaFormula::ForallIn(
        "k".to_string(),
        Box::new(TlaExpr::Nat),
        Box::new(TlaFormula::Expr(TlaExpr::Cmp(
            TlaCmpOp::Gt,
            Box::new(pow_expr(TlaExpr::Int(2), TlaExpr::Var("k".to_string()))),
            Box::new(TlaExpr::Int(0)),
        ))),
    );

    let obligation = TlaObligation::new(goal)
        .with_declare(TlaDeclare::Constant {
            name: "pow".to_string(),
            arity: 2,
        })
        .with_hypothesis("pow_base", pow_base)
        .with_hypothesis("pow_step", pow_step)
        .with_tactic("induction");

    let result = prove_tla_obligation_traced(&obligation);
    assert!(
        result.proved,
        "expected power_positive to prove; got error: {:?}",
        result.error
    );
}
