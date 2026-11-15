// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Check the SMT-LIB transport through the real proof-producing AY entry.

use super::*;
use clean_auto::bridge::ay_contract::{AyLogic, AyProofBackend, AyProofResult};

fn integer(value: i128) -> Expr {
    let magnitude = Expr::nat_lit(u64::try_from(value.unsigned_abs()).unwrap());
    if value < 0 {
        Expr::app(
            Expr::const_(Name::from_string("Int.neg"), vec![]),
            magnitude,
        )
    } else {
        magnitude
    }
}

#[test]
fn test_integer_division_proof_transport_rounding_signs_zero_and_large_values() {
    let min = i128::from(i64::MIN);
    for (head, dividend, divisor, expected) in [
        ("Int.div", -7, 2, -3),
        ("Int.ediv", -7, 2, -4),
        ("Int.div", -7, -2, 3),
        ("Int.ediv", -7, -2, 4),
        ("Int.mod", -7, 2, -1),
        ("Int.emod", -7, 2, 1),
        ("Int.mod", -7, -2, -1),
        ("Int.emod", -7, -2, 1),
        ("Int.div", -7, 0, 0),
        ("Int.ediv", -7, 0, 0),
        ("Int.mod", -7, 0, -7),
        ("Int.emod", -7, 0, -7),
        ("Int.div", min, -1, -min),
        ("Int.ediv", min, -1, -min),
        ("Int.mod", min, 0, min),
        ("Int.emod", min, 0, min),
    ] {
        for (claimed, negate, unsat) in [
            (expected, false, false),
            (expected, true, true),
            (expected + 1, false, true),
        ] {
            let mut translator = SmtLibTranslator::new();
            let id = FVarId::new(1);
            let variable = translator.register_fvar(id, SmtSort::Int, Expr::fvar(id));
            let operation = Expr::apps(
                Expr::const_(Name::from_string(head), vec![]),
                [Expr::fvar(id), integer(divisor)],
            );
            let mut claim = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![]),
                [
                    Expr::const_(Name::from_string("Int"), vec![]),
                    operation,
                    integer(claimed),
                ],
            );
            if negate {
                claim = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), claim);
            }
            let formula = translator.translate_expr(&claim).unwrap();
            let dividend = translator.translate_expr(&integer(dividend)).unwrap();
            let mut backend = AyProofBackend::new_with_proofs(AyLogic::QfLia);
            backend.add_raw_declaration(&format!("(declare-const {variable} Int)"));
            backend.assert_formula(&format!("(= {variable} {dividend})"));
            backend.assert_formula(&formula);
            let result = backend.check_sat().unwrap();
            assert!(
                if unsat {
                    matches!(&result, AyProofResult::Unsat { .. })
                } else {
                    matches!(&result, AyProofResult::Sat)
                },
                "{head} {dividend} {divisor}: claimed={claimed}, negate={negate}: {result:?}"
            );
        }
    }
}
