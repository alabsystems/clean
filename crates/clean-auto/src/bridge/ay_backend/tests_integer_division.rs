// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exercise the real AY transport, including a bound symbolic dividend.

#![allow(deprecated)] // The owning host is also covered by the host-parity controls.

use super::translator::LeanExprTranslator;
use ay::Sort;
use ay_translate::{ops, Logic, TermTranslator, TranslationContext};
use clean_kernel::name::Name;
use clean_kernel::{Expr, FVarId};

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
fn test_integer_division_native_ay_rounding_signs_zero_and_large_values() {
    let min = i128::from(i64::MIN);
    let cases = [
        ("Int.div", -7, 2, -3),
        ("Int.ediv", -7, 2, -4),
        ("Int.div", -7, -2, 3),
        ("Int.ediv", -7, -2, 4),
        ("Int.div", 7, -2, -3),
        ("Int.ediv", 7, -2, -3),
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
    ];
    for (head, dividend, divisor, expected) in cases {
        // SAT guards against a translator that merely makes every goal false;
        // both UNSAT arms reject the negated truth and an incorrect result.
        for (claimed, negate, unsat) in [
            (expected, false, false),
            (expected, true, true),
            (expected + 1, false, true),
        ] {
            let tr = LeanExprTranslator::default();
            let mut ctx: TranslationContext<FVarId> = TranslationContext::new(Logic::QfLia);
            let id = FVarId::new(1);
            tr.register_fvar(&mut ctx, id, Sort::Int);
            let variable = tr.translate(&mut ctx, &Expr::fvar(id)).unwrap();
            let value = tr.translate(&mut ctx, &integer(dividend)).unwrap();
            let binding = ops::compare(&mut ctx, ops::Comparison::Eq, variable, value);
            ctx.assert_term(binding);
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
            let term = tr.translate(&mut ctx, &claim).unwrap();
            ctx.assert_term(term);
            let result = ctx.check_sat();
            assert!(
                if unsat {
                    result.is_unsat()
                } else {
                    result.is_sat()
                },
                "{head} {dividend} {divisor}: claimed={claimed}, negate={negate}: {result:?}"
            );
        }
    }
}
