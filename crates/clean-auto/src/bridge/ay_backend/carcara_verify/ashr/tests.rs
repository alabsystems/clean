// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use carcara::ast::ProofCommand;

fn admits(width: usize, word: &str, amount: &str) -> bool {
    let problem =
        format!("(set-logic QF_BV) (declare-const b Bool) (declare-const x (_ BitVec {width}))");
    let proof = format!(
        "(step t (cl (= (bvashr {word} {amount}) #b{})) :rule bitblast_ashr)",
        "0".repeat(width)
    );
    let (_, proof, _, mut pool) =
        carcara::parser::parse_instance(&problem, &proof, None, Default::default()).unwrap();
    let ProofCommand::Step(step) = &proof.commands[0] else {
        panic!("step")
    };
    safe_shift(step, &mut pool)
}

#[test]
fn negative_overshift_cannot_certify_a_satisfiable_problem() {
    let problem = "(set-logic QF_BV) (assert (not (= (bvashr #b10 #b10) #b00))) (check-sat)";
    let proof = include_str!("false-negative-overshift.alethe");
    let error = super::super::verify_alethe_proof(problem, proof)
        .expect_err("signed -2 >> 2 is -1, not zero");
    assert!(error
        .to_string()
        .contains("arithmetic shift may overshift a negative operand"));
    let nested = format!("(anchor :step end)\n{proof}\n(step end (cl false) :rule subproof)");
    let error = super::super::verify_alethe_proof(problem, &nested)
        .expect_err("nested steps get the same preflight");
    assert!(error
        .to_string()
        .contains("arithmetic shift may overshift a negative operand"));
}

#[test]
fn domain_guard_agrees_with_exhaustive_partial_bit_vectors() {
    let mut cases = 0;
    for width in 1usize..=5 {
        for pattern in 0..3usize.pow(width as u32) {
            let digits = (0..width)
                .map(|i| (pattern / 3usize.pow(i as u32)) % 3)
                .collect::<Vec<_>>();
            let bits = digits
                .iter()
                .map(|d| ["false", "true", "b"][*d])
                .collect::<Vec<_>>();
            let amount = format!("(@bbterm {})", bits.join(" "));
            let all_below = [false, true].into_iter().all(|b| {
                let value = digits.iter().enumerate().fold(0, |value, (i, d)| {
                    value | (usize::from(*d == 1 || *d == 2 && b) << i)
                });
                value < width
            });
            for sign in ["false", "true", "b"] {
                let mut source = vec!["b"; width];
                source[width - 1] = sign;
                let source = format!("(@bbterm {})", source.join(" "));
                assert_eq!(
                    admits(width, &source, &amount),
                    sign == "false" || all_below,
                    "width={width} pattern={pattern} sign={sign}"
                );
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 1089);
}

#[test]
fn raw_constants_and_bounded_symbolic_amounts_remain_admissible() {
    for value in 0usize..8 {
        for amount in 0usize..8 {
            assert_eq!(
                admits(3, &format!("#b{value:03b}"), &format!("#b{amount:03b}")),
                value < 4 || amount < 3
            );
        }
    }
    assert!(admits(4, "x", "(@bbterm b b false false)"));
    assert!(!admits(3, "x", "(@bbterm b b false)"));
    assert!(admits(1, "x", "#b0"));
    assert!(!admits(1, "x", "#b1"));
}

#[test]
fn pure_definitions_cannot_hide_a_negative_overshift() {
    let problem = "(set-logic QF_BV) (assert (not (= (bvashr #b10 #b10) #b00))) (check-sat)";
    let proof = include_str!("false-negative-overshift.alethe");
    let hidden = format!(
        "(define-fun bad_shift () (_ BitVec 2) (@bbterm false true))\n{}",
        proof.replace("(@bbterm false true)", "bad_shift")
    );
    let error = super::super::verify_alethe_proof(problem, &hidden)
        .expect_err("expanded definitions are inspected");
    assert!(error
        .to_string()
        .contains("arithmetic shift may overshift a negative operand"));
}
