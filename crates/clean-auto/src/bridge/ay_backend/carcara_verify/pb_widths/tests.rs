// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn truncated_high_bits_cannot_prove_distinct_words_equal() {
    let problem = "(set-logic QF_BV)\n(assert (not (= #b00 #b10)))\n(check-sat)\n";
    let proof = include_str!("truncated-equality.alethe");
    let error = check(problem, proof).expect_err("a satisfiable problem cannot be refuted");
    assert!(error
        .to_string()
        .contains("incomplete or invalid pseudo-Boolean bit expansion"));
}

#[test]
fn complete_word_equality_certificate_still_verifies() {
    let problem = "(set-logic QF_BV)\n(assert (not (= #b00 #b00)))\n(check-sat)\n";
    let proof = include_str!("truncated-equality.alethe")
        .replace("#b10", "#b00")
        .replace("(@pbbterm 0 1)", "(@pbbterm 0 0)")
        .replace("(- 0 0)", "(- (+ 0 (* 2 0)) (+ 0 (* 2 0)))");
    assert!(matches!(check(problem, &proof), Ok(true)));
}

fn admits(rule: &str, source: &str, target: &str) -> bool {
    let problem = "(set-logic QF_BV) (declare-const x (_ BitVec 3)) (declare-const y (_ BitVec 3))";
    let proof = format!("(step t (cl (= {source} {target})) :rule {rule})");
    let Ok((_, proof, _, mut pool)) =
        carcara::parser::parse_instance(problem, &proof, None, Default::default())
    else {
        return false;
    };
    let ProofCommand::Step(step) = &proof.commands[0] else {
        panic!("step");
    };
    complete_expansion(step, &mut pool)
}

#[test]
fn every_comparison_requires_its_exact_unsigned_or_signed_width() {
    for op in [
        "bveq", "bvult", "bvugt", "bvule", "bvuge", "bvslt", "bvsgt", "bvsle", "bvsge",
    ] {
        let signed = op.starts_with("bvs");
        let expected = if signed { 2 } else { 3 };
        for count in 1..=4 {
            let sum = if count == 1 {
                "1".into()
            } else {
                format!(
                    "(+ {})",
                    (0..count).map(|_| "1").collect::<Vec<_>>().join(" ")
                )
            };
            let difference = if signed {
                format!("(+ (- {sum} (* 4 0)) (- (* 4 0) {sum}))")
            } else {
                format!("(- {sum} {sum})")
            };
            let source_op = if op == "bveq" { "=" } else { op };
            let target_op = if op == "bveq" { "=" } else { ">=" };
            assert_eq!(
                admits(
                    &format!("pbblast_{op}"),
                    &format!("({source_op} x y)"),
                    &format!("({target_op} {difference} 0)")
                ),
                count == expected,
                "{op}: {count}"
            );
        }
    }
}

#[test]
fn word_expansions_reject_wrong_lengths_and_wrapping_integer_bits() {
    assert!(admits(
        "pbblast_pbbvar",
        "x",
        "(@pbbterm ((_ @int_of 0) x) ((_ @int_of 1) x) ((_ @int_of 2) x))"
    ));
    assert!(!admits(
        "pbblast_pbbvar",
        "x",
        "(@pbbterm ((_ @int_of 0) x))"
    ));
    assert!(admits("pbblast_pbbconst", "#b101", "(@pbbterm 1 0 1)"));
    for value in ["2", "(- 1)", "4294967296", "4294967297"] {
        assert!(!admits(
            "pbblast_pbbconst",
            "#b101",
            &format!("(@pbbterm 1 0 {value})")
        ));
    }
}

#[test]
fn nested_steps_and_definitions_cannot_hide_truncated_sums() {
    let proof = include_str!("truncated-equality.alethe");
    let proof = format!("(define-fun small () Int 0)\n(anchor :step finish)\n{proof}(step finish (cl (not (not (= #b00 #b10))) false) :rule subproof :discharge (a))")
        .replace("(- 0 0)", "(- small small)");
    let error = check("(set-logic QF_BV)", &proof).expect_err("nested incomplete sum");
    assert!(
        error
            .to_string()
            .contains("incomplete or invalid pseudo-Boolean bit expansion"),
        "{error}"
    );
}

#[test]
fn complete_signed_comparison_uses_lower_bits_and_one_sign_bit() {
    let problem = "(set-logic QF_BV) (assert (not (bvslt #b10 #b00))) (check-sat)";
    let proof = "(assume a (not (bvslt #b10 #b00)))
(step x (cl (= #b10 (@pbbterm 0 1))) :rule pbblast_pbbconst)
(step y (cl (= #b00 (@pbbterm 0 0))) :rule pbblast_pbbconst)
(step conv (cl (= (bvslt #b10 #b00) (bvslt (@pbbterm 0 1) (@pbbterm 0 0)))) :rule cong :premises (x y))
(step pb (cl (= (bvslt (@pbbterm 0 1) (@pbbterm 0 0)) (>= (+ (- 0 (* 2 0)) (- (* 2 1) 0)) 1))) :rule pbblast_bvslt)
(step calc (cl (= (>= (+ (- 0 (* 2 0)) (- (* 2 1) 0)) 1) true)) :rule evaluate)
(step eq (cl (= (bvslt #b10 #b00) true)) :rule trans :premises (conv pb calc))
(step simple (cl (= (= (bvslt #b10 #b00) true) (bvslt #b10 #b00))) :rule equiv_simplify)
(step imp (cl (not (= (bvslt #b10 #b00) true)) (bvslt #b10 #b00)) :rule equiv1 :premises (simple))
(step yes (cl (bvslt #b10 #b00)) :rule resolution :premises (eq imp))
(step done (cl) :rule resolution :premises (a yes))";
    assert!(matches!(check(problem, proof), Ok(true)));
}

#[test]
fn nullary_definition_expansions_and_defining_assertions_both_replay() {
    let problem = "(set-logic QF_UF)(declare-const p Bool)(define-fun alias () Bool p)(assert alias)(assert (not p))(check-sat)";
    let expanded =
        "(assume a p)(assume b (not p))(step done (cl) :rule resolution :premises (a b))";
    assert!(check_with_parser(problem, expanded, Default::default()).is_err());
    assert!(matches!(check(problem, expanded), Ok(true)));
    let defining = "(assume a alias)(assume d (= alias p))(assume b (not p))(step imp (cl (not alias) p) :rule equiv1 :premises (d))(step value (cl p) :rule resolution :premises (a imp))(step done (cl) :rule resolution :premises (value b))";
    assert!(matches!(check(problem, defining), Ok(true)));
    assert!(matches!(
        check_with_parser(problem, defining, Default::default()),
        Ok(true)
    ));
}

#[test]
fn nested_definition_expansion_preserves_source_authority_and_hole_rejection() {
    let problem = "(set-logic QF_UF)(declare-const p Bool)(declare-const unrelated Bool)(define-fun first () Bool p)(define-fun second () Bool first)(assert second)(assert (not p))(check-sat)";
    let proof = "(assume a p)(assume b (not p))(step done (cl) :rule resolution :premises (a b))";
    assert!(matches!(check(problem, proof), Ok(true)));
    for changed in [
        problem.replace("Bool p)", "Bool (not p))"),
        problem.replace("(assert second)", "(assert unrelated)"),
        problem.replace("(assert (not p))", "(assert unrelated)"),
    ] {
        assert!(!matches!(check(&changed, proof), Ok(true)));
    }
    for rule in ["hole", "trust"] {
        assert!(!matches!(
            check(problem, &proof.replace("resolution", rule)),
            Ok(true)
        ));
    }
}

#[test]
fn expanded_problem_definitions_do_not_hide_truncated_bit_sums() {
    let problem = "(set-logic QF_BV)(define-fun low () (_ BitVec 2) #b00)(assert (not (= low #b10)))(check-sat)";
    let proof = include_str!("truncated-equality.alethe");
    for config in [
        carcara::parser::Config::clean_dialect(),
        carcara::parser::Config::clean_dialect().apply_function_defs(true),
    ] {
        let error = check_with_parser(problem, proof, config)
            .expect_err("the complete-width guard applies in each parser mode");
        assert!(error
            .to_string()
            .contains("incomplete or invalid pseudo-Boolean bit expansion"));
    }
    assert!(check(problem, proof).is_err());
}
