// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::verify_alethe_proof;

const DECLARATIONS: &str = "(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 64) (_ BitVec 8)))
(declare-const b (Array (_ BitVec 64) (_ BitVec 8)))
(declare-const i (_ BitVec 64))
(declare-const j (_ BitVec 64))
(declare-const k (_ BitVec 64))
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))";

fn row_problem(conclusion: &str) -> String {
    format!("{DECLARATIONS}\n(assert (not (= i j)))\n(assert (not {conclusion}))\n(check-sat)")
}

fn row_proof(conclusion: &str, premises: &str) -> String {
    format!("(assume guard (not (= i j)))\n(assume neg (not {conclusion}))\n(step row (cl {conclusion}) :rule arrays_row {premises})\n(step done (cl) :rule resolution :premises (row neg))")
}

#[test]
fn array_read_over_write_checks_64_bit_index_guard() {
    let conclusion = "(= (select (store a i x) j) (select a j))";
    assert!(matches!(
        verify_alethe_proof(
            &row_problem(conclusion),
            &row_proof(conclusion, ":premises (guard)")
        ),
        Ok(true)
    ));
}

#[test]
fn array_read_over_write_rejects_changed_array_index_and_missing_guard() {
    for conclusion in [
        "(= (select (store a i x) j) (select b j))",
        "(= (select (store a i x) j) (select a k))",
        "(= (select (store a i x) k) (select a k))",
    ] {
        assert!(verify_alethe_proof(
            &row_problem(conclusion),
            &row_proof(conclusion, ":premises (guard)")
        )
        .is_err());
    }
    let conclusion = "(= (select (store a i x) j) (select a j))";
    assert!(verify_alethe_proof(&row_problem(conclusion), &row_proof(conclusion, "")).is_err());
    let forged = row_proof(conclusion, ":premises (guard)").replace(
        "(assume guard (not (= i j)))",
        "(assume guard (not (= i k)))",
    );
    assert!(verify_alethe_proof(&row_problem(conclusion), &forged).is_err());
}

#[test]
fn array_read_at_written_index_checks_value_and_index() {
    for (conclusion, valid) in [
        ("(= (select (store a i x) i) x)", true),
        ("(= (select (store a i x) j) x)", false),
        ("(= (select (store a i x) i) y)", false),
    ] {
        let problem = format!("{DECLARATIONS}\n(assert (not {conclusion}))\n(check-sat)");
        let proof = format!("(assume neg (not {conclusion}))\n(step row (cl {conclusion}) :rule arrays_idx)\n(step done (cl) :rule resolution :premises (row neg))");
        let result = verify_alethe_proof(&problem, &proof);
        if valid {
            assert!(matches!(result, Ok(true)));
        } else {
            assert!(result.is_err());
        }
    }
}

#[test]
fn array_proofs_still_reject_holes_and_unknown_rules() {
    let conclusion = "(= (select (store a i x) j) (select a j))";
    let proof = row_proof(conclusion, ":premises (guard)");
    assert!(matches!(
        verify_alethe_proof(
            &row_problem(conclusion),
            &proof.replace(":rule arrays_row", ":rule hole")
        ),
        Ok(false)
    ));
    assert!(verify_alethe_proof(
        &row_problem(conclusion),
        &proof.replace(":rule arrays_row", ":rule unverified_array_row")
    )
    .is_err());
}

// Added in Clean: actual dialect parse/check, not a rule-name probe.
fn lambda_refutation(declarations: &str, read: &str, result: &str, valid: bool) {
    let equality = format!("(= {read} {result})");
    let problem =
        format!("(set-logic ALL)\n{declarations}\n(assert (not {equality}))\n(check-sat)");
    let proof = format!("(assume n (not {equality}))\n(step b (cl {equality}) :rule arrays_lambda)\n(step done (cl) :rule resolution :premises (b n))");
    let checked = verify_alethe_proof(&problem, &proof);
    if valid {
        assert!(
            matches!(checked, Ok(true)),
            "{checked:?}\n{problem}\n{proof}"
        );
    } else {
        assert!(
            checked.is_err(),
            "wrong beta result was accepted: {checked:?}"
        );
    }
}

#[test]
fn array_lambda_beta_checks_actual_substitution_and_capture() {
    lambda_refutation("", "(select (lambda ((x Int)) (+ x 1)) 3)", "(+ 3 1)", true);
    lambda_refutation(
        "",
        "(select (lambda ((x Int)) (+ x 1)) 3)",
        "(+ 3 2)",
        false,
    );
    lambda_refutation(
        "(declare-const y Int)",
        "(select (lambda ((x Int)) (forall ((y Int)) (= x y))) y)",
        "(forall ((z Int)) (= y z))",
        true,
    );
    lambda_refutation(
        "(declare-const y Int)",
        "(select (lambda ((x Int)) (forall ((y Int)) (= x y))) y)",
        "(forall ((y Int)) (= y y))",
        false,
    );
    lambda_refutation(
        "(declare-const y Int)",
        "(select (lambda ((x Int)) (forall ((x Int)) (= x x))) y)",
        "(forall ((z Int)) (= z z))",
        true,
    );
}

#[test]
fn array_lambda_contexts_preserve_aliases_reversal_and_function_lambdas() {
    use carcara::{
        ast::pool::TermPool,
        parser::{Config, Parser},
    };
    let definitions = "(declare-const r (Array Int Int))\n\
        (declare-fun accepts ((Array Int Int)) Bool)\n\
        (define-fun maker () (Array Int Int) (lambda ((x Int)) x))\n\
        (define-fun function-maker () (-> Int Int) (lambda ((x Int)) x))";
    let sources = [
        "(= r (lambda ((x Int)) x))",
        "(= (lambda ((x Int)) x) r)",
        "(let ((f (lambda ((x Int)) x))) (= r f))",
        "(let ((f (lambda ((x Int)) x))) (let ((f (lambda ((x Bool)) 1))) (= (select f true) 1)))",
        "(accepts (lambda ((x Int)) x))",
        "(= (store (lambda ((x Int)) x) 0 1) r)",
        "(= ((as const (Array Int (Array Int Int))) r) (lambda ((x Int)) r))",
        "(= ((as const (Array Int (Array Int Int))) (lambda ((x Int)) x))\n\
            (lambda ((x Int)) (lambda ((y Int)) y)))",
    ];
    for source in sources {
        let mut pool = carcara::ast::pool::PrimitivePool::new();
        let mut parser = Parser::new(
            &mut pool,
            Config::clean_dialect().apply_function_defs(true),
            definitions,
        )
        .unwrap();
        parser.parse_problem().unwrap();
        parser.reset(source).unwrap();
        let term = parser
            .parse_term()
            .unwrap_or_else(|error| panic!("{source}: {error}"));
        drop(parser);
        assert_eq!(*pool.sort(&term), carcara::ast::Sort::Bool);
    }
    let equality = "(= ((lambda ((x Int)) (+ x 1)) 3) (+ 3 1))";
    let problem = format!("(assert (not {equality}))");
    let proof = format!("(assume n (not {equality}))\n(step b (cl {equality}) :rule beta_equiv)\n(step done (cl) :rule resolution :premises (b n))");
    assert!(matches!(verify_alethe_proof(&problem, &proof), Ok(true)));
}

#[test]
fn array_lambda_rejects_mixed_roles_bad_sorts_extra_premises_and_default_axioms() {
    for source in [
        "(declare-const r (Array Int Int)) (assert (= r (lambda ((x Bool)) 0)))",
        "(declare-const r (Array Int Int)) (assert (= r (lambda ((x Int) (y Int)) x)))",
        "(declare-const r (Array Int Int)) (assert (let ((f (lambda ((x Int)) x))) (and (= r f) (= (f 0) 0))))",
    ] {
        let mut pool = carcara::ast::pool::PrimitivePool::new();
        let parsed = carcara::parser::Parser::new(&mut pool, carcara::parser::Config::clean_dialect(), source)
            .and_then(|mut parser| parser.parse_problem());
        assert!(parsed.is_err(), "invalid Array/Function source accepted: {source}");
    }
    lambda_refutation(
        "(declare-fun lambda-array (Int Int) (Array Int Int))",
        "(select (lambda-array 0 0) 0)",
        "0",
        false,
    );
    lambda_refutation(
        "(declare-fun default ((Array Int Int)) Int)",
        "(default (lambda ((x Int)) x))",
        "0",
        false,
    );
    let equality = "(= (select (lambda ((x Int)) x) 0) 0)";
    let problem = format!("(assert true) (assert (not {equality}))");
    let proof = format!("(assume h true)\n(assume n (not {equality}))\n(step b (cl {equality}) :rule arrays_lambda :premises (h))\n(step done (cl) :rule resolution :premises (b n))");
    assert!(verify_alethe_proof(&problem, &proof).is_err());
}

#[test]
fn array_lambda_interval_original_three_premises_have_an_independent_refutation() {
    let lambda = "(lambda ((i Int)) (and (<= (- 2) i) (<= i 1)))";
    for (index, actual, expected, equiv, tail) in [
        ("0", "true", "false", "equiv_pos1", "false (not true)"),
        ("2", "false", "true", "equiv_pos2", "(not true) false"),
    ] {
        // The exact original three formulas of AY's maintained interval case;
        // no lambda axiom is appended to the problem's assumptions.
        let problem = format!(
            "(declare-const r (Array Int Bool)) (declare-const alias (Array Int Bool))\n\
            (assert (= r {lambda}))\n(assert (= alias r))\n\
            (assert (= (select alias {index}) {expected}))"
        );
        let body = format!("(and (<= (- 2) {index}) (<= {index} 1))");
        let proof = format!(
            "\
(assume a0 (= r {lambda}))\n\
(assume a1 (= alias r))\n\
(assume a2 (= (select alias {index}) {expected}))\n\
(step b (cl (= (select {lambda} {index}) {body})) :rule arrays_lambda)\n\
(step e (cl (= {body} {actual})) :rule evaluate)\n\
(step ix (cl (= {index} {index})) :rule eq_reflexive)\n\
(step c0 (cl (= (select r {index}) (select {lambda} {index}))) :rule cong :premises (a0 ix))\n\
(step c1 (cl (= (select alias {index}) (select r {index}))) :rule cong :premises (a1 ix))\n\
(step v (cl (= (select alias {index}) {actual})) :rule trans :premises (c1 c0 b e))\n\
(step s (cl (= {expected} (select alias {index}))) :rule symm :premises (a2))\n\
(step clash (cl (= {expected} {actual})) :rule trans :premises (s v))\n\
(step eq (cl (not (= {expected} {actual})) {tail}) :rule {equiv})\n\
(step q (cl {tail}) :rule resolution :premises (clash eq))\n\
(step t (cl true) :rule true)\n\
(step f (cl false) :rule resolution :premises (q t))\n\
(step nf (cl (not false)) :rule false)\n\
(step done (cl) :rule resolution :premises (f nf))"
        );
        let checked = verify_alethe_proof(&problem, &proof);
        assert!(matches!(&checked, Ok(true)), "{index}: {checked:?}");
        let wrong = proof.replace(":rule arrays_lambda", ":rule hole");
        assert!(matches!(verify_alethe_proof(&problem, &wrong), Ok(false)));
        let withdrawn = problem.replace(
            &format!("(assert (= (select alias {index}) {expected}))"),
            "",
        );
        assert!(
            verify_alethe_proof(&withdrawn, &proof).is_err(),
            "the real contradictory source is required"
        );
    }
}

#[test]
fn array_lambda_indexed_domains_use_native_sort_parsing_without_namespace_adoption() {
    lambda_refutation(
        "",
        "(select (lambda ((x (_ BitVec 8))) x) #x07)",
        "#x07",
        true,
    );
    let source = "(declare-const r (Array (_ BitVec 8) Bool))\n\
        (assert (= r (lambda ((x (_ BitVec (! 8 :named hidden-width)))) true)))";
    let mut pool = carcara::ast::pool::PrimitivePool::new();
    let parsed =
        carcara::parser::Parser::new(&mut pool, carcara::parser::Config::clean_dialect(), source)
            .and_then(|mut parser| parser.parse_problem());
    assert!(
        parsed.is_err(),
        "role lookahead must not adopt :named sort payloads"
    );
}
