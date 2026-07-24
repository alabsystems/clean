// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the WhyML VC parser.

use super::*;

const SIMPLE_WHYML: &str = "\
theory ArraySum
  goal sum_nonneg:
    forall n: int. 0 <= n -> sum n >= 0
  goal sum_zero:
    sum 0 = 0
end";

#[test]
fn test_parse_whyml_vcs_simple() {
    let vcs = parse_whyml_vcs(SIMPLE_WHYML).expect("should parse");
    assert_eq!(vcs.len(), 2);
    assert_eq!(vcs[0].name, "ArraySum.sum_nonneg");
    assert_eq!(vcs[1].name, "ArraySum.sum_zero");
    assert!(vcs.iter().all(|vc| vc.status == VcStatus::Unknown));
}

#[test]
fn test_parse_whyml_vcs_source_line() {
    let vcs = parse_whyml_vcs(SIMPLE_WHYML).expect("should parse");
    assert_eq!(vcs[0].source_line, Some(2));
    assert_eq!(vcs[1].source_line, Some(4));
}

#[test]
fn test_parse_whyml_vcs_empty_errors() {
    let result = parse_whyml_vcs("");
    assert!(result.is_err());
    assert!(matches!(result.unwrap_err(), WhymlParseError::EmptyInput));
}

#[test]
fn test_parse_whyml_vcs_no_goals_errors() {
    let result = parse_whyml_vcs("theory Empty\nend");
    assert!(result.is_err());
    assert!(matches!(result.unwrap_err(), WhymlParseError::NoGoals));
}

#[test]
fn test_parse_whyml_vcs_with_source_file() {
    let input = "\
(* file: arrays.mlw *)
theory Test
  goal g1: true
end";
    let vcs = parse_whyml_vcs(input).expect("should parse");
    assert_eq!(vcs[0].source_file.as_deref(), Some("arrays.mlw"));
}

#[test]
fn test_parse_whyml_vcs_standalone_goals() {
    let input = "\
goal standalone_goal:
  0 <= 1";
    let vcs = parse_whyml_vcs(input).expect("should parse");
    assert_eq!(vcs.len(), 1);
    assert_eq!(vcs[0].name, "standalone_goal");
}

#[test]
fn test_parse_whyml_formula_true() {
    let f = parse_whyml_formula("true");
    assert_eq!(f, VcFormula::bool_lit(true));
}

#[test]
fn test_parse_whyml_formula_false() {
    let f = parse_whyml_formula("false");
    assert_eq!(f, VcFormula::bool_lit(false));
}

#[test]
fn test_parse_whyml_formula_integer() {
    let f = parse_whyml_formula("42");
    assert_eq!(f, VcFormula::int_lit(42));
}

#[test]
fn test_parse_whyml_formula_variable() {
    let f = parse_whyml_formula("x");
    assert_eq!(f, VcFormula::var("x"));
}

#[test]
fn test_parse_whyml_formula_implication() {
    let f = parse_whyml_formula("a -> b");
    assert_eq!(f.kind, VcFormulaKind::Implies);
    assert_eq!(f.args.len(), 2);
}

#[test]
fn test_parse_whyml_formula_conjunction() {
    let f = parse_whyml_formula(r"a /\ b");
    assert_eq!(f.kind, VcFormulaKind::And);
    assert_eq!(f.args.len(), 2);
}

#[test]
fn test_parse_whyml_formula_disjunction() {
    let f = parse_whyml_formula(r"a \/ b");
    assert_eq!(f.kind, VcFormulaKind::Or);
    assert_eq!(f.args.len(), 2);
}

#[test]
fn test_parse_whyml_formula_negation() {
    let f = parse_whyml_formula("not x");
    assert_eq!(f.kind, VcFormulaKind::Not);
    assert_eq!(f.args.len(), 1);
}

#[test]
fn test_parse_whyml_formula_equality() {
    let f = parse_whyml_formula("x = 0");
    assert_eq!(f.kind, VcFormulaKind::Eq);
    assert_eq!(f.args.len(), 2);
}

#[test]
fn test_parse_whyml_formula_inequality() {
    let f = parse_whyml_formula("x <> 0");
    assert_eq!(f.kind, VcFormulaKind::Not);
    assert_eq!(f.args.len(), 1);
    assert_eq!(f.args[0].kind, VcFormulaKind::Eq);
}

#[test]
fn test_parse_whyml_formula_le() {
    let f = parse_whyml_formula("0 <= n");
    assert_eq!(f.kind, VcFormulaKind::Le);
    assert_eq!(f.args.len(), 2);
}

#[test]
fn test_parse_whyml_formula_forall() {
    let f = parse_whyml_formula("forall n: int. n >= 0");
    assert_eq!(f.kind, VcFormulaKind::Forall);
    assert_eq!(f.bound_vars, vec!["n"]);
    assert_eq!(f.args.len(), 1);
}

#[test]
fn test_parse_whyml_formula_exists() {
    let f = parse_whyml_formula("exists x: int. x = 0");
    assert_eq!(f.kind, VcFormulaKind::Exists);
    assert_eq!(f.bound_vars, vec!["x"]);
}

#[test]
fn test_parse_whyml_formula_func_app() {
    let f = parse_whyml_formula("sum n");
    assert_eq!(f.kind, VcFormulaKind::FuncApp("sum".to_string()));
    assert_eq!(f.args.len(), 1);
}

#[test]
fn test_extract_whyml_name() {
    assert_eq!(
        extract_whyml_name("theory ArraySum", "theory"),
        Some("ArraySum".to_string())
    );
    assert_eq!(extract_whyml_name("theory", "theory"), None);
}

#[test]
fn test_extract_goal_name() {
    assert_eq!(
        extract_goal_name("goal sum_nonneg:"),
        Some("sum_nonneg".to_string())
    );
    assert_eq!(
        extract_goal_name("goal my_lemma: true"),
        Some("my_lemma".to_string())
    );
}

#[test]
fn test_parse_whyml_bound_vars_simple() {
    let vars = parse_whyml_bound_vars("n: int");
    assert_eq!(vars, vec!["n"]);
}

#[test]
fn test_parse_whyml_bound_vars_multiple() {
    let vars = parse_whyml_bound_vars("x: int, y: bool");
    assert_eq!(vars, vec!["x", "y"]);
}

#[test]
fn test_parse_whyml_bound_vars_compact() {
    let vars = parse_whyml_bound_vars("x y: int");
    assert_eq!(vars, vec!["x", "y"]);
}

#[test]
fn test_make_vc_name_with_theory() {
    assert_eq!(make_vc_name(Some("Theory"), "goal1"), "Theory.goal1");
}

#[test]
fn test_make_vc_name_without_theory() {
    assert_eq!(make_vc_name(None, "goal1"), "goal1");
}

#[test]
fn test_tokenize_whyml() {
    let tokens = tokenize_whyml("f (x + 1) y");
    assert_eq!(tokens, vec!["f", "(x + 1)", "y"]);
}

#[test]
fn test_tokenize_whyml_single() {
    let tokens = tokenize_whyml("x");
    assert_eq!(tokens, vec!["x"]);
}
