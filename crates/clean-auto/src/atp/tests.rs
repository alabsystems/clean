// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the ATP module: TPTP parsing, clausification, and proving.

use super::runner::{AtpConfig, AtpRunner};
use super::szs::SzsStatus;
use super::tptp_parser::{parse_tptp, FofFormula, FofTerm, TptpRole};

// ---------------------------------------------------------------------------
// TPTP Parser Tests
// ---------------------------------------------------------------------------

#[test]
fn test_parse_cnf_simple_clause() {
    let input = "cnf(c1, axiom, p(X) | ~q(X)).";
    let problem = parse_tptp(input).expect("should parse CNF clause");
    assert_eq!(problem.formulas.len(), 1);
    assert_eq!(problem.formulas[0]._name, "c1");
    assert_eq!(problem.formulas[0].role, TptpRole::Axiom);
    assert!(problem.formulas[0].is_cnf);
}

#[test]
fn test_parse_fof_conjecture() {
    let input = r#"
        fof(ax1, axiom, ![X]: (p(X) => q(X))).
        fof(ax2, axiom, p(a)).
        fof(goal, conjecture, q(a)).
    "#;
    let problem = parse_tptp(input).expect("should parse FOF problem");
    assert_eq!(problem.formulas.len(), 3);
    assert_eq!(problem.formulas[2].role, TptpRole::Conjecture);
    assert!(problem.has_conjecture());
}

#[test]
fn test_parse_equality() {
    let input = "fof(eq1, axiom, a = b).";
    let problem = parse_tptp(input).expect("should parse equality");
    assert_eq!(problem.formulas.len(), 1);
    match &problem.formulas[0].formula {
        FofFormula::Equal(FofTerm::Func(a, a_args), FofTerm::Func(b, b_args)) => {
            assert_eq!(a, "a");
            assert_eq!(b, "b");
            assert!(a_args.is_empty());
            assert!(b_args.is_empty());
        }
        other => panic!("expected equality, got {other:?}"),
    }
}

#[test]
fn test_parse_disequality() {
    let input = "fof(neq1, axiom, a != b).";
    let problem = parse_tptp(input).expect("should parse disequality");
    match &problem.formulas[0].formula {
        FofFormula::NotEqual(_, _) => {}
        other => panic!("expected disequality, got {other:?}"),
    }
}

#[test]
fn test_parse_comments() {
    let input = r#"
        % This is a comment
        fof(ax1, axiom, p(a)).
        /* Block comment */
        fof(ax2, axiom, q(b)).
    "#;
    let problem = parse_tptp(input).expect("should skip comments");
    assert_eq!(problem.formulas.len(), 2);
}

#[test]
fn test_parse_quantifiers() {
    let input = "fof(q1, axiom, ![X]: ?[Y]: r(X, Y)).";
    let problem = parse_tptp(input).expect("should parse quantifiers");
    match &problem.formulas[0].formula {
        FofFormula::Forall(vs, body) => {
            assert_eq!(vs, &["X"]);
            match body.as_ref() {
                FofFormula::Exists(vs2, _) => {
                    assert_eq!(vs2, &["Y"]);
                }
                other => panic!("expected Exists, got {other:?}"),
            }
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

#[test]
fn test_parse_iff_and_implies() {
    let input = "fof(i1, axiom, (p <=> q) => r).";
    let problem = parse_tptp(input).expect("should parse iff and implies");
    match &problem.formulas[0].formula {
        FofFormula::Implies(_, _) => {}
        other => panic!("expected Implies, got {other:?}"),
    }
}

#[test]
fn test_parse_true_false() {
    let input = "fof(tf, axiom, $true & ~$false).";
    let problem = parse_tptp(input).expect("should parse $true and $false");
    match &problem.formulas[0].formula {
        FofFormula::And(left, right) => {
            assert_eq!(**left, FofFormula::True);
            match right.as_ref() {
                FofFormula::Not(inner) => assert_eq!(**inner, FofFormula::False),
                other => panic!("expected Not(False), got {other:?}"),
            }
        }
        other => panic!("expected And, got {other:?}"),
    }
}

#[test]
fn test_parse_negated_conjecture() {
    let input = "cnf(nc1, negated_conjecture, ~p(a)).";
    let problem = parse_tptp(input).expect("should parse negated_conjecture");
    assert_eq!(problem.formulas[0].role, TptpRole::NegatedConjecture);
}

// ---------------------------------------------------------------------------
// ATP Runner Tests
// ---------------------------------------------------------------------------

#[test]
fn test_atp_simple_cnf_unsat() {
    // p(a), ~p(X) | q(X), ~q(a) => contradiction
    let input = r#"
        cnf(c1, axiom, p(a)).
        cnf(c2, axiom, ~p(X) | q(X)).
        cnf(c3, axiom, ~q(a)).
    "#;
    let config = AtpConfig {
        max_iterations: 10_000,
        problem_name: "test_unsat".to_string(),
        ..AtpConfig::default()
    };
    let runner = AtpRunner::new(config);
    let result = runner.run(input).expect("should succeed");
    assert_eq!(result.status, SzsStatus::Unsatisfiable);
    assert!(result.output.contains("SZS status Unsatisfiable"));
}

#[test]
fn test_atp_fof_theorem() {
    // If p(a) and forall X: p(X) => q(X), then q(a)
    let input = r#"
        fof(ax1, axiom, p(a)).
        fof(ax2, axiom, ![X]: (p(X) => q(X))).
        fof(goal, conjecture, q(a)).
    "#;
    let config = AtpConfig {
        max_iterations: 10_000,
        problem_name: "test_fof".to_string(),
        ..AtpConfig::default()
    };
    let runner = AtpRunner::new(config);
    let result = runner.run(input).expect("should succeed");
    assert_eq!(result.status, SzsStatus::Theorem);
    assert!(result.output.contains("SZS status Theorem"));
}

#[test]
fn test_atp_equality_symmetry() {
    // a = b, conjecture: b = a
    let input = r#"
        fof(ax1, axiom, a = b).
        fof(goal, conjecture, b = a).
    "#;
    let config = AtpConfig {
        max_iterations: 10_000,
        problem_name: "test_eq_sym".to_string(),
        ..AtpConfig::default()
    };
    let runner = AtpRunner::new(config);
    let result = runner.run(input).expect("should succeed");
    assert_eq!(result.status, SzsStatus::Theorem);
}

#[test]
fn test_atp_equality_transitivity() {
    // a = b, b = c, conjecture: a = c
    let input = r#"
        fof(ax1, axiom, a = b).
        fof(ax2, axiom, b = c).
        fof(goal, conjecture, a = c).
    "#;
    let config = AtpConfig {
        max_iterations: 10_000,
        problem_name: "test_eq_trans".to_string(),
        ..AtpConfig::default()
    };
    let runner = AtpRunner::new(config);
    let result = runner.run(input).expect("should succeed");
    assert_eq!(result.status, SzsStatus::Theorem);
}

#[test]
fn test_atp_satisfiable_cnf() {
    // p(a) is satisfiable (no contradiction)
    let input = "cnf(c1, axiom, p(a)).";
    let config = AtpConfig {
        max_iterations: 1_000,
        problem_name: "test_sat".to_string(),
        ..AtpConfig::default()
    };
    let runner = AtpRunner::new(config);
    let result = runner.run(input).expect("should succeed");
    assert!(
        result.status == SzsStatus::Satisfiable || result.status == SzsStatus::ResourceOut,
        "expected Satisfiable or ResourceOut, got {:?}",
        result.status
    );
}

#[test]
fn test_atp_congruence() {
    // a = b, conjecture: f(a) = f(b)
    let input = r#"
        fof(ax1, axiom, a = b).
        fof(goal, conjecture, f(a) = f(b)).
    "#;
    let config = AtpConfig {
        max_iterations: 10_000,
        problem_name: "test_congr".to_string(),
        ..AtpConfig::default()
    };
    let runner = AtpRunner::new(config);
    let result = runner.run(input).expect("should succeed");
    assert_eq!(result.status, SzsStatus::Theorem);
}

#[test]
fn test_atp_pelletier_1() {
    // Pelletier problem 1: (p => q) <=> (~q => ~p)
    let input = r#"
        fof(pel1, conjecture, ((p => q) <=> (~q => ~p))).
    "#;
    let config = AtpConfig {
        max_iterations: 50_000,
        problem_name: "PEL001".to_string(),
        ..AtpConfig::default()
    };
    let runner = AtpRunner::new(config);
    let result = runner.run(input).expect("should succeed");
    assert_eq!(result.status, SzsStatus::Theorem);
}

#[test]
fn test_atp_pelletier_4() {
    // Pelletier problem 4: ((p => q) => p) => p  (Peirce's law in classical)
    // Variant: ~((p => q) => p) => ~p is a theorem of classical FOL
    // Actually: ((p => q) => p) => p is a tautology
    let input = r#"
        fof(pel4, conjecture, (((p => q) => p) => p)).
    "#;
    let config = AtpConfig {
        max_iterations: 50_000,
        problem_name: "PEL004".to_string(),
        ..AtpConfig::default()
    };
    let runner = AtpRunner::new(config);
    let result = runner.run(input).expect("should succeed");
    assert_eq!(result.status, SzsStatus::Theorem);
}

#[test]
fn test_atp_empty_clause_direct() {
    // Direct empty clause should be unsatisfiable
    let input = "cnf(empty, axiom, $false).";
    let config = AtpConfig {
        max_iterations: 100,
        problem_name: "test_empty".to_string(),
        ..AtpConfig::default()
    };
    let runner = AtpRunner::new(config);
    let result = runner.run(input).expect("should succeed");
    assert_eq!(result.status, SzsStatus::Unsatisfiable);
}

#[test]
fn test_szs_output_format() {
    let input = r#"
        cnf(c1, axiom, p(a)).
        cnf(c2, axiom, ~p(a)).
    "#;
    let config = AtpConfig {
        max_iterations: 10_000,
        problem_name: "FMT001".to_string(),
        ..AtpConfig::default()
    };
    let runner = AtpRunner::new(config);
    let result = runner.run(input).expect("should succeed");
    assert!(result
        .output
        .contains("% SZS status Unsatisfiable for FMT001"));
    assert!(result
        .output
        .contains("% SZS output start Proof for FMT001"));
    assert!(result.output.contains("% SZS output end Proof for FMT001"));
}

#[test]
fn test_parse_integer_name() {
    let input = "cnf(42, axiom, p(a)).";
    let problem = parse_tptp(input).expect("should parse integer names");
    assert_eq!(problem.formulas[0]._name, "42");
}

#[test]
fn test_parse_multiple_variables_in_quantifier() {
    let input = "fof(q1, axiom, ![X, Y, Z]: r(X, Y, Z)).";
    let problem = parse_tptp(input).expect("should parse multi-var quantifier");
    match &problem.formulas[0].formula {
        FofFormula::Forall(vs, _) => {
            assert_eq!(vs.len(), 3);
            assert_eq!(vs[0], "X");
            assert_eq!(vs[1], "Y");
            assert_eq!(vs[2], "Z");
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}
