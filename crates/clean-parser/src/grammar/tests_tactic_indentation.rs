// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn alternative_tactic_source(mode: &str, indent: usize) -> String {
    let continuation = " ".repeat(indent);
    let body = if mode == "first" {
        format!("  first\n  | have h : True := True.intro\n{continuation}exact h\n")
    } else {
        format!(
            "  {mode} b with\n  | false =>\n    have h : True := True.intro\n{continuation}exact h\n  | true => exact True.intro\n",
        )
    };
    format!("theorem probe (b : Bool) : True := by\n{body}")
}

fn assert_alternative_tactic_refused(mode: &str) {
    // `skip` is nullary, so the deeper `exact` cannot be a term argument.
    // A deeper identifier after `have ... := term` can instead be part of
    // that term, which is a type error rather than a parser error in Lean.
    let source = alternative_tactic_source(mode, 6)
        .replace("have h : True := True.intro", "skip")
        .replace("exact h", "exact True.intro");
    assert!(
        crate::parse_file_with_tactics_located(&source, &alternative_tactic_patterns()).is_err(),
        "a deeper line must not become a sibling tactic: {source}",
    );
}

fn alternative_tactic_patterns() -> TacticPatterns {
    TacticPatterns::from([
        ("skip".to_string(), TacticArgPattern::Nullary),
        ("exact".to_string(), TacticArgPattern::TermArg),
    ])
}

#[test]
fn test_alternative_tactic_cases_refuses_deeper_sibling() {
    assert_alternative_tactic_refused("cases");
}

#[test]
fn test_alternative_tactic_match_refuses_deeper_sibling() {
    assert_alternative_tactic_refused("match");
}

#[test]
fn test_alternative_tactic_first_refuses_deeper_sibling() {
    assert_alternative_tactic_refused("first");
}

#[test]
fn test_alternative_tactic_aligned_siblings_and_term_continuations() {
    for mode in ["cases", "match", "first"] {
        for source in [
            alternative_tactic_source(mode, 4),
            // This still parses as a term application; elaboration must
            // reject its type instead of demanding a parser refusal.
            alternative_tactic_source(mode, 6),
            alternative_tactic_source(mode, 4)
                .replace("h : True := True.intro", "h : True :=\n      True.intro"),
            alternative_tactic_source(mode, 4).replace(
                "h : True := True.intro",
                "h : True := by\n      exact True.intro",
            ),
            alternative_tactic_source(mode, 4)
                .replace("True.intro\n    exact h", "True.intro; exact h"),
            alternative_tactic_source(mode, 4)
                .replace("True.intro\n    exact h", "True.intro;\n      exact h"),
        ] {
            let decls = crate::parse_file_with_tactics_located(&source, &TacticPatterns::new())
                .expect("aligned siblings and an indented term argument are legal");
            assert!(matches!(decls.as_slice(), [SurfaceDecl::Theorem { .. }]));
        }
    }
}

#[test]
fn test_alternative_tactic_semicolon_separates_only_the_next_sibling() {
    for indent in [4, 6] {
        let source = format!(
            "theorem probe (b : Bool) : True := by\n  cases b with\n  | false =>\n    have h : True := True.intro;\n      skip\n{}exact h\n  | true => exact True.intro\n",
            " ".repeat(indent),
        );
        let parsed =
            crate::parse_file_with_tactics_located(&source, &alternative_tactic_patterns());
        assert_eq!(parsed.is_ok(), indent == 4, "{source}\n{parsed:?}");
    }
}

#[test]
fn test_alternative_tactic_contextual_have_name_and_explicit_rhs() {
    let source = "theorem probe (a : Nat) : a = a := by\n  have split : True ∨ True := Or.inl True.intro\n  cases split with\n  | inl hle =>\n    have h : a = a :=\n      @Eq.refl Nat a\n    exact h\n  | inr h => exact Eq.refl a\n";
    let decls = crate::parse_file_with_tactics_located(source, &TacticPatterns::new())
        .expect("a contextual tactic name is a legal hypothesis name");
    let [SurfaceDecl::Theorem { proof, .. }] = decls.as_slice() else {
        panic!("expected the whole theorem: {decls:?}");
    };
    let SurfaceExpr::ByTactic(_, tactics) = proof.as_ref() else {
        panic!("expected a by proof: {proof:?}");
    };
    assert_eq!(tactics.len(), 2);
    assert!(
        matches!(&tactics[0], SurfaceTactic::Have(_, Some(name), _, _)
        if name.name() == crate::SurfaceName::generated_path("split").name())
    );
    let SurfaceTactic::Cases(_, _, _, alternatives) = &tactics[1] else {
        panic!("expected both cases: {tactics:?}");
    };
    assert_eq!(alternatives.len(), 2);
    assert_eq!(alternatives[0].tactics.len(), 2);
    assert_eq!(alternatives[1].tactics.len(), 1);
}

#[test]
fn test_nested_by_dedent_terminates_inner_block() {
    // Inner `by` block should terminate when `exact h` dedents back to
    // outer block's column. Without indent tracking, inner `by` would
    // greedily consume `exact h`.
    let input = "by\n  have h : P := by\n    exact proof\n  exact h";
    let expr = Parser::parse_expr(input).unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(
                tactics.len(),
                2,
                "outer by should have 2 tactics (have + exact), got {}: {tactics:?}",
                tactics.len()
            );
            assert!(
                matches!(&tactics[0], SurfaceTactic::Have(..)),
                "first tactic should be Have, got {:?}",
                tactics[0]
            );
            assert!(
                matches!(&tactics[1], SurfaceTactic::Named { ref name, .. } if name == "exact"),
                "second tactic should be Exact, got {:?}",
                tactics[1]
            );
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_have_term_proof_dedent_terminates_outer_tactic() {
    let input = "by\n  have h : a = c := calc\n    a = b := h1\n    _ = c := h2\n  exact h";
    let expr = Parser::parse_expr(input).unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(
                tactics.len(),
                2,
                "outer by should have 2 tactics (have + exact), got {}: {tactics:?}",
                tactics.len()
            );
            match &tactics[0] {
                SurfaceTactic::Have(_, Some(name), _, proof) => {
                    assert_eq!(
                        (name).name(),
                        crate::SurfaceName::generated_path("h").name()
                    );
                    match proof.as_ref() {
                        SurfaceTactic::Term(_, expr) => {
                            assert!(matches!(expr.as_ref(), SurfaceExpr::CalcBlock(_, _)));
                        }
                        other => panic!("expected term proof, got {other:?}"),
                    }
                }
                other => panic!("Expected Have, got {other:?}"),
            }
            assert!(
                matches!(&tactics[1], SurfaceTactic::Named { ref name, .. } if name == "exact"),
                "second tactic should be exact, got {:?}",
                tactics[1]
            );
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_tactic_let_value_dedent_terminates_outer_tactic() {
    let input = "by\n  let h : Nat := f x\n  exact h";
    let expr = Parser::parse_expr(input).unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(
                tactics.len(),
                2,
                "outer by should have 2 tactics (let + exact), got {}: {tactics:?}",
                tactics.len()
            );
            match &tactics[0] {
                SurfaceTactic::Let(_, name, _, val) => {
                    assert_eq!(
                        (name).name(),
                        crate::SurfaceName::generated_path("h").name()
                    );
                    match val.as_ref() {
                        SurfaceExpr::App(_, _, args) => {
                            assert_eq!(args.len(), 1, "let value should stay `f x`, got {val:?}");
                        }
                        other => panic!("expected application let value, got {other:?}"),
                    }
                }
                other => panic!("Expected Let, got {other:?}"),
            }
            assert!(
                matches!(&tactics[1], SurfaceTactic::Named { ref name, .. } if name == "exact"),
                "second tactic should be exact, got {:?}",
                tactics[1]
            );
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

/// Regression: the type `T` in `suffices h : T by tac` must stop at the `by`
/// keyword and NOT swallow the trailing `by` block as an application argument.
/// Before the `stop_app_at_by` guard in `parse_tactic_suffices`, the type `p`
/// was parsed as `p (by exact h2)`, consuming the tactic block (and any
/// dedented continuation) as application arguments.
#[test]
fn test_suffices_inline_by_type_not_swallowed() {
    let input = "by\n  suffices h2 : p by exact h2\n  exact h";
    let expr = Parser::parse_expr(input).unwrap();
    let SurfaceExpr::ByTactic(_, tactics) = expr else {
        panic!("Expected ByTactic, got {expr:?}");
    };
    assert_eq!(
        tactics.len(),
        2,
        "outer by should have 2 tactics (suffices + exact), got {}: {tactics:?}",
        tactics.len()
    );
    match &tactics[0] {
        SurfaceTactic::Suffices(_, Some(name), ty, proof_tacs) => {
            assert_eq!(
                (name).name(),
                crate::SurfaceName::generated_path("h2").name()
            );
            // The type must be the bare identifier `p`, NOT an application that
            // swallowed the `by` block.
            assert!(
                matches!(ty.as_ref(), SurfaceExpr::Ident(_, n) if (n).name() == crate::SurfaceName::generated_path("p").name()),
                "suffices type should be the bare `p`, not an app swallowing `by`; got {ty:?}"
            );
            assert_eq!(
                proof_tacs.len(),
                1,
                "expected one proof tactic (`exact h2`)"
            );
            assert!(
                matches!(&proof_tacs[0], SurfaceTactic::Named { name, .. } if name == "exact"),
                "suffices proof tactic should be `exact`, got {:?}",
                proof_tacs[0]
            );
        }
        other => panic!("Expected Suffices, got {other:?}"),
    }
    assert!(
        matches!(&tactics[1], SurfaceTactic::Named { ref name, .. } if name == "exact"),
        "second outer tactic should be `exact`, got {:?}",
        tactics[1]
    );
}

#[test]
fn test_suffices_from_term_dedent_terminates_outer_tactic() {
    let input = "by\n  suffices h : a = c from calc\n    a = b := h1\n    _ = c := h2\n  exact h";
    let expr = Parser::parse_expr(input).unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(
                tactics.len(),
                2,
                "outer by should have 2 tactics (suffices + exact), got {}: {tactics:?}",
                tactics.len()
            );
            match &tactics[0] {
                SurfaceTactic::Suffices(_, Some(name), _, proof_tacs) => {
                    assert_eq!(
                        (name).name(),
                        crate::SurfaceName::generated_path("h").name()
                    );
                    assert_eq!(proof_tacs.len(), 1, "expected one proof tactic");
                    match &proof_tacs[0] {
                        SurfaceTactic::Term(_, expr) => {
                            assert!(matches!(expr.as_ref(), SurfaceExpr::CalcBlock(_, _)));
                        }
                        other => panic!("expected term proof, got {other:?}"),
                    }
                }
                other => panic!("Expected Suffices, got {other:?}"),
            }
            assert!(
                matches!(&tactics[1], SurfaceTactic::Named { ref name, .. } if name == "exact"),
                "second tactic should be exact, got {:?}",
                tactics[1]
            );
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_repeat_dedent_terminates_sub_block() {
    // `repeat` sub-block should terminate when `exact h` dedents past
    // the first tactic column of the repeat block.
    let input = "by\n  repeat\n    simp\n    ring\n  exact h";
    let expr = Parser::parse_expr(input).unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(
                tactics.len(),
                2,
                "outer by should have 2 tactics (repeat + exact), got {}: {tactics:?}",
                tactics.len()
            );
            match &tactics[0] {
                SurfaceTactic::Repeat(_, inner) => {
                    assert_eq!(
                        inner.len(),
                        2,
                        "repeat should contain 2 tactics (simp + ring), got {}: {inner:?}",
                        inner.len()
                    );
                }
                other => panic!("Expected Repeat, got {other:?}"),
            }
            assert!(
                matches!(&tactics[1], SurfaceTactic::Named { ref name, .. } if name == "exact"),
                "second tactic should be Exact, got {:?}",
                tactics[1]
            );
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_all_goals_dedent_terminates_sub_block() {
    let input = "by\n  all_goals\n    simp\n    ring\n  exact h";
    let expr = Parser::parse_expr(input).unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(
                tactics.len(),
                2,
                "outer by should have 2 tactics, got {}: {tactics:?}",
                tactics.len()
            );
            match &tactics[0] {
                SurfaceTactic::AllGoals(_, inner) => {
                    assert_eq!(inner.len(), 2, "all_goals should contain simp + ring");
                }
                other => panic!("Expected AllGoals, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_case_dedent_terminates_sub_block() {
    // Each `case` block should terminate at the dedent where the next
    // `case` starts.
    let input = "by\n  case zero =>\n    simp\n  case succ =>\n    exact h";
    let expr = Parser::parse_expr(input).unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(
                tactics.len(),
                2,
                "outer by should have 2 case tactics, got {}: {tactics:?}",
                tactics.len()
            );
            match &tactics[0] {
                SurfaceTactic::Case(_, name, _binders, tacs) => {
                    assert_eq!(
                        (name).name(),
                        crate::SurfaceName::generated_path("zero").name()
                    );
                    assert_eq!(tacs.len(), 1, "case zero should have 1 tactic (simp)");
                    assert!(matches!(&tacs[0], SurfaceTactic::Simp { .. }));
                }
                other => panic!("Expected Case, got {other:?}"),
            }
            match &tactics[1] {
                SurfaceTactic::Case(_, name, _binders, tacs) => {
                    assert_eq!(
                        (name).name(),
                        crate::SurfaceName::generated_path("succ").name()
                    );
                    assert_eq!(tacs.len(), 1, "case succ should have 1 tactic (exact)");
                }
                other => panic!("Expected Case, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_same_line_tactic_not_affected_by_indent() {
    // Same-line `by exact h` should work regardless of indent tracking.
    // preceded_by_newline is false, so at_dedent never triggers.
    let input = "by exact rfl";
    let expr = Parser::parse_expr(input).unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            assert!(
                matches!(&tactics[0], SurfaceTactic::Named { ref name, .. } if name == "exact")
            );
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_try_dedent_terminates_sub_block() {
    let input = "by\n  try\n    simp\n  exact h";
    let expr = Parser::parse_expr(input).unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(
                tactics.len(),
                2,
                "outer by should have 2 tactics (try + exact), got {}: {tactics:?}",
                tactics.len()
            );
            match &tactics[0] {
                SurfaceTactic::Try(_, inner) => {
                    assert_eq!(inner.len(), 1, "try should contain 1 tactic (simp)");
                }
                other => panic!("Expected Try, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

fn location_hyp_names(tactic: &SurfaceTactic) -> Vec<String> {
    let SurfaceTactic::Named { args, .. } = tactic else {
        panic!("expected a named tactic, got {tactic:?}");
    };
    args.iter()
        .map(|arg| match arg {
            SurfaceExpr::Ident(_, name) => name.to_string(),
            other => panic!("expected a hypothesis name, got {other:?}"),
        })
        .collect()
}

/// Lean's `locationHyp` is `(ppSpace colGt term:max)+`: the names of `at`
/// end at a line that starts at the tactic block's column. `obtain` and
/// `rcases` are neither keywords nor tactic names here, so they used to be
/// read as further hypotheses of `push_neg at h`.
#[test]
fn test_parse_location_hyps_stop_at_the_next_line_of_the_block() {
    for next in ["obtain ⟨x, hx⟩ := h", "rcases h with ⟨x, hx⟩"] {
        let src = format!("by\n  push_neg at h\n  {next}\n  exact ⟨x, hx⟩");
        let expr = Parser::parse_expr(&src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
        let SurfaceExpr::ByTactic(_, tactics) = expr else {
            panic!("expected ByTactic, got {expr:?}");
        };
        assert_eq!(tactics.len(), 3, "{src}: {tactics:?}");
        assert_eq!(
            location_hyp_names(&tactics[0]),
            vec!["h".to_string()],
            "{src}"
        );
    }
}

/// A name on a later line RIGHT of the block's column continues the list,
/// as `colGt` allows.
#[test]
fn test_parse_location_hyps_continue_on_a_deeper_line() {
    let src = "by\n  push_neg at h\n    h2\n  exact h";
    let expr = Parser::parse_expr(src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    let SurfaceExpr::ByTactic(_, tactics) = expr else {
        panic!("expected ByTactic, got {expr:?}");
    };
    assert_eq!(tactics.len(), 2, "{tactics:?}");
    assert_eq!(
        location_hyp_names(&tactics[0]),
        vec!["h".to_string(), "h2".to_string()]
    );
}
