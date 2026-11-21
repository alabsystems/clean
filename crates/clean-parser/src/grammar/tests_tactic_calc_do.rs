// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser tests for `calc` and tactic combinator parsing (#1789).
//!
//! Tests that `calc` expressions produce `SurfaceExpr::CalcBlock`
//! and tactic combinators (try, repeat, first, paren, case, etc.)
//! are correctly parsed.
//!
//! Do-notation tests are in `tests_do.rs`.

#![allow(clippy::unwrap_used)]

use super::*;

// ── calc block tests ────────────────────────────────────────────────────

#[test]
fn test_parse_calc_single_step() {
    let expr = Parser::parse_expr("calc a = b := rfl").unwrap();
    match expr {
        SurfaceExpr::CalcBlock(_, steps) => {
            assert_eq!(steps.len(), 1);
            assert!(matches!(&steps[0].proof, SurfaceCalcJustification::Term(_)));
        }
        other => panic!("Expected CalcBlock, got {other:?}"),
    }
}

#[test]
fn test_parse_calc_by_tactic_justification() {
    let expr = Parser::parse_expr("calc a = b := by simp").unwrap();
    match expr {
        SurfaceExpr::CalcBlock(_, steps) => {
            assert_eq!(steps.len(), 1);
            match &steps[0].proof {
                SurfaceCalcJustification::Tactic(tacs) => {
                    assert_eq!(tacs.len(), 1);
                    assert!(matches!(&tacs[0], SurfaceTactic::Simp { .. }));
                }
                other => panic!("Expected Tactic justification, got {other:?}"),
            }
        }
        other => panic!("Expected CalcBlock, got {other:?}"),
    }
}

#[test]
fn test_parse_calc_implicit_rfl() {
    // A calc step without `:=` gets an implicit rfl justification
    let expr = Parser::parse_expr("calc a = a").unwrap();
    match expr {
        SurfaceExpr::CalcBlock(_, steps) => {
            assert_eq!(steps.len(), 1);
            match &steps[0].proof {
                SurfaceCalcJustification::Term(SurfaceExpr::Ident(_, name)) => {
                    assert_eq!(
                        (name).name(),
                        crate::SurfaceName::generated_path("rfl").name()
                    );
                }
                other => panic!("Expected implicit rfl, got {other:?}"),
            }
        }
        other => panic!("Expected CalcBlock, got {other:?}"),
    }
}

/// A multi-step calc whose subsequent `_` step sits to the LEFT of the first
/// step's column must still be parsed as a single block. Mirrors Lean's
/// grammar, where the step list has its own `withPosition`, so the `_` steps
/// align with each other rather than with the first step.
#[test]
fn test_parse_calc_multistep_underscore_left_of_first() {
    let src = "calc a ≤ b := h1\n    _ ≤ c := h2";
    let expr = Parser::parse_expr(src).unwrap();
    match expr {
        SurfaceExpr::CalcBlock(_, steps) => {
            assert_eq!(
                steps.len(),
                2,
                "both calc steps should be captured: {steps:?}"
            );
        }
        other => panic!("Expected CalcBlock, got {other:?}"),
    }
}

/// A three-step calc with the `_` steps aligned below the first step.
#[test]
fn test_parse_calc_three_steps() {
    let src = "calc a ≤ b := h1\n    _ ≤ c := h2\n    _ ≤ d := h3";
    let expr = Parser::parse_expr(src).unwrap();
    match expr {
        SurfaceExpr::CalcBlock(_, steps) => {
            assert_eq!(
                steps.len(),
                3,
                "all three calc steps should be captured: {steps:?}"
            );
        }
        other => panic!("Expected CalcBlock, got {other:?}"),
    }
}

/// Semicolon-separated calc steps on a single line still parse as a multi-step
/// block (regression guard for the step-column re-base).
#[test]
fn test_parse_calc_semicolon_separated_steps() {
    let expr = Parser::parse_expr("calc a = b := rfl; _ = c := rfl").unwrap();
    match expr {
        SurfaceExpr::CalcBlock(_, steps) => {
            assert_eq!(steps.len(), 2, "both semicolon-separated steps: {steps:?}");
        }
        other => panic!("Expected CalcBlock, got {other:?}"),
    }
}

// ── tactic combinator tests ────────────────────────────────────────────

#[test]
fn test_parse_by_try_exact() {
    let expr = Parser::parse_expr("by try exact rfl").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Try(_, tacs) => {
                    assert_eq!(tacs.len(), 1);
                    assert!(
                        matches!(&tacs[0], SurfaceTactic::Named { ref name, .. } if name == "exact")
                    );
                }
                other => panic!("Expected Try, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_repeat_assumption() {
    let expr = Parser::parse_expr("by repeat assumption").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Repeat(_, tacs) => {
                    assert_eq!(tacs.len(), 1);
                    assert!(
                        matches!(&tacs[0], SurfaceTactic::Named { ref name, .. } if name == "assumption")
                    );
                }
                other => panic!("Expected Repeat, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_first_pipe() {
    let expr = Parser::parse_expr("by first | exact rfl | simp | ring").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::First(_, alts) => {
                    assert_eq!(alts.len(), 3);
                }
                other => panic!("Expected First, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_paren() {
    let expr = Parser::parse_expr("by (simp; ring)").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Paren(_, inner) => {
                    assert_eq!(inner.len(), 2);
                    assert!(matches!(&inner[0], SurfaceTactic::Simp { .. }));
                    assert!(
                        matches!(&inner[1], SurfaceTactic::Named { ref name, .. } if name == "ring")
                    );
                }
                other => panic!("Expected Paren, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_case() {
    let expr = Parser::parse_expr("by case succ => simp").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Case(_, name, _binders, body) => {
                    assert_eq!(
                        (name).name(),
                        crate::SurfaceName::generated_path("succ").name()
                    );
                    assert!(!body.is_empty());
                }
                other => panic!("Expected Case, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_unfold() {
    let expr = Parser::parse_expr("by unfold Nat.add").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Named { name, args, .. } => {
                    assert_eq!(name, "unfold");
                    assert_eq!(args.len(), 1);
                    match &args[0] {
                        SurfaceExpr::Ident(_, ident) => assert_eq!(
                            (ident).name(),
                            crate::SurfaceName::generated_path("Nat.add").name()
                        ),
                        other => panic!("Expected Ident arg, got {other:?}"),
                    }
                }
                other => panic!("Expected Named(unfold), got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

/// The names an `unfold` tactic carries, in source order, each with its
/// location arguments.
fn unfold_names_and_locations(tactic: &SurfaceTactic) -> Vec<(String, Vec<String>)> {
    let one = |t: &SurfaceTactic| match t {
        SurfaceTactic::Named { name, args, .. } if name == "unfold" => {
            let spelled: Vec<String> = args
                .iter()
                .map(|arg| match arg {
                    SurfaceExpr::Ident(_, ident) => ident.to_string(),
                    other => panic!("Expected Ident arg, got {other:?}"),
                })
                .collect();
            (spelled[0].clone(), spelled[1..].to_vec())
        }
        other => panic!("Expected Named(unfold), got {other:?}"),
    };
    match tactic {
        SurfaceTactic::Paren(_, inner) => inner.iter().map(one).collect(),
        single => vec![one(single)],
    }
}

/// Lean's `unfold id+`: `unfold a b` unfolds `a`, then `b` (Mathbot's Llvm2 task
/// spells it `unfold loweredAddKernel sourceAddKernel`).
#[test]
fn test_parse_by_unfold_several_names() {
    let expr = Parser::parse_expr("by unfold loweredAddKernel sourceAddKernel").unwrap();
    let SurfaceExpr::ByTactic(_, tactics) = expr else {
        panic!("Expected ByTactic, got {expr:?}");
    };
    assert_eq!(tactics.len(), 1);
    assert_eq!(
        unfold_names_and_locations(&tactics[0]),
        vec![
            ("loweredAddKernel".to_string(), vec![]),
            ("sourceAddKernel".to_string(), vec![]),
        ]
    );
}

/// The hypothesis location belongs to `split`, not to a trailing tactic.
#[test]
fn test_split_location_is_one_tactic_with_an_actual_name_argument() {
    let expr = Parser::parse_expr("by split at h").unwrap();
    let SurfaceExpr::ByTactic(_, tactics) = expr else {
        panic!("expected a tactic block");
    };
    assert_eq!(
        tactics.len(),
        1,
        "the location must not become another tactic"
    );
    let SurfaceTactic::Named { name, args, .. } = &tactics[0] else {
        panic!("expected named split, got {:?}", tactics[0]);
    };
    assert_eq!(name, "split");
    assert_eq!(args.len(), 1);
    assert!(matches!(&args[0], SurfaceExpr::Ident(_, name) if name.to_string() == "h"));
}

/// Every name is unfolded at the one location the tactic names.
#[test]
fn test_parse_by_unfold_several_names_share_the_location() {
    let expr = Parser::parse_expr("by unfold f Nat.g at h ⊢").unwrap();
    let SurfaceExpr::ByTactic(_, tactics) = expr else {
        panic!("Expected ByTactic, got {expr:?}");
    };
    assert_eq!(tactics.len(), 1);
    let at = vec!["h".to_string(), "⊢".to_string()];
    assert_eq!(
        unfold_names_and_locations(&tactics[0]),
        vec![("f".to_string(), at.clone()), ("Nat.g".to_string(), at)]
    );
}

/// The name list ends at the next tactic: a same-column line is a new tactic,
/// and so is a tactic name on the same line after `;`.
#[test]
fn test_parse_by_unfold_names_stop_at_the_next_tactic() {
    let expr =
        Parser::parse_expr("by\n  unfold loweredAddKernel sourceAddKernel\n  rw [Nat.add_assoc]")
            .unwrap();
    let SurfaceExpr::ByTactic(_, tactics) = expr else {
        panic!("Expected ByTactic, got {expr:?}");
    };
    assert_eq!(tactics.len(), 2, "{tactics:?}");
    assert_eq!(unfold_names_and_locations(&tactics[0]).len(), 2);
    assert!(matches!(&tactics[1], SurfaceTactic::Rw(..)), "{tactics:?}");

    let expr = Parser::parse_expr("by\n  unfold f\n  g").unwrap();
    let SurfaceExpr::ByTactic(_, tactics) = expr else {
        panic!("Expected ByTactic, got {expr:?}");
    };
    assert_eq!(
        unfold_names_and_locations(&tactics[0]),
        vec![("f".to_string(), vec![])],
        "a name on the next line at the tactic's column is not unfolded: {tactics:?}"
    );
}

#[test]
fn test_parse_by_revert_clear() {
    let expr = Parser::parse_expr("by revert x; clear y").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 2);
            match &tactics[0] {
                SurfaceTactic::Named { name, args, .. } if name == "revert" => {
                    assert_eq!(args.len(), 1, "revert should have 1 arg, got {:?}", args);
                }
                other => panic!("Expected Named revert, got {other:?}"),
            }
            match &tactics[1] {
                SurfaceTactic::Named { name, args, .. } if name == "clear" => {
                    assert_eq!(args.len(), 1, "clear should have 1 arg, got {:?}", args);
                }
                other => panic!("Expected Named clear, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_subst() {
    let expr = Parser::parse_expr("by subst h").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Named { name, args, .. } if name == "subst" => {
                    assert_eq!(args.len(), 1, "subst should have 1 arg, got {:?}", args);
                }
                other => panic!("Expected Named subst, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_norm_num() {
    let expr = Parser::parse_expr("by norm_num").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            assert!(
                matches!(&tactics[0], SurfaceTactic::Named { ref name, .. } if name == "norm_num")
            );
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_ring() {
    let expr = Parser::parse_expr("by ring").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            assert!(matches!(&tactics[0], SurfaceTactic::Named { ref name, .. } if name == "ring"));
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_linarith() {
    let expr = Parser::parse_expr("by linarith").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            assert!(matches!(&tactics[0], SurfaceTactic::Named { name, .. } if name == "linarith"));
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_aesop() {
    let expr = Parser::parse_expr("by aesop").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            assert!(
                matches!(&tactics[0], SurfaceTactic::Named { ref name, .. } if name == "aesop")
            );
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_tauto() {
    let expr = Parser::parse_expr("by tauto").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            assert!(
                matches!(&tactics[0], SurfaceTactic::Named { ref name, .. } if name == "tauto")
            );
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_simp_at_hyp() {
    let expr = Parser::parse_expr("by simp at h").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Simp { location, .. } => match location {
                    SurfaceTacticLocation::Hyps(names) => {
                        assert_eq!(names, &[crate::SurfaceName::generated_path("h")]);
                    }
                    other => panic!("Expected Hyps location, got {other:?}"),
                },
                other => panic!("Expected Simp, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_simp_at_hyp_and_goal_unicode_turnstile() {
    let expr = Parser::parse_expr("by simp at h ⊢").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Simp { location, .. } => match location {
                    SurfaceTacticLocation::HypsAndGoal(names) => {
                        assert_eq!(names, &[crate::SurfaceName::generated_path("h")]);
                    }
                    other => panic!("Expected HypsAndGoal location, got {other:?}"),
                },
                other => panic!("Expected Simp, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_simp_at_hyp_and_goal_ascii_turnstile() {
    let expr = Parser::parse_expr("by simp at h |-").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Simp { location, .. } => match location {
                    SurfaceTacticLocation::HypsAndGoal(names) => {
                        assert_eq!(names, &[crate::SurfaceName::generated_path("h")]);
                    }
                    other => panic!("Expected HypsAndGoal location, got {other:?}"),
                },
                other => panic!("Expected Simp, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_dsimp_at_hyp_and_goal_turnstile_named_args() {
    let expr = Parser::parse_expr("by dsimp at h ⊢").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Named { name, args, .. } => {
                    assert_eq!(name, "dsimp");
                    assert_eq!(args.len(), 2);
                    assert!(
                        matches!(&args[0], SurfaceExpr::Ident(_, ident) if (ident).name() == crate::SurfaceName::generated_path("h").name())
                    );
                    assert!(
                        matches!(&args[1], SurfaceExpr::Ident(_, ident) if (ident).name() == crate::SurfaceName::generated_path("⊢").name())
                    );
                }
                other => panic!("Expected Named dsimp tactic, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

// ── braced tactic block tests ────────────────────────────────────────

#[test]
fn test_parse_by_braced_single_tactic() {
    // `{ simp }` in tactic mode is tacticSeqBracketed — focuses on first goal
    let expr = Parser::parse_expr("by { simp }").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::FocusBlock(_, inner) => {
                    assert_eq!(inner.len(), 1);
                    assert!(matches!(&inner[0], SurfaceTactic::Simp { .. }));
                }
                other => panic!("Expected FocusBlock (from braces), got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_braced_multi_tactic() {
    let expr = Parser::parse_expr("by { intro h; exact h }").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::FocusBlock(_, inner) => {
                    assert_eq!(inner.len(), 2);
                    assert!(
                        matches!(&inner[0], SurfaceTactic::Named { ref name, .. } if name == "intro")
                    );
                    assert!(
                        matches!(&inner[1], SurfaceTactic::Named { ref name, .. } if name == "exact")
                    );
                }
                other => panic!("Expected FocusBlock (from braces), got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

// ── cdot focus dot tests ─────────────────────────────────────────────

#[test]
fn test_parse_by_cdot_single() {
    // `· simp` focuses on first goal and runs simp
    let expr = Parser::parse_expr("by \u{00b7} simp").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::FocusBlock(_, inner) => {
                    assert_eq!(inner.len(), 1);
                    assert!(matches!(&inner[0], SurfaceTactic::Simp { .. }));
                }
                other => panic!("Expected FocusBlock (from cdot focus), got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_constructor_then_cdots() {
    // `constructor; · exact rfl; · simp`. A bullet's body is a full
    // `tacticSeq` (`cdotTk tacticSeqIndentGt`, `Init/NotationExtra.lean:
    // 320-322`) and `;` separates ITS tactics, so the second bullet is NESTED
    // in the first. The pinned Lean v4.30.0-rc2 on
    // `example : 1 = 1 ∧ True := by constructor; · exact rfl; · simp`
    // reports "1:55: error: No goals to be solved" at the SECOND `·` and
    // leaves `case right` unsolved: the second bullet ran inside the first.
    let expr = Parser::parse_expr("by constructor; \u{00b7} exact rfl; \u{00b7} simp").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 2, "constructor + one cdot-focused block");
            assert!(
                matches!(&tactics[0], SurfaceTactic::Named { ref name, .. } if name == "constructor")
            );
            match &tactics[1] {
                SurfaceTactic::FocusBlock(_, inner) => {
                    assert_eq!(inner.len(), 2, "exact + the nested bullet");
                    assert!(
                        matches!(&inner[0], SurfaceTactic::Named { ref name, .. } if name == "exact")
                    );
                    match &inner[1] {
                        SurfaceTactic::FocusBlock(_, nested) => {
                            assert_eq!(nested.len(), 1);
                            assert!(matches!(&nested[0], SurfaceTactic::Simp { .. }));
                        }
                        other => panic!("Expected the nested cdot FocusBlock, got {other:?}"),
                    }
                }
                other => panic!("Expected FocusBlock for the first cdot, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}
