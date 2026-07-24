// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser tests for `<;>` sequential focus combinator and `conv` tactic (#1789).

#![allow(clippy::unwrap_used)]

use super::*;

// ── <;> sequential focus combinator tests ──────────────────────────────

#[test]
fn test_parse_seq_focus_simple() {
    // `simp <;> ring` — apply simp, then ring to every resulting goal
    let expr = Parser::parse_expr("by simp <;> ring").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::SeqFocus(_, lhs, rhs) => {
                    assert!(matches!(lhs.as_ref(), SurfaceTactic::Simp { .. }));
                    assert!(
                        matches!(rhs.as_ref(), SurfaceTactic::Named { ref name, .. } if name == "ring")
                    );
                }
                other => panic!("Expected SeqFocus, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_seq_focus_chain() {
    // `split <;> simp <;> ring` — left-associative chaining
    let expr = Parser::parse_expr("by split <;> simp <;> ring").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::SeqFocus(_, lhs, rhs) => {
                    // Outer: (split <;> simp) <;> ring
                    assert!(
                        matches!(rhs.as_ref(), SurfaceTactic::Named { ref name, .. } if name == "ring")
                    );
                    match lhs.as_ref() {
                        SurfaceTactic::SeqFocus(_, inner_lhs, inner_rhs) => {
                            assert!(
                                matches!(inner_lhs.as_ref(), SurfaceTactic::Named { ref name, .. } if name == "split")
                            );
                            assert!(matches!(inner_rhs.as_ref(), SurfaceTactic::Simp { .. }));
                        }
                        other => panic!("Expected inner SeqFocus, got {other:?}"),
                    }
                }
                other => panic!("Expected SeqFocus, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_seq_focus_with_semicolon_separation() {
    // `constructor; split <;> omega` — semicolon before, <;> in second tactic
    let expr = Parser::parse_expr("by constructor; split <;> omega").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 2, "constructor and split<;>omega");
            assert!(
                matches!(&tactics[0], SurfaceTactic::Named { ref name, .. } if name == "constructor")
            );
            match &tactics[1] {
                SurfaceTactic::SeqFocus(_, lhs, rhs) => {
                    assert!(
                        matches!(lhs.as_ref(), SurfaceTactic::Named { ref name, .. } if name == "split")
                    );
                    assert!(
                        matches!(rhs.as_ref(), SurfaceTactic::Named { ref name, .. } if name == "omega")
                    );
                }
                other => panic!("Expected SeqFocus, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

// ── conv tactic parser tests ───────────────────────────────────────────

#[test]
fn test_parse_conv_goal() {
    let expr = Parser::parse_expr("by conv => rw [h]").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Conv(_, loc, body) => {
                    assert!(matches!(loc, SurfaceTacticLocation::Goal));
                    assert_eq!(body.len(), 1);
                    assert!(matches!(&body[0], SurfaceTactic::Rw(_, _, _)));
                }
                other => panic!("Expected Conv, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_conv_at_hyp() {
    let expr = Parser::parse_expr("by conv at h => simp").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Conv(_, loc, body) => {
                    match loc {
                        SurfaceTacticLocation::Hyps(names) => {
                            assert_eq!(names, &["h"]);
                        }
                        other => panic!("Expected Hyps location, got {other:?}"),
                    }
                    assert_eq!(body.len(), 1);
                    assert!(matches!(&body[0], SurfaceTactic::Simp { .. }));
                }
                other => panic!("Expected Conv, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_conv_at_hyp_and_goal_ascii_turnstile() {
    let expr = Parser::parse_expr("by conv at h |- => simp").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Conv(_, loc, body) => {
                    match loc {
                        SurfaceTacticLocation::HypsAndGoal(names) => {
                            assert_eq!(names, &["h"]);
                        }
                        other => panic!("Expected HypsAndGoal location, got {other:?}"),
                    }
                    assert_eq!(body.len(), 1);
                    assert!(matches!(&body[0], SurfaceTactic::Simp { .. }));
                }
                other => panic!("Expected Conv, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

// ── conv navigation tactic parser tests ─────────────────────────────

#[test]
fn test_parse_conv_lhs() {
    let expr = Parser::parse_expr("by conv => lhs; rw [h]").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Conv(_, _, body) => {
                    assert_eq!(body.len(), 2);
                    assert!(matches!(&body[0], SurfaceTactic::Named { name, .. } if name == "lhs"));
                    assert!(matches!(&body[1], SurfaceTactic::Rw(_, _, _)));
                }
                other => panic!("Expected Conv, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_conv_rhs() {
    let expr = Parser::parse_expr("by conv => rhs; simp").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Conv(_, _, body) => {
                    assert_eq!(body.len(), 2);
                    assert!(matches!(&body[0], SurfaceTactic::Named { name, .. } if name == "rhs"));
                    assert!(matches!(&body[1], SurfaceTactic::Simp { .. }));
                }
                other => panic!("Expected Conv, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_conv_arg() {
    let expr = Parser::parse_expr("by conv => arg 2").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Conv(_, _, body) => {
                    assert_eq!(body.len(), 1);
                    match &body[0] {
                        SurfaceTactic::ConvArg(_, i) => assert_eq!(*i, 2),
                        other => panic!("Expected ConvArg, got {other:?}"),
                    }
                }
                other => panic!("Expected Conv, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_conv_enter() {
    let expr = Parser::parse_expr("by conv => enter [1, x, -2]").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Conv(_, _, body) => {
                    assert_eq!(body.len(), 1);
                    match &body[0] {
                        SurfaceTactic::ConvEnter(_, args) => {
                            assert_eq!(args.len(), 3);
                            assert!(matches!(&args[0], ConvEnterArg::Index(1)));
                            assert!(matches!(&args[1], ConvEnterArg::Name(n) if n == "x"));
                            assert!(matches!(&args[2], ConvEnterArg::Index(-2)));
                        }
                        other => panic!("Expected ConvEnter, got {other:?}"),
                    }
                }
                other => panic!("Expected Conv, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

// ── def_match_body parser tests ─────────────────────────────────────

#[test]
fn test_parse_def_match_single_arm() {
    let decl = Parser::parse_decl("def f | 0 => 1").unwrap();
    match decl {
        SurfaceDecl::Def { name, val, .. } => {
            assert_eq!(name, "f");
            assert!(matches!(*val, SurfaceExpr::PatternMatchLambda(_, _, _)));
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_parse_def_match_multi_arm() {
    let decl = Parser::parse_decl("def f | 0 => 1 | n => n").unwrap();
    match decl {
        SurfaceDecl::Def { name, val, .. } => {
            assert_eq!(name, "f");
            match *val {
                SurfaceExpr::PatternMatchLambda(_, _, ref body) => {
                    if let SurfaceExpr::Match(_, _, _, ref arms) = **body {
                        assert_eq!(arms.len(), 2);
                    } else {
                        panic!("Expected Match inside PatternMatchLambda");
                    }
                }
                other => panic!("Expected PatternMatchLambda, got {other:?}"),
            }
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_parse_def_match_where_syntax() {
    let decl = Parser::parse_decl("def f : Nat -> Nat where | 0 => 1 | n => n").unwrap();
    match decl {
        SurfaceDecl::Def { name, val, .. } => {
            assert_eq!(name, "f");
            assert!(matches!(*val, SurfaceExpr::PatternMatchLambda(_, _, _)));
        }
        other => panic!("Expected Def, got {other:?}"),
    }
}

#[test]
fn test_parse_def_match_missing_arrow_is_loud() {
    let err = Parser::parse_decl("def f | 0")
        .expect_err("a missing equation arrow must not fabricate SyntheticSorry");
    match err {
        ParseError::UnexpectedToken { message, .. } => {
            assert_eq!(message, "expected FatArrow, got Eof");
        }
        other => panic!("Expected UnexpectedToken, got {other:?}"),
    }
}

#[test]
fn test_parse_theorem_match() {
    let decl = Parser::parse_decl("theorem foo : Nat -> Bool | 0 => true | _ => false").unwrap();
    match decl {
        SurfaceDecl::Theorem { name, proof, .. } => {
            assert_eq!(name, "foo");
            assert!(matches!(*proof, SurfaceExpr::PatternMatchLambda(_, _, _)));
        }
        other => panic!("Expected Theorem, got {other:?}"),
    }
}

// ── repeat/try tactic sequence parsing (#1834) ──────────────────────

#[test]
fn test_parse_repeat_tactic_seq() {
    // In Lean 4, `repeat simp; ring` means `repeat (simp; ring)` — the repeat
    // binds the entire tactic sequence.
    let expr = Parser::parse_expr("by repeat simp; ring").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(
                tactics.len(),
                1,
                "should be a single Repeat wrapping the seq"
            );
            match &tactics[0] {
                SurfaceTactic::Repeat(_, tacs) => {
                    // Repeat now directly holds the tactic sequence [simp, ring]
                    assert_eq!(tacs.len(), 2);
                    assert!(matches!(&tacs[0], SurfaceTactic::Simp { .. }));
                    assert!(
                        matches!(&tacs[1], SurfaceTactic::Named { ref name, .. } if name == "ring")
                    );
                }
                other => panic!("Expected Repeat, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_try_tactic_seq() {
    // `try simp; ring` should parse as `try (simp; ring)`
    let expr = Parser::parse_expr("by try simp; ring").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1, "should be a single Try wrapping the seq");
            match &tactics[0] {
                SurfaceTactic::Try(_, tacs) => {
                    // Try now directly holds the tactic sequence [simp, ring]
                    assert_eq!(tacs.len(), 2);
                    assert!(matches!(&tacs[0], SurfaceTactic::Simp { .. }));
                    assert!(
                        matches!(&tacs[1], SurfaceTactic::Named { ref name, .. } if name == "ring")
                    );
                }
                other => panic!("Expected Try, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_repeat_single_tactic_no_paren() {
    // `repeat assumption` should still produce Repeat(Assumption), no wrapping
    let expr = Parser::parse_expr("by repeat assumption").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Repeat(_, tacs) => {
                    assert_eq!(tacs.len(), 1, "single tactic should be a 1-element vec");
                    assert!(
                        matches!(&tacs[0], SurfaceTactic::Named { ref name, .. } if name == "assumption"),
                        "single tactic should be assumption"
                    );
                }
                other => panic!("Expected Repeat, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

// ── cases/induction with-clause alternative parsing (#1836) ─────────

#[test]
fn test_parse_cases_with_alts_tactic_bodies() {
    // Verify that cases with alternatives parses the tactic bodies correctly
    let expr = Parser::parse_expr("by cases n with | zero => simp | succ m => omega").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Cases(_, _target, alts) => {
                    assert_eq!(alts.len(), 2, "should have 2 alternatives");
                    assert_eq!(alts[0].name, "zero");
                    assert_eq!(alts[0].tactics.len(), 1);
                    assert!(matches!(&alts[0].tactics[0], SurfaceTactic::Simp { .. }));
                    assert_eq!(alts[1].name, "succ");
                    assert_eq!(alts[1].args, vec!["m"]);
                    assert_eq!(alts[1].tactics.len(), 1);
                    assert!(
                        matches!(&alts[1].tactics[0], SurfaceTactic::Named { ref name, .. } if name == "omega")
                    );
                }
                other => panic!("Expected Cases, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_induction_with_multi_tactic_alts() {
    // Induction with multi-tactic alternative bodies
    let expr =
        Parser::parse_expr("by induction n with | zero => simp; ring | succ n ih => rw [ih]; simp")
            .unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Induction { alts, .. } => {
                    assert_eq!(alts.len(), 2, "should have 2 alternatives");
                    assert_eq!(alts[0].name, "zero");
                    assert_eq!(
                        alts[0].tactics.len(),
                        2,
                        "zero alt should have 2 tactics (simp; ring)"
                    );
                    assert_eq!(alts[1].name, "succ");
                    assert_eq!(alts[1].args, vec!["n", "ih"]);
                    assert_eq!(
                        alts[1].tactics.len(),
                        2,
                        "succ alt should have 2 tactics (rw [ih]; simp)"
                    );
                }
                other => panic!("Expected Induction, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

// ── match tactic tests (#1789) ──────────────────────────────────────

/// `by match h with | true => exact rfl | false => contradiction`
/// should parse as SurfaceTactic::Match with 2 arms containing tactic sequences
#[test]
fn test_parse_tactic_match_basic() {
    let expr =
        Parser::parse_expr("by match h with | true => exact rfl | false => contradiction").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1, "expected 1 tactic (match)");
            match &tactics[0] {
                SurfaceTactic::Match(_, discrs, arms) => {
                    assert_eq!(discrs.len(), 1, "1 discriminant");
                    assert_eq!(arms.len(), 2, "2 match arms");
                    // First arm: true => exact rfl
                    assert_eq!(arms[0].tactics.len(), 1);
                    assert!(
                        matches!(&arms[0].tactics[0], SurfaceTactic::Named { ref name, .. } if name == "exact"),
                        "first arm body should be exact"
                    );
                    // Second arm: false => contradiction
                    assert_eq!(arms[1].tactics.len(), 1);
                    assert!(
                        matches!(&arms[1].tactics[0], SurfaceTactic::Named { ref name, .. } if name == "contradiction"),
                        "second arm body should be contradiction"
                    );
                }
                other => panic!("Expected Match tactic, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

/// `by match n with | zero => simp; ring | succ => rw [ih]`
/// Multi-tactic arm bodies separated by semicolons
#[test]
fn test_parse_tactic_match_multi_tactic_arms() {
    let expr =
        Parser::parse_expr("by match n with | zero => simp; ring | succ => rw [ih]").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Match(_, discrs, arms) => {
                    assert_eq!(discrs.len(), 1);
                    assert_eq!(arms.len(), 2);
                    // First arm has 2 tactics: simp; ring
                    assert_eq!(arms[0].tactics.len(), 2, "zero arm should have 2 tactics");
                    // Second arm has 1 tactic: rw [ih]
                    assert_eq!(arms[1].tactics.len(), 1, "succ arm should have 1 tactic");
                }
                other => panic!("Expected Match tactic, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}
