// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser tests for `by` tactic block parsing (#1789).
//!
//! Tests that `by` expressions produce `SurfaceExpr::ByTactic` with correctly
//! parsed `SurfaceTactic` sequences for all major tactic forms.

#![allow(clippy::unwrap_used)]

use super::*;

#[test]
fn test_parse_by_exact() {
    let expr = Parser::parse_expr("by exact rfl").unwrap();
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
fn test_parse_by_apply() {
    let expr = Parser::parse_expr("by apply Nat.add_comm").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            assert!(
                matches!(&tactics[0], SurfaceTactic::Named { ref name, .. } if name == "apply")
            );
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_intro_rfl() {
    let expr = Parser::parse_expr("by intro h; rfl").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 2);
            match &tactics[0] {
                SurfaceTactic::Named { name, args, .. } if name == "intro" => {
                    assert_eq!(args.len(), 1, "intro should have 1 arg, got {:?}", args);
                }
                other => panic!("Expected Named intro, got {other:?}"),
            }
            // Phase 3D.6: rfl now parses as Named (keyword-to-Named routing, #2440)
            match &tactics[1] {
                SurfaceTactic::Named { name, args, .. } if name == "rfl" => {
                    assert!(args.is_empty(), "rfl should have no args");
                }
                other => panic!("Expected Named rfl, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_rfl() {
    let expr = Parser::parse_expr("by rfl").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            // Phase 3D.6: rfl now parses as Named (keyword-to-Named routing, #2440)
            match &tactics[0] {
                SurfaceTactic::Named { name, args, .. } if name == "rfl" => {
                    assert!(args.is_empty(), "rfl should have no args");
                }
                other => panic!("Expected Named rfl, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_simp() {
    let expr = Parser::parse_expr("by simp").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            assert!(matches!(&tactics[0], SurfaceTactic::Simp { .. }));
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_simp_only_with_lemmas() {
    let expr = Parser::parse_expr("by simp only [Nat.add_zero, Nat.zero_add]").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Simp { only, lemmas, .. } => {
                    assert!(only);
                    assert_eq!(lemmas.len(), 2);
                }
                other => panic!("Expected Simp, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_rw() {
    let expr = Parser::parse_expr("by rw [Nat.add_comm]").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Rw(_, rules, _) => assert_eq!(rules.len(), 1),
                other => panic!("Expected Rw, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_rwa_desugars_to_rw_then_assumption() {
    // Lean 4 core: `rwa [r]` is the macro `(rw [r]; assumption)`. The parser
    // desugars it into a parenthesized sequence so it reuses the existing,
    // kernel-checked `rw` and `assumption` handlers.
    let expr = Parser::parse_expr("by rwa [Nat.add_comm]").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Paren(_, inner) => {
                    assert_eq!(inner.len(), 2, "rwa should desugar to two sub-tactics");
                    match &inner[0] {
                        SurfaceTactic::Rw(_, rules, _) => assert_eq!(rules.len(), 1),
                        other => panic!("Expected first sub-tactic to be Rw, got {other:?}"),
                    }
                    assert!(
                        matches!(&inner[1], SurfaceTactic::Named { ref name, .. } if name == "assumption"),
                        "Expected second sub-tactic to be `assumption`, got {:?}",
                        inner[1]
                    );
                }
                other => panic!("Expected Paren (rw; assumption), got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_rwa_reverse_and_location() {
    // `rwa [<- h] at k` must accept the same rule/location grammar as `rw`.
    let expr = Parser::parse_expr("by rwa [<- h] at k").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Paren(_, inner) => {
                    assert_eq!(inner.len(), 2);
                    match &inner[0] {
                        SurfaceTactic::Rw(_, rules, _) => {
                            assert_eq!(rules.len(), 1);
                            assert!(rules[0].reverse, "`<-` should mark the rule reverse");
                        }
                        other => panic!("Expected Rw, got {other:?}"),
                    }
                }
                other => panic!("Expected Paren, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_constructor() {
    let expr = Parser::parse_expr("by constructor").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            assert!(
                matches!(&tactics[0], SurfaceTactic::Named { ref name, .. } if name == "constructor")
            );
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_cases_with_alts() {
    let expr = Parser::parse_expr("by cases n with | zero => rfl | succ m => simp").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Cases(_, _, alts) => {
                    assert_eq!(alts.len(), 2);
                    assert_eq!(alts[0].name, "zero");
                    assert_eq!(alts[1].name, "succ");
                    assert_eq!(alts[1].args, vec!["m"]);
                }
                other => panic!("Expected Cases, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_induction() {
    let expr =
        Parser::parse_expr("by induction n with | zero => rfl | succ ih => exact ih").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Induction { alts, .. } => {
                    assert_eq!(alts.len(), 2);
                    assert_eq!(alts[0].name, "zero");
                    assert_eq!(alts[1].name, "succ");
                }
                other => panic!("Expected Induction, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_induction_generalizing_parses_into_new_fields() {
    // `induction n generalizing m with …` must stop the target parse at
    // `generalizing` (not absorb `generalizing m` as application arguments)
    // and populate the new `generalizing` field with `["m"]`.
    let expr = Parser::parse_expr(
        "by induction n generalizing m with | zero => rfl | succ k ih => exact ih",
    )
    .unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Induction {
                    target,
                    using_recursor,
                    generalizing,
                    alts,
                    ..
                } => {
                    // Target is the bare major premise `n`, not `n generalizing m`.
                    assert!(
                        matches!(target.as_ref(), SurfaceExpr::Ident(_, name) if name == "n"),
                        "target should be the bare ident `n`, got {target:?}"
                    );
                    assert!(using_recursor.is_none(), "no `using` clause expected");
                    assert_eq!(generalizing, &vec!["m".to_string()]);
                    assert_eq!(alts.len(), 2);
                    assert_eq!(alts[0].name, "zero");
                    assert_eq!(alts[1].name, "succ");
                }
                other => panic!("Expected Induction, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_induction_generalizing_multiple_idents() {
    let expr = Parser::parse_expr("by induction n generalizing m p with | zero => rfl").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => match &tactics[0] {
            SurfaceTactic::Induction { generalizing, .. } => {
                assert_eq!(generalizing, &vec!["m".to_string(), "p".to_string()]);
            }
            other => panic!("Expected Induction, got {other:?}"),
        },
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_induction_using_recursor() {
    // `induction n using Nat.rec with …` captures the recursor term and does
    // not swallow `using Nat.rec` into the target application.
    let expr = Parser::parse_expr(
        "by induction n using Nat.rec with | zero => rfl | succ k ih => exact ih",
    )
    .unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => match &tactics[0] {
            SurfaceTactic::Induction {
                target,
                using_recursor,
                generalizing,
                alts,
                ..
            } => {
                assert!(
                    matches!(target.as_ref(), SurfaceExpr::Ident(_, name) if name == "n"),
                    "target should be `n`, got {target:?}"
                );
                let rec = using_recursor
                    .as_ref()
                    .expect("`using` clause should be captured");
                // `Nat.rec` parses as a dotted projection `Nat .rec` (base `Nat`,
                // field `rec`). Confirm the recursor term is captured as that
                // qualified name rather than swallowed into the target.
                match rec.as_ref() {
                    SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
                        assert!(
                            matches!(base.as_ref(), SurfaceExpr::Ident(_, n) if n == "Nat"),
                            "recursor base should be `Nat`, got {base:?}"
                        );
                        assert_eq!(field, "rec", "recursor field should be `rec`");
                    }
                    SurfaceExpr::Ident(_, name) => {
                        assert_eq!(name, "Nat.rec", "recursor ident should be `Nat.rec`");
                    }
                    other => panic!("recursor term should be `Nat.rec`, got {other:?}"),
                }
                assert!(generalizing.is_empty());
                assert_eq!(alts.len(), 2);
            }
            other => panic!("Expected Induction, got {other:?}"),
        },
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_induction_using_and_generalizing_combined() {
    // Lean clause order: `using` before `generalizing`, both before `with`.
    let expr = Parser::parse_expr(
        "by induction n using Nat.rec generalizing m with | zero => rfl | succ k ih => exact ih",
    )
    .unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => match &tactics[0] {
            SurfaceTactic::Induction {
                using_recursor,
                generalizing,
                ..
            } => {
                assert!(using_recursor.is_some(), "`using` clause should be present");
                assert_eq!(generalizing, &vec!["m".to_string()]);
            }
            other => panic!("Expected Induction, got {other:?}"),
        },
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_induction_plain_still_has_empty_clauses() {
    // Control: plain `induction n with …` has no generalizing / using clauses.
    let expr =
        Parser::parse_expr("by induction n with | zero => rfl | succ k ih => exact ih").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => match &tactics[0] {
            SurfaceTactic::Induction {
                using_recursor,
                generalizing,
                alts,
                ..
            } => {
                assert!(using_recursor.is_none());
                assert!(generalizing.is_empty());
                assert_eq!(alts.len(), 2);
            }
            other => panic!("Expected Induction, got {other:?}"),
        },
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_omega() {
    let expr = Parser::parse_expr("by omega").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            assert!(
                matches!(&tactics[0], SurfaceTactic::Named { ref name, .. } if name == "omega")
            );
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_multi_semicolon() {
    let expr = Parser::parse_expr("by intro x; rw [Nat.add_comm]; simp").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 3);
            assert!(
                matches!(&tactics[0], SurfaceTactic::Named { ref name, .. } if name == "intro")
            );
            assert!(matches!(&tactics[1], SurfaceTactic::Rw(_, _, _)));
            assert!(matches!(&tactics[2], SurfaceTactic::Simp { .. }));
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_sorry() {
    let expr = Parser::parse_expr("by sorry").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            assert!(matches!(&tactics[0], SurfaceTactic::Named { name, .. } if name == "sorry"));
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_assumption() {
    let expr = Parser::parse_expr("by assumption").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            assert!(
                matches!(&tactics[0], SurfaceTactic::Named { ref name, .. } if name == "assumption")
            );
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_intro_multiple_names() {
    let expr = Parser::parse_expr("by intro a b c").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Named { name, args, .. } if name == "intro" => {
                    assert_eq!(args.len(), 3, "intro should have 3 args, got {:?}", args);
                }
                other => panic!("Expected Named intro, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_have_then_exact() {
    let expr = Parser::parse_expr("by have h : Nat := 42; exact h").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 2);
            assert!(matches!(&tactics[0], SurfaceTactic::Have(_, _, _, _)));
            assert!(
                matches!(&tactics[1], SurfaceTactic::Named { ref name, .. } if name == "exact")
            );
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_in_theorem() {
    let decls = Parser::parse_file("theorem foo : True := by trivial").unwrap();
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        SurfaceDecl::Theorem { proof, .. } => match proof.as_ref() {
            SurfaceExpr::ByTactic(_, tactics) => {
                assert_eq!(tactics.len(), 1);
                assert!(
                    matches!(&tactics[0], SurfaceTactic::Named { ref name, .. } if name == "trivial")
                );
            }
            other => panic!("Expected ByTactic proof, got {other:?}"),
        },
        other => panic!("Expected Theorem, got {other:?}"),
    }
}

#[test]
fn test_parse_by_left_right() {
    let expr = Parser::parse_expr("by left").unwrap();
    match &expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert!(matches!(&tactics[0], SurfaceTactic::Named { ref name, .. } if name == "left"));
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }

    let expr = Parser::parse_expr("by right").unwrap();
    match &expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert!(
                matches!(&tactics[0], SurfaceTactic::Named { ref name, .. } if name == "right")
            );
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_decide() {
    let expr = Parser::parse_expr("by decide").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert!(
                matches!(&tactics[0], SurfaceTactic::Named { ref name, .. } if name == "decide")
            );
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_contradiction() {
    let expr = Parser::parse_expr("by contradiction").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert!(
                matches!(&tactics[0], SurfaceTactic::Named { ref name, .. } if name == "contradiction")
            );
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_exfalso() {
    let expr = Parser::parse_expr("by exfalso").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert!(
                matches!(&tactics[0], SurfaceTactic::Named { ref name, .. } if name == "exfalso")
            );
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_split() {
    let expr = Parser::parse_expr("by split").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert!(
                matches!(&tactics[0], SurfaceTactic::Named { ref name, .. } if name == "split")
            );
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

// ── Indentation-based block boundary tests (#1798) ───────────────────

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
                &tactics[0]
            );
            assert!(
                matches!(&tactics[1], SurfaceTactic::Named { ref name, .. } if name == "exact"),
                "second tactic should be Exact, got {:?}",
                &tactics[1]
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
                    assert_eq!(name, "h");
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
                &tactics[1]
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
                    assert_eq!(name, "h");
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
                &tactics[1]
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
            assert_eq!(name, "h2");
            // The type must be the bare identifier `p`, NOT an application that
            // swallowed the `by` block.
            assert!(
                matches!(ty.as_ref(), SurfaceExpr::Ident(_, n) if n == "p"),
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
                &proof_tacs[0]
            );
        }
        other => panic!("Expected Suffices, got {other:?}"),
    }
    assert!(
        matches!(&tactics[1], SurfaceTactic::Named { ref name, .. } if name == "exact"),
        "second outer tactic should be `exact`, got {:?}",
        &tactics[1]
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
                    assert_eq!(name, "h");
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
                &tactics[1]
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
                &tactics[1]
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
                    assert_eq!(name, "zero");
                    assert_eq!(tacs.len(), 1, "case zero should have 1 tactic (simp)");
                    assert!(matches!(&tacs[0], SurfaceTactic::Simp { .. }));
                }
                other => panic!("Expected Case, got {other:?}"),
            }
            match &tactics[1] {
                SurfaceTactic::Case(_, name, _binders, tacs) => {
                    assert_eq!(name, "succ");
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

#[test]
fn test_parse_by_injection_with_clause_then_next_tactic() {
    // `injection h with h'` followed by a tactic on the next line previously
    // leaked the `with` clause into the tactic sequence: the generic arg parser
    // stopped at `with`, leaving it for `tactic_seq`, whose term-mode `expr()`
    // then greedily swallowed the *following* `obtain ⟨_, h⟩` and choked
    // mid-pattern → decl-level recovery ("parser recovery produced raw
    // declaration"). This is the `dummy_lower_sound` shape in trust-ir's
    // Semantics/Dialect.lean. The `injection` arm now consumes its own
    // `with <names>` clause (stopping at the newline), so the next tactic is
    // parsed cleanly.
    let src = "by\n  injection h with h'\n  obtain ⟨_, hr⟩ := hc\n  trivial";
    let expr = Parser::parse_expr(src).expect("injection-with then obtain parses");
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(
                tactics.len(),
                3,
                "injection / obtain / trivial are 3 tactics"
            );
            assert!(
                matches!(&tactics[0], SurfaceTactic::Named { name, args, .. }
                    if name == "injection" && args.len() == 1),
                "injection takes only the hypothesis arg; with-names are consumed"
            );
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}
