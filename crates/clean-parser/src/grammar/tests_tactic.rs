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

/// `*` in a simp lemma list is Lean's "also use every local hypothesis"
/// element. It is not a term, so it must set `use_hypotheses` and stay out of
/// `lemmas` — previously it raised `Unexpected token: Star` and dropped the
/// remainder of the declaration into parser recovery.
#[test]
fn test_parse_simp_star_sets_use_hypotheses() {
    let cases: [(&str, bool, usize); 5] = [
        ("by simp [*]", false, 0),
        ("by simp only [*]", true, 0),
        ("by simp [Nat.add_zero, *]", false, 1),
        ("by simp [*, Nat.add_zero]", false, 1),
        ("by simp [*, Nat.add_zero, Nat.zero_add]", false, 2),
    ];
    for (src, want_only, want_lemmas) in cases {
        let expr = Parser::parse_expr(src).unwrap_or_else(|e| panic!("{src} should parse: {e:?}"));
        let SurfaceExpr::ByTactic(_, tactics) = expr else {
            panic!("{src}: expected ByTactic");
        };
        match &tactics[0] {
            SurfaceTactic::Simp {
                only,
                lemmas,
                use_hypotheses,
                ..
            } => {
                assert!(*use_hypotheses, "{src}: `*` must set use_hypotheses");
                assert_eq!(*only, want_only, "{src}: `only` flag");
                assert_eq!(lemmas.len(), want_lemmas, "{src}: named lemma count");
            }
            other => panic!("{src}: expected Simp, got {other:?}"),
        }
    }
}

/// A star-free lemma list must leave `use_hypotheses` false.
#[test]
fn test_parse_simp_without_star_leaves_use_hypotheses_false() {
    for src in [
        "by simp",
        "by simp [Nat.add_zero]",
        "by simp only [foo, bar]",
    ] {
        let expr = Parser::parse_expr(src).unwrap_or_else(|e| panic!("{src} should parse: {e:?}"));
        let SurfaceExpr::ByTactic(_, tactics) = expr else {
            panic!("{src}: expected ByTactic");
        };
        match &tactics[0] {
            SurfaceTactic::Simp { use_hypotheses, .. } => {
                assert!(
                    !*use_hypotheses,
                    "{src}: no `*`, so use_hypotheses is false"
                );
            }
            other => panic!("{src}: expected Simp, got {other:?}"),
        }
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
fn test_parse_by_rwa_retains_its_focused_closing_mode() {
    let expr = Parser::parse_expr("by rwa [Nat.add_comm]").unwrap();
    match expr {
        SurfaceExpr::ByTactic(_, tactics) => {
            assert_eq!(tactics.len(), 1);
            match &tactics[0] {
                SurfaceTactic::Rwa(_, rules, location) => {
                    assert_eq!(rules.len(), 1);
                    assert!(
                        matches!(location, SurfaceTacticLocation::Goal),
                        "Expected goal location, got {location:?}"
                    );
                }
                other => panic!("Expected focused Rwa, got {other:?}"),
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
                SurfaceTactic::Rwa(_, rules, location) => {
                    assert_eq!(rules.len(), 1);
                    assert!(rules[0].reverse, "`<-` should mark the rule reverse");
                    assert!(matches!(
                        location,
                        SurfaceTacticLocation::Hyps(names)
                            if names.len() == 1 && names[0].is_unescaped_component("k")
                    ));
                }
                other => panic!("Expected Rwa, got {other:?}"),
            }
        }
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_by_rwa_requires_one_hypothesis_after_at() {
    for source in [
        "by rwa [h] at",
        "by rwa [h] at *",
        "by rwa [h] at h1 h2",
        "by rwa [h] at ⊢",
    ] {
        let mut parser = Parser::new(source.strip_prefix("by ").unwrap());
        let error = parser.tactic().expect_err(source);
        assert!(matches!(
            error,
            ParseError::UnexpectedToken { message, .. }
                if message == "expected one hypothesis after `rwa … at`"
        ));

        // `by` deliberately recovers a tactic parse error into a synthetic
        // node. Its public file parser must retain the actual named refusal.
        let file = crate::parse_file_with_diagnostics(&format!("example : True := {source}"))
            .expect("file parser must recover the malformed tactic");
        assert_eq!(file.diagnostics.len(), 1, "{source}");
        let diagnostic = &file.diagnostics[0];
        assert_eq!(diagnostic.tactic.as_deref(), Some("rwa"), "{source}");
        assert!(
            diagnostic
                .message
                .contains("expected one hypothesis after `rwa … at`"),
            "{source}: {diagnostic:?}"
        );
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
                SurfaceTactic::Cases(_, _, _, alts) => {
                    assert_eq!(alts.len(), 2);
                    assert_eq!(
                        (alts[0].name).name(),
                        crate::SurfaceName::generated_path("zero").name()
                    );
                    assert_eq!(
                        (alts[1].name).name(),
                        crate::SurfaceName::generated_path("succ").name()
                    );
                    assert_eq!(alts[1].args, vec![crate::SurfaceName::generated_path("m")]);
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
                    assert_eq!(
                        (alts[0].name).name(),
                        crate::SurfaceName::generated_path("zero").name()
                    );
                    assert_eq!(
                        (alts[1].name).name(),
                        crate::SurfaceName::generated_path("succ").name()
                    );
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
                        matches!(target.as_ref(), SurfaceExpr::Ident(_, name) if (name).name() == crate::SurfaceName::generated_path("n").name()),
                        "target should be the bare ident `n`, got {target:?}"
                    );
                    assert!(using_recursor.is_none(), "no `using` clause expected");
                    assert_eq!(generalizing, &vec![crate::SurfaceName::generated_path("m")]);
                    assert_eq!(alts.len(), 2);
                    assert_eq!(
                        (alts[0].name).name(),
                        crate::SurfaceName::generated_path("zero").name()
                    );
                    assert_eq!(
                        (alts[1].name).name(),
                        crate::SurfaceName::generated_path("succ").name()
                    );
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
                assert_eq!(
                    generalizing,
                    &vec![
                        crate::SurfaceName::generated_path("m"),
                        crate::SurfaceName::generated_path("p")
                    ]
                );
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
                    matches!(target.as_ref(), SurfaceExpr::Ident(_, name) if (name).name() == crate::SurfaceName::generated_path("n").name()),
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
                            matches!(base.as_ref(), SurfaceExpr::Ident(_, n) if (n).name() == crate::SurfaceName::generated_path("Nat").name()),
                            "recursor base should be `Nat`, got {base:?}"
                        );
                        assert_eq!(
                            (field).name(),
                            crate::SurfaceName::generated_path("rec").name(),
                            "recursor field should be `rec`"
                        );
                    }
                    SurfaceExpr::Ident(_, name) => {
                        assert_eq!(
                            (name).name(),
                            crate::SurfaceName::generated_path("Nat.rec").name(),
                            "recursor ident should be `Nat.rec`"
                        );
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
                assert_eq!(generalizing, &vec![crate::SurfaceName::generated_path("m")]);
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

#[path = "tests_tactic_indentation.rs"]
mod indentation;

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

// ====================================================================
// `prefix:max` heads an application; a sort keyword heads a dotted NAME.
// ===========================================================================

/// `prefix:$prec $op => $f` expands to `notation:$prec $op arg:$prec => $f arg`
/// (`Lean/Elab/Mixfix.lean`:28-29), so at `max` the operand is a `term:max` — an
/// ATOM, since an application sits at leadPrec 1023 — and the result is itself a
/// max-precedence term, which `app := trailing_parser:leadPrec:maxPrec many1
/// argument` takes as its FUNCTION.
///
/// Clean parsed the operand with a full application, so `↿(f p.1) p.2` became
/// `↿((f p.1) p.2)` and `f p.1 : β` was applied to `p.2`:
/// `Function.hasUncurryInduction` (Mathlib/Logic/Function/Basic.lean) died
/// "function type fvar#1 is not a function type, but 1 argument(s) remain".
/// Ground-truthed on the pinned v4.30.0-rc2, which accepts the shape.
#[test]
fn test_prefix_max_operator_takes_an_atom_and_heads_an_application() {
    let src = "prefix:max \"@@\" => uncurry2\nexample : Nat := @@(g 1) pair\n";
    let report = crate::parse_file(src).expect("the prefix declaration and its use parse");
    let rendered = format!("{report:?}");
    assert!(
        !rendered.contains("RawDecl"),
        "the use must parse, not recover: {rendered}"
    );
}

/// A `prefix` BELOW max keeps its declared level, so its operand is still parsed
/// at that level rather than as an atom — the control for the rule above.
#[test]
fn test_prefix_below_max_keeps_its_declared_operand_level() {
    let src = "prefix:60 \"@@@\" => negate\nexample : Nat := @@@ a * b\n";
    let report = crate::parse_file(src).expect("the prefix declaration and its use parse");
    assert!(!format!("{report:?}").contains("RawDecl"));
}

/// Lean's tokenizer is maximal-munch on identifiers, so only a BARE `Prop` is
/// the sort keyword: `Prop.le` is an ordinary dotted name. Measured on the
/// pinned binary, which accepts `def Prop.le : Nat := 3; def f : Nat := Prop.le`.
/// Clean read the head as the sort and reported "Unknown identifier: le (dot
/// notation on type-valued expression)" — `Mathlib/Order/Basic.lean`'s
/// `instance Prop.le : LE Prop` and every use of it.
#[test]
fn test_sort_keyword_followed_by_a_dot_is_a_dotted_name() {
    for src in [
        "def usesIt : Nat := Prop.le\n",
        "def usesType : Nat := Type.mk2\n",
        "def usesSort : Nat := Sort.x\n",
    ] {
        let report = crate::parse_file(src).expect("a keyword-headed dotted name parses");
        assert!(
            !format!("{report:?}").contains("RawDecl"),
            "must parse as a name: {src}"
        );
    }
}

/// The control: a BARE sort keyword is still the sort, and a dot after
/// whitespace is not part of a name (the adjacency rule `keyword_name_head`
/// owns).
#[test]
fn test_bare_sort_keyword_is_still_the_sort() {
    for src in [
        "example : Prop := True\n",
        "example (p : Prop) : Prop := p\n",
        "example : Type := Nat\n",
    ] {
        let report = crate::parse_file(src).expect("a bare sort keyword parses");
        assert!(!format!("{report:?}").contains("RawDecl"), "{src}");
    }
}

// ── simp argument modifiers (Lean's `simpArg`) ──────────────────────────
//
// `parse_simp_lemmas` opened every element with
// `let _ = self.eat(&TokenKind::LeftArrow) || self.eat(&TokenKind::Minus);`
// — the modifier was consumed and thrown away into a `Vec<SurfaceExpr>` with
// no field to carry it. Downstream that made `simp [← h]` run `h` FORWARD and
// `simp [-h]` *add* the lemma Lean removes, a silent inversion of the request.

/// The lemma list of `by simp only [...]`, or a panic naming what was parsed.
fn simp_args_of(src: &str) -> Vec<crate::surface::SurfaceSimpArg> {
    match Parser::parse_expr(src).unwrap() {
        SurfaceExpr::ByTactic(_, tactics) => match tactics.into_iter().next() {
            Some(SurfaceTactic::Simp { lemmas, .. }) => lemmas,
            other => panic!("Expected Simp, got {other:?}"),
        },
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_simp_plain_argument_carries_no_modifier() {
    let args = simp_args_of("by simp only [foo]");
    assert_eq!(args.len(), 1);
    assert!(!args[0].reverse, "a plain argument is not reversed");
    assert!(!args[0].erase, "a plain argument is not erased");
}

#[test]
fn test_parse_simp_left_arrow_argument_records_reverse() {
    let args = simp_args_of("by simp only [← foo]");
    assert_eq!(args.len(), 1);
    assert!(args[0].reverse, "`←` must be recorded, not eaten");
    assert!(!args[0].erase);
}

#[test]
fn test_parse_simp_ascii_left_arrow_argument_records_reverse() {
    let args = simp_args_of("by simp only [<- foo]");
    assert_eq!(args.len(), 1);
    assert!(args[0].reverse, "`<-` must be recorded, not eaten");
}

#[test]
fn test_parse_simp_minus_argument_records_erase() {
    let args = simp_args_of("by simp only [-foo]");
    assert_eq!(args.len(), 1);
    assert!(args[0].erase, "`-` must be recorded, not eaten");
    assert!(!args[0].reverse);
}

#[test]
fn test_parse_simp_modifiers_are_per_element() {
    let args = simp_args_of("by simp only [a, ← b, -c, d]");
    assert_eq!(args.len(), 4);
    assert_eq!(
        args.iter()
            .map(|a| (a.reverse, a.erase))
            .collect::<Vec<_>>(),
        vec![(false, false), (true, false), (false, true), (false, false)]
    );
}

#[test]
fn test_parse_simp_star_still_parses_beside_a_modified_argument() {
    match Parser::parse_expr("by simp [← a, *]").unwrap() {
        SurfaceExpr::ByTactic(_, tactics) => match tactics.into_iter().next() {
            Some(SurfaceTactic::Simp {
                lemmas,
                use_hypotheses,
                ..
            }) => {
                assert!(use_hypotheses, "`*` must still be recognised");
                assert_eq!(lemmas.len(), 1);
                assert!(lemmas[0].reverse);
            }
            other => panic!("Expected Simp, got {other:?}"),
        },
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_parse_simpa_argument_modifiers_share_the_simp_list() {
    match Parser::parse_expr("by simpa only [← a, -b] using h").unwrap() {
        SurfaceExpr::ByTactic(_, tactics) => match tactics.into_iter().next() {
            Some(SurfaceTactic::Simpa { lemmas, .. }) => {
                assert_eq!(lemmas.len(), 2);
                assert!(lemmas[0].reverse);
                assert!(lemmas[1].erase);
            }
            other => panic!("Expected Simpa, got {other:?}"),
        },
        other => panic!("Expected ByTactic, got {other:?}"),
    }
}

#[test]
fn test_simp_all_keeps_only_and_ordered_erasure() {
    let expr = Parser::parse_expr("by simp_all only [reduceCtorEq, -reduceCtorEq, h]").unwrap();
    let SurfaceExpr::ByTactic(_, tactics) = expr else {
        panic!("expected tactic block")
    };
    assert_eq!(tactics.len(), 1);
    let SurfaceTactic::Simp {
        all,
        only,
        lemmas,
        location,
        ..
    } = &tactics[0]
    else {
        panic!("expected structured simp_all")
    };
    assert!(*all && *only);
    assert!(matches!(location, SurfaceTacticLocation::Goal));
    assert_eq!(lemmas.len(), 3);
    assert!(!lemmas[0].erase && lemmas[1].erase && !lemmas[2].erase);
    for source in ["by simp_all at h", "by simp_all at ⊢"] {
        let mut parser = Parser::new(source.strip_prefix("by ").unwrap());
        let error = parser.tactic().expect_err(source);
        assert!(matches!(error, ParseError::UnexpectedToken { message, .. }
            if message == "simp_all does not take a location"));
        let report = crate::parse_file_with_diagnostics(&format!("example : True := {source}"))
            .expect("file recovery retains the diagnostic");
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].tactic.as_deref(), Some("simp_all"));
        assert!(report.diagnostics[0]
            .message
            .contains("simp_all does not take a location"));
    }
}
