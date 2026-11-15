// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Anti-regression for the SILENT tactic-failure class (plan brick T0 / RC-Q,
//! `docs/plans/TACTICS_TO_100_2026-07-29.md`).
//!
//! When a tactic's argument grammar fails, [`Parser::by_body`] recovers the
//! whole block to a `SyntheticSorry`. That is fine — Lean recovers too — but
//! the recovery diagnostic used to carry no hint of WHICH tactic failed, and
//! `clean check` used a parse entry point that discarded recovery diagnostics
//! outright. The observable result was a declaration that failed with the
//! single line `declaration uses synthetic sorry` and **nothing anywhere naming
//! the construct**. 27 of 374 probed tactic invocations behaved that way.
//!
//! These tests lock the two halves of the fix:
//!   1. every tactic-block recovery names the tactic (`diagnostic.tactic`), and
//!      names the OUTERMOST one, not the punctuation it stopped at;
//!   2. `| _ =>` / `| ctor _ =>` case alternatives parse (Lean `binderIdent`),
//!      so they stop being part of the silent class at all.

use crate::surface::{SurfaceDecl, SurfaceExpr, SurfaceTactic};
use crate::{parse_file_with_diagnostics, ParserRecoveryDiagnostic};

fn diagnostics(source: &str) -> Vec<ParserRecoveryDiagnostic> {
    parse_file_with_diagnostics(source)
        .expect("file-level parse must recover, not hard-fail")
        .diagnostics
}

/// The tactic name recorded for the first tactic-block recovery, if any.
fn recovered_tactic(source: &str) -> Option<String> {
    diagnostics(source).into_iter().find_map(|d| d.tactic)
}

#[test]
fn test_tactic_recovery_names_the_failing_tactic() {
    // (source, the tactic the diagnostic must name)
    let cases: &[(&str, &str)] = &[
        ("theorem p (a : Nat) : a = a := by\n  set x := a\n", "set"),
        (
            "theorem p (a : Nat) : a = a := by\n  set x := a with hx\n",
            "set",
        ),
        (
            "theorem p (a : Nat) : a = a := by\n  conv_rhs => rfl\n",
            "conv_rhs",
        ),
        (
            "theorem p (a : Nat) : a = a := by\n  conv_lhs => rfl\n",
            "conv_lhs",
        ),
        (
            "theorem p (a : Nat) : a = a := by\n  conv in a => rfl\n",
            "conv",
        ),
        // `by module` used to sit here; `module` is an identifier now (only
        // the file header reads it as a keyword), so it reaches the
        // elaborator as an unknown tactic and is refused there BY NAME, as
        // Lean 4.8.0 refuses it ("unknown tactic").
        // `simp [*]` used to sit here; it parses since the star element landed,
        // so the `simp` attribution row now uses a lemma list that is still
        // genuinely malformed (a `←` modifier with no lemma after it).
        ("theorem p (a : Nat) : a = a := by\n  simp [←]\n", "simp"),
        // `rcases h with -` used to sit here; `-` parses since the clear
        // pattern landed, so the row uses a tuple with a trailing comma, which
        // Lean refuses too ("unexpected token '⟩'; expected rcasesPat").
        (
            "theorem p (a b : Nat) (h : a = b) : a = b := by\n  rcases h with ⟨a,⟩\n",
            "rcases",
        ),
        (
            "theorem p (a b : Nat) (h : a = b) : a = b := by\n  on_goal 1 => exact h\n",
            "on_goal",
        ),
        ("theorem p (a : Nat) : a = a := by\n  let' x := a\n", "let'"),
        (
            "theorem p (a b : Nat) (h : a = b) : a = b := by\n  rw\n",
            "rw",
        ),
        (
            "theorem p (a b : Nat) (h : a = b) : a = b := by\n  revert\n",
            "revert",
        ),
        (
            "theorem p (a b : Nat) (h : a = b) : a = b := by\n  unfold\n",
            "unfold",
        ),
    ];
    for (source, expected) in cases {
        let named = recovered_tactic(source);
        assert_eq!(
            named.as_deref(),
            Some(*expected),
            "tactic-block recovery must NAME `{expected}`; a recovery with no \
             attribution degrades the declaration to an unattributable synthetic \
             sorry. Source:\n{source}"
        );
    }
}

/// The attribution must survive a stop on a token that is not itself a tactic.
///
/// `set x := a` fails on `:=`. Naming `:=` is useless; the honest answer is
/// `set`, the tactic that under-consumed its arguments.
#[test]
fn test_recovery_attributes_to_tactic_not_punctuation() {
    let diags = diagnostics("theorem p (a : Nat) : a = a := by\n  set x := a\n");
    let diag = diags
        .first()
        .expect("a recovery diagnostic must be recorded");
    assert_eq!(diag.tactic.as_deref(), Some("set"));
    assert!(
        diag.message.contains("unsupported tactic syntax `set`"),
        "message must lead with the tactic, got: {}",
        diag.message
    );
}

/// A nested failure reports the whole chain, outermost first, so the outer
/// tactic is always present even when the inner token is the proximate cause.
#[test]
fn test_recovery_reports_the_nesting_chain() {
    let diags =
        diagnostics("theorem p (a : Nat) : a = a := by\n  simp (config := { decide := true })\n");
    let diag = diags
        .first()
        .expect("a recovery diagnostic must be recorded");
    assert_eq!(
        diag.tactic.as_deref(),
        Some("simp"),
        "the machine-readable attribution must be the OUTERMOST tactic"
    );
    assert!(
        diag.message.contains("`simp`") && diag.message.contains("`config`"),
        "message must show the outer tactic and the inner stop, got: {}",
        diag.message
    );
}

/// A well-formed tactic block records no recovery at all — the diagnostic is
/// not fired speculatively.
#[test]
fn test_clean_tactic_block_records_no_recovery() {
    for source in [
        "theorem p (a b : Nat) (h : a = b) : a = b := by\n  exact h\n",
        "theorem p (b : Bool) : b = b := by\n  cases b with\n  | true => rfl\n  | false => rfl\n",
        "theorem p (a : Nat) : a = a := by\n  simp\n",
    ] {
        assert!(
            diagnostics(source).is_empty(),
            "a well-formed tactic block must record no parser recovery:\n{source}"
        );
    }
}

fn first_tactic(source: &str) -> SurfaceTactic {
    let decls = parse_file_with_diagnostics(source).expect("parse").decls;
    for decl in decls {
        if let SurfaceDecl::Theorem { proof, .. } = decl {
            if let SurfaceExpr::ByTactic(_, tacs) = *proof {
                return tacs.into_iter().next().expect("a tactic");
            }
            panic!("proof did not parse as a `by` block: {proof:?}");
        }
    }
    panic!("no theorem in source");
}

/// Lean's `inductionAlt` names the constructor with `ident <|> hole`, so `_` is
/// a legal alternative name. `expect_ident` rejected it, so the whole block
/// recovered to a synthetic sorry — while the elaborator's
/// `alts.iter().find(|a| a.name == "_")` branch sat there as dead code
/// (plan brick T5b).
#[test]
fn test_wildcard_case_alternative_parses() {
    let tac = first_tactic("theorem p (b : Bool) : b = b := by\n  cases b with\n  | _ => rfl\n");
    let SurfaceTactic::Cases(_, _, _, alts) = tac else {
        panic!("expected Cases, got {tac:?}");
    };
    assert_eq!(alts.len(), 1);
    assert_eq!(
        alts[0].name,
        crate::SurfaceName::generated_path("_"),
        "the wildcard alternative name must be `_`"
    );
}

#[test]
fn test_wildcard_alternative_after_named_alternative_parses() {
    let tac = first_tactic(
        "theorem p (b : Bool) : b = b := by\n  cases b with\n  | true => rfl\n  | _ => rfl\n",
    );
    let SurfaceTactic::Cases(_, _, _, alts) = tac else {
        panic!("expected Cases, got {tac:?}");
    };
    assert_eq!(
        alts.iter().map(|a| a.name.clone()).collect::<Vec<_>>(),
        ["true", "_"]
            .map(crate::SurfaceName::generated_path)
            .to_vec()
    );
}

/// Alternative arguments are `binderIdent*`, so an anonymous `_` binder is
/// legal: `| succ k _ => …`. `parse_ident_list` stopped at the `_`, the
/// following `expect(FatArrow)` failed, and the block recovered silently.
#[test]
fn test_anonymous_binder_in_case_alternative_parses() {
    let tac = first_tactic(
        "theorem p (n : Nat) : n + 0 = n := by\n  induction n with\n  | zero => rfl\n  \
         | succ k _ => rfl\n",
    );
    let SurfaceTactic::Induction { alts, .. } = tac else {
        panic!("expected Induction, got {tac:?}");
    };
    let succ = alts
        .iter()
        .find(|a| (a.name).name() == crate::SurfaceName::generated_path("succ").name())
        .expect("succ alternative");
    assert_eq!(
        succ.args,
        vec![
            crate::SurfaceName::generated_path("k"),
            crate::SurfaceName::generated_path("_")
        ]
    );
}

/// Wildcard alternatives must not silently swallow the block: a wildcard
/// alternative parses AND the block records no recovery.
#[test]
fn test_wildcard_alternative_records_no_recovery() {
    for source in [
        "theorem p (b : Bool) : b = b := by\n  cases b with\n  | _ => rfl\n",
        "theorem p (n : Nat) : n = n := by\n  induction n with\n  | _ => rfl\n",
        "theorem p (n : Nat) : n + 0 = n := by\n  induction n with\n  | zero => rfl\n  \
         | succ k _ => rfl\n",
    ] {
        assert!(
            diagnostics(source).is_empty(),
            "wildcard/anonymous-binder alternative must parse cleanly:\n{source}"
        );
    }
}

#[test]
fn explicit_constructor_case_alternative_preserves_marker_and_binders() {
    let source = "theorem p (w : Word n) : True := by\n  cases w with\n  | nil => trivial\n  | @snoc n w b => trivial\n";
    let parsed = parse_file_with_diagnostics(source).unwrap();
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let SurfaceDecl::Theorem { proof, .. } = &parsed.decls[0] else {
        panic!("theorem")
    };
    let SurfaceExpr::ByTactic(_, tactics) = proof.as_ref() else {
        panic!("tactic proof")
    };
    let SurfaceTactic::Cases(_, _, _, alts) = &tactics[0] else {
        panic!("cases")
    };
    assert!(!alts[0].explicit);
    assert!(alts[1].explicit);
    let expanded = crate::instantiate_tactic_template(tactics, &[], &[], true).unwrap();
    let SurfaceTactic::Cases(_, _, _, expanded_alts) = &expanded[0] else {
        panic!("expanded cases")
    };
    assert!(!expanded_alts[0].explicit);
    assert!(expanded_alts[1].explicit);
    assert_eq!(expanded_alts[1].args.len(), 3);
    assert_eq!(alts[1].name.to_string(), "snoc");
    assert_eq!(
        alts[1]
            .args
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        ["n", "w", "b"]
    );
}

#[test]
fn explicit_wildcard_alternative_is_refused() {
    assert!(!diagnostics("theorem p : True := by cases x with | @_ => trivial").is_empty());
}

#[test]
fn complete_trust_cg_byte_core_source_has_no_parser_recovery() {
    let source = include_str!("../../tests/fixtures/trust_cg_byte_core.lean");
    let parsed = parse_file_with_diagnostics(source).expect("complete source parses");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
}
