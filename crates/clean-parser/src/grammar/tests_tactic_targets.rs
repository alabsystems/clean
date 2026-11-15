// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parser tests for Lean 4.8 forms trust-ir's `lean/trust_ir-semantics`
//! package uses and Clean failed to parser recovery, each against Lean
//! 4.8.0's grammar (`Init/Tactics.lean`):
//!
//! - `generalize h : e = x at h₁ ⊢` — `generalizeArg,+ (location)?`;
//! - `module` as an identifier — only the module header reads it as a
//!   keyword.
//!
//! Every accepting row has a twin that Lean 4.8.0 also refuses (checked with
//! the pinned toolchain as an oracle). The elaboration half of each row is in
//! `crates/clean-elab/tests/tactic_alt_syntax_e2e/annotated_targets.rs`.

#![allow(clippy::unwrap_used)]

use crate::surface::{SurfaceDecl, SurfaceExpr, SurfaceTactic};

/// The declarations of `src`; no recovery of either kind may have happened.
fn decls_of(src: &str) -> Vec<SurfaceDecl> {
    let report = crate::parse_file_with_diagnostics(src).expect("source should parse");
    assert!(
        report.diagnostics.is_empty(),
        "no parser recovery expected: {:#?}",
        report.diagnostics
    );
    assert_eq!(
        raw_decls(&report.decls),
        0,
        "no recovery placeholder expected: {:#?}",
        report.decls
    );
    report.decls
}

/// The tactic block of the last theorem in `src`.
fn tactics_of(src: &str) -> Vec<SurfaceTactic> {
    let decls = decls_of(src);
    let proof = decls
        .iter()
        .rev()
        .find_map(|d| match d {
            SurfaceDecl::Theorem { proof, .. } => Some(proof),
            _ => None,
        })
        .expect("a theorem");
    match proof.as_ref() {
        SurfaceExpr::ByTactic(_, tactics) => tactics.clone(),
        other => panic!("expected a ByTactic proof, got {other:?}"),
    }
}

/// Recovery placeholders in `decls`, those inside a `namespace`, `section` or
/// `mutual` block included.
fn raw_decls(decls: &[SurfaceDecl]) -> usize {
    decls
        .iter()
        .map(|decl| match decl {
            SurfaceDecl::RawDecl { .. } => 1,
            SurfaceDecl::Namespace { decls, .. }
            | SurfaceDecl::Section { decls, .. }
            | SurfaceDecl::Mutual { decls, .. } => raw_decls(decls),
            _ => 0,
        })
        .sum()
}

/// `src` must NOT parse cleanly (hard error, recovery placeholder, or
/// tactic-block recovery).
fn assert_refused(src: &str, what: &str) {
    if let Ok(report) = crate::parse_file_with_diagnostics(src) {
        assert!(
            report.diagnostics.len() + raw_decls(&report.decls) > 0,
            "{what} must be refused (Lean 4.8 rejects it), got {:#?}",
            report.decls
        );
    }
}

fn name(text: &str) -> crate::SurfaceName {
    crate::SurfaceName::generated_path(text)
}

// --- `generalize … at` ---------------------------------------------------

fn named_args(tactic: &SurfaceTactic, expected_name: &str) -> Vec<SurfaceExpr> {
    match tactic {
        SurfaceTactic::Named { name, args, .. } if name == expected_name => args.clone(),
        other => panic!("expected `{expected_name}`, got {other:?}"),
    }
}

fn ident_text(arg: &SurfaceExpr) -> String {
    match arg {
        SurfaceExpr::Ident(_, n) => n.to_string(),
        SurfaceExpr::Hole(_) => "_".to_string(),
        other => panic!("expected a name slot, got {other:?}"),
    }
}

#[test]
fn test_generalize_at_hypotheses_and_goal_encodes_the_location() {
    // `generalize hm : (2 : Int) ^ w = m at hlt ⊢` (AggregateProps.lean).
    let tactics = tactics_of(
        "theorem t (w i : Nat) (hlt : i < 2 ^ w) : i < 2 ^ w + 1 := by\n  \
         generalize hm : 2 ^ w = m at hlt ⊢\n  omega\n",
    );
    let args = named_args(&tactics[0], "generalize");
    let slots: Vec<String> = args[1..].iter().map(ident_text).collect();
    assert_eq!(slots, ["m", "hm", "hlt", "⊢"]);
}

#[test]
fn test_generalize_at_hypothesis_without_equation_keeps_the_slot() {
    let tactics = tactics_of(
        "theorem t (w i : Nat) (hlt : i < 2 ^ w) : i < 2 ^ w + 1 := by\n  \
         generalize 2 ^ w = m at hlt\n  omega\n",
    );
    let args = named_args(&tactics[0], "generalize");
    let slots: Vec<String> = args[1..].iter().map(ident_text).collect();
    assert_eq!(slots, ["m", "_", "hlt"]);
}

#[test]
fn test_generalize_without_location_is_unchanged() {
    let tactics = tactics_of(
        "theorem t (w : Nat) : 2 ^ w = 2 ^ w := by\n  generalize hm : 2 ^ w = m\n  rfl\n",
    );
    let args = named_args(&tactics[0], "generalize");
    let slots: Vec<String> = args[1..].iter().map(ident_text).collect();
    assert_eq!(slots, ["m", "hm"]);
}

// --- `module` ------------------------------------------------------------

#[test]
fn test_module_is_an_identifier_outside_the_header() {
    // `def module (j : Json)`, `module : Module`, `{ module := … }`
    // (TrustIrEval/Decode.lean, Run.lean).
    let decls = decls_of(
        "structure Batch where\n  module : Nat\n  runs : List Nat\n\n\
         def module (j : Nat) : Nat := j + 1\n\n\
         def batch (j : Nat) : Batch := { module := module j, runs := [] }\n",
    );
    assert_eq!(decls.len(), 3, "{decls:#?}");
    assert!(
        matches!(&decls[1], SurfaceDecl::Def { name: n, .. } if *n == name("module")),
        "{:#?}",
        decls[1]
    );
    let lambda = crate::grammar::Parser::parse_expr("fun module => module").expect("a lambda");
    assert!(matches!(lambda, SurfaceExpr::Lambda(..)), "{lambda:?}");
}

#[test]
fn test_module_header_keyword_is_consumed() {
    let decls = decls_of("/- header -/\nmodule\n\ndef a : Nat := 1\n");
    assert_eq!(decls.len(), 1, "{decls:#?}");
    assert!(
        matches!(&decls[0], SurfaceDecl::Def { name: n, .. } if *n == name("a")),
        "{:#?}",
        decls[0]
    );
}

#[test]
fn test_module_after_the_first_command_is_no_header() {
    // Lean's header precedes every command: a later `module` is an identifier
    // in command position, which no command starts with (Lean 4.8.0 and
    // v4.30.0-rc2: "unexpected identifier; expected command").
    assert_refused(
        "namespace Foo\n\nmodule\n\ndef b : Nat := 2\n\nend Foo\n",
        "`module` after a command",
    );
}

#[test]
fn test_module_in_tactic_position_reaches_the_elaborator_by_name() {
    // Not a tactic in Lean 4.8 ("unknown tactic"); it no longer hides behind
    // a keyword token, and the elaborator refuses it by name.
    let tactics = tactics_of("theorem t (a b : Nat) : a + b = b + a := by\n  module\n");
    assert!(
        matches!(&tactics[0], SurfaceTactic::Named { name, args, .. } if name == "module" && args.is_empty()),
        "{:?}",
        tactics[0]
    );
}
