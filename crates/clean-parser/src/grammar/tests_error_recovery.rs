// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for file-level error recovery in the parser.
//!
//! When `file()` encounters a declaration that fails to parse, it should
//! skip to the next declaration keyword and continue, producing a `RawDecl`
//! placeholder for the malformed region.

use super::*;
use crate::ParserDiagnosticSeverity;

/// Recursively search a declaration tree for a `Def`/`Theorem` with the given
/// name nested inside a namespace/section whose qualified path matches
/// `expected_scope` (`None` means top level).
fn find_def_scope(
    decls: &[SurfaceDecl],
    target: &str,
    current_scope: Option<String>,
) -> Option<Option<String>> {
    for d in decls {
        match d {
            SurfaceDecl::Def { name, .. } | SurfaceDecl::Theorem { name, .. } if name == target => {
                return Some(current_scope.clone());
            }
            SurfaceDecl::Namespace {
                name, decls: inner, ..
            } => {
                let scope = Some(match &current_scope {
                    Some(outer) => format!("{outer}.{name}"),
                    None => name.clone(),
                });
                if let Some(found) = find_def_scope(inner, target, scope) {
                    return Some(found);
                }
            }
            SurfaceDecl::Section { decls: inner, .. } => {
                if let Some(found) = find_def_scope(inner, target, current_scope.clone()) {
                    return Some(found);
                }
            }
            _ => {}
        }
    }
    None
}

#[test]
fn test_namespace_body_error_recovery_keeps_following_decl_scoped() {
    // A malformed declaration *inside* a namespace must not collapse the whole
    // namespace. The subsequent `def good` must stay scoped under `Foo` (so it
    // elaborates as `Foo.good`, not the top-level `good`), and the error must
    // still be reported as a recovery diagnostic.
    let input = "namespace Foo\n  def bad := \n  def good := 1\nend Foo\n";
    let report = Parser::parse_file_with_diagnostics(input)
        .expect("namespace body recovery should not fail");

    // `good` must be found nested under namespace `Foo`, never hoisted to top level.
    let scope = find_def_scope(&report.decls, "good", None)
        .expect("recovered `good` should still be present in the parse tree");
    assert_eq!(
        scope,
        Some("Foo".to_string()),
        "`good` must remain scoped under `Foo` after in-namespace recovery, got scope {scope:?} in {:?}",
        report.decls
    );

    // Exactly one Namespace decl, no stray top-level RawDecl (the bad decl is a
    // RawDecl *inside* the namespace, and `end Foo` is consumed, not stray).
    let ns_count = report
        .decls
        .iter()
        .filter(|d| matches!(d, SurfaceDecl::Namespace { .. }))
        .count();
    assert_eq!(
        ns_count, 1,
        "expected one Namespace decl after recovery, got {:?}",
        report.decls
    );
    let toplevel_raw = report
        .decls
        .iter()
        .filter(|d| matches!(d, SurfaceDecl::RawDecl { .. }))
        .count();
    assert_eq!(
        toplevel_raw, 0,
        "in-namespace recovery should not leak a top-level RawDecl (no stray end), got {:?}",
        report.decls
    );

    // The original error must still surface as a recovery diagnostic.
    assert!(
        report
            .diagnostics
            .iter()
            .any(|diag| diag.code == "parser.recovery"
                && diag.severity == ParserDiagnosticSeverity::Error),
        "in-namespace recovery must still report the original error, got {:?}",
        report.diagnostics
    );
}

#[test]
fn test_def_match_arm_body_may_start_with_explicit_application() {
    // `@` is overloaded: `@[attr]` starts a declaration attribute, while
    // `@Bool.rec` starts an explicit application expression. The declaration
    // boundary check used to classify both as attributes, so the second
    // equation below degraded into a RawDecl and swallowed its body.
    let input = r#"
def lookupRatHint : List Lit → List RatHint → List (List Lit)
  | _, List.nil => List.nil
  | D, List.cons rh rest =>
      @Bool.rec (fun _ => List (List Lit))
        (lookupRatHint D rest) rh.rHints (clauseEq D rh.dClause)

def afterLookup := true
"#;
    let report = Parser::parse_file_with_diagnostics(input)
        .expect("explicit application in definition equation body should parse");

    assert!(
        report.diagnostics.is_empty(),
        "valid explicit application must not trigger parser recovery: {:?}",
        report.diagnostics
    );
    assert_eq!(
        report.decls.len(),
        2,
        "unexpected declarations: {:?}",
        report.decls
    );
    assert!(
        matches!(&report.decls[0], SurfaceDecl::Def { name, .. } if name == "lookupRatHint"),
        "lookupRatHint must remain a parsed definition: {:?}",
        report.decls
    );
    assert!(
        report
            .decls
            .iter()
            .all(|decl| !matches!(decl, SurfaceDecl::RawDecl { .. })),
        "valid equation body must not degrade to RawDecl: {:?}",
        report.decls
    );
}

#[test]
fn test_namespace_body_error_recovery_preserves_sibling_decl() {
    // A malformed declaration inside a namespace must not swallow the closing
    // `end Foo`; the namespace closes and a following top-level `def sibling`
    // is parsed as its own top-level declaration.
    let input = "namespace Foo\n  def bad := \nend Foo\ndef sibling := 2\n";
    let decls = Parser::parse_file(input).expect("namespace recovery should not fail");

    // `sibling` is top level (scope None), `bad` is the malformed region.
    let sibling_scope =
        find_def_scope(&decls, "sibling", None).expect("`sibling` should be present");
    assert_eq!(
        sibling_scope, None,
        "`sibling` must be a top-level decl after the namespace closes, got scope {sibling_scope:?} in {decls:?}"
    );
    let ns_count = decls
        .iter()
        .filter(|d| matches!(d, SurfaceDecl::Namespace { .. }))
        .count();
    assert_eq!(
        ns_count, 1,
        "expected exactly one Namespace decl, got {decls:?}"
    );
    // No stray top-level RawDecl: `end Foo` was consumed by the namespace.
    assert_eq!(
        decls
            .iter()
            .filter(|d| matches!(d, SurfaceDecl::RawDecl { .. }))
            .count(),
        0,
        "no stray top-level RawDecl expected, got {decls:?}"
    );
}

#[test]
fn test_section_body_error_recovery_keeps_following_decl() {
    // The same recovery applies to `section` bodies.
    let input = "section S\n  def bad := \n  def good := 1\nend S\n";
    let decls = Parser::parse_file(input).expect("section recovery should not fail");

    let scope = find_def_scope(&decls, "good", None)
        .expect("recovered `good` should still be present in the section");
    // Sections do not contribute a name prefix, so the scope is top-level None,
    // but `good` must still live *inside* the Section node (not hoisted out as a
    // sibling that loses the section's variable/open context).
    assert_eq!(scope, None, "section does not prefix names; got {scope:?}");
    let section_count = decls
        .iter()
        .filter(|d| matches!(d, SurfaceDecl::Section { .. }))
        .count();
    assert_eq!(
        section_count, 1,
        "expected one Section decl after recovery, got {decls:?}"
    );
    // `good` must be inside the Section, with no stray top-level def/raw.
    let toplevel_good = decls
        .iter()
        .any(|d| matches!(d, SurfaceDecl::Def { name, .. } if name == "good"));
    assert!(
        !toplevel_good,
        "`good` must stay inside the section, not be hoisted to top level: {decls:?}"
    );
}

#[test]
fn test_pre_namespace_error_recovery_resyncs_at_namespace() {
    // Regression guard for the originally-reported (but already-working) case:
    // a malformed top-level declaration before a `namespace` must resync at the
    // namespace boundary, parse the namespace body, and report the error.
    let input = "def bad := \nnamespace Foo\n  def good := 1\nend Foo\n";
    let report = Parser::parse_file_with_diagnostics(input).expect("pre-namespace recovery");

    let scope = find_def_scope(&report.decls, "good", None)
        .expect("`good` should be recovered after resyncing at namespace");
    assert_eq!(
        scope,
        Some("Foo".to_string()),
        "`good` must be scoped under `Foo`, got {scope:?} in {:?}",
        report.decls
    );
    assert!(
        report
            .decls
            .iter()
            .any(|d| matches!(d, SurfaceDecl::RawDecl { .. })),
        "the malformed `def bad` should appear as a top-level RawDecl, got {:?}",
        report.decls
    );
    assert!(
        report
            .diagnostics
            .iter()
            .any(|diag| diag.code == "parser.recovery"),
        "pre-namespace recovery must report the original error, got {:?}",
        report.diagnostics
    );
}

#[test]
fn test_file_error_recovery_skips_malformed_decls() {
    // A file with a valid def, a malformed def (recognized keyword but bad body),
    // and another valid def. The parser should recover from the malformed declaration
    // via skip_to_next_decl and return all three entries.
    let input = r"
        def foo := 1
        def ??? := !!!
        def bar := 2
    ";
    let decls = Parser::parse_file(input).expect("file-level recovery should not fail");

    // We should get at least the two valid defs
    let def_names: Vec<&str> = decls
        .iter()
        .filter_map(|d| match d {
            SurfaceDecl::Def { name, .. } => Some(name.as_str()),
            _ => None,
        })
        .collect();
    assert!(
        def_names.contains(&"foo"),
        "should recover 'foo', got defs: {def_names:?}"
    );
    assert!(
        def_names.contains(&"bar"),
        "should recover 'bar', got defs: {def_names:?}"
    );

    // The malformed region should appear as a RawDecl
    let raw_count = decls
        .iter()
        .filter(|d| matches!(d, SurfaceDecl::RawDecl { .. }))
        .count();
    assert!(
        raw_count >= 1,
        "expected at least one RawDecl for the malformed region, got {raw_count}"
    );
}

#[test]
fn test_file_error_recovery_reports_recovery_location() {
    let input = r"
        def foo := 1
        def ??? := !!!
        def bar := 2
    ";
    let report = Parser::parse_file_with_diagnostics(input).expect("recovery report should parse");

    assert!(
        report
            .diagnostics
            .iter()
            .any(|diag| diag.code == "parser.recovery"
                && diag.resumed_token.contains("Def")
                && diag.recovered_at.line > 0),
        "expected parser recovery diagnostic with resumed declaration location, got {:?}",
        report.diagnostics
    );
}

#[test]
fn test_indent_error_recovery_reports_block_location() {
    let input = r"
        def foo := by
          show
        def bar := 2
    ";
    let report = Parser::parse_file_with_diagnostics(input).expect("recovery report should parse");

    let show_byte = input.find("show").expect("test input should contain show");
    let bar_byte = input
        .rfind("def bar")
        .expect("test input should contain recovery declaration");
    assert!(
        report.diagnostics.iter().any(|diag| {
            diag.code == "parser.indent_recovery"
                && diag.severity == ParserDiagnosticSeverity::Error
                && diag.construct == "by tactic block"
                && diag
                    .block_start
                    .as_ref()
                    .is_some_and(|loc| loc.byte == show_byte)
                && diag.recovered_at.byte == bar_byte
                && diag.recovered_at.line > 0
        }),
        "expected indentation recovery diagnostic with block location, got {:?}",
        report.diagnostics
    );
}

#[test]
fn test_do_block_error_recovery_reports_block_location() {
    let input = r"
        def foo := do
          let
        def bar := 2
    ";
    let report = Parser::parse_file_with_diagnostics(input).expect("recovery report should parse");

    let let_byte = input.find("let").expect("test input should contain let");
    let bar_byte = input
        .rfind("def bar")
        .expect("test input should contain recovery declaration");
    assert!(
        report.diagnostics.iter().any(|diag| {
            diag.code == "parser.indent_recovery"
                && diag.construct == "do block"
                && diag
                    .block_start
                    .as_ref()
                    .is_some_and(|loc| loc.byte == let_byte)
                && diag.recovered_at.byte == bar_byte
                && diag.recovered_at.line > 0
        }),
        "expected do-block indentation recovery diagnostic, got {:?}",
        report.diagnostics
    );
}

#[test]
fn test_do_block_error_recovery_keeps_following_decl() {
    // Companion to the diagnostic-location test: do-block recovery must stop
    // at the next top-level declaration boundary rather than consuming to EOF,
    // so the sibling `def bar` is still parsed as its own declaration instead
    // of being swallowed into the malformed region.
    let input = r"
        def foo := do
          let
        def bar := 2
    ";
    let decls = Parser::parse_file(input).expect("do-block recovery should not fail");

    let def_names: Vec<&str> = decls
        .iter()
        .filter_map(|d| match d {
            SurfaceDecl::Def { name, .. } => Some(name.as_str()),
            _ => None,
        })
        .collect();
    assert!(
        def_names.contains(&"bar"),
        "do-block recovery must preserve the following `def bar`, got defs: {def_names:?} in {decls:?}"
    );
}

#[test]
fn test_do_sequence_error_recovery_reports_block_location() {
    let input = r"
        def foo := do
          if true then
            let
          else
            return 0
        def bar := 2
    ";
    let report = Parser::parse_file_with_diagnostics(input).expect("recovery report should parse");

    assert!(
        report
            .diagnostics
            .iter()
            .any(|diag| diag.code == "parser.indent_recovery"
                && diag.construct == "do sequence"
                && diag.block_start.is_some()
                && diag.recovered_at.line > 0),
        "expected do-sequence indentation recovery diagnostic, got {:?}",
        report.diagnostics
    );
}

#[test]
fn test_calc_error_recovery_reports_block_location() {
    let input = r"
        def foo := calc
          a = b :=
        def bar := 2
    ";
    let report = Parser::parse_file_with_diagnostics(input).expect("recovery report should parse");

    assert!(
        report
            .diagnostics
            .iter()
            .any(|diag| diag.code == "parser.indent_recovery"
                && diag.construct.starts_with("calc ")
                && diag.block_start.is_some()
                && diag.recovered_at.line > 0),
        "expected calc indentation recovery diagnostic, got {:?}",
        report.diagnostics
    );
}

#[test]
fn test_file_error_recovery_all_valid() {
    // When all declarations are valid, recovery should not affect the result.
    let input = r"
        def a := 1
        def b := 2
        axiom c : Type
    ";
    let decls = Parser::parse_file(input).expect("all-valid file should parse");
    assert_eq!(decls.len(), 3, "expected 3 declarations, got {:?}", decls);
}

#[test]
fn test_file_error_recovery_all_malformed() {
    // Even if every declaration is malformed, the parser should not abort.
    let input = "$$$ @@@ %%% &&&";
    let decls = Parser::parse_file(input).expect("all-malformed file should still return Ok");
    // Should get at least one RawDecl for the skipped content
    assert!(
        !decls.is_empty(),
        "expected at least one RawDecl placeholder"
    );
    for d in &decls {
        assert!(
            matches!(d, SurfaceDecl::RawDecl { .. }),
            "expected all RawDecl, got {d:?}"
        );
    }
}

#[test]
fn test_stray_end_at_toplevel_does_not_hang() {
    // Regression for `Mathbot/Bridges/NNVerification.lean` audit item 4
    // (docs/mathbot/CLEAN-VERIFIER-AUDIT-2026-05-27.md). A stray `end Foo`
    // at the top level (no enclosing `namespace`/`section`) previously
    // caused an infinite loop: `decl_with_modifiers` had no case for
    // `TokenKind::End`, and `End` is in `is_decl_keyword`, so the
    // recovery loop in `skip_to_next_decl_impl` exited without consuming
    // the offending token. `file()` then re-dispatched on the same token
    // forever, allocating gigabytes of debug-formatted error strings.
    //
    // After the fix, `decl_with_modifiers` handles `End` explicitly,
    // consuming the keyword and an optional dotted name, and returning a
    // `RawDecl`. As a defense-in-depth measure, `skip_to_next_decl_impl`
    // now guarantees at least one token of progress when entered on a
    // declaration-start token. Either fix on its own breaks the loop;
    // both are kept so a future regression in one is caught by the other.
    let start = std::time::Instant::now();
    let decls = Parser::parse_file("end Mathbot.NNVerification\n")
        .expect("stray end should not be a hard parse error");
    let elapsed = start.elapsed();
    assert!(
        elapsed.as_secs() < 5,
        "stray-end recovery took {elapsed:?}; previously hung indefinitely"
    );
    assert!(
        !decls.is_empty(),
        "expected at least one (Raw)Decl for the stray end"
    );
    // The leading `end` should appear as a RawDecl rather than as a
    // successfully-parsed Namespace/Section closer.
    assert!(
        decls
            .iter()
            .any(|d| matches!(d, SurfaceDecl::RawDecl { .. })),
        "stray end should produce a RawDecl; got {decls:?}"
    );
}

#[test]
fn test_bare_end_does_not_hang() {
    // The simplest reduction of the NNVerification hang: just `end` with
    // no enclosing block.
    let start = std::time::Instant::now();
    let decls = Parser::parse_file("end\n").expect("bare end should not be a hard parse error");
    let elapsed = start.elapsed();
    assert!(
        elapsed.as_secs() < 5,
        "bare-end recovery took {elapsed:?}; previously hung indefinitely"
    );
    assert!(!decls.is_empty(), "expected at least one decl for bare end");
}

#[test]
fn test_namespace_end_pair_still_parses() {
    // Sanity check: the stray-end handler must not steal the closing
    // `end` of a real namespace block.
    let decls =
        Parser::parse_file("namespace Foo\nend Foo\n").expect("namespace/end pair should parse");
    let ns_count = decls
        .iter()
        .filter(|d| matches!(d, SurfaceDecl::Namespace { .. }))
        .count();
    assert_eq!(ns_count, 1, "expected one Namespace decl, got {decls:?}");
    let raw_count = decls
        .iter()
        .filter(|d| matches!(d, SurfaceDecl::RawDecl { .. }))
        .count();
    assert_eq!(
        raw_count, 0,
        "namespace/end pair should not produce a stray RawDecl, got {decls:?}"
    );
}

#[test]
fn test_nnverification_minimal_repro_terminates() {
    // Mirror the smallest reproducer found by bisecting
    // `Mathbot/Bridges/NNVerification.lean` (audit item 4): a comment,
    // a `set_option`, and a top-level `end NAMESPACE`. The combination
    // does not constitute a valid Lean program, but `parse_file` must
    // terminate quickly with a recoverable diagnostic rather than hang.
    let input = "set_option autoImplicit false\nend Mathbot.NNVerification\n";
    let start = std::time::Instant::now();
    let _ = Parser::parse_file(input).expect("minimal repro should not hard-fail");
    let elapsed = start.elapsed();
    assert!(
        elapsed.as_secs() < 5,
        "NNVerification minimal repro took {elapsed:?}; previously hung indefinitely"
    );
}
