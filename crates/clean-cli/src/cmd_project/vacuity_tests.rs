// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit battery for the K5 vacuous-pass defect.
//!
//! `clean project check` reported `declarations_checked: 0, declarations_failed:
//! 0, status: pass` on a package of 1,580 declarations, and did not refuse a
//! deliberate type error, because every declaration sat inside a `namespace`
//! block that elaborates to ONE `ElabResult::Multiple` the checker answered
//! `(skipped)` for without looking inside.
//!
//! These are the in-process halves of the battery: the counting side (what the
//! parser reports as the population to check), the fail-closed guard that
//! refuses an unflattened block, and the whole-run vacuity gate. The
//! process-boundary half — exit codes and real elaboration — lives in
//! `crates/clean-cli/tests/project_check_cli.rs`.

use clean_elab::{ElabError, ElabResult};

use super::*;

fn parse(source: &str) -> Vec<SurfaceDecl> {
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    parse_file_with_tactics(source, &patterns).expect("fixture should parse")
}

fn declaration_leaves(source: &str) -> usize {
    parse(source).iter().map(count_declaration_leaves).sum()
}

#[test]
fn namespace_members_are_counted_as_declarations_not_as_one_block() {
    // The defect's parse-side half: three declarations inside one block.
    let source = "namespace Battery\n\
                  def a : Nat := 1\n\
                  def b : Nat := 2\n\
                  theorem ab : True := True.intro\n\
                  end Battery\n";
    assert_eq!(parse(source).len(), 1, "one top-level block");
    assert_eq!(declaration_leaves(source), 3, "three declarations in it");
}

#[test]
fn section_mutual_and_nested_blocks_are_counted_through() {
    assert_eq!(
        declaration_leaves("section\ndef s : Nat := 1\ndef t : Nat := 2\nend\n"),
        2
    );
    assert_eq!(
        declaration_leaves(
            "namespace Outer\nnamespace Inner\ndef deep : Nat := 1\nend Inner\nend Outer\n"
        ),
        1
    );
    assert_eq!(
        declaration_leaves("mutual\ndef m1 : Nat := 1\ndef m2 : Nat := 2\nend\n"),
        2
    );
}

#[test]
fn administrative_forms_declare_nothing_and_are_not_counted() {
    // `declarations_parsed` is the population the checker is expected to
    // examine; administrative forms are not in it. (A PROJECT holding only
    // these still fails `nothing_checked`: it checked nothing.)
    assert_eq!(declaration_leaves("import Foo\nimport Bar.Baz\n"), 0);
    assert_eq!(declaration_leaves("universe u\nvariable (x : Nat)\n"), 0);
    assert_eq!(declaration_leaves("namespace Empty\nend Empty\n"), 0);
}

#[test]
fn a_parse_recovered_declaration_still_counts_as_a_declaration() {
    // A `RawDecl` is a declaration the parser could not read. It must stay in
    // the denominator: absorbing it would let a file of unreadable declarations
    // report "nothing to check".
    let decls = parse("def ok : Nat := 1\ndef := := :=\n");
    let raw = decls
        .iter()
        .filter(|decl| matches!(decl, SurfaceDecl::RawDecl { .. }))
        .count();
    assert!(raw >= 1, "fixture should produce a recovered RawDecl");
    assert_eq!(
        decls.iter().map(count_declaration_leaves).sum::<usize>(),
        decls.len(),
        "every leaf here, recovered or not, is one declaration"
    );
}

/// The guard that makes the defect impossible to reintroduce silently: a block
/// that still holds declarations must never answer "(skipped)".
#[test]
fn an_unflattened_block_is_refused_instead_of_skipped() {
    let env = Environment::new();
    let decl = parse("def inner : Nat := 1\n")
        .into_iter()
        .next()
        .expect("one decl");
    let block = ElabResult::Multiple(vec![ElabResult::Failed {
        name: "Battery.inner".to_string(),
        decl: Box::new(decl),
        error: Box::new(ElabError::ParseError("deliberate".to_string())),
    }]);

    let verdict = typecheck_elab_result(&block, &env);
    let message = verdict.expect_err("a block holding a declaration must not be skipped");
    assert!(
        message.contains("unflattened"),
        "the refusal must say why: {message}"
    );

    // And the flattened form reaches the single-declaration checker as a real
    // failure, never as a pass.
    let mut leaves: Vec<&ElabResult> = Vec::new();
    block.leaf_decls(&mut leaves);
    assert_eq!(leaves.len(), 1);
    let leaf_verdict = typecheck_elab_result(leaves[0], &env);
    assert!(
        leaf_verdict.is_err(),
        "a Failed leaf must never typecheck as a pass"
    );
}

#[test]
fn an_empty_block_is_still_administrative() {
    let env = Environment::new();
    let empty = ElabResult::Multiple(Vec::new());
    assert_eq!(
        typecheck_elab_result(&empty, &env).expect("an empty block checks nothing"),
        "(skipped)"
    );
    let only_commands = ElabResult::Multiple(vec![ElabResult::Skipped]);
    assert_eq!(
        typecheck_elab_result(&only_commands, &env).expect("no declarations inside"),
        "(skipped)"
    );
}

#[test]
fn checking_nothing_while_declarations_exist_is_a_blocker() {
    // The K5 numbers themselves: 1,580 parsed, 0 checked, reported as `pass`.
    let blocker = vacuous_run_blocker(1580, 0).expect("0 of 1580 checked must block");
    assert_eq!(blocker.kind, "nothing_checked");
    assert!(blocker.message.contains("1580"));

    // Round-22 verification: a comment-only / admin-only package parsed 0
    // and checked 0, and that passed. Checking nothing is never a pass.
    let empty = vacuous_run_blocker(0, 0).expect("0 of 0 checked must block");
    assert_eq!(empty.kind, "nothing_checked");
    assert!(
        vacuous_run_blocker(1580, 1).is_none(),
        "this gate is the backstop, not the verdict: one checked declaration \
         clears it and the per-declaration rows carry the verdict"
    );
}

#[test]
fn alias_declaration_leaves_count_every_generated_name() {
    assert_eq!(declaration_leaves("alias copied := original"), 1);
    assert_eq!(
        declaration_leaves("alias ⟨forward, backward⟩ := equivalence"),
        2
    );
    assert_eq!(declaration_leaves("alias ⟨_, backward⟩ := equivalence"), 1);
    assert_eq!(declaration_leaves("alias ⟨_, _⟩ := equivalence"), 0);
}
