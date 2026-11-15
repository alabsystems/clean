// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `#guard`, `#print axioms` and `#guard_msgs` through the elaborator's file
//! entry (`parse_file` → `preprocess_decl_with_context` →
//! `elaborate_decl_and_register_with_context_and_warning`), the path `clean
//! check` drives.
//!
//! Every expected message below is what the pinned Lean 4.8.0 binary printed
//! for the same source (oracle runs of 2026-09-30); the negative controls are
//! inputs Lean 4.8.0 rejects. Before these commands existed, each of them was
//! skipped and replaced by `#check _`, whose metavariable reached the kernel
//! as `Unknown free variable: FVarId(9223372036854775809)`.

use clean_elab::{
    elaborate_decl_and_register_with_context_and_warning, preprocess_decl_with_context,
    CommandOutput, ElabError, ElabResult, FileContext, RegistrationWarning,
    RegistrationWarningKind,
};
use clean_kernel::Environment;
use clean_parser::parse_file;

/// What registration returned for one declaration (the parts these tests
/// read).
#[derive(Debug)]
struct Registered {
    result: ElabResult,
    warning: Option<RegistrationWarning>,
}

/// Elaborate `source` declaration by declaration; one outcome per top-level
/// declaration, in order.
fn run(source: &str) -> Vec<Result<Registered, ElabError>> {
    let mut env = Environment::with_prelude();
    let mut fc = FileContext::new();
    let decls = parse_file(source).unwrap_or_else(|e| panic!("parse error: {e}\n{source}"));
    decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut fc);
            elaborate_decl_and_register_with_context_and_warning(&mut env, &processed, &mut fc).map(
                |r| Registered {
                    result: r.result,
                    warning: r.warning,
                },
            )
        })
        .collect()
}

fn last(source: &str) -> Result<Registered, ElabError> {
    run(source).pop().expect("source has a declaration")
}

/// The info messages of a `#print axioms` outcome.
fn axioms_messages(outcome: &Result<Registered, ElabError>) -> Vec<String> {
    match outcome {
        Ok(Registered {
            result: ElabResult::Command(CommandOutput::PrintAxioms(r)),
            ..
        }) => r.messages.clone(),
        other => panic!("expected a `#print axioms` result, got {other:?}"),
    }
}

fn error_text(outcome: Result<Registered, ElabError>) -> String {
    match outcome {
        Err(e) => e.to_string(),
        Ok(r) => panic!("expected a refusal, got {:?}", r.result),
    }
}

fn is_guard_msgs_pass(outcome: &Result<Registered, ElabError>) -> bool {
    matches!(
        outcome,
        Ok(Registered {
            result: ElabResult::Command(CommandOutput::GuardMsgs(_)),
            ..
        })
    )
}

const AXIOMS: &str = "axiom A : Prop\n\
axiom hB : A\n\
axiom hC : A\n\
axiom P : Nat → Prop\n\
axiom hP : ∀ n, P n\n\
theorem t1 : A ∧ A := ⟨hC, hB⟩\n\
def D : Prop := P 0\n\
theorem t2 : D ∧ A := ⟨hP 0, hB⟩\n\
theorem t3 : A ∧ D := ⟨hB, hP 0⟩\n\
inductive W : Prop where\n  | mk : A → W\n\
theorem t4 : W := W.mk hC\n\
namespace N\ntheorem t5 : A := hB\nend N\n\
theorem t6 : True := True.intro\n";

const T1_MESSAGE: &str = "'t1' depends on axioms: [A, hC, hB]";

#[test]
fn test_print_axioms_lists_axioms_in_lean_traversal_order() {
    // Lean 4.8.0 prints in `CollectAxioms` order, NOT sorted: the type's
    // constants before the value's, depth first, an axiom's own type unwalked.
    for (cmd, expected) in [
        ("#print axioms t1", T1_MESSAGE),
        ("#print axioms t2", "'t2' depends on axioms: [P, A, hP, hB]"),
        ("#print axioms t3", "'t3' depends on axioms: [A, P, hB, hP]"),
        ("#print axioms t4", "'t4' depends on axioms: [A, hC]"),
        ("#print axioms t6", "'t6' does not depend on any axioms"),
    ] {
        let outcome = last(&format!("{AXIOMS}{cmd}\n"));
        assert_eq!(
            axioms_messages(&outcome),
            vec![expected.to_string()],
            "{cmd}"
        );
    }
}

#[test]
fn test_print_axioms_resolves_through_namespace_and_open_like_lean() {
    let open_in = last(&format!("{AXIOMS}open N in\n#print axioms t5\n"));
    assert_eq!(
        axioms_messages(&open_in),
        vec!["'N.t5' depends on axioms: [A, hB]".to_string()]
    );
    let inside = run(&format!("{AXIOMS}namespace N\n#print axioms t5\nend N\n"));
    let inside = inside.last().expect("namespace block");
    let Ok(Registered {
        result: ElabResult::Multiple(members),
        ..
    }) = inside
    else {
        panic!("expected the namespace block, got {inside:?}");
    };
    assert!(
        matches!(
            members.as_slice(),
            [ElabResult::Command(CommandOutput::PrintAxioms(r))]
                if r.messages == ["'N.t5' depends on axioms: [A, hB]"]
        ),
        "{members:?}"
    );
}

#[test]
fn test_print_axioms_unknown_constant_is_refused_with_lean_text() {
    let error = error_text(last(&format!("{AXIOMS}#print axioms nope\n")));
    assert_eq!(error, "unknown constant 'nope'");
}

#[test]
fn test_print_axioms_explicit_sorry_reports_sorry_ax() {
    let outcome = last("theorem s : 1 = 2 := sorry\n#print axioms s\n");
    assert_eq!(
        axioms_messages(&outcome),
        vec!["'s' depends on axioms: [sorryAx]".to_string()]
    );
}

#[test]
fn test_guard_msgs_matching_expectation_passes() {
    for (header, doc) in [
        ("#guard_msgs in", format!("/-- info: {T1_MESSAGE} -/")),
        // `whitespace := normalized` (the default) reads a newline as a space.
        (
            "#guard_msgs in",
            "/-- info: 't1' depends on\naxioms: [A, hC, hB] -/".to_string(),
        ),
        (
            "#guard_msgs (whitespace := exact) in",
            format!("/-- info: {T1_MESSAGE} -/"),
        ),
        (
            "#guard_msgs (whitespace := lax) in",
            "/-- info:   't1' depends   on axioms: [A, hC, hB] -/".to_string(),
        ),
        (
            "#guard_msgs (info, drop all) in",
            format!("/-- info: {T1_MESSAGE} -/"),
        ),
        ("#guard_msgs (drop info) in", String::new()),
        ("#guard_msgs (error, drop all) in", String::new()),
    ] {
        let outcome = last(&format!("{AXIOMS}{doc}\n{header}\n#print axioms t1\n"));
        assert!(is_guard_msgs_pass(&outcome), "{header} {doc}: {outcome:?}");
    }
}

#[test]
fn test_guard_msgs_differing_expectation_fails_with_lean_report() {
    // Lean 4.8.0 accepts NONE of these: the order differs, a filter leaves
    // the info unchecked, spacing differs under the default normalization,
    // or a second expected message was never produced.
    for (header, doc, produced) in [
        (
            "#guard_msgs in",
            "/-- info: 't1' depends on axioms: [A, hB, hC] -/".to_string(),
            format!("info: {T1_MESSAGE}"),
        ),
        (
            "#guard_msgs(error) in",
            format!("/-- info: {T1_MESSAGE} -/"),
            String::new(),
        ),
        (
            "#guard_msgs(drop info) in",
            format!("/-- info: {T1_MESSAGE} -/"),
            String::new(),
        ),
        (
            "#guard_msgs in",
            "/-- info:   't1' depends   on axioms: [A, hC, hB] -/".to_string(),
            format!("info: {T1_MESSAGE}"),
        ),
        (
            "#guard_msgs in",
            format!(
                "/--\ninfo: {T1_MESSAGE}\n---\ninfo: 't2' depends on axioms: [P, A, hP, hB]\n-/"
            ),
            format!("info: {T1_MESSAGE}"),
        ),
    ] {
        let error = error_text(last(&format!(
            "{AXIOMS}{doc}\n{header}\n#print axioms t1\n"
        )));
        assert_eq!(
            error,
            format!(
                "❌ Docstring on `#guard_msgs` does not match generated message:\n\n{produced}"
            ),
            "{header} {doc}"
        );
    }
}

#[test]
fn test_guard_msgs_expected_error_is_consumed_and_unexpected_error_is_reported() {
    let expected = last(&format!(
        "{AXIOMS}/-- error: unknown constant 'nope' -/\n#guard_msgs in\n#print axioms nope\n"
    ));
    assert!(is_guard_msgs_pass(&expected), "{expected:?}");
    let unexpected = error_text(last(&format!(
        "{AXIOMS}#guard_msgs in\n#print axioms nope\n"
    )));
    assert_eq!(
        unexpected,
        "❌ Docstring on `#guard_msgs` does not match generated message:\n\n\
         error: unknown constant 'nope'"
    );
}

#[test]
fn test_guard_msgs_sorry_warning_matches_but_sorry_stays_in_the_census() {
    let outcome = last(
        "/-- warning: declaration uses 'sorry' -/\n#guard_msgs in\ntheorem s : 1 = 2 := sorry\n",
    );
    let registered = outcome.expect("Lean 4.8.0 accepts this #guard_msgs");
    assert!(
        matches!(registered.result, ElabResult::Theorem { .. }),
        "{:?}",
        registered.result
    );
    assert!(
        registered
            .warning
            .as_ref()
            .is_some_and(|w| matches!(w.kind, RegistrationWarningKind::ExplicitSorry)),
        "the guard must not launder the sorry: {:?}",
        registered.warning
    );
    // Without the docstring the guard fails. Lean 4.8.0 and 4.30.0-rc2 both
    // keep `s` (a later `#check s` prints `s : 1 = 2`) and report the
    // mismatch as an error, exit 1. Clean keeps the registered theorem and
    // carries the failed assertion as a source error beside it
    // (`ElabResult::Diagnosed`, 058b395a3), which every front door reads.
    let silent = last("#guard_msgs in\ntheorem s : 1 = 2 := sorry\n")
        .expect("the failed guard keeps the declaration, as Lean does");
    let ElabResult::Multiple(members) = &silent.result else {
        panic!("expected the declaration beside the failed guard, got {silent:?}");
    };
    assert!(
        matches!(members.first(), Some(ElabResult::Theorem { .. })),
        "{members:?}"
    );
    assert!(
        silent
            .warning
            .as_ref()
            .is_some_and(|w| matches!(w.kind, RegistrationWarningKind::ExplicitSorry)),
        "the failed guard must not launder the sorry: {:?}",
        silent.warning
    );
    let message = silent
        .result
        .source_error_message()
        .expect("the failed guard is a source error");
    assert!(
        message.ends_with("warning: declaration uses 'sorry'"),
        "{message}"
    );
}

/// `Pred.implies`'s shape in miniature. The arms do not overlap: that is the
/// match compiler's business, not `#guard`'s, and this file pins `#guard`.
const SHAPE: &str = "inductive Shape where\n  | top\n  | interval (lo hi : Nat)\n\
def Shape.implies : Shape → Shape → Bool\n\
  | .top, .top => true\n\
  | .interval _ _, .top => true\n\
  | .top, .interval _ _ => false\n\
  | .interval a b, .interval c d => c ≤ a && b ≤ d\n";

/// Every `#guard` below needs `Shape.implies` itself to have elaborated;
/// without this a refusal of the definition would read as a `#guard` result.
fn assert_shape_registered(outcomes: &[Result<Registered, ElabError>]) {
    for (i, outcome) in outcomes.iter().take(2).enumerate() {
        let elaborated = outcome.as_ref().is_ok_and(|registered| {
            let mut leaves = Vec::new();
            registered.result.leaf_decls(&mut leaves);
            !leaves.is_empty()
                && !leaves
                    .iter()
                    .any(|leaf| matches!(leaf, ElabResult::Failed { .. }))
        });
        assert!(
            elaborated,
            "SHAPE declaration {i} must elaborate: {outcome:?}"
        );
    }
}

#[test]
fn test_guard_true_evaluation_passes_as_checked_example() {
    for cmd in [
        "#guard 1 + 1 = 2",
        "#guard (2 : Nat) == 2",
        "#guard Shape.implies .top .top = true",
        "#guard Shape.implies (.interval 2 5) (.interval 0 7) = true",
        "#guard Shape.implies (.interval 0 7) (.interval 2 5) = false",
        "#guard_msgs in\n#guard true",
    ] {
        let mut outcomes = run(&format!("{SHAPE}{cmd}\n"));
        assert_shape_registered(&outcomes);
        let outcome = outcomes.pop().expect("the #guard");
        assert!(
            matches!(
                outcome,
                Ok(Registered {
                    result: ElabResult::Example { .. },
                    ..
                })
            ),
            "{cmd}: {outcome:?}"
        );
    }
}

#[test]
fn test_guard_false_evaluation_is_refused() {
    // Negative controls Lean 4.8.0 rejects: `did not evaluate to `true``.
    for cmd in [
        "#guard 1 + 1 = 3",
        "#guard Shape.implies .top (.interval 0 7) = true",
        "#guard Shape.implies (.interval 0 7) (.interval 2 5)",
    ] {
        let mut outcomes = run(&format!("{SHAPE}{cmd}\n"));
        assert_shape_registered(&outcomes);
        let error = error_text(outcomes.pop().expect("the #guard"));
        assert!(
            error.starts_with("expression\n") && error.ends_with("\ndid not evaluate to `true`"),
            "{cmd}: {error}"
        );
    }
}

#[test]
fn test_guard_ill_typed_or_out_of_scope_term_is_refused() {
    // Lean 4.8.0: `type mismatch` for a `Nat`, and `unknown identifier 'n'`
    // for a section variable (`#guard` elaborates without `variable`s).
    let mismatch = last("#guard (5 : Nat)\n");
    assert!(mismatch.is_err(), "{mismatch:?}");
    let outcomes = run("section\nvariable (n : Nat)\n#guard n = n\nend\n");
    let section = outcomes.last().expect("section block");
    let Ok(Registered {
        result: ElabResult::Multiple(members),
        ..
    }) = section
    else {
        panic!("expected the section block, got {section:?}");
    };
    assert!(
        members.iter().any(|m| matches!(
            m,
            ElabResult::Failed { error, .. } if error.to_string().contains("Unknown identifier")
        )),
        "a #guard over a section variable must be refused: {members:?}"
    );
    assert!(
        !members
            .iter()
            .any(|m| matches!(m, ElabResult::Example { .. })),
        "{members:?}"
    );
}
