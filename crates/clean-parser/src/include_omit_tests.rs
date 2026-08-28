// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `include` / `omit`, and the parser fail-open they exposed.
//!
//! # The defect these fixtures pin
//!
//! `variable`'s binder list accepts a run of bare names (`variable α β`), and
//! that run had no line discipline. A command line the parser did not
//! recognise was therefore absorbed as MORE BINDERS by the `variable` command
//! above it. Measured against Mathlib `Logic/Function/Basic.lean`:
//!
//! ```text
//! variable {α : Sort u} {f : α → α} (h : Involutive f)
//!
//! include h
//! ```
//!
//! parsed as FOUR section variables — `{f}`, `(h : Involutive f)`, and then
//! untyped `include` and untyped `h`. The second `h` shadowed the real one, so
//! every declaration in `namespace Involutive` elaborated `h` as a meta FVar
//! and failed.
//!
//! The trigger was never `include`. `omit h` and `frobnicate h` were absorbed
//! identically — **any** unrecognised `<ident> <ident>` line silently minted
//! untyped section variables. [`frobnicate_after_variable_is_not_absorbed`] is
//! the fixture that proves it, because `frobnicate` is not a Lean command at
//! all: nothing about the fix can be explained by teaching the parser one more
//! keyword.
//!
//! Two independent changes close it, and both are pinned here:
//!   1. a bare-name run may not continue onto a line that starts at or left of
//!      the `variable` keyword's own column, so the command line is released;
//!   2. `include` / `omit` are real commands, and an identifier in command
//!      position that no arm claims is a NAMED refusal, never a silent guess.

use crate::{parse_file, SurfaceDecl};

/// The Mathlib shape, reduced: a typed section variable followed by a command
/// line at column 0.
fn src(command_line: &str) -> String {
    format!(
        "variable {{f : Nat → Nat}} (h : Foo f)\n\n{command_line}\n\ntheorem t : True := trivial\n"
    )
}

/// Binders of the first `variable` declaration, as `(name, has_type)`.
fn variable_binders(decls: &[SurfaceDecl]) -> Vec<(String, bool)> {
    decls
        .iter()
        .find_map(|d| match d {
            SurfaceDecl::Variable { binders, .. } => Some(
                binders
                    .iter()
                    .map(|b| (b.name.clone(), b.ty.is_some()))
                    .collect(),
            ),
            _ => None,
        })
        .expect("a `variable` declaration")
}

/// The two REAL section variables, and nothing else.
fn assert_variable_untouched(decls: &[SurfaceDecl]) {
    assert_eq!(
        variable_binders(decls),
        vec![("f".to_string(), true), ("h".to_string(), true)],
        "the `variable` line must bind exactly its own two typed binders; an \
         extra entry here is the fail-open re-opening, and an UNTYPED `h` \
         would shadow the real one"
    );
}

#[test]
fn test_include_after_variable_is_not_absorbed_as_binders() {
    let decls = parse_file(&src("include h")).expect("parses");
    assert_variable_untouched(&decls);

    let found = decls.iter().any(
        |d| matches!(d, SurfaceDecl::IncludeVars { names, .. } if names == &["h".to_string()]),
    );
    assert!(
        found,
        "`include h` must parse as an Include command: {decls:#?}"
    );
}

#[test]
fn test_omit_after_variable_is_not_absorbed_as_binders() {
    let decls = parse_file(&src("omit h")).expect("parses");
    assert_variable_untouched(&decls);

    let found = decls
        .iter()
        .any(|d| matches!(d, SurfaceDecl::OmitVars { names, .. } if names == &["h".to_string()]));
    assert!(found, "`omit h` must parse as an Omit command: {decls:#?}");
}

/// THE fixture. `frobnicate` is not a Lean command, so a parser that absorbs
/// it is guessing, and one that names it is refusing. Nothing here depends on
/// `include` being special.
#[test]
fn test_frobnicate_after_variable_is_not_absorbed_as_binders() {
    let decls = parse_file(&src("frobnicate h")).expect("parses");
    assert_variable_untouched(&decls);

    let named = decls.iter().any(
        |d| matches!(d, SurfaceDecl::RawDecl { content, .. } if content.contains("frobnicate")),
    );
    assert!(
        named,
        "an unrecognised command must be refused BY NAME, not absorbed: {decls:#?}"
    );
}

/// The refusal names the token and says what it is.
#[test]
fn test_unknown_command_refusal_names_the_token() {
    let decls = parse_file("frobnicate h\n\ntheorem t : True := trivial\n").expect("parses");
    let content = decls
        .iter()
        .find_map(|d| match d {
            SurfaceDecl::RawDecl { content, .. } => Some(content.clone()),
            _ => None,
        })
        .expect("a RawDecl for the unknown command");
    assert!(
        content.contains("unknown command") && content.contains("frobnicate"),
        "refusal must name the token: {content:?}"
    );
}

/// The declaration AFTER the command line still parses. The barrier releases
/// the line; it does not resync the whole file.
#[test]
fn test_declaration_after_an_unknown_command_still_parses() {
    for line in ["include h", "omit h", "frobnicate h"] {
        let decls = parse_file(&src(line)).expect("parses");
        let has_theorem = decls
            .iter()
            .any(|d| matches!(d, SurfaceDecl::Theorem { name, .. } if name == "t"));
        assert!(
            has_theorem,
            "`{line}` swallowed the following theorem: {decls:#?}"
        );
    }
}

/// No regression: a bare-name run on the `variable` line itself still binds
/// every name on it.
#[test]
fn test_variable_bare_name_run_on_one_line_still_binds_all() {
    let decls = parse_file("variable α β\n\ntheorem t : True := trivial\n").expect("parses");
    assert_eq!(
        variable_binders(&decls),
        vec![("α".to_string(), false), ("β".to_string(), false)]
    );
}

/// No regression: an INDENTED continuation line is a continuation, not a new
/// command, and is still absorbed — the barrier is a column rule, not a line
/// rule.
#[test]
fn test_variable_binders_continue_on_an_indented_line() {
    let decls = parse_file("variable {α : Type}\n  (x : α)\n\ntheorem t : True := trivial\n")
        .expect("parses");
    assert_eq!(
        variable_binders(&decls),
        vec![("α".to_string(), true), ("x".to_string(), true)]
    );
}

/// A bare-name run that STARTS on the `variable` line stops at the barrier
/// rather than running through it.
#[test]
fn test_variable_bare_run_stops_at_the_next_command_line() {
    let decls =
        parse_file("variable α β\ninclude α\n\ntheorem t : True := trivial\n").expect("parses");
    assert_eq!(
        variable_binders(&decls),
        vec![("α".to_string(), false), ("β".to_string(), false)]
    );
    assert!(
        decls
            .iter()
            .any(|d| matches!(d, SurfaceDecl::IncludeVars { .. })),
        "`include α` must survive as a command: {decls:#?}"
    );
}

/// `universe` has the same greedy ident loop and the same barrier.
#[test]
fn test_universe_does_not_absorb_the_next_command_line() {
    let decls =
        parse_file("universe u v\ninclude h\n\ntheorem t : True := trivial\n").expect("parses");
    let names = decls
        .iter()
        .find_map(|d| match d {
            SurfaceDecl::UniverseDecl { names, .. } => Some(names.clone()),
            _ => None,
        })
        .expect("a `universe` declaration");
    assert_eq!(names, vec!["u".to_string(), "v".to_string()]);
}

/// `include` is not a reserved word in Lean, so the command fires only when a
/// name follows it. A lone `include` is not a command.
#[test]
fn test_include_without_a_name_is_not_a_command() {
    let decls = parse_file("include\n\ntheorem t : True := trivial\n").expect("parses");
    assert!(
        !decls
            .iter()
            .any(|d| matches!(d, SurfaceDecl::IncludeVars { .. })),
        "a bare `include` must not parse as an inclusion command: {decls:#?}"
    );
}

/// `include a b c` includes every name on the line.
#[test]
fn test_include_takes_several_names() {
    let decls =
        parse_file("variable (a b c : Nat)\ninclude a b c\n\ntheorem t : True := trivial\n")
            .expect("parses");
    let names = decls
        .iter()
        .find_map(|d| match d {
            SurfaceDecl::IncludeVars { names, .. } => Some(names.clone()),
            _ => None,
        })
        .expect("an inclusion command");
    assert_eq!(
        names,
        vec!["a".to_string(), "b".to_string(), "c".to_string()]
    );
}

/// The invariant the whole change exists to hold: no command line, recognised
/// or not, may mint an untyped section variable.
#[test]
fn test_no_command_line_mints_an_untyped_section_variable() {
    for line in [
        "include h",
        "omit h",
        "frobnicate h",
        "attribute_like_thing h",
    ] {
        let decls = parse_file(&src(line)).expect("parses");
        for d in &decls {
            if let SurfaceDecl::Variable { binders, .. } = d {
                for b in binders {
                    assert!(
                        b.ty.is_some(),
                        "`{line}` minted untyped section variable `{}`: {decls:#?}",
                        b.name
                    );
                }
            }
        }
    }
}

/// `include h` must not swallow the `omit h` on the NEXT line.
///
/// This is the same fail-open as the `variable` one, one command over, and it
/// was in the first cut of this very fix: `include_omit_names` ran its ident
/// loop with no line discipline, so the two lines parsed as ONE command with
/// names `["h", "omit", "h"]` and the `omit` never existed. Measured
/// 2026-08-25 before the barrier: three declarations where four were written.
#[test]
fn test_include_does_not_absorb_the_following_omit_line() {
    let code = "variable {α : Type} (h : α)\n\
                include h\n\
                omit h\n\
                theorem t : True := trivial\n";
    let decls = parse_file(code).expect("parses");
    let kinds: Vec<&str> = decls.iter().map(decl_kind).collect();
    assert_eq!(
        kinds,
        vec!["Variable", "IncludeVars", "OmitVars", "Theorem"],
        "`include h` and `omit h` are two commands, not one three-name command"
    );
    match (&decls[1], &decls[2]) {
        (SurfaceDecl::IncludeVars { names: inc, .. }, SurfaceDecl::OmitVars { names: om, .. }) => {
            assert_eq!(
                inc,
                &vec!["h".to_string()],
                "include takes only its own line"
            );
            assert_eq!(om, &vec!["h".to_string()], "omit takes only its own line");
        }
        other => panic!("expected IncludeVars then OmitVars, got {other:?}"),
    }
}

/// A name INDENTED past the keyword is still a continuation, exactly as for
/// `variable`. Lean would not accept this shape (its `include` takes its names
/// on one line), so this rule is strictly more permissive and can only accept
/// inputs Lean accepts.
#[test]
fn test_include_names_may_continue_on_an_indented_line() {
    let code = "include h\n  k\ntheorem t : True := trivial\n";
    let decls = parse_file(code).expect("parses");
    match &decls[0] {
        SurfaceDecl::IncludeVars { names, .. } => {
            assert_eq!(names, &vec!["h".to_string(), "k".to_string()]);
        }
        other => panic!("expected IncludeVars, got {other:?}"),
    }
}

/// `include` alone on its line is NOT the command — the first name has to sit
/// on the keyword's own line. Without this the dispatcher would commit to the
/// command arm and then take the next line's first identifier as the name.
#[test]
fn test_include_with_its_name_on_the_next_line_is_not_the_command() {
    let code = "include\nfoo\n";
    let decls = parse_file(code).expect("parses");
    assert_eq!(
        decl_kind(&decls[0]),
        "RawDecl",
        "unknown command, not IncludeVars"
    );
}

/// THE REMAINING FAIL-OPEN, recorded as measured rather than as intent.
///
/// `omit h` written after a TERM-MODE proof never reaches the command
/// dispatcher at all: the proof `:= trivial` is an application head, and the
/// argument loop has no line discipline of its own, so it takes `omit` and `h`
/// as two arguments. Measured 2026-08-25:
///   `proof: App(Ident("trivial"), [Ident("omit"), Ident("h")])`
///
/// This is a DIFFERENT parser path from the two barriers this change adds —
/// term application, not a command's name run — and closing it means giving
/// argument position the `colGt` rule Lean gets for free from `withPosition`.
/// That is a much larger blast radius (every multi-line application in
/// Mathlib) and is deliberately NOT attempted here. The test asserts today's
/// behaviour so that a future fix flips it deliberately instead of silently.
#[test]
fn test_omit_after_a_term_mode_proof_is_absorbed_by_the_proof() {
    let code = "variable {α : Type} (h : α)\n\
                include h\n\
                theorem before : True := trivial\n\
                omit h\n\
                theorem after : True := trivial\n";
    let decls = parse_file(code).expect("parses");
    let kinds: Vec<&str> = decls.iter().map(decl_kind).collect();
    assert_eq!(
        kinds,
        vec!["Variable", "IncludeVars", "Theorem", "Theorem"],
        "MEASURED, not desired: there is no OmitVars — `:= trivial` ate the \
         `omit h` line as two application arguments"
    );
}

/// Short name for a declaration's variant, for the shape assertions above.
fn decl_kind(decl: &SurfaceDecl) -> &'static str {
    match decl {
        SurfaceDecl::Variable { .. } => "Variable",
        SurfaceDecl::IncludeVars { .. } => "IncludeVars",
        SurfaceDecl::OmitVars { .. } => "OmitVars",
        SurfaceDecl::Theorem { .. } => "Theorem",
        SurfaceDecl::RawDecl { .. } => "RawDecl",
        _ => "other",
    }
}
