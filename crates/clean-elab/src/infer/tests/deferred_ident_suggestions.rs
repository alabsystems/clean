// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The "did you mean" scan runs for the REPORTED unknown identifier only.
//!
//! `unknown_ident_error` used to run the nearest-theorem Levenshtein scan over
//! every accessible theorem each time an identifier failed to resolve —
//! including on speculative paths that catch the error and move on (a pattern
//! name tried as a constructor before it is bound as a variable). The scan is
//! now deferred (`ElabError::UnknownIdentDeferred`) and materialized at the
//! declaration boundary (`ElabError::with_ident_suggestions`). These pins
//! hold both halves: a declaration that SUCCEEDS after such a speculative
//! miss runs no scan, and a reported miss still carries its suggestions.

use super::*;

fn prelude_env_with_theorem(name: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let prop_name = Name::from_string("deferredTestProp");
    env.add_decl(Declaration::Axiom {
        name: prop_name.clone(),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("prop axiom should register");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("deferredTestProof"),
        level_params: vec![],
        type_: Expr::const_(prop_name.clone(), vec![]),
    })
    .expect("proof axiom should register");
    env.add_decl_structural(Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::const_(prop_name, vec![]),
        value: Expr::const_(Name::from_string("deferredTestProof"), vec![]),
    })
    .expect("theorem should register");
    env
}

#[test]
fn test_deferred_suggestions_speculative_pattern_name_runs_no_scan() {
    let env = Environment::with_prelude();
    let decl = parse_decl_for_elab("def pickDeferred (n : Nat) : Nat := match n with | k => k")
        .expect("parse");
    let scans_before = nearest_theorem_scan_count();
    let minted_before = deferred_ident_error_count();
    let mut ctx = ElabCtx::new(&env);
    let result = ctx.elab_decl(&decl);
    assert!(
        result.is_ok(),
        "a match binding a pattern variable must elaborate, got {result:?}"
    );
    assert!(
        deferred_ident_error_count() > minted_before,
        "the pattern name `k` must have been tried as a constant and missed, \
         or this test is not exercising a speculative miss at all"
    );
    assert_eq!(
        nearest_theorem_scan_count(),
        scans_before,
        "a declaration that succeeded reported no unknown identifier, so no \
         nearest-theorem scan may have run"
    );
}

#[test]
fn test_deferred_suggestions_unmaterialized_error_renders_as_plain_unknown_ident() {
    let env = prelude_env_with_theorem("add_comm_deferred");
    let mut ctx = ElabCtx::new(&env);
    let surface = parse_expr("add_comm_deferre").expect("parse");
    let scans_before = nearest_theorem_scan_count();
    let err = ctx
        .elaborate(&surface)
        .expect_err("identifier should be unknown");
    assert!(
        matches!(&err, ElabError::UnknownIdentDeferred { name, .. } if name == "add_comm_deferre"),
        "inside the elaborator the error is deferred, got {err:?}"
    );
    assert_eq!(err.to_string(), "Unknown identifier: add_comm_deferre");
    assert_eq!(
        nearest_theorem_scan_count(),
        scans_before,
        "raising the error must not scan"
    );

    let reported = err.with_ident_suggestions(&env);
    assert_eq!(
        nearest_theorem_scan_count(),
        scans_before + 1,
        "materializing the reported error scans exactly once"
    );
    match reported {
        ElabError::UnknownIdentWithSuggestions { name, suggestions } => {
            assert_eq!(name, "add_comm_deferre");
            assert_eq!(
                suggestions.first().map(String::as_str),
                Some("add_comm_deferred")
            );
        }
        other => panic!("expected UnknownIdentWithSuggestions, got {other:?}"),
    }
}

#[test]
fn test_deferred_suggestions_registration_boundary_reports_them() {
    // The production entry `clean check` goes through: the error that leaves
    // the per-declaration boundary is materialized.
    let mut env = prelude_env_with_theorem("add_comm_boundary");
    let decl = parse_decl_for_elab("def usesTypo : Prop := add_comm_boundar").expect("parse");
    let err = crate::elaborate_decl_and_register(&mut env, &decl)
        .expect_err("a typo'd identifier must fail the declaration");
    let rendered = err.to_string();
    assert!(
        rendered.contains("nearest theorem names") && rendered.contains("add_comm_boundary"),
        "the reported error must carry its suggestions, got: {rendered}"
    );
}
