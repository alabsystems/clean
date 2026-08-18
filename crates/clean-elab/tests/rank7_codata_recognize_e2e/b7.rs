// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! B7 observational soundness artifacts for the rank-7 end-to-end lane.

use super::*;

/// The observational theorem holds, with an EMPTY axiom closure.
///
/// This is rank 7's actual width-one claim: for every finite depth, observing
/// the source equals decoding the forced target. The axiom-closure assertion
/// distinguishes a proof from a formalization that imports extra authority.
#[test]
fn observational_soundness_is_proved_with_empty_axiom_closure() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/codata/is2_extraction_soundness.lean");
    let src = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("B7 fixture must exist at {}: {e}", path.display()));
    let env = elab(&src);

    let thm = Name::from_string("doubler_extraction_observationally_correct");
    assert!(
        env.get_const(&thm).is_some(),
        "the observational theorem must be registered"
    );
    let deps = env
        .axiom_deps(&thm)
        .unwrap_or_else(|| panic!("{thm} must be registered"));
    assert!(
        deps.is_empty(),
        "the observational theorem must have an EMPTY axiom closure — \
         anything else means this is a formalization, not a proof; got {deps:?}"
    );
}

/// A wrong emitted term must break the indexed observational theorem.
#[test]
fn soundness_theorem_is_not_vacuous() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/codata/is2_extraction_soundness_MUST_FAIL.lean");
    let src = std::fs::read_to_string(&path).expect("negative control must exist");

    let mut env = Environment::with_prelude();
    let decls = parse_file(&src).expect("the mutant must still PARSE");
    let mut failed = false;
    for decl in &decls {
        if elaborate_decl_and_register(&mut env, decl).is_err() {
            failed = true;
        }
    }
    assert!(
        failed,
        "the observational theorem must NOT hold for a wrong emitted term — \
         if this passes, the theorem is vacuous"
    );
}

/// The same certificate holds for a structurally different, plain chain.
#[test]
fn plain_lane_soundness_is_proved_with_empty_axiom_closure() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/codata/st_extraction_soundness.lean");
    let src = std::fs::read_to_string(&path).expect("plain-lane B7 fixture must exist");
    let env = elab(&src);

    let thm = Name::from_string("count_extraction_observationally_correct");
    let deps = env
        .axiom_deps(&thm)
        .unwrap_or_else(|| panic!("{thm} must be registered"));
    assert!(
        deps.is_empty(),
        "the plain-lane observational theorem must have an EMPTY axiom \
         closure; got {deps:?}"
    );
}

/// The plain-lane theorem's wrong-target control must fail too.
#[test]
fn plain_lane_theorem_is_not_vacuous() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/codata/st_extraction_soundness_MUST_FAIL.lean");
    let src = std::fs::read_to_string(&path).expect("negative control must exist");
    let mut env = Environment::with_prelude();
    let decls = parse_file(&src).expect("the mutant must still PARSE");
    let mut failed = false;
    for decl in &decls {
        if elaborate_decl_and_register(&mut env, decl).is_err() {
            failed = true;
        }
    }
    assert!(
        failed,
        "a wrong emitted term must break the plain-lane theorem — \
         if this passes, the theorem is vacuous"
    );
}
