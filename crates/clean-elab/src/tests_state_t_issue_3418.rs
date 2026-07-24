// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression coverage for issue #3418 using the exact naming
//! (`Sem` / `SemError` / `MState`) from the issue body's narrative error
//! message.
//!
//! The core fix for #3418 landed in:
//!   - `2ee0f17da` (Unit := PUnit.{1} as a reducible definition)
//!   - `42b95848d` (StateT.modify/modifyGet registration + coverage)
//!
//! `lib_tests.rs` already covers the `MySem`/`MyError`/`MyState` rename
//! variant (`test_state_t_set_punit_unit_equality`,
//! `test_state_t_modify_punit_unit_equality`). This file locks in coverage
//! against the exact `Sem` / `SemError` / `MState` naming from the issue
//! body so future textual searches against the error-message narrative
//! also match live test coverage.

use crate::elaborate_decl_and_register;
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

/// Regression test for #3418 using the exact `Sem`/`SemError`/`MState`
/// naming from the issue body narrative.
///
/// The issue's error message states:
///   "expected `Sem Unit`, got `StateT MState (Except SemError) PUnit.{1}`"
///
/// This test elaborates a declaration that triggers exactly that
/// unification obligation and asserts it succeeds.
#[test]
fn test_state_t_set_sem_abbrev_punit_unit_issue_body_naming() {
    let mut env = Environment::with_prelude();
    let code = r#"
inductive SemError where
  | notFound : SemError

structure MState where
  counter : Nat

abbrev Sem (a : Type) := StateT MState (Except SemError) a

def Sem.setState (s : MState) : Sem Unit := StateT.set s
"#;
    let decls = parse_file(code).expect("should parse #3418 issue-body snippet");
    for (i, decl) in decls.iter().enumerate() {
        let result = elaborate_decl_and_register(&mut env, decl);
        assert!(
            result.is_ok(),
            "#3418 regression (issue-body naming): decl {} should elaborate: {:?}",
            i,
            result
        );
    }

    let info = env.get_const(&Name::from_string("Sem.setState"));
    assert!(
        info.is_some(),
        "Sem.setState should be registered (issue-body-naming regression)"
    );
    let info = info.unwrap();
    assert!(
        info.level_params.is_empty(),
        "Sem.setState should have zero universe params, but has: {:?}",
        info.level_params
    );
}
