// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression coverage for issue #3534.
//!
//! #3534 — "`instance : Inhabited T := ⟨0⟩` fails with
//!          NotImplemented(\"class Inhabited not found in environment\") even
//!          though `def a : Inhabited T := ⟨0⟩` succeeds."
//!
//! Before the fix, this program failed under the default prelude:
//!
//! ```lean
//! instance : Inhabited Nat := ⟨0⟩
//! ```
//!
//! ...with:
//!
//! ```
//! NotImplemented("class Inhabited not found in environment (must be
//! declared as a class/structure first)")
//! ```
//!
//! while the seemingly-identical `def` form elaborated successfully:
//!
//! ```lean
//! def a : Inhabited Nat := ⟨0⟩   -- ok
//! ```
//!
//! ## Root cause
//!
//! The `instance` elaborator (`elab_instance.rs`) unconditionally required the
//! class to have been registered via `register_structure_fields`, because it
//! used `env.get_structure_field_names(class_name)` as the FIRST operation on
//! every instance regardless of syntactic form. Kernel-builtin classes like
//! `Inhabited` are registered via `add_inductive()` during prelude init but
//! never via `register_structure_fields`, so this lookup failed before the
//! elaborator ever examined the user-supplied value.
//!
//! The `def` path, by contrast, routes through `elab_anonymous_ctor`, which
//! uses `get_inductive(class_name)` — a lookup populated by `add_inductive`
//! alone. This is why `def a : Inhabited Nat := ⟨0⟩` worked even when the
//! `instance` form failed.
//!
//! ## Fix
//!
//! Detect the short-form instance syntax (`instance : Class := expr`, which
//! the parser represents as a single pseudo-field named `_value`) and route
//! it through a new helper that elaborates the value expression against the
//! class type as the expected type. This dispatches through the same general
//! elaboration path that `def` uses, so it works uniformly for user-defined
//! classes AND kernel-builtins that are registered only via `add_inductive`.
//!
//! The long-form `where`-syntax path is unchanged.

use crate::elaborate_decl_and_register;
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

fn elaborate_all(env: &mut Environment, code: &str, label: &str) {
    let decls = parse_file(code).unwrap_or_else(|e| panic!("{label}: parse failed: {e:?}"));
    for (i, decl) in decls.iter().enumerate() {
        let result = elaborate_decl_and_register(env, decl);
        assert!(
            result.is_ok(),
            "{label}: decl {i} should elaborate, got: {result:?}"
        );
    }
}

/// Exact repro from the issue body. Short-form instance of a kernel-builtin
/// class (`Inhabited`) that is registered via `add_inductive` only.
///
/// Uses a named instance so this test is independent of whether the prelude
/// already registers `instInhabitedNat` (which it does for `Nat` and `Bool`).
/// Before the fix, this failed with `NotImplemented("class Inhabited not
/// found in environment...")` regardless of the instance name.
#[test]
fn test_issue_3534_instance_inhabited_nat_short_form() {
    let mut env = Environment::with_prelude();
    let code = "instance myInhNat : Inhabited Nat := ⟨0⟩\n";
    elaborate_all(&mut env, code, "#3534 exact repro");
    assert!(
        env.get_const(&Name::from_string("myInhNat")).is_some(),
        "myInhNat should be registered after #3534 fix"
    );
}

/// Parity check: `def` form should continue to work (regression guard).
#[test]
fn test_issue_3534_def_inhabited_nat_still_works() {
    let mut env = Environment::with_prelude();
    let code = "def a : Inhabited Nat := ⟨0⟩\n";
    elaborate_all(&mut env, code, "#3534 def form parity");
    assert!(env.get_const(&Name::from_string("a")).is_some());
}

/// Short form with a named instance.
#[test]
fn test_issue_3534_named_instance_short_form() {
    let mut env = Environment::with_prelude();
    let code = "instance inhNat : Inhabited Nat := ⟨0⟩\n";
    elaborate_all(&mut env, code, "#3534 named instance");
    assert!(env.get_const(&Name::from_string("inhNat")).is_some());
}

/// Short form over a different primitive type (`Inhabited String`).
#[test]
fn test_issue_3534_instance_inhabited_string_short_form() {
    let mut env = Environment::with_prelude();
    let code = "instance : Inhabited String := ⟨\"\"⟩\n";
    elaborate_all(&mut env, code, "#3534 String variant");
    assert!(env
        .get_const(&Name::from_string("instInhabitedString"))
        .is_some());
}

/// Short form over a user-defined class (independent of Inhabited): the
/// fix must also work when the class IS registered via
/// `register_structure_fields`, to keep the user-defined path working.
#[test]
fn test_issue_3534_user_class_short_form() {
    let mut env = Environment::with_prelude();
    let code = r#"
class Foo (α : Type) where
  bar : α

instance : Foo Nat := ⟨0⟩
"#;
    elaborate_all(&mut env, code, "#3534 user class short form");
    assert!(env.get_const(&Name::from_string("instFooNat")).is_some());
}

/// Long-form (`where` syntax) must continue to work for user-defined classes.
/// Regression guard for the unchanged path.
#[test]
fn test_issue_3534_user_class_where_form_still_works() {
    let mut env = Environment::with_prelude();
    let code = r#"
class Foo (α : Type) where
  bar : α

instance : Foo Nat where
  bar := 0
"#;
    elaborate_all(&mut env, code, "#3534 user class where form");
    assert!(env.get_const(&Name::from_string("instFooNat")).is_some());
}
