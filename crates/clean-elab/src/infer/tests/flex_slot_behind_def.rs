// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A dependent-pair constructor applied against a goal that is a `def`
//! application, not a syntactic occurrence of the constructor's own inductive.
//!
//! `Exists.intro : {α} → {p : α → Prop} → (w : α) → p w → Exists p`. When the
//! expected type is `CP (Nat.succ x)` for `def CP (y : Nat) : Prop := ∃ a b, a + b = y`,
//! its head is `CP`, so nothing pins `?p` before the arguments are elaborated.
//! The second argument is then checked against `?p (Nat.succ x)`, and because
//! the witness is a COMPOUND term that constraint is not a Miller pattern:
//! `try_pattern_unify` declines, the structural `App`/`App` rule pairs the two
//! spines POSITIONALLY, `?p := @Exists Nat` is committed, and the argument fails
//! against the predicate lambda with
//!
//! ```text
//! Type mismatch: expected Exists Nat (Nat.succ fvar#0), got
//!   cannot unify expressions of different shape: Discriminant(5) vs Discriminant(4)
//! ```
//!
//! — where the printed "expected" is the poisoned assignment, not anything the
//! user wrote. Lean pins the slot from the expected type first
//! (`propagateExpectedType`, `Elab/App.lean`); Clean now does too, via
//! `elab_app.rs::rigid_arg_in_flex_slot`.
//!
//! Both controls below PASSED before the fix and must keep passing: they fix
//! the boundary at "the goal is behind a `def` AND the proof argument is a
//! compound application". Writing the goal inline exposes the `Exists` head, and
//! passing a bare hypothesis variable routes through
//! `typed_value_arg_in_open_slot` instead.

use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

/// Elaborate every declaration of `code` into a fresh prelude environment,
/// asserting each one registers.
fn elaborate_all(code: &str) -> Environment {
    let decls = parse_file(code).expect("fixture must parse");
    let mut env = Environment::with_prelude();
    let mut file_ctx = crate::FileContext::new();
    for (i, decl) in decls.iter().enumerate() {
        let processed = crate::preprocess_decl_with_context(decl, &mut file_ctx);
        let result = crate::elaborate_decl_and_register(&mut env, &processed);
        assert!(
            result.is_ok(),
            "declaration {} failed: {:?}",
            i,
            result.err()
        );
    }
    env
}

const FIXTURE: &str = r"
def CP (y : Nat) : Prop :=
  Exists (fun (a : Nat) => Exists (fun (b : Nat) => Eq (Nat.add a b) y))

theorem inner1 (x : Nat) :
    Exists (fun (b : Nat) => Eq (Nat.add (Nat.succ x) b) (Nat.succ x)) :=
  Exists.intro Nat.zero rfl

theorem outer_syntactic (x : Nat) :
    Exists (fun (a : Nat) =>
      Exists (fun (b : Nat) => Eq (Nat.add a b) (Nat.succ x))) :=
  Exists.intro (Nat.succ x) (inner1 x)

theorem outer_fvar (x : Nat)
    (h : Exists (fun (b : Nat) => Eq (Nat.add (Nat.succ x) b) (Nat.succ x))) :
    CP (Nat.succ x) :=
  Exists.intro (Nat.succ x) h

theorem outer_bad (x : Nat) : CP (Nat.succ x) :=
  Exists.intro (Nat.succ x) (inner1 x)
";

/// All five declarations elaborate and kernel-register. `outer_bad` is the one
/// that was rejected; the other four are the controls that were always green.
#[test]
fn exists_intro_against_def_headed_goal_elaborates() {
    let env = elaborate_all(FIXTURE);
    for n in ["CP", "inner1", "outer_syntactic", "outer_fvar", "outer_bad"] {
        assert!(
            env.get_const(&Name::from_string(n)).is_some(),
            "declaration {n} must register"
        );
    }
}

/// The `Type`-valued twin of the same shape: `Sigma.mk` against a goal behind a
/// `def`. Same slot shape (`?β w`), same fix — this pins that the repair is keyed
/// on the SLOT, not on `Prop` and not on `Exists`.
///
/// Measured on the pre-fix release binary (2026-08-29): `outer_sigma` was
/// rejected with `Type mismatch: expected fvar#9223372036854775809
/// (Nat.succ Nat.zero), got cannot unify expressions of different shape:
/// Discriminant(3) vs Discriminant(4)` — the same poisoning wearing a different
/// face, here with `?β` still unassigned at print time. Both arguments are
/// compound applications on purpose: a bare `Nat.zero` in the first slot would
/// route through `typed_value_arg_in_open_slot` instead and the case would stop
/// discriminating.
#[test]
fn sigma_mk_against_def_headed_goal_elaborates() {
    let code = r"
def CT (y : Nat) : Type :=
  Sigma (fun (a : Nat) => Nat)

def inner2 (n : Nat) : Nat := n

def outer_sigma : CT (Nat.succ Nat.zero) :=
  Sigma.mk (Nat.succ Nat.zero) (inner2 Nat.zero)
";
    let env = elaborate_all(code);
    assert!(
        env.get_const(&Name::from_string("outer_sigma")).is_some(),
        "outer_sigma must register"
    );
}
