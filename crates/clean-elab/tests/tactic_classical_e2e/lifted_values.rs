// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{try_elaborate_into, Environment, Name};

#[test]
fn let_i_lifts_only_explicit_rhs_goals_after_the_continuation() {
    let mut env = Environment::with_prelude();
    for source in [
        "def liftedValue : Nat := by
  letI supplied : Nat := ?_
  exact supplied
  exact 23",
        "example : liftedValue = 23 := rfl",
        "def liftedArgument : Nat := by
  letI a : Nat := Nat.succ ?_
  exact a
  exact 22",
        "example : liftedArgument = 23 := rfl",
        "def liftedPair : Nat := by
  letI pair : Nat × Nat := (?a, ?b)
  exact pair.1 + pair.2
  case a => exact 20
  case b => exact 3",
        "example : liftedPair = 23 := rfl",
        "def liftedFunction : Nat := by
  letI f : Nat → Nat := fun n => ?body
  exact f 23
  case body => exact n",
        "example : liftedFunction = 23 := rfl",
        "def liftedSibling : Nat × Nat := by
  constructor
  letI a : Nat := ?_
  exact a
  exact 19
  exact 31",
        "example : liftedSibling = (19, 31) := rfl",
        "def solvedNatural : Nat := by
  letI a : Nat := @id _ 23
  exact a",
        "example : solvedNatural = 23 := rfl",
    ] {
        try_elaborate_into(&mut env, source).unwrap_or_else(|error| panic!("{source}\n{error}"));
    }
}

#[test]
fn let_i_synthetic_rhs_hole_survives_a_user_macro() {
    let mut env = Environment::with_prelude();
    let source = r#"macro "bumpLift " x:term : term => `(Nat.succ $x)
def macroLifted : Nat := by
  letI a : Nat := bumpLift ?_
  exact a
  exact 22
theorem macroLifted_result : macroLifted = 23 := rfl"#;
    try_elaborate_into(&mut env, source).expect("the macro operand must stay a lifted goal");
    assert!(env
        .get_const(&Name::from_string("macroLifted_result"))
        .is_some());
}

#[test]
fn let_i_refuses_unfinished_even_unused_rhs_goals() {
    let mut env = Environment::with_prelude();
    for body in [
        "letI supplied : Nat := ?_\n  exact 0",
        "letI supplied : Nat := _\n  exact 0",
        "letI supplied : Nat := _\n  exact 0\n  exact 23",
        "letI pair : Nat × Nat := (_, ?b)\n  exact 0\n  exact 20\n  exact 3",
        "letI supplied : Nat := ?_\n  exact 0\n  exact supplied",
    ] {
        let source = format!("def unfinished : Nat := by\n  {body}");
        assert!(try_elaborate_into(&mut env, &source).is_err(), "{source}");
        assert!(env.get_const(&Name::from_string("unfinished")).is_none());
    }
}
