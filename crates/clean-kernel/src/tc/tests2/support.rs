// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared Nat-inductive fixture helpers for tc/tests2 test suites.
//!
//! Consolidates the repeated Nat environment setup that was duplicated
//! across no_confusion, iota, and recursor test files.

use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

/// Core helper: add a minimal Nat inductive (zero/succ) to an environment.
/// Returns the Nat name and Nat type reference.
pub(super) fn add_nat_inductive(env: &mut Environment) -> (Name, Expr) {
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::arrow(nat_ref.clone(), nat_ref.clone()),
                },
            ],
        }],
    };

    env.add_inductive(decl)
        .expect("invariant: Nat inductive registers");
    (nat, nat_ref)
}

/// Plain Nat environment (no Eq).
pub(super) fn make_nat_env() -> Environment {
    let mut env = Environment::new();
    let _ = add_nat_inductive(&mut env);
    env
}

/// Nat environment with Eq initialized (needed for noConfusion tests).
pub(super) fn make_nat_env_with_eq() -> Environment {
    let mut env = make_nat_env();
    env.init_eq().expect("invariant: Eq initializes");
    env
}

/// Nat environment returning the Nat type expression.
pub(super) fn make_nat_env_and_ref() -> (Environment, Expr) {
    let mut env = Environment::new();
    let (_nat, nat_ref) = add_nat_inductive(&mut env);
    (env, nat_ref)
}

/// Nat environment returning both the Name and type expression.
pub(super) fn make_nat_env_named() -> (Environment, Name, Expr) {
    let mut env = Environment::new();
    let (nat, nat_ref) = add_nat_inductive(&mut env);
    (env, nat, nat_ref)
}
