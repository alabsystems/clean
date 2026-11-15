// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pattern lambdas whose LATER positions depend on earlier ones —
//! `fun ⟨_, _⟩ ⟨_, _⟩ h => …` against `∀ p q : α × β, p.1 = q.1 → …` — the
//! shape of `Mathlib/Order/Basic.lean`'s `Prod` preorder instance. Each
//! position is destructured by its own `match` before the next is bound, so
//! the hypothesis binds at its destructured type and the term kernel-checks.

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::Environment;
use clean_parser::parse_file;

fn elab(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

#[test]
fn test_dependent_hypothesis_after_two_destructured_positions() {
    let mut env = Environment::with_prelude();
    let src = "theorem t1 : ∀ (p q : Nat × Nat), p.1 = q.1 → p.1 = q.1 := fun ⟨_, _⟩ ⟨_, _⟩ h => h\n\
               theorem t2 : ∀ (p q : Nat × Nat), p.1 = q.1 → q.1 = p.1 := fun ⟨_, _⟩ ⟨_, _⟩ h => h.symm\n\
               theorem t3 : ∀ (p q : Nat × Nat), p = q → q = p := fun | ⟨_, _⟩, ⟨_, _⟩, h => h.symm\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("dependent pattern lambdas must elaborate and kernel-check: {e}");
    }
}

#[test]
fn test_destructured_components_are_bound_in_order() {
    let mut env = Environment::with_prelude();
    let src = "def t5 : Nat × Nat → Nat → Nat := fun ⟨a, b⟩ c => a + b + c\n\
               theorem t5_eval : t5 (1, 2) 3 = 6 := rfl\n\
               def t6 : Nat × Nat → Nat × Nat → Nat := fun ⟨a, _⟩ ⟨_, d⟩ => a + d\n\
               theorem t6_eval : t6 (1, 2) (3, 4) = 5 := rfl\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("destructuring lambdas must keep positional binding: {e}");
    }
}
