// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression coverage for the flex-head beta-redex unification bug.
//!
//! `Eq.mp (congrArg (fun o => P (C o)) h) proof` elaborates congrArg against
//! an expected type whose sides are FLEX applications (`?f a₁ = ?f a₂`, the
//! slot metas minted by the pre-arg expected-result unification). The
//! resulting constraint pair is
//!
//! ```text
//! (fun o => Ev s n (Value.nat o)) x   =?=   ?f x
//! ```
//!
//! Two defects conspired to reject it (and, worse, to poison `?f` for every
//! later consumer, surfacing far away as an opaque shape mismatch with a
//! mangled expected type — the trust-spec-temporal FiniteModel
//! `exactScalarVar` regression):
//!
//! 1. The App/App argument WHNF beta-reduced the LEFT side first, destroying
//!    the very lambda the flex head must be assigned; first-order
//!    decomposition of the reduced form then projected the TYPE-INCORRECT
//!    head `?f := Ev s n` (`Nat → Prop` slot, `Value → Prop` candidate).
//! 2. `unify_meta` assigned it without ever comparing types.
//!
//! The fixes: keep a Lam-headed argument unreduced when the opposite
//! argument is flex-headed (so the spines pair and `?f` receives the
//! most-general lambda — Lean's pattern imitation for this shape), and
//! type-guard function-typed metavariable assignments on meta-free Pi
//! domains (returning `Stuck`, Lean's postpone, instead of poisoning).

use clean_kernel::Environment;
use clean_parser::parse_file;

/// The minimal reproducer distilled from trust-spec-temporal's FiniteModel
/// prelude (`exactScalarVar`): transport a constructor-indexed inductive
/// proposition along a projection equality via `Eq.mp ∘ congrArg`.
#[test]
fn eq_mp_congr_arg_lambda_motive_over_constructor_elaborates() {
    let code = r#"
structure State where
  scalar : String -> Nat
  function : String -> Nat -> Bool

inductive Value where
  | nat : Nat -> Value

inductive Ev : State -> String -> Value -> Prop where
  | var (state : State) (name : String) : Ev state name (Value.nat (state.scalar name))

theorem probeMp (state : State) (name : String) (value : Nat)
    (coordinate : state.scalar name = value) :
    Ev state name (Value.nat value) :=
  Eq.mp
    (congrArg (fun output => Ev state name (Value.nat output)) coordinate)
    (Ev.var state name)
"#;
    let decls = parse_file(code).expect("parse should succeed");
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
}

/// The same transport where the motive needs no constructor wrapper — the
/// flex head must still receive the lambda, not a projected spine head.
#[test]
fn eq_mp_congr_arg_plain_lambda_motive_elaborates() {
    let code = r#"
structure State where
  scalar : String -> Nat
  function : String -> Nat -> Bool

inductive P : Nat -> Prop where
  | intro (n : Nat) : P n

theorem transport (state : State) (name : String) (value : Nat)
    (coordinate : state.scalar name = value) :
    P value :=
  Eq.mp
    (congrArg (fun output => P output) coordinate)
    (P.intro (state.scalar name))
"#;
    let decls = parse_file(code).expect("parse should succeed");
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
}
