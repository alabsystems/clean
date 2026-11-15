// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! G32 (ledger (102)): the builtin `Except` is Lean 4.8.0's two-universe
//! `Except.{u, v}`, and instance search meets its `Monad.{u_1, max u_1 u}`
//! instance at mixed universes by deciding a class level only after the
//! arguments (`infer/instance.rs`). Lean verdicts measured with the pinned
//! toolchain on 2026-10-16; repro `reports/trust-ir-semantics-probe/repros/
//! G32-except-two-universes.lean`.

use clean_kernel::Environment;

use crate::{ElabError, ElabResult};

fn run_source(source: &str) -> Vec<Result<ElabResult, ElabError>> {
    let mut env = Environment::with_prelude();
    let mut file = crate::FileContext::new();
    let declarations = clean_parser::parse_file(source).expect("test source parses");
    declarations
        .iter()
        .map(|decl| {
            let decl = crate::preprocess_decl_with_context(decl, &mut file);
            crate::elaborate_decl_and_register_with_context(&mut env, &decl, &mut file)
        })
        .collect()
}

#[test]
fn test_except_error_and_value_universes_are_independent() {
    let results = run_source(
        "def typeResult : Except String Type := .ok Nat\n\
         theorem typeResult_ok : typeResult = Except.ok Nat := rfl\n\
         def liftResult {ε : Type} {α : Type 1} (e : Except ε α) : Except ε α := e.bind pure\n\
         def p6 {ε : Type 1} {α : Type} (a : α) : Except ε α := pure a\n",
    );
    for result in &results {
        assert!(result.is_ok(), "Lean 4.8.0 accepts this: {result:?}");
    }
}

/// `Except String Type : Type 1`; Lean refuses it at `Type`.
#[test]
fn test_except_universe_is_the_max_of_both() {
    let results = run_source("def typeResultLow : (Except String Type : Type) := .ok Nat\n");
    let error = results[0]
        .as_ref()
        .expect_err("Lean 4.8.0 refuses `(Except String Type : Type)`");
    assert!(
        error.to_string().contains("universe level conflict"),
        "{error}"
    );
}

/// The everyday `Type 0` monad is unchanged: `do`, `throw`, `tryCatch`,
/// `<$>` and `ExceptT` all still elaborate and compute.
#[test]
fn test_except_monad_at_type_zero_still_computes() {
    let results = run_source(
        "def f : Except String Nat := do\n  let x ← pure 1\n  if x > 5 then throw \"big\"\n  return x + 1\n\
         theorem f_ok : f = .ok 2 := rfl\n\
         def k : Except String Nat := tryCatch (throw \"e\") (fun _ => pure 3)\n\
         theorem k_ok : k = .ok 3 := rfl\n\
         def h (e : Except String Nat) : Except String Nat := (· + 1) <$> e\n\
         def m : ExceptT String Id Nat := do\n  let x ← pure 1\n  if x > 5 then throw \"big\"\n  return x\n",
    );
    for result in &results {
        assert!(result.is_ok(), "Lean 4.8.0 accepts this: {result:?}");
    }
}
