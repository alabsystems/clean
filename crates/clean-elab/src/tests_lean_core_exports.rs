// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! G44 (ledger (114)): the builtin prelude carries Lean 4.8.0's `Init`
//! `export` aliases whose targets it declares, so `forIn` is `ForIn.forIn`
//! (`export ForIn (forIn)`, `Init/Core.lean`). Lean verdicts measured with
//! the pinned toolchain on 2026-10-16; repro
//! `reports/trust-ir-semantics-probe/repros/G44-forin-export-alias.lean`.

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
fn test_for_in_export_alias_elaborates_and_computes() {
    let results = run_source(
        "def sumFor (xs : List Nat) : Id Nat :=\n  \
         forIn xs 0 (fun x acc => pure (ForInStep.yield (acc + x)))\n\
         theorem sumFor_two : sumFor [1, 2] = 3 := rfl\n",
    );
    for result in &results {
        assert!(result.is_ok(), "Lean 4.8.0 accepts this: {result:?}");
    }
}

/// Twin: Lean refuses a step function that returns a bare accumulator
/// ("failed to synthesize instance HAdd Nat Nat (ForInStep Nat)"); the
/// refusal must be about the step type, never an unknown `forIn`.
#[test]
fn test_for_in_export_alias_keeps_the_step_type() {
    let results = run_source(
        "def sumForBad (xs : List Nat) : Id Nat :=\n  \
         forIn xs 0 (fun x acc => pure (acc + x))\n",
    );
    let error = results[0]
        .as_ref()
        .expect_err("Lean 4.8.0 refuses a non-`ForInStep` step");
    let text = error.to_string();
    assert!(
        !text.contains("Unknown identifier"),
        "`forIn` must resolve: {text}"
    );
}
