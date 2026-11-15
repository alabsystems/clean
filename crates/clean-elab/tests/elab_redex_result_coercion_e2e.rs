// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Where Lean 4.8.0 settles a term's type before it sees the expected type,
//! and where it lets the expected type in first, measured by the inc8
//! differential hunt (5,985 coercion-context files judged by Lean 4.8.0;
//! Clean `a9203a200` accepted 87 statements Lean refutes):
//!
//! * `redex_result.lean`: a fully applied lambda with untyped binders,
//!   elaborated in Lean's order (`infer/elab_beta_redex.rs`), whose head
//!   settles a GROUND result type that differs from a ground expected type,
//!   is coerced as a whole, as Lean's `ensureHasType` coerces the result of
//!   `elabAppArgs`; and an identity-like head meets the expected type before
//!   its argument (`propagateExpectedType`).
//! * `binop_leaf.lean`: a compound operand of an arithmetic operator is
//!   elaborated with no expected type and coerced, as `binop%` elaborates a
//!   leaf (`infer/elab_binop_leaf.rs`): `(id ((1 : Nat) - 7) - 7 : Int)` is
//!   `-7`, where Clean proved `-13`; the expected type reaches a polymorphic
//!   head's slot before a sibling operand pins it (`min (1 - 7) 9 : Int` is
//!   `-6`); and a field-notation receiver's numerals wait for the expected
//!   type (`infer/elab_proj_waiting.rs`: `((some (1 - 7)).getD 0 : Int)` is
//!   `-6`, where Clean proved `0`).
//! * `defaulting_leaf.lean`: a LATER operand whose result is an open
//!   `outParam` (`HAdd.hAdd (1 : Nat) 0`, `xs[0]!`) runs Lean's
//!   `synthesizeSyntheticMVarsUsingDefault`, so an earlier operand whose type
//!   only its numerals decide is `Nat` and coerced (`(id (1 - 7) + HAdd.hAdd
//!   (1 : Nat) 0 : Int)` is `1`; the first cut of this change proved `-5`),
//!   and an operand before it, or one whose instance is found, is not.
//! * `redex_escape.lean`: a β-redex whose head queues an instance goal over
//!   its binder (`Decidable (y = 1)`) is elaborated again with the binder
//!   types its first attempt settled, so the goal is answered in place (the
//!   answer escaped the closed binder, and `decide` refused a true statement,
//!   or the let-chain's typing proved `((fun y => if y = 1 then (0 : Nat) - 1
//!   else 2) 1 : Int) = -1`; Lean: `0`).
//!
//! Measured 2026-10-29 (Clean `a9203a200`, the inc8 differential hunt): `clean
//! check` accepted `((fun y => y - (7 : Nat)) 1 : Int) ≠ 0 := by decide`, a
//! statement Lean 4.8.0 refutes (`↑((fun y => y - 7) 1) = 0`). Lean's order
//! typed the redex at `Nat` and then failed on the mismatch with `Int`, so the
//! let-chain's term stood, and the let-chain elaborated the body against
//! `Int` (`↑1 - ↑7 = -6`).
//!
//! Lean 4.8.0 accepts every fixture (`lean <file>`, exit 0) and refuses each
//! mutation (one theorem's `=` turned into `≠`, 19, 44, 14 and 5 errors);
//! Clean at `a9203a200` accepted 8 and 18 of the first two fixtures'
//! mutations. [`ILL_TYPED`] is refused
//! by Lean 4.8.0 and here.

use std::sync::mpsc;
use std::time::Duration;

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::{parse_file_with_diagnostics, SurfaceDecl};

/// Run `body` on its own thread and fail if it has not finished within a
/// minute. A hang detector, not a latency budget.
fn within_a_minute(what: &str, body: impl FnOnce() + Send + 'static) {
    let (done, finished) = mpsc::channel();
    let worker = std::thread::Builder::new()
        .name(what.to_string())
        .stack_size(256 << 20)
        .spawn(move || {
            body();
            let _ = done.send(());
        })
        .expect("spawn the test body");
    match finished.recv_timeout(Duration::from_secs(60)) {
        Ok(()) => worker.join().expect("test body"),
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            if let Err(panic) = worker.join() {
                std::panic::resume_unwind(panic);
            }
        }
        Err(mpsc::RecvTimeoutError::Timeout) => {
            panic!("hang detector: `{what}` did not finish within one minute")
        }
    }
}

fn decl_name(decl: &SurfaceDecl) -> String {
    match decl {
        SurfaceDecl::Def { name, .. } | SurfaceDecl::Theorem { name, .. } => name.to_string(),
        _ => String::from("<other>"),
    }
}

/// Elaborate every declaration of `source` in order, as `clean check` does:
/// each one's name and error, if any.
fn elaborate(source: &str) -> (Environment, Vec<(String, Option<String>)>) {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let report =
        parse_file_with_diagnostics(source).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    assert!(
        report.diagnostics.is_empty(),
        "fixture must parse without recovery: {:?}",
        report.diagnostics
    );
    let mut results = Vec::new();
    for decl in &report.decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let error = elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
            .err()
            .map(|e| e.to_string());
        results.push((decl_name(decl), error));
    }
    (env, results)
}

fn failures(results: &[(String, Option<String>)]) -> Vec<(&str, &str)> {
    results
        .iter()
        .filter_map(|(name, error)| error.as_deref().map(|e| (name.as_str(), e)))
        .collect()
}

const REDEX_RESULT: &str = include_str!("elab_redex_result_coercion/redex_result.lean");
const BINOP_LEAF: &str = include_str!("elab_redex_result_coercion/binop_leaf.lean");
const DEFAULTING_LEAF: &str = include_str!("elab_redex_result_coercion/defaulting_leaf.lean");
const REDEX_ESCAPE: &str = include_str!("elab_redex_result_coercion/redex_escape.lean");
/// Each fixture and its theorem count.
const FIXTURES: &[(&str, &str, usize)] = &[
    ("redex_result", REDEX_RESULT, 19),
    ("binop_leaf", BINOP_LEAF, 44),
    ("defaulting_leaf", DEFAULTING_LEAF, 14),
    ("redex_escape", REDEX_ESCAPE, 5),
];

/// A fixture's theorem names, in order.
fn theorems(fixture: &'static str) -> Vec<&'static str> {
    fixture
        .lines()
        .filter_map(|line| line.strip_prefix("theorem "))
        .filter_map(|rest| rest.split_whitespace().next())
        .collect()
}

#[test]
fn each_fixture_elaborates_at_leans_values() {
    within_a_minute("fixtures", || {
        for (label, fixture, count) in FIXTURES {
            let (env, results) = elaborate(fixture);
            let failed = failures(&results);
            assert!(failed.is_empty(), "`{label}` must elaborate: {failed:#?}");
            let names = theorems(fixture);
            assert_eq!(names.len(), *count, "`{label}`'s theorem count");
            for theorem in names {
                let name = Name::from_string(theorem);
                assert!(
                    env.get_const(&name).is_some(),
                    "`{theorem}` must be registered"
                );
                let deps = env
                    .axiom_deps(&name)
                    .unwrap_or_else(|| panic!("`{theorem}` must have an axiom closure"));
                assert!(
                    deps.is_empty(),
                    "`{theorem}` must be axiom-free, got {deps:?}"
                );
            }
        }
    });
}

/// Each theorem's `=` turned into `≠` is refused, for its value. Each
/// mutation is checked over the fixture's definitions alone (the other
/// theorems are the positive test's), under its own hang detector.
#[test]
fn each_negated_theorem_is_refused() {
    for (label, fixture, _) in FIXTURES {
        let prelude: String = fixture
            .lines()
            .filter(|l| !l.starts_with("theorem "))
            .map(|l| format!("{l}\n"))
            .collect();
        for theorem in theorems(fixture) {
            let line = fixture
                .lines()
                .find(|l| l.starts_with(&format!("theorem {theorem} ")))
                .expect("the theorem's line");
            assert_eq!(line.matches(") = (").count(), 1, "`{theorem}`: one `=`");
            let mutated = format!("{prelude}{}\n", line.replace(") = (", ") ≠ ("));
            within_a_minute(theorem, move || {
                let (_, results) = elaborate(&mutated);
                let failed = failures(&results);
                assert_eq!(
                    failed.iter().map(|(name, _)| *name).collect::<Vec<_>>(),
                    vec![theorem],
                    "`{label}`: only the negated `{theorem}` may fail: {failed:#?}"
                );
                let error = failed[0].1.to_lowercase();
                assert!(
                    error.contains("decide"),
                    "`{theorem}` must be refused by `decide` for its value: {error}"
                );
            });
        }
    }
}

/// Statements Lean 4.8.0 refutes whose operand holds a term Lean postpones
/// (`match`) or a `let` whose numerals must wait with the probe's: a leaf
/// probe that elaborated those in place, or let the inner `let` drain its
/// numerals, settled `Nat` where Lean's leaf is still open, and accepted
/// these (each was accepted by an intermediate build of this change).
const REFUTED: &[&str] = &[
    "def nN : Nat := 1\ntheorem n0 : (((fun z => z - 7) (match 0 with | _ => Nat.succ 0) - 3 : Int)) ≠ (-9) := by decide\n",
    "def nN : Nat := 1\ntheorem n2 : (((let z := (· - 7) (min 1 9 - 5); z) - 3 : Int)) ≠ (-14) := by decide\n",
];

#[test]
fn a_leaf_lean_leaves_open_is_not_settled_alone() {
    within_a_minute("refuted", || {
        for source in REFUTED {
            let (_, results) = elaborate(source);
            assert_eq!(
                failures(&results).len(),
                1,
                "the theorem in `{source}` must be refused, as Lean 4.8.0 refuses it: {results:#?}"
            );
        }
    });
}

/// Lean 4.8.0 refuses each of these (`HSub Nat Nat Int`, `HAdd UInt8 UInt8
/// Nat`): the body's type is settled before the expected type is seen, and
/// no instance makes the operator land in the expected type.
const ILL_TYPED: &[&str] = &[
    "def d0 := ((fun y => y - 7) (1 : Nat) : Int)",
    "def d1 := ((fun y z => y - z) (1 : Nat) (3 : Nat) : Int)",
    "def d2 := ((fun y z => y - z) 1 (3 : Nat) : Int)",
    "def d4 := ((fun y => y + (7 : UInt8)) 250 : Nat)",
    "def d5 := ((fun x y => x - y) (2 : Nat) 5 : Int)",
];

#[test]
fn a_redex_lean_finds_ill_typed_stays_refused() {
    within_a_minute("ill_typed", || {
        for source in ILL_TYPED {
            let (_, results) = elaborate(source);
            assert!(
                !failures(&results).is_empty(),
                "`{source}` must be refused, as Lean 4.8.0 refuses it: {results:#?}"
            );
        }
    });
}
