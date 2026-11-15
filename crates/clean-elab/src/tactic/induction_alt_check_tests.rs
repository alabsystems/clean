// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `with`-alternative checks of `cases`/`induction`
//! (`tactic::induction_alt_check`), each against what pinned Lean
//! v4.30.0-rc2 does with the same source.
//!
//! Every refusal below is a file Lean rejects with the message quoted; every
//! acceptance is a file Lean accepts. Before the checks, Clean took the first
//! `| _ =>` for every case and never elaborated a later alternative, so
//! `| _ => rfl | _ => exact Nat.zero` (an ill-typed second alternative)
//! was accepted.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

const TWO: &str = "inductive AltT where\n  | a : AltT\n  | b : AltT\n";

const IDX: &str = "inductive AltV : Nat → Type where\n  | z : AltV 0\n  | s : AltV 1\n";

fn elab(code: &str) -> (Environment, Vec<Result<ElabResult, crate::ElabError>>) {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).expect("parse_file should succeed");
    let results = decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
        })
        .collect();
    (env, results)
}

/// The last declaration of `prefix ++ body` is refused with `expected` in its
/// error, and every earlier one elaborates.
fn assert_refused(prefix: &str, body: &str, expected: &str) {
    let (_, results) = elab(&format!("{prefix}{body}"));
    let (last, earlier) = results.split_last().expect("at least one declaration");
    for r in earlier {
        r.as_ref().expect("the inductive prefix elaborates");
    }
    let err = last
        .as_ref()
        .expect_err("Lean refuses this alternative list");
    let msg = format!("{err:?}");
    assert!(msg.contains(expected), "expected `{expected}` in {msg}");
}

/// Every declaration elaborates and `t1` is registered free of `sorry`.
fn assert_accepted(prefix: &str, body: &str) {
    let (env, results) = elab(&format!("{prefix}{body}"));
    for r in &results {
        r.as_ref().expect("Lean accepts this alternative list");
    }
    let name = Name::from_string("t1");
    let deps = env.axiom_deps(&name).expect("t1 is registered");
    assert!(
        !deps.iter().any(|d| d.to_string().contains("sorry")),
        "t1 must not depend on sorry: {deps:?}"
    );
}

const WILDCARD_NOT_LAST: &str = "It must be the last alternative";

#[test]
fn test_induction_wildcard_before_named_alt_is_refused() {
    assert_refused(
        TWO,
        "theorem t1 (t : AltT) : t = t := by\n  induction t with\n  | _ => rfl\n  | b => rfl\n",
        WILDCARD_NOT_LAST,
    );
}

#[test]
fn test_cases_two_wildcards_are_refused() {
    assert_refused(
        TWO,
        "theorem t1 (t : AltT) : t = t := by\n  cases t with\n  | _ => rfl\n  | _ => rfl\n",
        WILDCARD_NOT_LAST,
    );
}

/// The case that exposed the gap: the second alternative is ill-typed and
/// Clean never elaborated it.
#[test]
fn test_induction_wildcard_shadowing_ill_typed_alt_is_refused() {
    assert_refused(
        TWO,
        "theorem t1 (t : AltT) : t = t := by\n  induction t with\n  | _ => rfl\n  | _ => exact Nat.zero\n",
        WILDCARD_NOT_LAST,
    );
}

#[test]
fn test_cases_duplicate_alt_is_refused() {
    assert_refused(
        TWO,
        "theorem t1 (t : AltT) : t = t := by\n  cases t with\n  | a => rfl\n  | a => rfl\n  | b => rfl\n",
        "Duplicate alternative name `a`",
    );
}

/// Lean: "Invalid alternative name `c`: There are no unhandled alternatives".
#[test]
fn test_cases_unknown_alt_is_refused() {
    assert_refused(
        TWO,
        "theorem t1 (t : AltT) : t = t := by\n  cases t with\n  | a => rfl\n  | b => rfl\n  | c => rfl\n",
        "Alternative `c` covers no case",
    );
}

/// Lean: "Alternative `s` is not needed" (`AltV.s : AltV 1` cannot be `AltV 0`).
#[test]
fn test_cases_unreachable_alt_is_refused() {
    assert_refused(
        IDX,
        "theorem t1 (v : AltV 0) : v = v := by\n  cases v with\n  | z => rfl\n  | s => rfl\n",
        "Alternative `s` covers no case",
    );
}

/// Known gap, pinned so it fails loudly the day it closes: Lean refuses this
/// ("Wildcard alternative is not needed"), Clean accepts it, as it did before
/// `induction_alt_check`. Clean drops unreachable cases, so it cannot tell
/// this wildcard from the one below that Lean accepts (module doc).
#[test]
fn test_cases_unneeded_wildcard_gap_is_accepted() {
    assert_accepted(
        TWO,
        "theorem t1 (t : AltT) : t = t := by\n  cases t with\n  | a => rfl\n  | b => rfl\n  | _ => rfl\n",
    );
}

/// Lean v4.30.0-rc2 accepts: the wildcard covers `s`, which is unreachable for
/// `AltV 0`, so Lean skips it without elaborating the right-hand side.
#[test]
fn test_cases_wildcard_over_only_unreachable_cases_is_accepted() {
    assert_accepted(
        IDX,
        "theorem t1 (v : AltV 0) : True := by\n  cases v with\n  | z => trivial\n  | _ => trivial\n",
    );
}

#[test]
fn test_cases_wildcard_last_is_accepted() {
    assert_accepted(
        TWO,
        "theorem t1 (t : AltT) : t = t := by\n  cases t with\n  | a => rfl\n  | _ => rfl\n",
    );
}

#[test]
fn test_induction_lone_wildcard_is_accepted() {
    assert_accepted(
        TWO,
        "theorem t1 (t : AltT) : t = t := by\n  induction t with\n  | _ => rfl\n",
    );
}

#[test]
fn test_induction_named_alts_out_of_order_are_accepted() {
    assert_accepted(
        "",
        "theorem t1 (n : Nat) : n + 0 = n := by\n  induction n with\n  | succ n ih => rfl\n  | zero => rfl\n",
    );
}

#[test]
fn test_cases_wildcard_with_binder_is_accepted() {
    assert_accepted(
        "",
        "theorem t1 (n : Nat) : n = n := by\n  cases n with\n  | zero => rfl\n  | _ k => rfl\n",
    );
}

#[test]
fn test_cases_only_reachable_alt_is_accepted() {
    assert_accepted(
        IDX,
        "theorem t1 (v : AltV 0) : v = v := by\n  cases v with\n  | z => rfl\n",
    );
}
