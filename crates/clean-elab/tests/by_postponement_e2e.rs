// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Brick B25 — `by`-block postponement to a metavar expected type
//! (`docs/plans/GAP_SWEEP_2026-07-09.md`, tactics_in_terms family).
//!
//! A `by`-block in subterm/argument position elaborates its tactic script
//! against the argument-slot type as the goal. When that slot is still an
//! unsolved metavariable at the point the block is reached — `Option.some`'s
//! `?α` in `some (by exact 2) : Option Nat` — running the tactic against the
//! bare metavar goal leaks a meta-encoded FVar and the block fails or produces
//! an uncertifiable term. Lean postpones the block (a `SyntheticMVarKind.tactic`
//! synthetic mvar) until the surrounding application pins its type
//! (`Lean/Elab/Term.lean` `synthesizeSyntheticMVars`, `Elab/Tactic/Basic.lean`
//! `byTactic`).
//!
//! Clean's fidelity fix: before elaborating a `by`-block argument whose slot is
//! an open metavariable, unify the application's RESULT type against the
//! expected type first (`by_block_arg_in_open_slot` → the pre-arg
//! expected-result unification in `elab_app`), pinning the slot so the tactic
//! sees a concrete goal. This is the effect Lean's postponement achieves.
//!
//! ACCEPTANCE BAR: every positive case pins the produced VALUE in-language with
//! a `rfl` theorem (kernel definitional equality against the ground-truth
//! constructor form) AND rests on zero axioms — so a dropped-tactic /
//! wrong-goal regression cannot pass silently. The negatives assert a LOUD
//! failure: a by-block whose type is genuinely uninferable, and a by-block that
//! produces the wrong-typed value, both ERROR — they are never silently
//! accepted as a bogus term.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Polymorphic single-field wrapper: the by-block's element type is a bare
/// metavar in `Box.wrap`'s argument slot until the expected `Box T` pins it.
const BOX_PRELUDE: &str = "
inductive Box (a : Type) where
  | wrap : a -> Box a
";

/// Polymorphic two-field pair: `Pair.mk (by …) (by …) : Pair Nat Nat` pins BOTH
/// slots from the expected tuple result before either tactic runs.
const PAIR_PRELUDE: &str = "
inductive Pair (a : Type) (b : Type) where
  | mk : a -> b -> Pair a b
";

fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("elaborate/kernel-check error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(format!(
                "declaration(s) failed to elaborate:\n{}",
                failures.join("\n")
            ));
        }
    }
    Ok(env)
}

fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for r in results {
                collect_failures(r, out);
            }
        }
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}

/// No positive by-block proof may rest on any axiom — in particular no `sorry`
/// auto-fill may back a postponed block (the never-silently-wrong bar).
fn assert_bedrock(env: &Environment, short_names: &[&str]) {
    for short in short_names {
        let name = env
            .constants()
            .map(|c| &c.name)
            .find(|n| n.last_component().as_deref() == Some(*short))
            .cloned()
            .unwrap_or_else(|| panic!("`{short}` was not registered"));
        let deps = env
            .axiom_deps(&name)
            .unwrap_or_else(|| panic!("{name}: axiom_deps returned None"));
        assert!(
            deps.is_empty(),
            "{name} must rest on zero axioms (no sorry, no domain axioms), got: {deps:?}"
        );
    }
}

#[test]
fn test_by_block_arg_type_pinned_by_result_wrapper() {
    // `Box.wrap`'s slot `?α` is pinned by unifying `Box ?α` with the expected
    // `Box Nat` BEFORE `exact 2` runs — the tactic then sees goal `Nat`.
    let src = format!(
        "{BOX_PRELUDE}
def bw : Box Nat := Box.wrap (by exact 2)
theorem bw_pin : bw = Box.wrap 2 := rfl
"
    );
    let env = elaborate_module(&src)
        .expect("by-block arg whose type is pinned by the wrapper result must elaborate");
    assert_bedrock(&env, &["bw", "bw_pin"]);
}

#[test]
fn test_by_block_arg_type_pinned_by_result_option() {
    // The canonical GAP_SWEEP probe `some (by exact 2) : Option Nat`.
    let src = "
def w : Option Nat := some (by exact 2)
theorem w_pin : w = some 2 := rfl
";
    let env = elaborate_module(src).expect("some (by exact 2) : Option Nat must elaborate");
    assert_bedrock(&env, &["w", "w_pin"]);
}

#[test]
fn test_by_block_two_args_pinned_from_tuple_result() {
    // Both slots `?α`, `?β` are pinned from the expected `Pair Nat Nat` result,
    // so each `by`-block runs against a concrete `Nat` goal.
    let src = format!(
        "{PAIR_PRELUDE}
def pr : Pair Nat Nat := Pair.mk (by exact 1) (by exact 2)
theorem pr_pin : pr = Pair.mk 1 2 := rfl
"
    );
    let env =
        elaborate_module(&src).expect("two by-blocks pinned from the tuple result must elaborate");
    assert_bedrock(&env, &["pr", "pr_pin"]);
}

#[test]
fn test_by_block_nested_in_argument() {
    // `some (some (by exact 7))` — the by-block is TWO application levels deep.
    // The outer `some` pins `?α := Option Nat`, the inner `some` then pins
    // `?β := Nat`; the tactic must not be dropped through the extra paren layer.
    let src = "
def n : Option (Option Nat) := some (some (by exact 7))
theorem n_pin : n = some (some 7) := rfl
";
    let env = elaborate_module(src).expect("nested by-block in argument position must elaborate");
    assert_bedrock(&env, &["n", "n_pin"]);
}

#[test]
fn test_by_block_nested_in_wrapper() {
    let src = format!(
        "{BOX_PRELUDE}
def nb : Box (Box Nat) := Box.wrap (Box.wrap (by exact 7))
theorem nb_pin : nb = Box.wrap (Box.wrap 7) := rfl
"
    );
    let env = elaborate_module(&src).expect("nested wrapper by-block must elaborate");
    assert_bedrock(&env, &["nb", "nb_pin"]);
}

#[test]
fn test_by_block_type_pinned_by_function_result_param() {
    // `pick`'s parameter slots are the POLYMORPHIC `?α` (a metavar at the point
    // the first-argument `by`-block is reached). `pick`'s result type IS that
    // `?α`, so unifying the result against the expected `Nat` pins `?α := Nat`
    // BEFORE the block runs — the tactic then sees goal `Nat` even though the
    // value is finally taken from the second parameter. Mirrors "by-block whose
    // type is pinned by the function's signature/later param". Without the pin
    // the block would run against a bare metavar goal and leak an FVar.
    let src = "
def pick {a : Type} (first : a) (second : a) : a := second
def pk : Nat := pick (by exact 0) 99
theorem pk_pin : pk = 99 := rfl
";
    let env = elaborate_module(src)
        .expect("by-block whose slot is pinned by the function signature must elaborate");
    assert_bedrock(&env, &["pk", "pk_pin"]);
}

#[test]
fn test_by_block_doubly_parenthesized() {
    // `some ((by exact 5))`: the by-block is wrapped in an extra paren layer
    // (`Paren(Paren(ByTactic …))`). The tactic must survive the unwrap.
    let src = "
def dp : Option Nat := some ((by exact 5))
theorem dp_pin : dp = some 5 := rfl
";
    let env = elaborate_module(src).expect("doubly-parenthesized by-block must elaborate");
    assert_bedrock(&env, &["dp", "dp_pin"]);
}

#[test]
fn test_by_block_uninferable_type_is_loud() {
    // No expected type constrains `Box.wrap`'s slot, and `rfl` cannot pin it
    // itself, so the by-block's goal stays a metavariable. This MUST fail
    // loudly — never silently produce a bogus wrapped term.
    let src = format!(
        "{BOX_PRELUDE}
def bad := Box.wrap (by rfl)
"
    );
    let err = elaborate_module(&src);
    assert!(
        err.is_err(),
        "a by-block with a genuinely uninferable goal type must fail LOUDLY, got: {err:?}"
    );
}

#[test]
fn test_by_block_wrong_value_type_is_rejected() {
    // After the slot is pinned to `Nat`, a by-block that produces a `Bool` must
    // be rejected — the postponement only SOLVES the goal type, it never
    // certifies a wrong-typed value.
    let src = "
def bad2 : Option Nat := some (by exact true)
";
    let err = elaborate_module(src);
    assert!(
        err.is_err(),
        "a by-block producing the wrong-typed value must be rejected, got: {err:?}"
    );
}
