// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end z-probes for **B22 — Id-monad reduction (do_notation p13/p14)**
//! of `docs/plans/GAP_SWEEP_2026-07-09.md`.
//!
//! Before B22, `Id`/`Id.run` were opaque **axioms** and the prelude had no
//! `Pure Id`/`Bind Id` instances, so `Id`/`Id.run`/`pure`/`bind` were all
//! definitionally inert. `Id.run (pure 5) = 5 := rfl` was REJECTED — a LOUD
//! coverage gap, not silent-wrong (the wrong pin `Id.run (pure 5) = 6 := rfl`
//! was also correctly rejected, so no false proof was ever accepted).
//!
//! B22 fix (zero kernel `tc/` changes, no axioms):
//! - `Id`/`Id.mk`/`Id.run` become reducible **definitions** (`Id α ≡ α`,
//!   `Id.run x ≡ x`), matching Lean `Init/Prelude.lean`
//!   (`clean-kernel::env::data_monad::init_id`);
//! - `instPureId : Pure Id := ⟨fun a => a⟩` / `instBindId : Bind Id :=
//!   ⟨fun ma f => f ma⟩` (`clean-kernel::env::data_monad_insts::init_monad_id_insts`);
//! - the existing B07 materialization pass rewrites `Pure.pure Id …` /
//!   `Bind.bind Id …` into instance-projected form, which the kernel reduces
//!   through ORDINARY delta + proj-of-mk iota + beta (`pure v ↦ v`,
//!   `bind ma f ↦ f ma`), then `Id.run`'s reducible identity yields the ground
//!   value — the identical sequence Lean's kernel performs.
//!
//! These tests drive the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`),
//! so a pass/fail here matches the observable `clean check` verdict.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_parser::parse_file;

/// Drive the real file pipeline against a caller-supplied environment.
fn elaborate_file_in(
    mut env: Environment,
    source: &str,
) -> Result<(Environment, Vec<ElabResult>), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    let mut results = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        results.push(elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?);
    }
    Ok((env, results))
}

fn elaborate_file(source: &str) -> Result<(Environment, Vec<ElabResult>), String> {
    elaborate_file_in(Environment::with_prelude(), source)
}

fn expect_pass(source: &str) {
    elaborate_file(source).unwrap_or_else(|e| panic!("file must fully check, got: {e}\n{source}"));
}

fn expect_fail(source: &str) -> String {
    match elaborate_file(source) {
        Ok(_) => panic!("file must be REJECTED, but it fully checked:\n{source}"),
        Err(e) => e,
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// The brick's acceptance pin, verbatim
// ═══════════════════════════════════════════════════════════════════════════

/// do_notation p13/p14 acceptance pin: `Id.run (pure 5) = 5 := rfl`. `pure 5`
/// resolves at `Pure Id` (its expected type is `Id.run`'s domain `Id α`),
/// materializes to `(Proj Pure 0 instPureId) Nat 5`, reduces to `5`, and
/// `Id.run`'s reducible identity yields the ground `5`.
#[test]
fn b22_id_run_pure_value_certified() {
    expect_pass("theorem id_run_pure_pin : Id.run (pure 5) = 5 := rfl");
}

/// The brick brief's do-block pin: `Id.run (do let x <- pure 3; pure (x+1))`
/// reduces to `4` (bind's `f ma`, then `pure` identity).
#[test]
fn b22_id_run_do_block_value_certified() {
    expect_pass("theorem id_run_do_pin : Id.run (do let x <- pure 3; pure (x + 1)) = 4 := rfl");
}

// ═══════════════════════════════════════════════════════════════════════════
// `Id α ≡ α` reducibility
// ═══════════════════════════════════════════════════════════════════════════

/// The reducible `Id` alias: `Id Nat` is def-eq to `Nat` at the type level.
#[test]
fn b22_id_alias_type_level_rfl() {
    expect_pass("theorem id_nat_is_nat : Id Nat = Nat := rfl");
}

/// `Id α ≡ α` at the term level: a value of type `Id Nat` is usable as `Nat`.
#[test]
fn b22_id_alias_term_level() {
    expect_pass(
        "def use_id (x : Id Nat) : Nat := x\n\
         theorem use_id_pin : use_id 5 = 5 := rfl",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// do-blocks over Id: def form + value pins via Id.run
// ═══════════════════════════════════════════════════════════════════════════

/// `def : Id Nat := do …` value-certifies through an `Id.run` pin.
#[test]
fn b22_id_do_def_value_certified() {
    expect_pass(
        "def di : Id Nat := do\n  let x <- pure 3\n  pure (x + 1)\n\n\
         theorem di_pin : Id.run di = 4 := rfl",
    );
}

/// A three-bind chain over Id reduces end-to-end.
#[test]
fn b22_id_bind_chain_value_certified() {
    expect_pass(
        "theorem id_chain_pin : \
         Id.run (do let a <- pure 1; let b <- pure 2; let c <- pure 3; pure (a + b + c)) = 6 \
         := rfl",
    );
}

/// A do-block over Id captured under a lambda binder (closure over the arg):
/// the monad is still concrete, so materialization + reduction fire.
#[test]
fn b22_id_do_under_lambda_value_certified() {
    expect_pass(
        "def fl : Nat -> Id Nat := fun n => do\n  let x <- pure n\n  pure (x + 1)\n\n\
         theorem fl_pin : Id.run (fl 4) = 5 := rfl",
    );
}

/// An argument-less (empty-closure) do-block behind a unit abstraction.
#[test]
fn b22_id_do_thunk_value_certified() {
    expect_pass(
        "def ft : Unit -> Id Nat := fun _ => do\n  let x <- pure 2\n  pure (x * 3)\n\n\
         theorem ft_pin : Id.run (ft ()) = 6 := rfl",
    );
}

/// `Id.run (pure v)` where `pure`/`run` compose to the identity, then a plain
/// `let` interleaved with a bind.
#[test]
fn b22_id_pure_let_interleaved_value_certified() {
    expect_pass(
        "def fli : Id Nat := do\n  let x := 10\n  let y <- pure 5\n  pure (x + y)\n\n\
         theorem fli_pin : Id.run fli = 15 := rfl",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// LOUD negatives — wrong values must be REJECTED (B22 adds reduction, not
// unsoundness; the same wrong pins the sweep confirmed stay rejected)
// ═══════════════════════════════════════════════════════════════════════════

/// The exact wrong pin the sweep verified stays rejected: `Id.run (pure 5) = 6`.
#[test]
fn b22_wrong_pure_value_rejected() {
    let err = expect_fail("theorem id_run_bad : Id.run (pure 5) = 6 := rfl");
    assert!(
        err.contains("mismatch") || err.contains("Kernel") || err.contains("type"),
        "wrong-value pin must die in the kernel, got: {err}"
    );
}

/// A do-block over Id must not certify a WRONG ground value.
#[test]
fn b22_wrong_do_value_rejected() {
    expect_fail("theorem id_do_bad : Id.run (do let x <- pure 3; pure (x + 1)) = 5 := rfl");
}

/// Empty-closure adversarial: the def-form pin must reject the wrong value too.
#[test]
fn b22_wrong_def_value_rejected() {
    expect_fail(
        "def dw : Id Nat := do\n  let x <- pure 3\n  pure (x + 1)\n\n\
         theorem dw_bad : Id.run dw = 5 := rfl",
    );
}
