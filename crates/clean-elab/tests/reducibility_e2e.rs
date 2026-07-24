// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression lock for **elaboration-time reducibility / transparency
//! wiring** (Gap sweep brick B14).
//!
//! ## The gap this guards
//!
//! Lean's kernel has no transparency modes — it delta-unfolds every definition
//! that has a value (only genuine `Opaque`/theorem heads stay folded), so its
//! final proof re-check is complete. Reducibility (`@[reducible]` /
//! `@[irreducible]` / `@[semireducible]`) is an *elaboration-time* concept:
//! `MetaM`'s `isDefEq`/`whnf` run at a `TransparencyMode` and consult
//! `canUnfold`. At the `.default` transparency used for ordinary elaboration an
//! `@[irreducible]` definition does **not** delta-unfold.
//!
//! Before B14, clean parsed `@[irreducible]` and stored the hint on the
//! constant, but the elaborator's def-eq / whnf delegated to the kernel's
//! transparency-blind reduction, so:
//!
//! ```lean
//! @[irreducible] def secret : Nat := 3
//! theorem secret_pin : secret = 3 := rfl   -- clean ACCEPTED (Lean REJECTS)
//! ```
//!
//! `rfl` proved *through* the irreducible definition — a silent over-accept
//! (`attributes_options/p04`, SILENT_WRONG register #16). B14 wires the
//! elaborator's reduction to honor the reducibility hint: an `@[irreducible]`
//! def stays folded during elaboration-time def-eq, so the `rfl` now fails
//! **loudly** at elaboration. The kernel's own final check is untouched (still
//! full-delta / Lean-faithful); the gate is purely at elaboration.
//!
//! ## Soundness direction (strictly narrowing)
//!
//! Blocking `@[irreducible]` unfolding makes elaboration-time def-eq accept a
//! *strict subset* of what it accepted before (it can only turn a former
//! accept into a reject, never the reverse). So this change can only convert
//! silent over-accepts into loud rejects — it cannot make clean accept anything
//! new. The negative controls below confirm legitimate `Regular`/`@[reducible]`
//! unfolding still computes.

use clean_kernel::env::Environment;
use clean_kernel::Name;

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

/// Drive the real file pipeline (`parse_file → preprocess → elaborate+register`)
/// for a multi-declaration source. Returns `Err` at the first declaration the
/// elaborator/kernel rejects, so negative controls can assert a loud reject.
fn try_elaborate(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(env)
}

/// A declaration must be present in the environment after elaboration.
fn assert_registered(env: &Environment, name: &str) {
    assert!(
        env.get_const(&Name::from_string(name)).is_some(),
        "`{name}` must be registered after elaboration"
    );
}

// ---------------------------------------------------------------------------
// GATE 1 — @[irreducible] def blocks `rfl` (the p04 silent-wrong, now LOUD).
// ---------------------------------------------------------------------------

#[test]
fn irreducible_def_blocks_rfl_through_it() {
    // `secret` is @[irreducible]; `secret = 3 := rfl` requires delta-unfolding
    // `secret`, which is forbidden at elaboration-time `.default` transparency.
    let err = try_elaborate(
        "@[irreducible] def secret : Nat := 3\ntheorem secret_pin : secret = 3 := rfl",
    )
    .expect_err("`secret = 3 := rfl` must be REJECTED: rfl cannot unfold an @[irreducible] def");
    // Loud, not silent: a real type/def-eq mismatch, not a swallowed success.
    assert!(
        !err.to_lowercase().contains("parse error"),
        "rejection must come from elaboration def-eq, not the parser: {err}"
    );
}

// ---------------------------------------------------------------------------
// GATE 2 — @[irreducible] is not a wall: reflexive `secret = secret := rfl`
// still holds (no unfolding needed — structural equality). (p05 stays green.)
// ---------------------------------------------------------------------------

#[test]
fn irreducible_def_reflexive_rfl_still_accepts() {
    let env = try_elaborate(
        "@[irreducible] def secret2 : Nat := 3\ntheorem secret2_refl : secret2 = secret2 := rfl",
    )
    .expect("`secret2 = secret2 := rfl` must ACCEPT: reflexivity needs no unfolding");
    assert_registered(&env, "secret2_refl");
}

// ---------------------------------------------------------------------------
// GATE 3 — @[reducible] def unfolds in def-eq (`rfl` proves through it). The
// reducible-through-a-value case pins that reducible really unfolds. (p01/p02.)
// ---------------------------------------------------------------------------

#[test]
fn reducible_def_unfolds_in_defeq() {
    // @[reducible] `myid` unfolds at every transparency, so `myid 3 = 3 := rfl`
    // holds. A @[reducible] type synonym `MyNatR := Nat` also stays transparent
    // to numeral / instance synthesis, so `xr : MyNatR := 5; yr := xr + 1` and
    // `yr = 6 := rfl` all elaborate.
    let env = try_elaborate(
        "@[reducible] def myid (n : Nat) : Nat := n\ntheorem myid_pin : myid 3 = 3 := rfl",
    )
    .expect("`myid 3 = 3 := rfl` must ACCEPT: @[reducible] unfolds in def-eq");
    assert_registered(&env, "myid_pin");

    let env = try_elaborate(
        "@[reducible] def MyNatR := Nat\ndef xr : MyNatR := 5\ndef yr := xr + 1\ntheorem yr_pin : yr = 6 := rfl",
    )
    .expect("@[reducible] type synonym must stay transparent to numeral/instance synthesis");
    assert_registered(&env, "yr_pin");
}

// ---------------------------------------------------------------------------
// GATE 4 — default/semireducible (`Regular`) def unfolds in def-eq at the
// elaboration `.default` transparency (only @[irreducible] is gated). A plain
// `def d := 7; d = 7 := rfl` must still compute through the value.
// ---------------------------------------------------------------------------

#[test]
fn default_def_unfolds_in_defeq() {
    let env = try_elaborate("def d : Nat := 7\ntheorem d_pin : d = 7 := rfl")
        .expect("`d = 7 := rfl` must ACCEPT: a plain (Regular) def unfolds at `.default`");
    assert_registered(&env, "d_pin");
}

// ---------------------------------------------------------------------------
// GATE 5 — value pins where computation must still happen: an @[irreducible]
// def used only reflexively, plus a Regular def that DOES compute a chain,
// coexist. The Regular chain must reduce; the irreducible reflexive holds.
// ---------------------------------------------------------------------------

#[test]
fn mixed_irreducible_and_computing_regular() {
    let env = try_elaborate(
        "@[irreducible] def locked : Nat := 5\n\
         def open_add : Nat := 2 + 3\n\
         theorem open_pin : open_add = 5 := rfl\n\
         theorem locked_refl : locked = locked := rfl",
    )
    .expect("Regular `open_add` must compute to 5; irreducible `locked` reflexive holds");
    assert_registered(&env, "open_pin");
    assert_registered(&env, "locked_refl");

    // And the through-value rfl on the irreducible one is still rejected.
    try_elaborate(
        "@[irreducible] def locked2 : Nat := 5\ntheorem locked2_bad : locked2 = 5 := rfl",
    )
    .expect_err("`locked2 = 5 := rfl` must be REJECTED (irreducible stays folded)");
}

// ---------------------------------------------------------------------------
// GATE 6 — empty closure / trivial program: a file with only an @[irreducible]
// def and no proof through it elaborates cleanly (the attribute is inert when
// nothing tries to unfold it — the p05/register-only shape).
// ---------------------------------------------------------------------------

#[test]
fn irreducible_def_alone_registers() {
    let env = try_elaborate("@[irreducible] def solo : Nat := 42")
        .expect("registering an @[irreducible] def by itself must succeed");
    assert_registered(&env, "solo");
    let info = env
        .get_const(&Name::from_string("solo"))
        .expect("solo registered");
    assert_eq!(
        info.reducibility,
        clean_kernel::env::Reducibility::Irreducible,
        "the @[irreducible] hint must be stored on the constant"
    );
}
