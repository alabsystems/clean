// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression lock for **simp-set discipline** (gap sweep brick B15).
//!
//! ## The gap this guards
//!
//! Lean's `simp` uses ONLY its simp set — the globally `@[simp]`-tagged lemmas
//! (plus the equation lemmas of `@[simp]`-tagged defs), the lemmas passed in
//! `simp [h]`, and, in `simp only [h]`, ONLY `h` — and it unfolds definitions at
//! `withReducible` transparency (only `@[reducible]` abbrevs, never a bare
//! semireducible `def`). A bare `simp` that neither rewrites via the set nor
//! reduces the goal to `True` fails **loudly** with "simp made no progress".
//!
//! Before B15, clean's `simp` unfolded semireducible defs and matched default
//! arithmetic lemmas *regardless of the simp set*, and its reflexivity closer ran
//! at full transparency. So `@[simp]` tagging and `attribute [-simp]` erasure were
//! unobservable and clean silently ACCEPTED proofs Lean REJECTS:
//!
//! ```lean
//! def mval7 : Nat := 5
//! theorem mval7_eq : mval7 = 5 := rfl          -- NOT @[simp]
//! theorem mval7_simp : mval7 = 5 := by simp    -- clean ACCEPTED (Lean: no progress)
//!
//! def g23 (n : Nat) : Nat := 0 + n
//! theorem g23_eq (n : Nat) : g23 n = n := Nat.zero_add n  -- NOT @[simp]
//! theorem t23 (m : Nat) : g23 m = m := by simp -- clean ACCEPTED (Lean: no progress)
//! ```
//!
//! B15 makes simp consult the actual simp set, honor `simp only` / `[-simp]`
//! erasure / `@[simp]` tagging, unfold at reducible transparency, and FAIL when
//! the set can't close or change the goal.
//!
//! ## Soundness direction (strictly narrowing)
//!
//! Every gate here is a change from a former ACCEPT to a REJECT (the silent-wrong
//! rows `attributes_options/p07,p09,c23`) or a MUST-STAY-GREEN positive
//! (`p06,p08,p20,c22`, and the default-arith `n + 0 = n`). simp can only accept a
//! strict subset after B15 — it never accepts anything new. The reflexivity closer
//! runs at reducible transparency; since a reducible-def-eq implies full-def-eq,
//! every proof simp still green-lights is kernel-verified.

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

/// Assert the tactic theorem named `name` (the LAST decl in `source`) does NOT
/// register a proof — either elaboration errors, or the const has no value.
/// This is the loud-reject the silent-wrong fix produces ("simp made no
/// progress" / unsolved goals).
fn assert_simp_rejected(name: &str, source: &str) {
    match try_elaborate(source) {
        Err(_) => {} // expected: simp could not (soundly) close the goal.
        Ok(env) => {
            if let Some(info) = env.get_const(&Name::from_string(name)) {
                assert!(
                    info.value.is_none(),
                    "`{name}` must NOT be closed by simp (Lean rejects it), \
                     but a proof was registered"
                );
            }
        }
    }
}

// ===========================================================================
// POSITIVES — bare simp closes when the SET applies (must stay green).
// ===========================================================================

/// p06: a `@[simp]`-tagged equation makes `simp` rewrite the def away and close.
#[test]
fn bare_simp_closes_via_registered_simp_lemma() {
    let env = try_elaborate(
        "def mval6 : Nat := 5\n\
         @[simp] theorem mval6_eq : mval6 = 5 := rfl\n\
         theorem mval6_simp : mval6 = 5 := by simp",
    )
    .expect("`mval6 = 5 := by simp` must ACCEPT: mval6_eq is @[simp]-tagged");
    assert_registered(&env, "mval6_simp");
}

/// The default simp set still contains the genuine core `@[simp]` arithmetic
/// lemmas (`Nat.add_zero`), so `n + 0 = n := by simp` closes — B15 tightens the
/// UNFOLDING of non-reducible defs, it does not strip the real default lemmas.
#[test]
fn bare_simp_closes_via_default_arith_lemma() {
    let env = try_elaborate("theorem add0 (n : Nat) : n + 0 = n := by simp")
        .expect("`n + 0 = n := by simp` must ACCEPT via the default @[simp] Nat.add_zero");
    assert_registered(&env, "add0");
}

/// p08: `attribute [simp] h` adds `h` to the set after the fact — observable.
#[test]
fn attribute_simp_command_adds_to_set() {
    let env = try_elaborate(
        "def mval8 : Nat := 7\n\
         theorem mval8_eq : mval8 = 7 := rfl\n\
         attribute [simp] mval8_eq\n\
         theorem mval8_simp : mval8 = 7 := by simp",
    )
    .expect("`attribute [simp] mval8_eq` must make `mval8 = 7 := by simp` close");
    assert_registered(&env, "mval8_simp");
}

/// c22: a `@[simp]` lemma over a NON-defeq equation (`g22 n = n`, where
/// `g22 n := 0 + n` and `0 + n` is not defeq to `n`) rewrites and closes.
#[test]
fn bare_simp_closes_via_nondefeq_registered_lemma() {
    let env = try_elaborate(
        "def g22 (n : Nat) : Nat := 0 + n\n\
         @[simp] theorem g22_eq (n : Nat) : g22 n = n := Nat.zero_add n\n\
         theorem t22 (m : Nat) : g22 m = m := by simp",
    )
    .expect("`g22 m = m := by simp` must ACCEPT: g22_eq is @[simp]-tagged");
    assert_registered(&env, "t22");
}

/// p20: a `@[simp]`-tagged DEFINITION is unfolded by bare simp (equation-lemma
/// analogue) — the tag on a def is now observable.
#[test]
fn bare_simp_unfolds_simp_tagged_def() {
    let env = try_elaborate(
        "@[simp] def double20 (n : Nat) : Nat := n + n\n\
         theorem double20_simp : double20 2 = 2 + 2 := by simp",
    )
    .expect("`double20 2 = 2 + 2 := by simp` must ACCEPT: double20 is @[simp]-tagged");
    assert_registered(&env, "double20_simp");
}

// ===========================================================================
// SILENT-WRONG → LOUD REJECT (the p07 / p09 / c23 fixes).
// ===========================================================================

/// p07: an UNtagged local equation is NOT in the simp set, and a bare
/// semireducible `def mval7 := 5` is opaque to simp — so `mval7 = 5 := by simp`
/// must report no progress. (Before B15 the full-transparency rfl closer unfolded
/// mval7 and silently accepted.)
#[test]
fn simp_rejects_untagged_lemma_free_defeq_goal() {
    assert_simp_rejected(
        "mval7_simp",
        "def mval7 : Nat := 5\n\
         theorem mval7_eq : mval7 = 5 := rfl\n\
         theorem mval7_simp : mval7 = 5 := by simp",
    );
}

/// c23: an UNtagged non-defeq equation lemma cannot be reached — simp must not
/// unfold the semireducible `g23` to expose `0 + n` for the default `Nat.zero_add`.
#[test]
fn simp_rejects_untagged_nondefeq_goal() {
    assert_simp_rejected(
        "t23",
        "def g23 (n : Nat) : Nat := 0 + n\n\
         theorem g23_eq (n : Nat) : g23 n = n := Nat.zero_add n\n\
         theorem t23 (m : Nat) : g23 m = m := by simp",
    );
}

/// p09: `attribute [-simp] h` erases a previously `@[simp]`-tagged lemma, so a
/// later `simp` no longer has it and the goal must not close. Erasure observable.
#[test]
fn simp_erase_is_observable() {
    assert_simp_rejected(
        "mval9_simp",
        "def mval9 : Nat := 7\n\
         @[simp] theorem mval9_eq : mval9 = 7 := rfl\n\
         attribute [-simp] mval9_eq\n\
         theorem mval9_simp : mval9 = 7 := by simp",
    );
}

/// The `@[simp]` tag on a DEF is observable in the negative direction too: WITHOUT
/// the tag the identical def is not unfolded and simp cannot close the goal.
#[test]
fn untagged_def_is_not_unfolded_by_simp() {
    assert_simp_rejected(
        "double20b_simp",
        "def double20b (n : Nat) : Nat := n + n\n\
         theorem double20b_simp : double20b 2 = 2 + 2 := by simp",
    );
}

// ===========================================================================
// simp only — uses ONLY the given lemmas; the default set is excluded.
// ===========================================================================

/// `simp only [Nat.zero_add]` on a goal whose LHS is literally `0 + n` closes:
/// the one passed lemma applies syntactically.
#[test]
fn simp_only_uses_passed_lemma() {
    let env = try_elaborate("theorem zonly (n : Nat) : 0 + n = n := by simp only [Nat.zero_add]")
        .expect("`0 + n = n := by simp only [Nat.zero_add]` must ACCEPT");
    assert_registered(&env, "zonly");
}

/// `simp only []` with an EMPTY lemma set must make no progress on a semireducible
/// `def` goal — the empty set closes nothing (no default lemmas, no def unfolds).
#[test]
fn simp_only_empty_set_closes_nothing() {
    assert_simp_rejected(
        "mval7_only",
        "def mval7 : Nat := 5\n\
         theorem mval7_only : mval7 = 5 := by simp only []",
    );
}

/// `simp only [Nat.zero_add]` must NOT unfold the semireducible `g23` to reach the
/// `0 + n` inside it — passing the lemma does not grant def-unfolding power.
#[test]
fn simp_only_does_not_unfold_semireducible_def() {
    assert_simp_rejected(
        "t23only",
        "def g23 (n : Nat) : Nat := 0 + n\n\
         theorem t23only (m : Nat) : g23 m = m := by simp only [Nat.zero_add]",
    );
}

// ===========================================================================
// Reducibility transparency — simp honors @[irreducible] (shared with B14).
// ===========================================================================

/// A bare `simp` must not unfold an `@[irreducible]` def either: `secret = 3` has
/// no applicable lemma and secret stays folded, so no progress.
#[test]
fn simp_honors_irreducible() {
    assert_simp_rejected(
        "secret_simp",
        "@[irreducible] def secret : Nat := 3\n\
         theorem secret_simp : secret = 3 := by simp",
    );
}

/// A `@[reducible]` (abbrev) def, by contrast, IS unfolded at simp's reducible
/// transparency, so `myid 3 = 3 := by simp` closes (the reflexivity closer sees
/// `3 = 3` after the reducible unfold).
#[test]
fn simp_unfolds_reducible_abbrev() {
    let env = try_elaborate(
        "@[reducible] def myid (n : Nat) : Nat := n\n\
         theorem myid_simp : myid 3 = 3 := by simp",
    )
    .expect("`myid 3 = 3 := by simp` must ACCEPT: @[reducible] unfolds at reducible transparency");
    assert_registered(&env, "myid_simp");
}

// ===========================================================================
// Empty-closure positive — a trivially-true simp goal still closes and its
// axiom closure stays foundational (no sorry / domain axiom sneaks in).
// ===========================================================================

#[test]
fn simp_reflexive_eq_self_closes_and_is_axiom_clean() {
    let env = try_elaborate("theorem selfeq (n : Nat) : (n = n) = True := by simp")
        .expect("`(n = n) = True := by simp` must ACCEPT via eq_self");
    assert_registered(&env, "selfeq");
    let deps = env
        .axiom_deps(&Name::from_string("selfeq"))
        .expect("selfeq must have an axiom_deps closure");
    for d in &deps {
        assert_eq!(
            d.to_string(),
            "propext",
            "selfeq axiom closure must be ⊆ {{propext}}, found {d:?}"
        );
    }
}
