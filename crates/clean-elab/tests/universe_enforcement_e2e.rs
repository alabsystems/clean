// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! UNIVERSE LEVEL ENFORCEMENT & HOLES — GAP_SWEEP_2026-07-09 brick B17.
//!
//! End-to-end pins for the six universe rows this brick closes. Each pin drives
//! the real elaborate → kernel-register path (the same path `clean check` uses),
//! so an "accepts" verdict is value-certified and a "rejects" verdict is a LOUD,
//! typed error — never a silent monomorphization or a silent sorryAx.
//!
//!   * universes/p16,p34 (SILENT-WRONG): `def bad.{u} : Sort u := Nat` was
//!     accepted and its `Sort u` signature silently rewritten to `Sort 1`
//!     (the unifier assigned the DECLARED param `u := 1`). It must now be a
//!     loud level mismatch. The correct polymorphic identity still accepts.
//!   * universes/p39: `@id.{2} Nat` was over-accepted and the correct
//!     `@id.{1} Nat` was wrongly rejected — the `@` marker was dropped when
//!     wrapped by a `.{}` universe instance, inverting the level check. Now
//!     `@id.{1} Nat` accepts (value-certified) and `@id.{2} Nat` loud-rejects.
//!   * universes/p12: `Type _` level holes now elaborate (levelMVarToParam).
//!   * universes/p09: `Type*` is Mathlib-only — loud-rejected under the strict
//!     `--prelude lean4-core` lane, accepted in the builtin (extension) lane.
//!   * universes/p20: a partial universe-instance list (`ULift.up.{1}` — two
//!     level params, one supplied) is a loud, typed `UniverseLevelMismatch`
//!     instead of an `UnknownIdent`/`UniverseInstNotConst` + silent sorryAx.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_parser::parse_file;

/// Prelude lane for a run: the builtin (Clean-native extension) lane vs the
/// strict `--prelude lean4-core` lane that rejects Mathlib-only surface.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Lane {
    Builtin,
    Lean4Core,
}

/// Drive a whole module through elaborate → kernel-register. Returns `Ok` only
/// when every declaration elaborates AND kernel-registers with no inner
/// failure; otherwise the first loud error is surfaced as `Err`.
fn run_module(source: &str, lane: Lane) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    if lane == Lane::Lean4Core {
        env.set_lean4_core_strict_monads(true);
    }
    // ULift is not in the base prelude; the `clean check` path registers it, so
    // mirror that here for the p20 pin.
    env.init_ulift().map_err(|e| format!("ulift init: {e}"))?;

    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("elab/kernel error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(format!(
                "inner declaration(s) failed: {}",
                failures.join("; ")
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

/// Assert a constant registered with an EMPTY axiom closure (no sorry, no
/// domain axiom leaked into an accepted universe-polymorphic declaration).
fn assert_empty_closure(env: &Environment, short: &str) {
    let name = env
        .constants()
        .map(|c| &c.name)
        .find(|n| n.last_component().as_deref() == Some(short))
        .cloned()
        .unwrap_or_else(|| panic!("no registered constant with short name `{short}`"));
    let deps = env
        .axiom_deps(&name)
        .unwrap_or_else(|| panic!("{name}: not registered (axiom_deps returned None)"));
    assert!(
        deps.is_empty(),
        "{name} should have an empty axiom closure, but rests on: {deps:?}"
    );
}

// ── universes/p16,p34 — SILENT-WRONG: ascribed poly result type enforced ─────

#[test]
fn test_sortu_polymorphic_body_loud_rejects() {
    // `Nat : Sort 1`, but the ascribed result type is `Sort u` for a FREE,
    // declared `u`. The unifier must NOT solve `u := 1` — this is a loud
    // mismatch, not a silent monomorphization (p16/p34).
    let err = run_module("def bad.{u} : Sort u := Nat", Lane::Lean4Core)
        .expect_err("`def bad.{u} : Sort u := Nat` must be a loud level mismatch");
    assert!(
        err.contains("mismatch") || err.contains("Mismatch") || err.contains("conflict"),
        "expected a level-mismatch style error, got: {err}"
    );
}

#[test]
fn test_polymorphic_sort_identity_accepts() {
    // The genuinely-polymorphic identity: body `a : Sort u` matches the ascribed
    // `Sort u` with u rigid. Must still accept, empty closure.
    let env = run_module("def ok.{u} (a : Sort u) : Sort u := a", Lane::Lean4Core)
        .expect("polymorphic Sort identity must accept");
    assert_empty_closure(&env, "ok");
}

// ── universes/p39 — explicit level instance in application position ──────────

#[test]
fn test_explicit_level_one_id_accepts_and_certifies() {
    // `@id.{1} Nat : Nat → Nat`; the value pin certifies it computes.
    let env = run_module(
        "def idNat1 := @id.{1} Nat\ntheorem idNat1_pin : idNat1 5 = 5 := rfl",
        Lane::Lean4Core,
    )
    .expect("`@id.{1} Nat` must accept and its value pin must certify");
    assert_empty_closure(&env, "idNat1_pin");
}

#[test]
fn test_explicit_level_two_id_loud_rejects() {
    // `@id.{2}` needs its argument at `Sort 2`, but `Nat : Sort 1` — loud reject.
    let err = run_module("def idNat2 := @id.{2} Nat", Lane::Lean4Core)
        .expect_err("`@id.{2} Nat` must loud-reject (Nat : Sort 1, not Sort 2)");
    assert!(
        err.contains("conflict") || err.contains("mismatch") || err.contains("Mismatch"),
        "expected a level-mismatch style error, got: {err}"
    );
}

// ── universes/p20 — partial universe-instance list is a loud typed error ─────

#[test]
fn test_partial_universe_instance_list_loud_rejects() {
    // `ULift.up` has TWO level params; supplying one is a partial list. It must
    // be a LOUD `UniverseLevelMismatch`, not an UnknownIdent + silent sorryAx.
    let err = run_module("def liftedNat : Type 1 := ULift.{1} Nat", Lane::Lean4Core)
        .expect_err("partial universe-instance list must loud-reject");
    assert!(
        err.to_lowercase().contains("universe level count mismatch")
            || err.contains("UniverseLevelMismatch"),
        "expected a universe-level-count mismatch, got: {err}"
    );
    // And crucially: not laundered into a sorry axiom.
    assert!(!err.contains("sorry"), "must not degrade to sorryAx: {err}");
}

// ── universes/p12 — `Type _` level holes ────────────────────────────────────

#[test]
fn test_type_underscore_level_hole_works() {
    let env = run_module(
        "def uId (\u{3b1} : Type _) (a : \u{3b1}) : \u{3b1} := a\n\
         theorem uId_pin : uId Nat 9 = 9 := rfl",
        Lane::Lean4Core,
    )
    .expect("`Type _` level hole must elaborate and the value pin must certify");
    assert_empty_closure(&env, "uId_pin");
}

#[test]
fn test_sort_underscore_level_hole_works() {
    run_module(
        "def sId (\u{3b1} : Sort _) (a : \u{3b1}) : \u{3b1} := a",
        Lane::Lean4Core,
    )
    .expect("`Sort _` level hole must elaborate");
}

// ── universes/p09 — `Type*` gated by prelude mode ───────────────────────────

#[test]
fn test_type_star_loud_rejects_under_lean4_core() {
    let err = run_module(
        "def starId (\u{3b1} : Type*) (a : \u{3b1}) : \u{3b1} := a",
        Lane::Lean4Core,
    )
    .expect_err("`Type*` is Mathlib-only — must loud-reject under lean4-core");
    assert!(
        err.contains("Type*") || err.contains("Mathlib") || err.contains("Lean4CoreOnly"),
        "expected a Mathlib-only rejection, got: {err}"
    );
}

#[test]
fn test_type_star_accepts_in_builtin_prelude() {
    // The Clean-native extension lane keeps `Type*` (fresh-universe semantics).
    run_module(
        "def starId (\u{3b1} : Type*) (a : \u{3b1}) : \u{3b1} := a",
        Lane::Builtin,
    )
    .expect("`Type*` must still accept in the builtin extension lane");
}

// ── `Sort*` gated by prelude mode — the `Sort` analogue of `Type*` ───────────
// `Sort*` is Mathlib's implicit-universe binder for `Sort` (used pervasively in
// `Mathlib/Logic/Basic.lean`: `variable {α : Sort*}`, `abbrev hidden {α :
// Sort*} …`). It elaborates to a fresh universe parameter exactly like `Type*`,
// and is gated LOUDLY under `--prelude lean4-core` for the same reason.

#[test]
fn test_sort_star_loud_rejects_under_lean4_core() {
    let err = run_module(
        "def sStarId (\u{3b1} : Sort*) (a : \u{3b1}) : \u{3b1} := a",
        Lane::Lean4Core,
    )
    .expect_err("`Sort*` is Mathlib-only — must loud-reject under lean4-core");
    assert!(
        err.contains("Sort*") || err.contains("Mathlib") || err.contains("Lean4CoreOnly"),
        "expected a Mathlib-only rejection, got: {err}"
    );
}

#[test]
fn test_sort_star_accepts_in_builtin_prelude() {
    // The Clean-native extension lane keeps `Sort*` (fresh-universe semantics),
    // matching `Type*`.
    run_module(
        "def sStarId (\u{3b1} : Sort*) (a : \u{3b1}) : \u{3b1} := a",
        Lane::Builtin,
    )
    .expect("`Sort*` must still accept in the builtin extension lane");
}
