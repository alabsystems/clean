// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! I1 — header-first resolution, written RED before the implementation.
//!
//! Ruling of record: `docs/design/2026-08-05-i1-ruling-header-elaboration.md`
//! (in the Trust superproject). Option A — header elaboration — was chosen over
//! fixpoint retry because elaboration is NOT monotone: `elab(source,
//! partial_env)` can produce a different term from `elab(source,
//! full_header_env)`, so the kernel certifies a term the source does not
//! denote. The ruling reproduces the counterexample; this file is that
//! counterexample as an executable test.
//!
//! THE SHAPE. `M.early` is written under `open Imported`, so with a partial
//! name index `pick` resolves to `Imported.pick = 0`. With the COMPLETE header
//! index, `M.pick` exists, and Clean's own resolver takes candidates from the
//! current namespace outward BEFORE consulting `open` decls
//! (`crates/clean-elab/src/infer/elab_core.rs:915`). So `early` means
//! `M.pick = 1`.
//!
//! Three tests, and the set is the point — no one of them is sufficient:
//!
//!   1. `test_later_sibling_wins_over_open_rejects_stale_meaning` — the
//!      NEGATIVE. `theorem locked : early = 0 := rfl` must be REJECTED,
//!      because under header-first semantics `early = 1`. It is accepted
//!      today. This is the red one.
//!   2. `test_later_sibling_wins_over_open_pins_the_value` — the CONTROL that
//!      an implementation which simply stops checking cannot pass:
//!      `theorem locked : early = 1 := rfl` must be ACCEPTED. Source-order
//!      semantics fails this, and so does reject-everything.
//!   3. `test_without_the_later_sibling_the_open_still_wins` — the CONTROL
//!      that header-first has not broken ordinary `open` resolution. With no
//!      `M.pick` anywhere, `early = 0` and `locked : early = 0 := rfl` must
//!      still be ACCEPTED.
//!
//! (1) alone would pass if we rejected everything. (2) alone would pass under
//! source order. (3) alone would pass under both. Together they pin exactly one
//! semantics.

use clean_elab::module_batch::{
    elaborate_module as batch_elaborate, BatchOptions, SourceUnit, UnitId,
};
use clean_kernel::env::Environment;
use clean_parser::parse_file;

/// Elaborate + kernel-check + register every declaration of `source` on the
/// default prelude, in ONE session. `Err` carries the first failure.
///
/// RETARGETED (I1): this used to be the source-order driver
/// (`preprocess_decl_with_context` + `elaborate_decl_and_register` per
/// declaration), which is what made the two tests below RED. It now calls the
/// header-first batch entry point. **Not one assertion in this file changed**
/// — the assertions are about what the language means, and only the checker
/// changed.
///
/// The whole fixture is one unit. That is the harder case, not the easier
/// one: within a unit the source-order driver is at its most convincing,
/// because every declaration really is visible to the checker in order. What
/// changes is only WHEN each one's meaning is fixed.
fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = clean_elab::FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    let units = [SourceUnit {
        id: UnitId(0),
        decls: &decls,
    }];
    let outcome = batch_elaborate(&mut env, &mut file_ctx, &units, BatchOptions::islands());
    if !outcome.is_clean() {
        return Err(format!("rejected: {}", outcome.render_rejections()));
    }
    if !outcome.committed {
        return Err("rejected: the batch was not committed".to_string());
    }
    Ok(env)
}

/// The module under test. `later` selects whether the LATER island declaring
/// `M.pick` is present; `stated` is the value `locked` claims `early` has.
fn module(later: bool, stated: &str) -> String {
    let tail = if later {
        "namespace M\ndef pick : Nat := 1\nend M\n"
    } else {
        ""
    };
    format!(
        "set_option autoImplicit false\n\
         namespace Imported\n\
         def pick : Nat := 0\n\
         end Imported\n\
         \n\
         namespace M\n\
         open Imported\n\
         def early : Nat := pick\n\
         theorem locked : early = {stated} := rfl\n\
         end M\n\
         \n\
         {tail}"
    )
}

/// RED. With `M.pick` declared later, current-namespace-outward resolution
/// beats the `open`, so `early` means `M.pick = 1` and `early = 0` is FALSE.
/// Accepting it is the kernel certifying a term the source does not denote.
#[test]
fn test_later_sibling_wins_over_open_rejects_stale_meaning() {
    let err = elaborate_module(&module(true, "0")).err();
    assert!(
        err.is_some(),
        "ACCEPTED `early = 0` while a later `M.pick := 1` exists — `early` was \
         elaborated against a PARTIAL name index (resolving `pick` to \
         `Imported.pick`) and the kernel then certified a proposition the \
         source does not denote. Header-first elaboration must stage `M.pick` \
         before any body elaborates."
    );
}

/// CONTROL — reject-everything cannot pass this. The same module, with the
/// proposition header-first semantics actually makes true.
#[test]
fn test_later_sibling_wins_over_open_pins_the_value() {
    let outcome = elaborate_module(&module(true, "1"));
    assert!(
        outcome.is_ok(),
        "REJECTED `early = 1`, which is what `early` means once every header is \
         staged: {}",
        outcome.err().unwrap_or_default()
    );
}

/// CONTROL — header-first must not break ordinary `open` resolution. With no
/// `M.pick` anywhere, `pick` is `Imported.pick = 0`.
#[test]
fn test_without_the_later_sibling_the_open_still_wins() {
    let outcome = elaborate_module(&module(false, "0"));
    assert!(
        outcome.is_ok(),
        "REJECTED `early = 0` with no `M.pick` in the module at all — the `open` \
         must still win when the current namespace has no candidate: {}",
        outcome.err().unwrap_or_default()
    );
}
