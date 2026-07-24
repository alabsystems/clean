// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Explicit per-run verify configuration** — the single source of truth for
//! the env knobs the Isabelle verify/translate lane reads, parsed ONCE at each
//! entry point and installed for the duration of that run.
//!
//! # The cross-run contamination hazard this removes
//!
//! Historically the lane read its config through **first-wins `OnceLock`
//! statics** — `translate_node_budget` / `s3_miller_enabled`
//! (`isabelle_pure_translate/mod.rs`), `reprove_enabled` (`isabelle_reprove.rs`),
//! and the `ISA_REJECT_SPECIFICS` reader (`isabelle_pure_verify/mod.rs`), plus
//! `set_var` mutations in the single-line probe. A `OnceLock` freezes on its
//! FIRST read for the whole process lifetime. When two verify runs co-host ONE
//! OS process (cargo's parallel test threads, an in-process shard loop, the
//! multi-shard group driver), whichever run reads a key first fixes it for the
//! other — the second run then silently verifies under the WRONG budget / flags
//! and reports different KV. That is exactly the documented "concurrency
//! contamination" factor in `designs/2026-07-15-isabelle-shard-verify.md` §1.3.
//!
//! # The fix: install-on-thread, restore-on-drop
//!
//! [`VerifyConfig`] is a small `Copy` struct built ONCE at each entry point via
//! [`VerifyConfig::from_env`] (the single env-parsing constructor) and
//! [`VerifyConfig::install`]ed onto the current thread. Install returns a
//! [`ConfigGuard`] that restores the previous config on `Drop`, so nested and
//! sequential installs compose cleanly. The deep translate/verify read-sites
//! consult the **thread-local active config** ([`active_translate_node_budget`]
//! et al.); with a config installed they read THIS run's value, so two runs on
//! two threads each see their own — no cross-contamination.
//!
//! # Byte-identical semantics
//!
//! When NO config is installed, every reader falls back to a per-key
//! `OnceLock` env parse that reproduces the exact historical behaviour and
//! default (so unit tests that translate directly, and any un-instrumented
//! caller, are unchanged). A single real run installs `from_env()`, whose fields
//! equal that env parse, so an isolated run is byte-identical to the pre-refactor
//! lane — the A/B determinism gates (`tests/isabelle_shard_determinism.rs`) are
//! the proof. The only observable change is that two DIFFERENTLY-configured runs
//! sharing one process no longer leak into each other.

use std::cell::Cell;
use std::sync::OnceLock;

use crate::hol::isabelle_pure_translate::{PREMISE_STEP_BUDGET_DEFAULT, S3_MILLER_DEFAULT};

/// The verify/translate lane's per-run configuration: exactly the env knobs that
/// were previously frozen in first-wins `OnceLock` statics. `Copy` so it installs
/// into a thread-local `Cell` with zero allocation and workers can capture it by
/// value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VerifyConfig {
    /// Per-theorem translation node budget (`ISA_TRANSLATE_NODE_BUDGET`). `None`
    /// (the default) = unlimited. See
    /// [`crate::hol::isabelle_pure_translate::TranslateError::BudgetExceeded`].
    pub translate_node_budget: Option<u64>,
    /// Whether the stage-3/4 proof-β-redex Miller-pattern interior operand solve
    /// is enabled (`ISA_S3_MILLER`; default [`S3_MILLER_DEFAULT`]).
    pub s3_miller: bool,
    /// Whether the reprove lane is enabled (`ISA_REPROVE` present and not `0`;
    /// **default ON**).
    pub reprove: bool,
    /// Whether the opt-in fine-grained rejection-specifics tally is enabled
    /// (`ISA_REJECT_SPECIFICS`; default OFF).
    pub reject_specifics: bool,
    /// Global deterministic step budget for ONE `prove_from_premises`
    /// premise-instantiation search attempt (`ISA_PREMISE_STEP_BUDGET`). `None`
    /// = unbounded (explicit opt-out via `ISA_PREMISE_STEP_BUDGET=0`); unset =
    /// the generous calibrated [`PREMISE_STEP_BUDGET_DEFAULT`]. The search
    /// (`prove_goal`/`drive_premise`) is an exponential premise-application
    /// walk that, on a pathological shape, is effectively unbounded even under
    /// its nominal fuel — this budget makes it a deterministic, wall-clock-free
    /// bounded reject. See
    /// [`crate::hol::isabelle_pure_translate::TranslateError::PremiseBudgetExceeded`].
    pub premise_step_budget: Option<u64>,
    /// **#107 superclass-conjunct spelling alignment** (`ISA_CLASS_OPERAND_ALIGN`;
    /// **default OFF**). When ON, a class **operation** that is itself a registered
    /// LOCALE-PREDICATE (`Thy.class.<c>`, e.g. `Orderings.class.preorder`) embeds
    /// to its `isabelle.polyinst.<c>` def-const application in EVERY escalation
    /// mode — not only under the `InstanceEmbed::Unfold` pass. This makes the
    /// superclass-locale operand spelling CONSISTENT between (a) the
    /// poly-inst-flavored operand a superclass locale-predicate bakes into the
    /// once-registered class-def bodies once its `class.<c>_def` line is
    /// poly-inst-registered, and (b) the operand the OfClass /
    /// `order_class.axioms`-leg reconstruction produces — closing the
    /// corpus-routing desync root-caused in
    /// `docs/analysis/zproof-eta-operand-decode.md` §11 (the `contains-free-var`
    /// Orderings OfClass family that flip-gate `--add`ed and failed). Default OFF
    /// ⇒ every escalation mode is byte-identical to the pre-flag lane (the
    /// `Opaque`/`Unfold` guard is unchanged); ON is the gated, to-be-flip-gate-
    /// validated additive. See §12 of the analysis doc for the flag lifecycle.
    pub class_operand_align: bool,
}

impl Default for VerifyConfig {
    /// The all-defaults config: exactly what an empty environment parses to
    /// (`from_env()` with no vars set). Handy for tests and as an explicit base.
    fn default() -> Self {
        Self {
            translate_node_budget: None,
            s3_miller: S3_MILLER_DEFAULT,
            reprove: true,
            reject_specifics: false,
            premise_step_budget: Some(PREMISE_STEP_BUDGET_DEFAULT),
            class_operand_align: false,
        }
    }
}

impl VerifyConfig {
    /// Parse the whole config from the process environment — the SINGLE
    /// constructor that reads env. Each field mirrors the exact rule the
    /// historical per-key `OnceLock` reader used, so `from_env()` is
    /// value-identical to the pre-refactor lazy statics.
    #[must_use]
    pub fn from_env() -> Self {
        Self {
            translate_node_budget: env_translate_node_budget(),
            s3_miller: env_s3_miller(),
            reprove: env_reprove(),
            reject_specifics: env_reject_specifics(),
            premise_step_budget: env_premise_step_budget(),
            class_operand_align: env_class_operand_align(),
        }
    }

    /// Install this config as the active config on the CURRENT thread for the
    /// lifetime of the returned guard. Restores the previously-active config on
    /// `Drop`, so installs nest and sequence cleanly. Every entry point
    /// (stream / batch / verify-one / retry / shard / parallel workers) installs
    /// once at the top of its run.
    #[must_use = "the config is only active while the guard is alive; bind it for the run"]
    pub fn install(self) -> ConfigGuard {
        let prev = ACTIVE.with(|a| a.replace(Some(self)));
        ConfigGuard { prev }
    }
}

thread_local! {
    /// The config active on THIS thread, or `None` when nothing is installed
    /// (readers then fall back to the per-key env `OnceLock`s below). A `Cell`
    /// (not `RefCell`) because [`VerifyConfig`] is `Copy` — reads on the
    /// translate hot path are a branch-free copy with no borrow-flag check.
    static ACTIVE: Cell<Option<VerifyConfig>> = const { Cell::new(None) };
}

/// RAII guard returned by [`VerifyConfig::install`]: restores the config that was
/// active before the install when it drops.
#[derive(Debug)]
#[must_use = "dropping the guard restores the previous config; bind it for the run's lifetime"]
pub struct ConfigGuard {
    prev: Option<VerifyConfig>,
}

impl Drop for ConfigGuard {
    fn drop(&mut self) {
        ACTIVE.with(|a| a.set(self.prev));
    }
}

/// The config active on this thread, if one is installed.
#[must_use]
pub fn active_config() -> Option<VerifyConfig> {
    ACTIVE.with(Cell::get)
}

/// The active translation node budget — this thread's installed config, else the
/// historical env `OnceLock` fallback. Consulted by
/// [`crate::hol::isabelle_pure_translate::translate_node_budget`].
#[must_use]
pub(crate) fn active_translate_node_budget() -> Option<u64> {
    match ACTIVE.with(Cell::get) {
        Some(c) => c.translate_node_budget,
        None => env_translate_node_budget_cached(),
    }
}

/// The active stage-3/4 Miller flag — installed config, else env fallback.
#[must_use]
pub(crate) fn active_s3_miller_enabled() -> bool {
    match ACTIVE.with(Cell::get) {
        Some(c) => c.s3_miller,
        None => env_s3_miller_cached(),
    }
}

/// The active reprove-lane flag — installed config, else env fallback.
#[must_use]
pub(crate) fn active_reprove_enabled() -> bool {
    match ACTIVE.with(Cell::get) {
        Some(c) => c.reprove,
        None => env_reprove_cached(),
    }
}

/// The active reject-specifics flag — installed config, else env fallback.
#[must_use]
pub(crate) fn active_reject_specifics_enabled() -> bool {
    match ACTIVE.with(Cell::get) {
        Some(c) => c.reject_specifics,
        None => env_reject_specifics_cached(),
    }
}

/// The active premise-search step budget — this thread's installed config, else
/// the historical env `OnceLock` fallback (which defaults to
/// [`PREMISE_STEP_BUDGET_DEFAULT`] when the var is unset). `None` = unbounded.
/// Consulted by
/// [`crate::hol::isabelle_pure_translate::premise_step_budget`].
#[must_use]
pub(crate) fn active_premise_step_budget() -> Option<u64> {
    match ACTIVE.with(Cell::get) {
        Some(c) => c.premise_step_budget,
        None => env_premise_step_budget_cached(),
    }
}

/// The active #107 superclass-conjunct spelling-alignment flag — this thread's
/// installed config, else the env `OnceLock` fallback (default OFF). Consulted by
/// [`crate::hol::isabelle_pure_translate::class_operand_align_enabled`] (which
/// layers a `#[cfg(test)]` thread-local override on top for the in-process A/B).
#[must_use]
pub(crate) fn active_class_operand_align() -> bool {
    match ACTIVE.with(Cell::get) {
        Some(c) => c.class_operand_align,
        None => env_class_operand_align_cached(),
    }
}

// --- The env-parsing rules (shared by `from_env` and the fallbacks). Each
// reproduces the EXACT historical parse so behaviour is byte-identical. ---

/// `ISA_TRANSLATE_NODE_BUDGET` → `Option<u64>` (`None` = unlimited).
fn env_translate_node_budget() -> Option<u64> {
    std::env::var("ISA_TRANSLATE_NODE_BUDGET")
        .ok()
        .and_then(|s| s.parse().ok())
}

/// `ISA_S3_MILLER`: `"1"` → true, `"0"` → false, else [`S3_MILLER_DEFAULT`].
fn env_s3_miller() -> bool {
    match std::env::var("ISA_S3_MILLER").ok().as_deref() {
        Some("1") => true,
        Some("0") => false,
        _ => S3_MILLER_DEFAULT,
    }
}

/// `ISA_REPROVE`: present and not empty and not `"0"` → true; unset → true.
fn env_reprove() -> bool {
    match std::env::var("ISA_REPROVE") {
        Ok(v) => !v.is_empty() && v != "0",
        Err(_) => true,
    }
}

/// `ISA_REJECT_SPECIFICS` present (any value) → true.
fn env_reject_specifics() -> bool {
    std::env::var_os("ISA_REJECT_SPECIFICS").is_some()
}

/// `ISA_PREMISE_STEP_BUDGET` → `Option<u64>` (the premise-search step budget).
///
/// * unset ⇒ [`PREMISE_STEP_BUDGET_DEFAULT`] (the generous, calibrated default —
///   this budget is ON by default, unlike the translate-node budget);
/// * `"0"` ⇒ `None` (explicit opt-out to the historical unbounded search, used
///   only for measurement / the A/B that reproduces the incident spin);
/// * a valid `u64` ⇒ that exact value;
/// * unparseable ⇒ [`PREMISE_STEP_BUDGET_DEFAULT`] (safe fallback, never
///   silently unbounded).
fn env_premise_step_budget() -> Option<u64> {
    match std::env::var("ISA_PREMISE_STEP_BUDGET") {
        Ok(s) => match s.trim().parse::<u64>() {
            Ok(0) => None,
            Ok(n) => Some(n),
            Err(_) => Some(PREMISE_STEP_BUDGET_DEFAULT),
        },
        Err(_) => Some(PREMISE_STEP_BUDGET_DEFAULT),
    }
}

/// `ISA_CLASS_OPERAND_ALIGN`: present and not empty and not `"0"` → true; unset
/// (or `"0"`) → false. Default OFF — the flag is strictly opt-in.
fn env_class_operand_align() -> bool {
    match std::env::var("ISA_CLASS_OPERAND_ALIGN") {
        Ok(v) => !v.is_empty() && v != "0",
        Err(_) => false,
    }
}

// The per-key `OnceLock` fallbacks: identical first-read-caches to the pre-
// refactor statics, so an un-installed caller behaves EXACTLY as before.

fn env_translate_node_budget_cached() -> Option<u64> {
    static C: OnceLock<Option<u64>> = OnceLock::new();
    *C.get_or_init(env_translate_node_budget)
}
fn env_s3_miller_cached() -> bool {
    static C: OnceLock<bool> = OnceLock::new();
    *C.get_or_init(env_s3_miller)
}
fn env_reprove_cached() -> bool {
    static C: OnceLock<bool> = OnceLock::new();
    *C.get_or_init(env_reprove)
}
fn env_reject_specifics_cached() -> bool {
    static C: OnceLock<bool> = OnceLock::new();
    *C.get_or_init(env_reject_specifics)
}
fn env_premise_step_budget_cached() -> Option<u64> {
    static C: OnceLock<Option<u64>> = OnceLock::new();
    *C.get_or_init(env_premise_step_budget)
}
fn env_class_operand_align_cached() -> bool {
    static C: OnceLock<bool> = OnceLock::new();
    *C.get_or_init(env_class_operand_align)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_install_reads_installed_config_then_restores() {
        let base = active_translate_node_budget();
        let cfg = VerifyConfig {
            translate_node_budget: Some(123),
            s3_miller: true,
            reprove: false,
            reject_specifics: true,
            premise_step_budget: Some(456),
            class_operand_align: true,
        };
        {
            let _g = cfg.install();
            assert_eq!(active_translate_node_budget(), Some(123));
            assert!(active_s3_miller_enabled());
            assert!(!active_reprove_enabled());
            assert!(active_reject_specifics_enabled());
            assert_eq!(active_premise_step_budget(), Some(456));
            assert!(active_class_operand_align());
        }
        // Guard drop restores the previous (un-installed) view.
        assert_eq!(active_translate_node_budget(), base);
    }

    #[test]
    fn test_installs_nest_and_restore_in_order() {
        let outer = VerifyConfig {
            translate_node_budget: Some(10),
            ..VerifyConfig::default()
        };
        let inner = VerifyConfig {
            translate_node_budget: Some(20),
            ..VerifyConfig::default()
        };
        let _go = outer.install();
        assert_eq!(active_translate_node_budget(), Some(10));
        {
            let _gi = inner.install();
            assert_eq!(active_translate_node_budget(), Some(20));
        }
        assert_eq!(active_translate_node_budget(), Some(10));
    }

    /// The mission gate: two configs with DIFFERENT budgets coexist in one
    /// process without leaking into each other. Two threads each install a
    /// distinct budget, rendezvous at a barrier so their lifetimes genuinely
    /// overlap, and each asserts it still sees its OWN budget — the exact
    /// cross-run contamination the first-wins `OnceLock` could not prevent.
    #[test]
    fn test_two_configs_with_different_budgets_coexist_in_one_process() {
        use std::sync::{Arc, Barrier};

        let barrier = Arc::new(Barrier::new(2));
        let b1 = Arc::clone(&barrier);
        let b2 = Arc::clone(&barrier);

        let t1 = std::thread::spawn(move || {
            let _g = VerifyConfig {
                translate_node_budget: Some(1_000),
                ..VerifyConfig::default()
            }
            .install();
            b1.wait(); // both configs are now installed and live simultaneously
            let seen = active_translate_node_budget();
            b1.wait();
            seen
        });
        let t2 = std::thread::spawn(move || {
            let _g = VerifyConfig {
                translate_node_budget: Some(2_000),
                ..VerifyConfig::default()
            }
            .install();
            b2.wait();
            let seen = active_translate_node_budget();
            b2.wait();
            seen
        });

        assert_eq!(
            t1.join().expect("t1"),
            Some(1_000),
            "thread 1 kept its own budget"
        );
        assert_eq!(
            t2.join().expect("t2"),
            Some(2_000),
            "thread 2 kept its own budget"
        );
    }

    #[test]
    fn test_default_matches_from_env_with_no_vars() {
        // With none of the four vars set, from_env() equals Default. (Runs in the
        // test process; the isabelle scale tests already serialize env mutation,
        // and this test sets nothing.)
        let d = VerifyConfig::default();
        assert_eq!(d.translate_node_budget, None);
        assert!(!d.s3_miller, "S3_MILLER default is off");
        assert!(d.reprove, "reprove default is on");
        assert!(!d.reject_specifics);
        assert_eq!(
            d.premise_step_budget,
            Some(PREMISE_STEP_BUDGET_DEFAULT),
            "premise-search budget is ON by default (finite, calibrated)"
        );
    }
}
