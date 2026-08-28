// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! U2 rung-0b constraint histogram (designs/2026-08-08-u2-universe-polymorphism-ladder.md).
//!
//! When `CLEAN_U2_HISTOGRAM=1`, every level-constraint event the solver
//! cannot (or can only barely) handle is emitted as one machine-parsable
//! stderr line: `[u2hist] class=<class> site=<site> detail=<..>`.
//! `scripts/u2_histogram.sh` aggregates the lines into the ranked
//! histogram that sizes rung 3 (algebraic solver + postponement) against
//! real Mathlib SOURCE. Zero cost when the variable is unset beyond one
//! cached boolean check; every emission site is a cold failure arm.

use clean_kernel::Level;
use std::sync::OnceLock;

/// Cached `CLEAN_U2_HISTOGRAM=1` check.
pub(crate) fn u2_hist_enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var("CLEAN_U2_HISTOGRAM").is_ok_and(|v| v == "1"))
}

/// Full-depth level rendering (std `Debug` truncates nested levels to
/// `..`, which hides exactly the algebraic shapes the histogram exists to
/// measure).
pub(crate) fn level_str(l: &Level) -> String {
    match l {
        Level::Zero => "0".into(),
        Level::Succ(a) => format!("S({})", level_str(a)),
        Level::Max(a, b) => format!("max({},{})", level_str(a), level_str(b)),
        Level::IMax(a, b) => format!("imax({},{})", level_str(a), level_str(b)),
        Level::Param(n) => format!("{n}"),
    }
}

/// Emit one histogram event line (no-op unless enabled).
pub(crate) fn u2_hist(class: &str, site: &str, detail: &str) {
    if u2_hist_enabled() {
        eprintln!("[u2hist] class={class} site={site} detail={detail}");
    }
}

/// Classify a level pair that FAILED to unify, for the rung-3 sizing
/// histogram. `l1_rigid`/`l2_rigid` say whether that side is a rigid
/// declared `Level::Param`.
pub(crate) fn classify_level_failure(
    l1: &Level,
    l2: &Level,
    l1_rigid: bool,
    l2_rigid: bool,
) -> &'static str {
    fn has_maximax(l: &Level) -> bool {
        match l {
            Level::Max(_, _) | Level::IMax(_, _) => true,
            Level::Succ(inner) => has_maximax(inner),
            _ => false,
        }
    }
    if !l1.has_params() && !l2.has_params() {
        "concrete-conflict"
    } else if has_maximax(l1) || has_maximax(l2) {
        "algebraic-maximax"
    } else if l1_rigid || l2_rigid {
        "rigid-blocked"
    } else {
        "shape-residual"
    }
}

/// U2 stage 3 mint trace — `CLEAN_U2_MINT_TRACE=1` emits one stderr line per
/// universe-level mint, naming the AUTHORITY that minted it:
/// `[u2mint] site=elabctx|proofstate name=u_N`.
///
/// This is the instrument that measured the stage-3 defect. Before the shared
/// [`crate::level_mint::LevelMint`] landed, a single tactic block could show
/// `site=proofstate name=u_3` and `site=elabctx name=u_3` — one name, two
/// unrelated levels (see `crate::level_mint` and
/// `infer::tests::tactic_bridge_levels`). It is kept because that is the only
/// way to SEE which authority minted a name, and the property it measures is
/// one a future refactor could silently lose. Same cost profile as
/// [`u2_hist`]: one cached boolean when off.
pub(crate) fn u2_mint_trace(site: &str, name: &str) {
    static ON: OnceLock<bool> = OnceLock::new();
    if *ON.get_or_init(|| std::env::var("CLEAN_U2_MINT_TRACE").is_ok_and(|v| v == "1")) {
        eprintln!("[u2mint] site={site} name={name}");
    }
}
