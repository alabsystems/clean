// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Explicit measurement and differential tool for EvalIR vocabulary reuse.
//!
//! Until 2026-09-08 these two procedures were ignored tests beside the
//! reuse tests. The org rule is that a first-party test passes, fails, or is
//! deleted — never ignored — and that measurement code lives in an explicit
//! tool that is run on purpose (`scripts/local_gate.sh`, leg
//! `no-ignored-tests`, refuses the push otherwise). They live here as library
//! functions so the `eval_ir_reuse_measure` binary can drive them:
//!
//! ```text
//! targo --unverified run -p clean-verify --bin eval_ir_reuse_measure -- measure
//! targo --unverified run -p clean-verify --bin eval_ir_reuse_measure -- differential
//! ```
//!
//! A violated invariant is an `Err`, never a panic, so the tool's exit status
//! is the verdict.

use super::{
    build_byte_prelude_spec_v1_with_stack, build_on_stack, shared_specification_with_stack,
    EvalIrVocabulary,
};
use crate::spec::{SpecError, Specification};
use clean_kernel::Name;
use std::time::{Duration, Instant};

/// Why a measurement or differential could not be completed.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ReuseMeasureError {
    /// A specification build failed.
    #[error(transparent)]
    Spec(#[from] SpecError),
    /// An invariant the procedure checks did not hold.
    #[error("invariant violated: {0}")]
    Invariant(String),
}

macro_rules! check {
    ($cond:expr, $($arg:tt)+) => {
        if !$cond {
            return Err(ReuseMeasureError::Invariant(format!($($arg)+)));
        }
    };
}

macro_rules! check_eq {
    ($left:expr, $right:expr, $($arg:tt)+) => {
        if $left != $right {
            return Err(ReuseMeasureError::Invariant(format!(
                "{} differs between the two builds",
                format!($($arg)+)
            )));
        }
    };
}

/// Timings and process residency around two consecutive checked byte builds
/// and one clone. Residency is `None` where the platform cannot report it —
/// never a guessed size.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ByteReuseMeasurement {
    /// Wall time of the first (cold) checked byte build.
    pub first_build: Duration,
    /// Wall time of the second builder request.
    pub second_build: Duration,
    /// Wall time of cloning the first specification.
    pub clone: Duration,
    /// Definitions in the built specification.
    pub definitions: usize,
    /// Constants in the built environment.
    pub constants: usize,
    /// Resident set (KiB) before the first build.
    pub rss_kib_before: Option<u64>,
    /// Resident set (KiB) after the first build.
    pub rss_kib_after_first: Option<u64>,
    /// Resident set (KiB) with the second build and the clone alive.
    pub rss_kib_with_copies: Option<u64>,
    /// Resident set (KiB) after every owned copy is dropped. Process RSS
    /// includes allocator retention, not exact live-object size.
    pub rss_kib_after_owned_drop: Option<u64>,
}

/// Cold byte build, second builder request, and clone — timed, with the
/// isolation invariants of the clone checked: a definition and an option
/// registered on the clone must not appear in either original build.
pub fn measure_consecutive_byte_builds_and_clone() -> Result<ByteReuseMeasurement, ReuseMeasureError>
{
    let rss_kib_before = resident_kib();
    let started = Instant::now();
    let first = build_byte_prelude_spec_v1_with_stack()?;
    let first_build = started.elapsed();
    let rss_kib_after_first = resident_kib();
    let started = Instant::now();
    let second = build_byte_prelude_spec_v1_with_stack()?;
    let second_build = started.elapsed();
    let started = Instant::now();
    let mut independent = first.clone();
    let clone = started.elapsed();
    let rss_kib_with_copies = resident_kib();
    check_eq!(
        first.definitions().len(),
        second.definitions().len(),
        "definition count"
    );
    check_eq!(
        first.env().num_constants(),
        second.env().num_constants(),
        "constant count"
    );
    independent
        .env_mut()
        .set_option("reuse-probe".into(), Some("changed".into()));
    independent.add_recursive_def(
        "def byte_reuse_probe : Nat := 7",
        "isolated clone measurement",
    )?;
    let probe = Name::from_string("byte_reuse_probe");
    check!(
        first.env().get_const(&probe).is_none(),
        "probe definition leaked into the first build"
    );
    check!(
        second.env().get_const(&probe).is_none(),
        "probe definition leaked into the second build"
    );
    check!(
        first.env().get_option("reuse-probe").is_none(),
        "probe option leaked into the first build"
    );
    check!(
        second.env().get_option("reuse-probe").is_none(),
        "probe option leaked into the second build"
    );
    let definitions = first.definitions().len();
    let constants = first.env().num_constants();
    drop(independent);
    drop(second);
    drop(first);
    Ok(ByteReuseMeasurement {
        first_build,
        second_build,
        clone,
        definitions,
        constants,
        rss_kib_before,
        rss_kib_after_first,
        rss_kib_with_copies,
        rss_kib_after_owned_drop: resident_kib(),
    })
}

/// Rebuilds the byte vocabulary through the original constructor and checks
/// the shared, cached specification against it definition by definition and
/// constant by constant. Returns the number of definitions compared.
pub fn vocabulary_cached_byte_matches_fresh_constructor() -> Result<usize, ReuseMeasureError> {
    let shared = shared_specification_with_stack(EvalIrVocabulary::ByteV1)?;
    let fresh = build_on_stack(
        "vocabulary-fresh-measure",
        "measure",
        Specification::new_eval_ir_byte_prelude_spec_v1,
    )?;
    check_eq!(
        shared.env().num_constants(),
        fresh.env().num_constants(),
        "constant count"
    );
    check_eq!(
        shared.definitions().len(),
        fresh.definitions().len(),
        "definition count"
    );
    for (name, expected) in fresh.definitions() {
        let actual = shared.get_definition(name).ok_or_else(|| {
            ReuseMeasureError::Invariant(format!(
                "definition {name} is missing from the cached vocabulary"
            ))
        })?;
        check_eq!(
            actual.elaborated_type,
            expected.elaborated_type,
            "type {name}"
        );
        check_eq!(
            actual.elaborated_value,
            expected.elaborated_value,
            "value {name}"
        );
        check_eq!(actual.proof_status, expected.proof_status, "status {name}");
        check_eq!(actual.is_axiom, expected.is_axiom, "axiom {name}");
    }
    for expected in fresh.env().constants() {
        let name = &expected.name;
        let actual = shared.env().get_const(name).ok_or_else(|| {
            ReuseMeasureError::Invariant(format!(
                "constant {name} is missing from the cached vocabulary"
            ))
        })?;
        check_eq!(
            actual.level_params,
            expected.level_params,
            "universes {name}"
        );
        check_eq!(actual.type_, expected.type_, "registered type {name}");
        check_eq!(actual.value, expected.value, "registered value {name}");
        check_eq!(actual.kind, expected.kind, "kind {name}");
        check_eq!(
            actual.is_reducible,
            expected.is_reducible,
            "unfolding {name}"
        );
        check_eq!(
            actual.reducibility,
            expected.reducibility,
            "reducibility {name}"
        );
    }
    Ok(fresh.definitions().len())
}

/// Measurement only; unavailable platforms report None, never a guessed size.
fn resident_kib() -> Option<u64> {
    let output = std::process::Command::new("ps")
        .args(["-o", "rss=", "-p", &std::process::id().to_string()])
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    std::str::from_utf8(&output.stdout)
        .ok()?
        .trim()
        .parse()
        .ok()
}
