// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Shared half of the patched-kernel control (unit P3 of the kernel
//! self-proof plan, `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`).
//!
//! The control asks one question of every place that mints an
//! authority-bearing acceptance: if `clean-kernel` were wrong about one
//! planted proof of `False`, would an accepted row still come out? A host
//! crate's `tests/patched_kernel_control.rs` includes this file with `#[path]`,
//! drives its sites on the planted pair, and hands the observations to
//! [`judge`] with one pin per site.
//!
//! The same test is built twice:
//!
//! * in the ordinary tree, where every site must refuse the pair, by name;
//! * by `scripts/patched_kernel_control.py`, in a scratch copy of the tree
//!   whose `clean-kernel` was patched to accept exactly `Nat.zero : False`,
//!   with [`MODE_ENV`] set. There a site that mints is a pinned gap (nothing
//!   but `clean-kernel` stands behind it) and a site that still refuses names
//!   who stopped it.
//!
//! [`MODE_ENV`] only says which table to compare with. It never relaxes an
//! assertion: the linked kernel is asked about the pair first, and a run whose
//! declared kernel is not the linked one fails in both directions.

use std::path::PathBuf;

use clean_kernel::{Declaration, Environment, Expr, Name, TypeChecker, TypeError};

/// Set by `scripts/patched_kernel_control.py` on the mutant leg, and by
/// nothing else.
pub const MODE_ENV: &str = "CLEAN_P3_KERNEL_UNDER_TEST";
/// The one mutant this control knows: `TypeChecker::check_type` also accepts
/// the closed term `Nat.zero` at type `False`.
pub const MUTANT_ID: &str = "check-type-nat-zero-false";

/// The tracked record the runner mints, relative to the repository root.
pub const RECORD_PATH: &str = "reports/self-proof-p3-2026-11-12/patched_kernel_control.json";

/// Who decided a site's outcome. Each host crate names only the deciders its
/// own sites meet.
#[allow(dead_code)]
pub mod by {
    /// The refusal is `clean-kernel`'s own (the only possible answer on the
    /// unmodified kernel for a site with no second checker).
    pub const CLEAN_KERNEL: &str = "clean-kernel";
    /// A row was minted and nothing but the (mutated) kernel was asked.
    pub const NONE: &str = "none";
    /// The refusal came from another entry of the SAME kernel that the
    /// mutation does not touch (`is_def_eq` called directly). It is not an
    /// independent check: a mutant placed there would pass it.
    pub const SAME_KERNEL_OTHER_ENTRY: &str = "clean-kernel-def-eq-entry";
    /// `clean-ck0`, which shares no code with `clean-kernel`.
    pub const CLEAN_CK0: &str = "clean-ck0";
    /// Lean 4's own kernel (`leanchecker --fresh` of the pinned toolchain).
    pub const LEAN_KERNEL: &str = "lean-kernel";
}

/// Which `clean-kernel` the run says it linked.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KernelUnderTest {
    Unmodified,
    Mutant,
}

impl KernelUnderTest {
    /// Read [`MODE_ENV`]. Any value but [`MUTANT_ID`] is a typo, never a mode.
    pub fn declared() -> Self {
        match std::env::var(MODE_ENV) {
            Err(std::env::VarError::NotPresent) => Self::Unmodified,
            Ok(value) if value == MUTANT_ID => Self::Mutant,
            other => panic!("{MODE_ENV} must be unset or `{MUTANT_ID}`, got {other:?}"),
        }
    }

    pub fn label(self) -> &'static str {
        match self {
            Self::Unmodified => "unmodified",
            Self::Mutant => MUTANT_ID,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// The site produced its acceptance (token, stamp, row, exit status).
    Minted,
    /// The site produced no acceptance.
    Refused,
}

impl Verdict {
    pub fn label(self) -> &'static str {
        match self {
            Self::Minted => "minted",
            Self::Refused => "refused",
        }
    }
}

/// One expected outcome: what happened, who decided it, and the exact name of
/// the refusal or of the minted object.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Outcome {
    pub verdict: Verdict,
    pub by: &'static str,
    pub detail: &'static str,
}

impl Outcome {
    pub const fn minted(detail: &'static str) -> Self {
        Self {
            verdict: Verdict::Minted,
            by: by::NONE,
            detail,
        }
    }

    pub const fn refused(by: &'static str, detail: &'static str) -> Self {
        Self {
            verdict: Verdict::Refused,
            by,
            detail,
        }
    }
}

/// The pin for one site: its outcome on the unmodified kernel and under the
/// mutant. A `mutant` outcome of [`Outcome::minted`] is a KNOWN GAP: the day
/// that site gains an independent check, the mutant leg stops matching and
/// the run fails until the pin is moved.
#[derive(Debug, Clone, Copy)]
pub struct Pin {
    pub site: &'static str,
    /// What the site mints and what production path it stands for.
    pub mints: &'static str,
    pub unmodified: Outcome,
    pub mutant: Outcome,
}

/// What a probe saw at one site.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Observed {
    pub site: &'static str,
    pub verdict: Verdict,
    pub by: &'static str,
    pub detail: String,
}

impl Observed {
    pub fn minted(site: &'static str, detail: impl Into<String>) -> Self {
        Self {
            site,
            verdict: Verdict::Minted,
            by: by::NONE,
            detail: detail.into(),
        }
    }

    pub fn refused(site: &'static str, by: &'static str, detail: impl Into<String>) -> Self {
        Self {
            site,
            verdict: Verdict::Refused,
            by,
            detail: detail.into(),
        }
    }
}

/// The planted claim: `False`.
pub fn planted_type() -> Expr {
    Expr::const_str("False")
}

/// The planted "proof": the closed, axiom-free, ill-typed term `Nat.zero`.
pub fn planted_value() -> Expr {
    Expr::const_str("Nat.zero")
}

/// `theorem <name> : False := Nat.zero`.
// Not every host crate hands the kernel a `Declaration`; some build their own
// carrier (an export record, a shard entry) around the same pair.
#[allow(dead_code)]
pub fn planted_theorem(name: &str) -> Declaration {
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: planted_type(),
        value: planted_value(),
    }
}

/// An honest closed proof, `theorem <name> : True := True.intro`, for the
/// non-vacuity control every site runs before the planted pair.
#[allow(dead_code)]
pub fn honest_theorem(name: &str) -> Declaration {
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::const_str("True"),
        value: Expr::const_str("True.intro"),
    }
}

/// Whether a lane's refusal message is the kernel's type mismatch on the
/// planted pair. Lanes that carry the error as text spell `TypeError` either
/// by its `Debug` name (`TypeMismatch { expected: .. False .., inferred: ..
/// Nat .. }`) or by its `Display` form (`Type mismatch: expected False, got
/// Nat`); any other refusal is not the one this control plants.
#[allow(dead_code)]
pub fn is_planted_mismatch(message: &str) -> bool {
    message.contains("Type mismatch: expected False, got Nat")
        || (message.contains("TypeMismatch")
            && message.contains("False")
            && message.contains("Nat"))
}

/// Ask the linked kernel's ordinary checker about the planted pair. `true`
/// means the mutation is live in this binary.
pub fn linked_kernel_accepts_planted_pair() -> bool {
    let env = Environment::with_prelude();
    let checker = TypeChecker::new(&env);
    checker
        .check_type(&Expr::const_str("True.intro"), &Expr::const_str("True"))
        .expect("the linked kernel must accept the honest pair `True.intro : True`");
    match checker.check_type(&planted_value(), &planted_type()) {
        Ok(()) => true,
        Err(TypeError::TypeMismatch { .. }) => false,
        Err(other) => {
            panic!("the planted pair must be accepted or refused as a type mismatch, got {other:?}")
        }
    }
}

/// Print the rows, then compare them with the pins for the declared kernel.
///
/// The rows are printed before anything is asserted, so a red run still shows
/// the whole measurement. Every failure line starts with a fixed needle:
/// `P3 WRONG ACCEPT` (an acceptance where a refusal is pinned), `P3 MUTATION
/// NOT LIVE`, `P3 KNOWN GAP CLOSED` (a refusal where a gap is pinned) or `P3
/// PIN MISMATCH`.
pub fn judge(package: &str, pins: &[Pin], observed: &[Observed]) {
    let kernel = KernelUnderTest::declared();
    let live = linked_kernel_accepts_planted_pair();
    println!(
        "P3_KERNEL\t{package}\t{}\tlinked-kernel-accepts-planted-pair={live}",
        kernel.label()
    );
    for pin in pins {
        println!("P3_SITE\t{package}\t{}\t{}", pin.site, pin.mints);
    }
    for row in observed {
        println!(
            "P3_ROW\t{package}\t{}\t{}\t{}\t{}\t{}",
            kernel.label(),
            row.site,
            row.verdict.label(),
            row.by,
            row.detail
        );
    }

    let mut failures = Vec::new();
    match (kernel, live) {
        (KernelUnderTest::Unmodified, true) => failures.push(format!(
            "P3 WRONG ACCEPT: the linked clean-kernel accepts `Nat.zero : False`, and this run did not declare the mutant ({MODE_ENV} is unset)"
        )),
        (KernelUnderTest::Mutant, false) => failures.push(format!(
            "P3 MUTATION NOT LIVE: {MODE_ENV}={MUTANT_ID}, but the linked clean-kernel refuses the planted pair, so this run measures nothing"
        )),
        (KernelUnderTest::Unmodified, false) | (KernelUnderTest::Mutant, true) => {}
    }

    let pinned_sites: Vec<&str> = pins.iter().map(|pin| pin.site).collect();
    let observed_sites: Vec<&str> = observed.iter().map(|row| row.site).collect();
    if pinned_sites != observed_sites {
        failures.push(format!(
            "P3 PIN MISMATCH: the pinned sites {pinned_sites:?} are not the observed sites {observed_sites:?}"
        ));
    }
    for (pin, row) in pins.iter().zip(observed) {
        let want = match kernel {
            KernelUnderTest::Unmodified => pin.unmodified,
            KernelUnderTest::Mutant => pin.mutant,
        };
        if (row.verdict, row.by, row.detail.as_str()) == (want.verdict, want.by, want.detail) {
            continue;
        }
        let needle = match (want.verdict, row.verdict) {
            (Verdict::Refused, Verdict::Minted) => "P3 WRONG ACCEPT",
            (Verdict::Minted, Verdict::Refused) => "P3 KNOWN GAP CLOSED",
            (Verdict::Minted, Verdict::Minted) | (Verdict::Refused, Verdict::Refused) => {
                "P3 PIN MISMATCH"
            }
        };
        failures.push(format!(
            "{needle} at {package}::{} on the {} kernel: pinned {} by {} ({}), observed {} by {} ({})",
            pin.site,
            kernel.label(),
            want.verdict.label(),
            want.by,
            want.detail,
            row.verdict.label(),
            row.by,
            row.detail
        ));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

fn record_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(RECORD_PATH)
}

fn outcome_of(value: &serde_json::Value, by_key: &str) -> (String, String, String) {
    let field = |key: &str| {
        value
            .get(key)
            .and_then(serde_json::Value::as_str)
            .unwrap_or_else(|| {
                panic!("{RECORD_PATH}: a site outcome lacks the string `{key}`: {value}")
            })
            .to_string()
    };
    (field("verdict"), field(by_key), field("detail"))
}

/// The tracked record must say, for this package, exactly what the pins say:
/// the same sites in the same order with the same outcomes on both kernels.
/// The record is minted by a mutant run; this keeps it and the pins from
/// drifting apart between such runs.
pub fn assert_record_matches_pins(package: &str, pins: &[Pin]) {
    let path = record_path();
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    let record: serde_json::Value =
        serde_json::from_str(&text).unwrap_or_else(|error| panic!("parse {RECORD_PATH}: {error}"));
    assert_eq!(
        record
            .get("mutation")
            .and_then(|mutation| mutation.get("id"))
            .and_then(serde_json::Value::as_str),
        Some(MUTANT_ID),
        "{RECORD_PATH}: the record is for another mutation"
    );
    let rows: Vec<&serde_json::Value> = record
        .get("sites")
        .and_then(serde_json::Value::as_array)
        .unwrap_or_else(|| panic!("{RECORD_PATH}: no `sites` array"))
        .iter()
        .filter(|row| row.get("package").and_then(serde_json::Value::as_str) == Some(package))
        .collect();
    let recorded: Vec<_> = rows
        .iter()
        .map(|row| {
            let site = row
                .get("site")
                .and_then(serde_json::Value::as_str)
                .unwrap_or_else(|| panic!("{RECORD_PATH}: a row lacks `site`: {row}"))
                .to_string();
            let unmodified = row
                .get("unmodified")
                .unwrap_or_else(|| panic!("{RECORD_PATH}: {site} lacks `unmodified`"));
            let mutant = row
                .get("mutant")
                .unwrap_or_else(|| panic!("{RECORD_PATH}: {site} lacks `mutant`"));
            (
                site,
                outcome_of(unmodified, "by"),
                outcome_of(mutant, "stopped_by"),
            )
        })
        .collect();
    let pinned: Vec<_> = pins
        .iter()
        .map(|pin| {
            let spell = |outcome: Outcome| {
                (
                    outcome.verdict.label().to_string(),
                    outcome.by.to_string(),
                    outcome.detail.to_string(),
                )
            };
            (
                pin.site.to_string(),
                spell(pin.unmodified),
                spell(pin.mutant),
            )
        })
        .collect();
    assert_eq!(
        recorded, pinned,
        "{RECORD_PATH} and the pins of {package} disagree; re-mint the record with scripts/patched_kernel_control.py --write-record"
    );
}
