// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! P3's Trust-leg contract, shared by every test that Clean's
//! `scripts/patched_kernel_control_trust.py` installs into a scratch copy of
//! Trust's tree (it is installed as `tests/p3_contract/contract.rs` beside each): the
//! declared kernel, the two outcomes, the liveness check, the lines the runner
//! reads (`P3_TRUST_PIN`, `P3_TRUST_KERNEL`, `P3_TRUST_CONTROL`, `P3_TRUST`)
//! and the comparison of the measured rows with the pins. It needs nothing but
//! `clean-kernel`, which every crate it is installed into links.
//!
//! Every pin, control and row is printed before anything is asserted, so a red
//! run still shows the whole measurement; the runner refuses a leg whose
//! printed rows do not match the printed pins site for site.

use clean_kernel::{Environment, Expr, TypeChecker};

pub(crate) const MODE_ENV: &str = "CLEAN_P3_KERNEL_UNDER_TEST";
pub(crate) const MUTANT_ID: &str = "check-type-nat-zero-false";

/// The kernel a run declares: the pinned Clean, or P3's mutant M1.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Kernel {
    Unmodified,
    Mutant,
}

impl Kernel {
    fn declared() -> Self {
        match std::env::var(MODE_ENV) {
            Err(std::env::VarError::NotPresent) => Self::Unmodified,
            Ok(value) if value == MUTANT_ID => Self::Mutant,
            other => panic!("{MODE_ENV} must be unset or `{MUTANT_ID}`, got {other:?}"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Outcome {
    Minted,
    Refused,
}

/// (site, unmodified, mutant). A mutant `Minted` is a named gap: the day the
/// site gains a check independent of `clean-kernel`, the mutant leg reports
/// `P3 KNOWN GAP CLOSED` and stays red until the table moves; the runner then
/// re-mints the record, which carries the pins and every installed file's
/// digest.
pub(crate) type Pin = (&'static str, Outcome, Outcome);

/// A measured site, its outcome and what the entry said.
pub(crate) type Row = (&'static str, Outcome, String);

/// A control stage and what it measured; every control must mint.
pub(crate) type Control = (&'static str, (Outcome, String));

/// The refusal the planted pair draws from an unmodified `check_type`.
pub(crate) fn is_planted_mismatch(message: &str) -> bool {
    message.contains("Type mismatch: expected False, got Nat")
        || (message.contains("TypeMismatch")
            && message.contains("False")
            && message.contains("Nat"))
}

/// Print the pins, then ask the kernel this test links about the honest and
/// the planted pair: the declared kernel must be the linked one. Returns the
/// declared kernel.
pub(crate) fn start(pins: &[Pin], env: &Environment, failures: &mut Vec<String>) -> Kernel {
    let declared = Kernel::declared();
    for (site, unmodified, mutant) in pins {
        println!("P3_TRUST_PIN\t{site}\t{unmodified:?}\t{mutant:?}");
    }
    let checker = TypeChecker::new(env);
    let honest_pair = checker.check_type(&Expr::const_str("True.intro"), &Expr::const_str("True"));
    let planted_pair = checker.check_type(&Expr::const_str("Nat.zero"), &Expr::const_str("False"));
    drop(checker);
    let live = planted_pair.is_ok();
    println!("P3_TRUST_KERNEL\tdeclared={declared:?}\tlive={live}");
    if let Err(error) = &honest_pair {
        failures
            .push(format!("P3 VACUOUS: the linked kernel refuses `True.intro : True`: {error:?}"));
    }
    // A match guard, not a let chain: the contract builds under edition 2021
    // (`trust-spec-temporal`) as well as 2024 (`trust-certify`).
    match &planted_pair {
        Err(error) if !is_planted_mismatch(&format!("{error:?}")) => failures.push(format!(
            "P3 UNEXPECTED REFUSAL: the linked kernel refuses the planted pair by {error:?}, not the type mismatch"
        )),
        _ => {}
    }
    match (declared, live) {
        (Kernel::Unmodified, true) => failures.push(format!(
            "P3 WRONG ACCEPT: {MODE_ENV} is unset, but the linked clean-kernel accepts the planted pair"
        )),
        (Kernel::Mutant, false) => failures.push(format!(
            "P3 MUTATION NOT LIVE: {MODE_ENV}={MUTANT_ID}, but the linked clean-kernel refuses the planted pair"
        )),
        _ => {}
    }
    declared
}

/// Print the controls; one that did not mint leaves the leg measuring nothing.
pub(crate) fn report_controls(control: &[Control], failures: &mut Vec<String>) {
    for (stage, (outcome, detail)) in control {
        println!("P3_TRUST_CONTROL\t{stage}\t{outcome:?}\t{detail}");
        if *outcome != Outcome::Minted {
            failures
                .push(format!("P3 VACUOUS: the control stage `{stage}` did not mint: {detail}"));
        }
    }
}

/// Print the rows, compare them with the pins for the declared kernel, and fail
/// the test with every failure collected.
pub(crate) fn finish(rows: &[Row], pins: &[Pin], declared: Kernel, mut failures: Vec<String>) {
    for (site, outcome, detail) in rows {
        println!("P3_TRUST\t{site}\t{outcome:?}\t{detail}");
    }
    let sites: Vec<&str> = rows.iter().map(|(site, _, _)| *site).collect();
    let pinned: Vec<&str> = pins.iter().map(|(site, _, _)| *site).collect();
    if sites != pinned {
        failures.push(format!("P3 SITES MOVED: measured {sites:?}, pinned {pinned:?}"));
    }
    for ((site, outcome, detail), (_, unmodified, mutant)) in rows.iter().zip(pins) {
        let pin = if declared == Kernel::Mutant { *mutant } else { *unmodified };
        match (pin, *outcome) {
            (Outcome::Refused, Outcome::Minted) => {
                failures.push(format!("P3 WRONG ACCEPT: {site}: {detail}"));
            }
            (Outcome::Minted, Outcome::Refused) => {
                failures.push(format!("P3 KNOWN GAP CLOSED: {site}: {detail}"));
            }
            (Outcome::Minted, Outcome::Minted) | (Outcome::Refused, Outcome::Refused) => {}
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
