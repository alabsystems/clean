// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A malformed step is refused, never a panic, through this adapter.
//!
//! `clean cert verify-external` crashed (an index out of bounds in the vendored
//! checker; Clean's release profile aborts on a panic) on a certificate whose
//! `drup` step concluding `(cl)` was renamed `pbblast_bvand`. The fix and the
//! sweep that found the other sites are in the vendored crate
//! (`third-party/carcara/carcara/tests/malformed_steps.rs` and
//! `third-party/carcara/DOWNSTREAM.md`, "Malformed steps are refused, not a
//! panic"). These tests send the same shapes through the whole adapter, whose
//! own guards (`bv_literals`, `pb_widths`, `ashr`) run first.

use super::verify_alethe_proof;
use std::panic::{self, AssertUnwindSafe};

/// Every rule name the vendored checker dispatches on, read from `get_rule`.
fn rule_names() -> Vec<String> {
    let source =
        include_str!("../../../../../../third-party/carcara/carcara/src/checker/shared.rs");
    let start = source
        .find("pub fn get_rule(")
        .expect("get_rule is in shared.rs");
    let end = start
        + source[start..]
            .find("_ => return None")
            .expect("get_rule ends");
    let mut names = Vec::new();
    for line in source[start..end].lines().map(str::trim) {
        let Some(arm) = line.split("=>").next().filter(|_| line.starts_with('"')) else {
            continue;
        };
        for name in arm.split('"').skip(1).step_by(2) {
            if !names.iter().any(|n| n == name) {
                names.push(name.to_owned());
            }
        }
    }
    names
}

/// `verify_alethe_proof`, with a panic caught and returned as `Err`.
fn verdict(problem: &str, proof: &str) -> Result<Result<bool, String>, String> {
    panic::catch_unwind(AssertUnwindSafe(|| {
        verify_alethe_proof(problem, proof).map_err(|e| e.to_string())
    }))
    .map_err(|payload| {
        payload
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_owned()))
            .unwrap_or_default()
    })
}

const DRUP_PROBLEM: &str = "(set-logic QF_UF)\n(declare-const a Bool)\n(declare-const c Bool)\n\
                            (assert (or a c))\n(assert (not a))\n(assert (not c))\n(check-sat)\n";
const DRUP_PROOF: &str = "(assume a0 (or a c))\n(assume a1 (not a))\n(assume a2 (not c))\n\
                          (step t0 (cl a c) :rule or :premises (a0))\n\
                          (step t1 (cl) :rule drup :premises (t0 a1 a2) :args ((cl)))\n";

#[test]
fn the_reported_crash_is_a_refusal() {
    assert_eq!(verdict(DRUP_PROBLEM, DRUP_PROOF), Ok(Ok(true)));
    let renamed = DRUP_PROOF.replace(":rule drup", ":rule pbblast_bvand");
    let error = verdict(DRUP_PROBLEM, &renamed)
        .expect("no panic")
        .expect_err("refused");
    // The adapter omits the checker's term details from the message.
    assert!(
        error.contains("step 't1' with rule 'pbblast_bvand'"),
        "{error}"
    );
}

/// Real certificate shapes: a pseudo-Boolean word equality (the certificate of
/// `pb_widths::tests::complete_word_equality_certificate_still_verifies`), an
/// anchor closed by `bind`, AY's bit-vector `poly_simp`, and the `drup`
/// refutation above. The vendored crate's own test covers the other rule
/// families; these are the shapes this adapter's guards look at.
fn bases() -> Vec<(String, String)> {
    let word = (
        "(set-logic QF_BV)\n(assert (not (= #b00 #b00)))\n(check-sat)\n".to_owned(),
        include_str!("pb_widths/truncated-equality.alethe")
            .replace("#b10", "#b00")
            .replace("(@pbbterm 0 1)", "(@pbbterm 0 0)")
            .replace("(- 0 0)", "(- (+ 0 (* 2 0)) (+ 0 (* 2 0)))"),
    );
    vec![
        word,
        (
            include_str!("soundness/ok_bind.smt2").to_owned(),
            include_str!("soundness/ok_bind.alethe").to_owned(),
        ),
        (
            include_str!("ay_corpus/poly_wrap_3eb448bf51b1.smt2").to_owned(),
            include_str!("ay_corpus/poly_wrap_3eb448bf51b1.alethe").to_owned(),
        ),
        (DRUP_PROBLEM.to_owned(), DRUP_PROOF.to_owned()),
    ]
}

/// Each step's text: from `(step ` to its closing parenthesis.
fn step_spans(proof: &str) -> Vec<(usize, usize)> {
    let mut spans = Vec::new();
    for (start, _) in proof.match_indices("(step ") {
        let mut depth = 0usize;
        for (offset, c) in proof[start..].char_indices() {
            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        spans.push((start, start + offset + 1));
                        break;
                    }
                }
                _ => {}
            }
        }
    }
    spans
}

/// `step` renamed to `rule`, with its `:args` replaced by `args` (dropped for
/// `None`); a step's `:args` is its last attribute in these certificates.
fn restep(step: &str, rule: &str, args: Option<&str>) -> String {
    let at = step.find(":rule ").expect("a step names its rule") + ":rule ".len();
    let name_end = at
        + step[at..]
            .find(|c: char| c.is_whitespace() || c == ')')
            .expect("the rule name ends");
    let tail = &step[name_end..step.len() - 1];
    let tail = tail.find(":args").map_or(tail, |k| &tail[..k]);
    let args = args.map(|a| format!(" :args ({a})")).unwrap_or_default();
    format!("{}{rule}{tail}{args})", &step[..at])
}

/// Every step of each base certificate renamed to every rule, with no `:args`,
/// with three integers and with the clause argument `(cl)`: refused or
/// accepted, never a panic.
#[test]
fn every_rule_on_every_step_is_judged_without_a_panic() {
    let rules = rule_names();
    assert!(
        rules.len() > 150,
        "read only {} rule names from get_rule",
        rules.len()
    );
    let shapes = [None, Some("0 1 2"), Some("(cl)")];
    let (mut runs, mut panics) = (0usize, Vec::new());
    for (problem, proof) in bases() {
        assert_eq!(
            verdict(&problem, &proof),
            Ok(Ok(true)),
            "base certificate does not verify:\n{proof}"
        );
        for (start, end) in step_spans(&proof) {
            for rule in &rules {
                for args in shapes {
                    let renamed = restep(&proof[start..end], rule, args);
                    let mutant = format!("{}{renamed}{}", &proof[..start], &proof[end..]);
                    runs += 1;
                    if let Err(message) = verdict(&problem, &mutant) {
                        panics.push(format!("{message}\n{mutant}"));
                    }
                }
            }
        }
    }
    assert!(
        panics.is_empty(),
        "{} of {runs} mutants panicked; the first:\n{}",
        panics.len(),
        panics[0]
    );
}
