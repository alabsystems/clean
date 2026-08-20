// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A3 — the GAP-2 encoding differential.**
//!
//! Link 2a, even when closed, says the module Clean proved about IS the module
//! the compiler emitted. It does not say that *running* that module under
//! Clean's `ir_eval` computes what running it under trust-ir computes. That
//! second half — GAP 2 — is what this gate measures.
//!
//! Read `clean_verify::ir_semdiff`'s module docs first: they record the one
//! finding everything else depends on, namely that trust-ir's semantics IS
//! written down (22,419 lines of Lean, plus a 12,493-line Rust reference
//! interpreter) but is joined to the shipped compiler only by a
//! **constructor-name** parity check. There is therefore no formal object
//! against which agreement could be PROVED, and this gate does not pretend
//! otherwise: it MEASURES, over a real input set, and prints every
//! disagreement.
//!
//! ## What a green here does and does not claim
//!
//! **Does:** on every input of a fully enumerated domain, Clean's kernel,
//! trust-ir's reference interpreter, and (where reachable) the shipped compiled
//! function return the same value, and Clean's measured fuel threshold stands in
//! one consistent relation to trust-ir's step count.
//!
//! **Does not:** that the two `IRInst` encodings denote the same function. The
//! bodies here exercise 6 of Clean's 28 `IRInst` constructors. The other 22 are
//! untouched by this measurement and are reported as such.

#[path = "crystal_a3_semdiff/chains.rs"]
mod chains;

#[path = "crystal_a3_semdiff/trust_exec.rs"]
mod trust_exec;

/// Falsification. A gate that cannot go red is not evidence.
#[path = "crystal_a3_semdiff/mutations.rs"]
mod mutations;

use std::collections::BTreeSet;
use std::path::PathBuf;

use clean_verify::ir_semdiff::{
    fuel_out_obligation, payload_is_unread, summarize, value_obligation, Agreement, ChainReport,
    DiffRow, EnumModel, RunResult, MAX_IR_NUMERAL,
};
use clean_verify::spec::Specification;
use clean_verify::test_utils::build_eval_ir_spec_with_stack;

use chains::{chains, Chain};

pub(crate) fn fixture(name: &str) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(name);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("committed fixture {} must be readable: {e}", path.display()))
}

/// Register a chain's module definitions into the spec.
///
/// These are the SAME constants `add_eval_ir_mode` / `add_eval_ir_kind_ord`
/// register, re-exported rather than re-typed, so the differential cannot drift
/// from the module the specification actually carries.
pub(crate) fn register_module(spec: &mut Specification, chain: &Chain) {
    for def in chain.clean_defs {
        spec.add_recursive_def(
            def,
            "crystal A3 differential: the chain's registered module",
        )
        .unwrap_or_else(|e| panic!("chain `{}` module def failed to register: {e}", chain.name));
    }
}

/// **E1 — ask the Clean KERNEL what this module does on this input.**
///
/// Two probes, both `Eq.refl` obligations the kernel discharges by reducing
/// `ir_eval`:
///
/// * the VALUE, tried against a small candidate set led by trust-ir's answer —
///   so a disagreement reports what Clean actually said instead of only that it
///   was not what trust-ir said;
/// * the exact fuel THRESHOLD, found from below, so the cost is pinned rather
///   than bounded.
///
/// Returns `(value, least accepted fuel)`.
fn clean_probe(
    spec: &mut Specification,
    chain: &Chain,
    tag: u32,
    trust_answer: Option<&RunResult>,
) -> (RunResult, Option<u32>) {
    // Candidate values: trust-ir's answer first, then every other value this
    // body could plausibly return. If none is accepted at any fuel, Clean is
    // saying something outside the candidate set and that is reported as such.
    let mut candidates: Vec<RunResult> = Vec::new();
    if let Some(a) = trust_answer {
        candidates.push(a.clone());
    }
    match chain.result_kind {
        clean_verify::ir_semdiff::ResultKind::Bool => {
            candidates.push(RunResult::Bool(true));
            candidates.push(RunResult::Bool(false));
        }
        clean_verify::ir_semdiff::ResultKind::Int => {
            for n in 0..=8u32 {
                candidates.push(RunResult::Int(n));
            }
        }
        clean_verify::ir_semdiff::ResultKind::EnumTag => {
            for n in 0..=8u32 {
                candidates.push(RunResult::EnumTag(n));
            }
        }
    }
    candidates.dedup();

    for fuel in 0..=MAX_IR_NUMERAL {
        for (idx, cand) in candidates.iter().enumerate() {
            let Ok(src) = value_obligation(
                &format!("a3_{}_t{tag}_f{fuel}_c{idx}", chain.name),
                chain.clean_module,
                chain.arg_shape,
                fuel,
                tag,
                cand,
            ) else {
                continue;
            };
            if spec
                .add_recursive_def(&src, "crystal A3: kernel-checked value probe")
                .is_ok()
            {
                return (cand.clone(), Some(fuel));
            }
        }
    }
    (
        RunResult::Fault("clean_no_candidate_matched".to_owned()),
        None,
    )
}

/// Confirm the machine is genuinely still RUNNING one step below the threshold.
///
/// Without this the "threshold" could be an artefact of the value probe rather
/// than a cost: `fuel_out` is a distinct, refutable outcome, so accepting it at
/// `k-1` is what turns "k fuel sufficed" into "k fuel was NEEDED".
fn clean_threshold_is_tight(
    spec: &mut Specification,
    chain: &Chain,
    tag: u32,
    threshold: u32,
) -> bool {
    if threshold == 0 {
        return true;
    }
    let Ok(src) = fuel_out_obligation(
        &format!("a3_{}_t{tag}_tight", chain.name),
        chain.clean_module,
        chain.arg_shape,
        threshold - 1,
        tag,
    ) else {
        return false;
    };
    spec.add_recursive_def(&src, "crystal A3: the threshold is tight from below")
        .is_ok()
}

/// Run one chain end to end and return its measured report.
fn measure(spec: &mut Specification, chain: &Chain) -> ChainReport {
    let text = fixture(chain.fixture);

    // A TagSurrogate enum declaration is sound only if the body never reads the
    // payload. Checked against the committed emitted text, mechanically.
    if chain.enum_model == EnumModel::TagSurrogate {
        payload_is_unread(chain.name, &text, chain.loaded_value).unwrap_or_else(|e| {
            panic!("chain `{}` may not elide its enum payload: {e}", chain.name)
        });
    }

    let (mut module, _subject_text) = trust_exec::build_module(
        &text,
        chain.original_name,
        chain.enum_decls,
        chain.ret_ty.clone(),
        chain.arg_shape,
        chain.arg_enum,
    )
    .unwrap_or_else(|e| panic!("chain `{}`: {e}", chain.name));
    let harness = trust_exec::attach_harness(&mut module, chain.arg_shape, chain.arg_enum)
        .unwrap_or_else(|e| panic!("chain `{}`: {e}", chain.name));

    register_module(spec, chain);

    let mut rows = Vec::new();
    for &tag in chain.domain {
        let (raw, tsteps) = trust_exec::run(&module, &harness, chain.arg_shape, tag);
        let tv = chain.result_kind.decode(&raw);
        // A fault is recorded, never dropped: a vanished leg would silently
        // become `Insufficient` and read as "not measured" instead of
        // "trust-ir refused where Clean answered".
        let trust_leg = Some((tv.clone(), tsteps));

        let (cv, cthreshold) = clean_probe(spec, chain, tag, Some(&tv));
        let mut notes = Vec::new();
        if let Some(t) = cthreshold {
            if !clean_threshold_is_tight(spec, chain, tag, t) {
                notes.push(format!(
                    "clean fuel {t} was accepted but fuel {} is not `fuel_out`: the threshold \
                     is an upper bound, not a pinned cost",
                    t.saturating_sub(1)
                ));
            }
        }
        if let Some(reason) = chain.shipped_absent {
            notes.push(format!("E3 absent: {reason}"));
        }

        rows.push(DiffRow {
            chain: chain.name.to_owned(),
            tag,
            trust: trust_leg,
            clean: Some((cv, cthreshold)),
            shipped: chain.shipped.and_then(|f| f(tag)),
            notes,
        });
    }

    summarize(chain.name, chain.enum_model, chain.total_domain, rows)
}

/// **The gate.** Every covered chain, every input of its domain, every executor.
#[test]
fn crystal_a3_semdiff_measures_encoding_agreement() {
    let mut spec = build_eval_ir_spec_with_stack();
    let mut reports = Vec::new();

    for chain in chains() {
        let report = measure(&mut spec, &chain);
        eprintln!("\n=== {} ===", report.chain);
        for row in &report.rows {
            eprintln!("{}", row.render());
            for note in &row.notes {
                eprintln!("      note: {note}");
            }
        }
        eprintln!("  {}", report.summary());
        reports.push(report);
    }

    eprintln!("\n--- GAP 2, measured ---");
    for r in &reports {
        eprintln!(
            "{:<20} {}  cost-uniform={}",
            r.chain,
            if r.is_green() {
                "AGREE"
            } else {
                "**DISAGREE**"
            },
            r.cost_is_uniform()
        );
    }
    eprintln!(
        "\nThis is a MEASUREMENT, not a proof. Clean's IRInst has 28 constructors; \n\
         the bodies above exercise {}. Agreement on a body's instruction mix says \n\
         nothing about the {} forms it never uses.",
        exercised_forms().len(),
        28 - exercised_forms().len()
    );

    let failed: Vec<&ChainReport> = reports.iter().filter(|r| !r.is_green()).collect();
    assert!(
        failed.is_empty(),
        "GAP-2 differential DISAGREEMENT on {} chain(s):\n{}",
        failed.len(),
        failed
            .iter()
            .map(|r| {
                let detail = r
                    .rows
                    .iter()
                    .filter_map(|row| match row.value_agreement() {
                        Agreement::Agree(_) => None,
                        other => Some(format!("    tag {}: {other:?}", row.tag)),
                    })
                    .collect::<Vec<_>>()
                    .join("\n");
                format!("  {}\n{detail}", r.summary())
            })
            .collect::<Vec<_>>()
            .join("\n")
    );
}

/// The `IRInst` forms the covered bodies actually exercise.
///
/// The denominator of the coverage claim, derived from the committed fixtures
/// rather than asserted, so it cannot drift from what is really being measured.
fn exercised_forms() -> BTreeSet<&'static str> {
    let mut forms = BTreeSet::new();
    for chain in chains() {
        let text = fixture(chain.fixture);
        for (needle, form) in [
            (" = load ", "load"),
            (" = extractfield ", "extractfield"),
            ("switch ", "switch"),
            ("br bb", "br"),
            (" = const ", "const_"),
            ("ret ", "ret"),
        ] {
            if text.contains(needle) {
                forms.insert(form);
            }
        }
    }
    forms
}

/// Coverage is stated over a REAL denominator and never rounded up.
#[test]
fn crystal_a3_coverage_is_reported_over_the_full_irinst_surface() {
    let forms = exercised_forms();
    assert!(
        forms.len() < 28,
        "if the covered bodies ever exercise all 28 IRInst forms, this gate's \
         honesty note must be rewritten rather than left claiming partial coverage"
    );
    eprintln!(
        "GAP-2 encoding coverage: {}/28 IRInst forms exercised: {:?}",
        forms.len(),
        forms
    );
}
