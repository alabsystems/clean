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
//! the chain's DECLARED relation to trust-ir's step count. Since 2026-08-20 the
//! cost half is part of the verdict rather than a printed aside: see
//! `clean_verify::ir_semdiff::cost`.
//!
//! **Does not:** that the two `IRInst` encodings denote the same function. The
//! three original chains exercise 6 of Clean's 30 `IRInst` constructors; the
//! W1 wide lane (`wide_chains.rs`, plan
//! `docs/analysis/evalir-completion-plan-2026-08-24.md` §5 W1) adds measured
//! rows over nine more (`icmp`, `binop`, `cast`, `condbr`, `call`, `store`,
//! `gep`, `insertfield`, `assert`) from already-committed emitted fixtures.
//! The remainder are untouched by this measurement and are reported as such,
//! and the MEASURED fraction is whatever the last minted
//! `data/crystal_gap2_semdiff_*.json` records — authored rows never count
//! until a gate run mints them (`scripts/evalir_coverage.py`'s rule).
//!
//! **Does not, second and newly measured:** pin ROUTING. A value differential is
//! blind to any permutation of target blocks that emit equal values, and
//! `from_source_system` — long described here as the sharpest chain — has 2,880
//! of them. `routing.rs` carries the structural comparison that does pin it, and
//! `crystal_a3_discriminating_power_is_measured` records the blindness per chain
//! from the committed fixtures.

#[path = "crystal_a3_semdiff/chains.rs"]
mod chains;

#[path = "crystal_a3_semdiff/trust_exec.rs"]
mod trust_exec;

/// Falsification. A gate that cannot go red is not evidence.
#[path = "crystal_a3_semdiff/mutations.rs"]
mod mutations;

/// Falsification for the COST half specifically, by perturbing the measured
/// quantity rather than a hardcoded probe.
#[path = "crystal_a3_semdiff/cost_mutations.rs"]
mod cost_mutations;

/// ROUTING, which no value differential on these bodies can see.
#[path = "crystal_a3_semdiff/routing.rs"]
mod routing;

/// The W1 wide lane: chain tables over the nine fixture-widened constructors.
#[path = "crystal_a3_semdiff/wide_chains.rs"]
mod wide_chains;

/// E2 for the wide lane — multi-fixture modules, direct arguments, and the
/// two per-input text harnesses.
#[path = "crystal_a3_semdiff/wide_exec.rs"]
mod wide_exec;

/// The W2a synthetic lane: authored micro-modules over the five constructors
/// no emitted body exercises (`select`, `undef`, `unreachable`,
/// `extractelement`, `unop`).
#[path = "crystal_a3_semdiff/synth_chains.rs"]
mod synth_chains;

/// The W2b synthetic lane: the memory tranche (`alloca`, `ptrdata`,
/// `ptrmetadata`, `ptrfromparts`), reusing the W2a table structs.
#[path = "crystal_a3_semdiff/w2b_chains.rs"]
mod w2b_chains;

/// The W2c synthetic lane: the call+module tranche (`callindirect`,
/// `globaladdr`) — the final synthetic tranche, reusing the W2a table structs.
#[path = "crystal_a3_semdiff/w2c_chains.rs"]
mod w2c_chains;

/// The W3 lane: the overflow value domain (`synth_overflow_u8` /
/// `synth_overflow_i8`) — the wave that replaced the dispatch arm's tagged
/// unmodelled outcome with real two-result semantics, reusing the W2a table
/// structs.
#[path = "crystal_a3_semdiff/w3_chains.rs"]
mod w3_chains;

/// The W4 lane: the float-comparison domain (`synth_fcmp`) — the wave that
/// replaced the LAST tagged dispatch arm with real semantics, completing the
/// battery's constructor coverage at 28 of the 30 census members exercised.
/// Reuses the W2a table
/// structs.
#[path = "crystal_a3_semdiff/w4_chains.rs"]
mod w4_chains;

/// The float-RESIDUE lane (`synth_fsign` / `synth_fround` / `synth_fminmax`)
/// — the wave that gave the seven answering residue OPERATORS real semantics
/// (the THIR lowerer's 28 were all exercised at W4; this lane adds operator
/// coverage inside `unop`/`binop`, so the coverage ladder is untouched by
/// design). Reuses the W2a table structs.
#[path = "crystal_a3_semdiff/wfr_chains.rs"]
mod wfr_chains;

/// The WAT lane: the two sequential atomic fetch-add constructors, measured
/// on the ONE Clean machine that executes them (ByteV1, `ir_byte_run_v1`) —
/// the legacy `ir_eval` the other lanes run refuses both.
#[path = "crystal_a3_semdiff/wat_chains.rs"]
mod wat_chains;

#[path = "crystal_a3_semdiff/trunc_transport.rs"]
mod trunc_transport;

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
    name_prefix: &str,
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
            for n in 0..=8u64 {
                candidates.push(RunResult::Int(n));
            }
        }
        clean_verify::ir_semdiff::ResultKind::EnumTag => {
            for n in 0..=8u64 {
                candidates.push(RunResult::EnumTag(n));
            }
        }
    }
    candidates.dedup();

    for fuel in 0..=MAX_IR_NUMERAL {
        for (idx, cand) in candidates.iter().enumerate() {
            let Ok(src) = value_obligation(
                &format!("{name_prefix}_{}_t{tag}_f{fuel}_c{idx}", chain.name),
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
    name_prefix: &str,
    threshold: u32,
) -> bool {
    if threshold == 0 {
        return true;
    }
    let Ok(src) = fuel_out_obligation(
        &format!("{name_prefix}_{}_t{tag}_tight", chain.name),
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
pub(crate) fn measure(spec: &mut Specification, chain: &Chain) -> ChainReport {
    measure_with(spec, chain, "a3", 0)
}

/// [`measure`], with the two knobs the cost-mutation battery needs.
///
/// `name_prefix` keeps two measurements in one `Specification` from colliding on
/// generated def names. `overhead_bias` perturbs the harness overhead subtracted
/// from trust-ir's step count — the quantity the cost gate compares — so a
/// mutation can falsify the COST verdict rather than a hardcoded probe.
pub(crate) fn measure_with(
    spec: &mut Specification,
    chain: &Chain,
    name_prefix: &str,
    overhead_bias: i64,
) -> ChainReport {
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
        let (raw, tsteps) = trust_exec::run(&module, &harness, chain.arg_shape, tag, overhead_bias);
        let tv = chain.result_kind.decode(&raw);
        // A fault is recorded, never dropped: a vanished leg would silently
        // become `Insufficient` and read as "not measured" instead of
        // "trust-ir refused where Clean answered".
        let trust_leg = Some((tv.clone(), tsteps));

        let (cv, cthreshold) = clean_probe(spec, chain, tag, name_prefix, Some(&tv));
        let mut notes = Vec::new();
        // Tightness is a GATED condition, not a note. A threshold that was
        // accepted but never shown NECESSARY is an upper bound, and an upper
        // bound compared against trust-ir's exact step count is not a cost
        // correspondence — it used to be recorded here as prose nothing read.
        let threshold_tight = match cthreshold {
            Some(t) => {
                let tight = clean_threshold_is_tight(spec, chain, tag, name_prefix, t);
                if !tight {
                    notes.push(format!(
                        "clean fuel {t} was accepted but fuel {} is not `fuel_out`: the threshold \
                         is an upper bound, not a pinned cost",
                        t.saturating_sub(1)
                    ));
                }
                tight
            }
            None => false,
        };
        if let Some(reason) = chain.shipped_absent {
            notes.push(format!("E3 absent: {reason}"));
        }

        rows.push(DiffRow {
            chain: chain.name.to_owned(),
            tag,
            trust: trust_leg,
            clean: Some((cv, cthreshold)),
            threshold_tight,
            shipped: chain.shipped.and_then(|f| f(tag)),
            notes,
        });
    }

    summarize(
        chain.name,
        chain.enum_model,
        chain.total_domain,
        chain.expected_cost_offset,
        rows,
    )
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
            "{:<20} {}  cost={:?} (pinned {:+})",
            r.chain,
            if r.is_green() { "AGREE" } else { "**RED**" },
            r.cost_verdict(),
            r.expected_cost_offset,
        );
    }
    eprintln!(
        "\nThis is a MEASUREMENT, not a proof. Clean's IRInst has {} constructors; \n\
         the bodies above exercise {}. Agreement on a body's instruction mix says \n\
         nothing about the {} forms it never uses.",
        irinst_census().len(),
        exercised_forms().len(),
        irinst_census().len() - exercised_forms().len()
    );

    // `is_green` consults BOTH halves. Stated separately here so a red says
    // which half failed instead of only that one did: before 2026-08-20 the
    // cost half could not fail at all.
    let cost_failed: Vec<&ChainReport> = reports.iter().filter(|r| !r.cost_is_pinned()).collect();
    assert!(
        cost_failed.is_empty(),
        "GAP-2 COST correspondence FAILED on {} chain(s). Cost is a gate, not a note:\n{}",
        cost_failed.len(),
        cost_failed
            .iter()
            .map(|r| format!(
                "  {}: verdict {:?}, pinned {:+}, offsets {:?}, loose thresholds {}",
                r.chain,
                r.cost_verdict(),
                r.expected_cost_offset,
                r.cost_offsets,
                r.loose_thresholds
            ))
            .collect::<Vec<_>>()
            .join("\n")
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

/// The `IRInst` census, DERIVED from the registered syntax rather than typed.
///
/// This ladder used to end in `== 28`, which is a stale pin the moment the
/// inductive gains a constructor — and in Phase B it gained two. Parsing the
/// `inductive IRInst : Type` telescope block is the same derivation
/// `scripts/evalir_coverage.py` and `scripts/evalir_adequacy_grid.py` perform,
/// so all three move together or the gates disagree out loud.
fn irinst_census() -> BTreeSet<String> {
    let src = include_str!("../src/spec/core_spec/eval_ir_syntax.rs");
    let lines: Vec<&str> = src.lines().collect();
    let at = lines
        .iter()
        .position(|l| l.contains("inductive IRInst : Type"))
        .expect("eval_ir_syntax.rs must declare `inductive IRInst : Type`");
    let mut out = BTreeSet::new();
    for line in &lines[at + 1..] {
        let t = line.trim();
        let Some(rest) = t.strip_prefix("| ") else {
            break;
        };
        let (name, _) = rest
            .split_once(" : ")
            .expect("every IRInst constructor line is `| name : telescope`");
        out.insert(name.to_string());
    }
    assert!(
        out.len() > 20,
        "the IRInst telescope parse collapsed ({} names) — schema drift",
        out.len()
    );
    out
}

/// The forms the Phase-B derived-bundle (lzd) chain exercises.
///
/// EMPTY today, and that is the claim: the two constructors Phase B added come
/// from the trust-ir bridge's callee sidecar, whose fixture is minted by the
/// chain step (B7), not by B2. Attributing them here before the fixture exists
/// would be exactly the rounding-up this file refuses everywhere else. When the
/// fixture lands, its needles go here and `OWED_BY_THE_LZD_CHAIN` below shrinks
/// in the same commit.
fn lzd_exercised_forms() -> BTreeSet<&'static str> {
    BTreeSet::new()
}

/// Modelled census members that still need their committed chain fixture.
const OWED_BY_THE_LZD_CHAIN: &[&str] = &["borrow", "copy"];

/// Declared syntax that all three evaluators deliberately refuse as unmodelled.
/// The typed refusal controls live in `eval_ir::release_tests`; they do not earn
/// an exercised semantic-differential form.
const UNMODELLED_SYNTAX_ONLY: &[&str] = &["release"];

/// Coverage is stated over a REAL denominator and never rounded up.
///
/// From W4 (2026-08-25) until Phase B the exercised fraction was pinned
/// COMPLETE at 28/28. Phase B added `borrow` and `copy` — modelled arms with
/// no committed battery fixture — so the honest statement is again a
/// FRACTION, and the two owed names are pinned by name rather than absorbed
/// into a smaller denominator. Both directions fail here: a fixture that stops
/// exercising a form (erosion) and a form that quietly leaves the owed list
/// without its fixture. EXERCISED is still not MEASURED: the measured fraction
/// is whatever the last minted artifact records.
///
/// The two sequential atomic fetch-add constructors appended on 2026-09-24
/// reached the census with neither a fixture nor an owed row, which turned
/// this test red; they are exercised by the WAT lane (`wat_chains.rs`), whose
/// E1 is the ByteV1 machine because the legacy one refuses them.
/// `release` remains in the same full census, but its syntax-only refusal is
/// separate from the modelled forms awaiting the lzd fixture.
#[test]
fn crystal_a3_coverage_is_reported_over_the_full_irinst_surface() {
    let narrow = exercised_forms();
    let wide: BTreeSet<&'static str> = narrow.union(&wide_exercised_forms()).copied().collect();
    let w2a: BTreeSet<&'static str> = wide.union(&synth_exercised_forms()).copied().collect();
    let w2b: BTreeSet<&'static str> = w2a.union(&w2b_exercised_forms()).copied().collect();
    let w2c: BTreeSet<&'static str> = w2b.union(&w2c_exercised_forms()).copied().collect();
    let w3: BTreeSet<&'static str> = w2c.union(&w3_exercised_forms()).copied().collect();
    let w4: BTreeSet<&'static str> = w3.union(&w4_exercised_forms()).copied().collect();
    let wat: BTreeSet<&'static str> = w4
        .union(&wat_chains::wat_exercised_forms())
        .copied()
        .collect();
    let combined: BTreeSet<&'static str> = wat.union(&lzd_exercised_forms()).copied().collect();

    let census = irinst_census();
    let n = census.len();
    let alien: Vec<&&str> = combined.iter().filter(|f| !census.contains(**f)).collect();
    assert!(
        alien.is_empty(),
        "a battery lane claims a form the IRInst census does not declare: {alien:?}"
    );
    let missing: BTreeSet<String> = census
        .iter()
        .filter(|c| !combined.contains(c.as_str()))
        .cloned()
        .collect();
    let expected_missing: BTreeSet<String> = OWED_BY_THE_LZD_CHAIN
        .iter()
        .chain(UNMODELLED_SYNTAX_ONLY)
        .map(|s| (*s).to_string())
        .collect();
    assert_eq!(
        missing,
        expected_missing,
        "the un-exercised IRInst forms must be EXACTLY the named fixture debt \
         ({OWED_BY_THE_LZD_CHAIN:?}) and syntax-only unmodelled forms \
         ({UNMODELLED_SYNTAX_ONLY:?}). A form that fell out is erosion — a committed fixture stopped \
         exercising it, and the ladder may only be rebuilt deliberately. A form that left \
         either list needs the committed fixture that earns exercised coverage; a \
         syntax-only form also needs its evaluator implementation. \
         Exercised {}/{n}: {combined:?}",
        combined.len(),
    );
    eprintln!(
        "GAP-2 encoding coverage: {}/{n} IRInst forms in the original chains {narrow:?}; \
         {}/{n} across original + W1 wide chains; {}/{n} adding the W2a synthetic chains; \
         {}/{n} adding the W2b synthetic chains; {}/{n} adding the W2c synthetic chains; \
         {}/{n} adding the W3 overflow chains; {}/{n} adding the W4 fcmp chain; {}/{n} \
         adding the WAT byte-profile atomic chains; {}/{n} adding the Phase-B \
         derived-bundle chain — the outstanding {} modelled forms \
         {OWED_BY_THE_LZD_CHAIN:?} are owed by the lzd chain (B7), while \
         {UNMODELLED_SYNTAX_ONLY:?} remain syntax-only and unmodelled. All are pinned by \
         name, never rounded away. The MEASURED fraction is \
         whatever the last minted data/crystal_gap2_semdiff_*.json records — this test \
         derives what the committed fixtures EXERCISE, which becomes measured only when a \
         gate run mints it, and a synthetic chain's rows measure E1/E2 agreement on \
         authored text, never a producer's body.",
        narrow.len(),
        wide.len(),
        w2a.len(),
        w2b.len(),
        w2c.len(),
        w3.len(),
        w4.len(),
        wat.len(),
        combined.len(),
        OWED_BY_THE_LZD_CHAIN.len(),
    );
}

// ═══════════════════════════ the W1 wide lane ═══════════════════════════

use std::collections::HashSet;

use clean_verify::ir_semdiff::wide::{wide_fuel_out_obligation, wide_value_obligation};
use wide_chains::{wide_chains, WideChain, WideInput, WideTrustInput};

/// Register a wide chain's module lines, once per SOURCE across the whole
/// gate run: `has_loose_bvars` and `loose_bvar_range` share the minted
/// two-function `ir_hlb_module`, and re-registering a definition is a
/// duplicate-declaration error, not a no-op.
fn register_wide_module(
    spec: &mut Specification,
    chain: &WideChain,
    registered: &mut HashSet<&'static str>,
) {
    for def in chain.clean_defs {
        if registered.insert(*def) {
            spec.add_recursive_def(def, "crystal A3 W1: the chain's registered module")
                .unwrap_or_else(|e| {
                    panic!(
                        "wide chain `{}` module def failed to register: {e}",
                        chain.name
                    )
                });
        }
    }
}

/// The interpreter's own "outside my bounded subset" family. Only these codes
/// downgrade an E2 answer to a recorded refusal, and only on a chain that
/// DECLARED the lane may refuse — every other fault stays a first-class
/// answer, because "trust-ir faulted where Clean returned" is a finding.
fn is_unsupported_code(code: &str) -> bool {
    code.starts_with("unsupported_")
}

/// E1 for a wide input: probe the original evaluator equality, fuel from
/// below, candidates led by the other executors' answers so a disagreement
/// reports what Clean actually said. Most witnesses are `Eq.refl`; the
/// full-width truncation witness transports through checked arithmetic laws
/// to avoid expanding the default repeated-subtraction model.
fn wide_clean_probe(
    spec: &mut Specification,
    chain: &WideChain,
    input: &WideInput,
    idx: usize,
    trust_answer: Option<&RunResult>,
) -> (RunResult, Option<u32>) {
    let mut candidates: Vec<RunResult> = Vec::new();
    if let Some(a) = trust_answer {
        candidates.push(a.clone());
    }
    if let Some(s) = &input.shipped {
        candidates.push(s.clone());
    }
    candidates.push(RunResult::Unit);
    candidates.push(RunResult::Bool(true));
    candidates.push(RunResult::Bool(false));
    for n in 0..=8u64 {
        candidates.push(RunResult::Int(n));
    }
    candidates.dedup();

    for fuel in 0..=MAX_IR_NUMERAL {
        for (c, cand) in candidates.iter().enumerate() {
            let name = format!("w1_{}_i{idx}_f{fuel}_c{c}", chain.name);
            let obligation = if chain.name == "get_char_val_trunc" && fuel == 2 {
                trunc_transport::value_obligation
            } else {
                wide_value_obligation
            };
            let Ok(src) = obligation(
                &name,
                chain.clean_module,
                chain.clean_fid,
                fuel,
                &input.clean_tail,
                cand,
                chain.encoding,
            ) else {
                continue;
            };
            if spec
                .add_recursive_def(&src, "crystal A3 W1: kernel-checked value probe")
                .is_ok()
            {
                if chain.name == "get_char_val_trunc" && fuel == 2 {
                    trunc_transport::verify_closed(spec, &name);
                }
                return (cand.clone(), Some(fuel));
            }
        }
    }
    (
        RunResult::Fault("clean_no_candidate_matched".to_owned()),
        None,
    )
}

/// The wide form of [`clean_threshold_is_tight`].
fn wide_threshold_is_tight(
    spec: &mut Specification,
    chain: &WideChain,
    input: &WideInput,
    idx: usize,
    threshold: u32,
) -> bool {
    if threshold == 0 {
        return true;
    }
    let Ok(src) = wide_fuel_out_obligation(
        &format!("w1_{}_i{idx}_tight", chain.name),
        chain.clean_module,
        chain.clean_fid,
        threshold - 1,
        &input.clean_tail,
    ) else {
        return false;
    };
    spec.add_recursive_def(&src, "crystal A3 W1: the threshold is tight from below")
        .is_ok()
}

/// E2 for one wide input, refusal-aware.
///
/// Returns the trust leg (`None` = a recorded refusal on a may-refuse chain)
/// plus any note. Panics on failures a chain did NOT declare it may have —
/// a broken instrument must be loud, not `Insufficient`.
fn wide_trust_leg(
    chain: &WideChain,
    input: &WideInput,
    fixture_texts: &[(String, &'static str)],
) -> (Option<(RunResult, Option<u32>)>, Vec<String>) {
    let mut notes = Vec::new();
    let (harness_text, overhead) = match &input.trust {
        WideTrustInput::Args(_) => (None, 0),
        WideTrustInput::Harness { text, overhead } => (Some(text.as_str()), *overhead),
    };
    let module = match wide_exec::build_wide_module(
        fixture_texts,
        chain.type_decls,
        chain.func_ids,
        &chain.sigs,
        harness_text,
    ) {
        Ok(m) => m,
        Err(e) => {
            let Some(reason) = chain.e2_may_refuse else {
                panic!("wide chain `{}`: E2 module build failed: {e}", chain.name);
            };
            notes.push(format!("E2 refused (module build): {e} — {reason}"));
            return (None, notes);
        }
    };
    let target = wide_exec::wide_target(&module, harness_text.is_some())
        .unwrap_or_else(|e| panic!("wide chain `{}`: {e}", chain.name));
    let args = match &input.trust {
        WideTrustInput::Args(a) => a.clone(),
        WideTrustInput::Harness { .. } => Vec::new(),
    };
    let (value, steps) = wide_exec::run_wide(&module, target, args, overhead);
    if let RunResult::Fault(code) = &value {
        if let Some(reason) = chain.e2_may_refuse {
            if is_unsupported_code(code) {
                notes.push(format!("E2 refused (interpreter): {code} — {reason}"));
                return (None, notes);
            }
        }
    }
    (Some((value, steps)), notes)
}

/// Run one wide chain end to end.
fn measure_wide(
    spec: &mut Specification,
    chain: &WideChain,
    registered: &mut HashSet<&'static str>,
) -> ChainReport {
    let fixture_texts: Vec<(String, &'static str)> = chain
        .fixtures
        .iter()
        .map(|(file, original)| (fixture(file), *original))
        .collect();

    register_wide_module(spec, chain, registered);
    if chain.name == "get_char_val_trunc" {
        trunc_transport::register(spec, chain);
    }

    let mut rows = Vec::new();
    for (idx, input) in chain.inputs.iter().enumerate() {
        let (trust_leg, mut notes) = wide_trust_leg(chain, input, &fixture_texts);
        notes.insert(0, format!("input: {}", input.label));

        let trust_value = trust_leg.as_ref().map(|(v, _)| v);
        let (cv, cthreshold) = wide_clean_probe(spec, chain, input, idx, trust_value);
        let threshold_tight = match cthreshold {
            Some(t) => {
                let tight = wide_threshold_is_tight(spec, chain, input, idx, t);
                if !tight {
                    notes.push(format!(
                        "clean fuel {t} was accepted but fuel {} is not `fuel_out`: the \
                         threshold is an upper bound, not a pinned cost",
                        t.saturating_sub(1)
                    ));
                }
                tight
            }
            None => false,
        };
        if let Some(reason) = chain.shipped_absent {
            notes.push(format!("E3 absent: {reason}"));
        }

        rows.push(DiffRow {
            chain: chain.name.to_owned(),
            tag: u32::try_from(idx).expect("input count fits u32"),
            trust: trust_leg,
            clean: Some((cv, cthreshold)),
            threshold_tight,
            shipped: input.shipped.clone(),
            notes,
        });
    }

    summarize(
        chain.name,
        chain.enum_model,
        chain.total_domain,
        chain.expected_cost_offset,
        rows,
    )
}

/// **The W1 gate, per chain.** Every assertion below is the block that used to
/// live at the end of `crystal_a3_semdiff_wide_measures_encoding_agreement`,
/// moved here BYTE FOR BYTE and handed a one-element `reports` so its two loops
/// are unchanged. Nothing is relaxed: the same four obligations bind — E1
/// answers on every row, zero value disagreements, and then either the full
/// narrow-gate standard (pinned cost + green) or, for a chain that DECLARED
/// `e2_may_refuse`, an exact accounting of every Insufficient row.
fn assert_wide_chain(chain: WideChain, r: ChainReport) {
    let reports = vec![(chain, r)];
    // E1 is our own kernel: it must ANSWER on every row, whatever the other
    // legs did. A no-candidate here is an instrument failure, never a shrug.
    for (_, r) in &reports {
        for row in &r.rows {
            let clean_answered = matches!(
                &row.clean,
                Some((v, _)) if !matches!(v, RunResult::Fault(_))
            );
            assert!(
                clean_answered,
                "W1 chain `{}` row {}: Clean's kernel probe found no accepted value \
                 ({:?}) — the E1 leg may never be silently absent",
                r.chain, row.tag, row.clean
            );
        }
    }

    // Verdicts. A chain whose E2 leg answered everywhere is held to the full
    // narrow-gate standard: value agreement AND the pinned cost offset. A
    // chain with recorded refusals must have DECLARED the possibility, and is
    // still held to zero disagreements on every row two executors reached —
    // refused rows stay printed as Insufficient, never folded into agreement
    // (the `Level::kind_ord` / GAP2 §"Insufficient" precedent).
    for (chain, r) in &reports {
        let refused = r.rows.iter().filter(|row| row.trust.is_none()).count();
        assert_eq!(
            r.disagreed,
            0,
            "W1 chain `{}` has {} value DISAGREEMENT(s):\n{}",
            r.chain,
            r.disagreed,
            r.rows
                .iter()
                .filter_map(|row| match row.value_agreement() {
                    Agreement::Agree(_) | Agreement::Insufficient => None,
                    other => Some(format!("    input {}: {other:?}", row.tag)),
                })
                .collect::<Vec<_>>()
                .join("\n")
        );
        if refused == 0 {
            assert!(
                r.cost_is_pinned(),
                "W1 chain `{}` COST failed: verdict {:?}, pinned {:+}, offsets {:?}, \
                 loose thresholds {}",
                r.chain,
                r.cost_verdict(),
                r.expected_cost_offset,
                r.cost_offsets,
                r.loose_thresholds
            );
            assert!(
                r.is_green(),
                "W1 chain `{}` is not green: {}",
                r.chain,
                r.summary()
            );
        } else {
            assert!(
                chain.e2_may_refuse.is_some(),
                "W1 chain `{}` recorded {refused} E2 refusal(s) without declaring the \
                 lane may refuse — an undeclared refusal is an instrument failure",
                r.chain
            );
            assert_eq!(
                r.insufficient,
                r.rows
                    .iter()
                    .filter(|row| row.trust.is_none() && row.shipped.is_none())
                    .count(),
                "W1 chain `{}`: every Insufficient row must be exactly a recorded \
                 E2 refusal with no shipped leg — nothing else may be silent",
                r.chain
            );
        }
    }
}

/// One `#[test]` per wide chain.
///
/// WHY: as ONE test over all ten chains this never finished — the suite rows
/// record `timed out after 28800s` and `after 7200s`, exit -1, and CLAUDE.md
/// names sharding it as open work. A target that times out reports NOTHING, so
/// the repo's only two-machine semantic-agreement evidence was being thrown
/// away wholesale. Ten rows can each pass, fail, or time out on their own.
///
/// The spec build is shared: `build_eval_ir_spec_with_stack` is OnceLock-cached
/// per process, so ten tests in one binary pay for it once.
macro_rules! wide_chain_tests {
    ($($name:ident => $chain:literal,)*) => {
        $(
            #[test]
            fn $name() {
                let mut spec = if $chain == "get_char_val_trunc" {
                    trunc_transport::new_spec()
                } else {
                    build_eval_ir_spec_with_stack()
                };
                let mut registered: HashSet<&'static str> = HashSet::new();
                let chain = wide_chains()
                    .into_iter()
                    .find(|c| c.name == $chain)
                    .unwrap_or_else(|| panic!("wide chain `{}` is no longer in wide_chains()", $chain));
                let report = measure_wide(&mut spec, &chain, &mut registered);
                eprintln!("\n=== W1 {} ===", report.chain);
                for row in &report.rows {
                    eprintln!("{}", row.render());
                    for note in &row.notes {
                        eprintln!("      note: {note}");
                    }
                }
                eprintln!("  {}", report.summary());
                assert_wide_chain(chain, report);
            }
        )*
    };
}

wide_chain_tests! {
    crystal_a3_semdiff_w1chain_bvar_in_range => "bvar_in_range",
    crystal_a3_semdiff_w1chain_is_valid_char => "is_valid_char",
    crystal_a3_semdiff_w1chain_flat_flags_contains => "flat_flags_contains",
    crystal_a3_semdiff_w1chain_flat_flags_with => "flat_flags_with",
    crystal_a3_semdiff_w1chain_node_id_index => "node_id_index",
    crystal_a3_semdiff_w1chain_get_char_val_trunc => "get_char_val_trunc",
    crystal_a3_semdiff_w1chain_has_loose_bvars => "has_loose_bvars",
    crystal_a3_semdiff_w1chain_loose_bvar_range => "loose_bvar_range",
    crystal_a3_semdiff_w1chain_strict_monads => "strict_monads",
    crystal_a3_semdiff_w1chain_simp_priority_value => "simp_priority_value",
}

/// Every chain named in the shard table above must still exist, and every chain
/// in `wide_chains()` must have a shard. Without this a chain could be added to
/// the table and silently never measured -- the coverage hole sharding is most
/// likely to introduce.
#[test]
fn crystal_a3_semdiff_w1_shards_cover_every_wide_chain() {
    let declared: BTreeSet<&'static str> = [
        "bvar_in_range",
        "is_valid_char",
        "flat_flags_contains",
        "flat_flags_with",
        "node_id_index",
        "get_char_val_trunc",
        "has_loose_bvars",
        "loose_bvar_range",
        "strict_monads",
        "simp_priority_value",
    ]
    .into_iter()
    .collect();
    let actual: BTreeSet<&'static str> = wide_chains().into_iter().map(|c| c.name).collect();
    assert_eq!(
        declared, actual,
        "the per-chain shard table and wide_chains() have diverged — a chain \
         present in one and absent from the other is never measured"
    );
}

/// The GAP 2 coverage MEASUREMENT, split out of the old monolithic test. It
/// reads fixture text only, so it costs nothing and does not need the shards.
#[test]
fn crystal_a3_semdiff_w1_reports_irinst_coverage() {
    let combined: BTreeSet<&'static str> = exercised_forms()
        .union(&wide_exercised_forms())
        .copied()
        .collect();
    eprintln!(
        "\nThis is a MEASUREMENT, not a proof. Original + W1 chains exercise {}/{} \n\
         IRInst forms; the other {} are untouched by this battery. The committed \n\
         MEASURED fraction stays whatever the last minted \n\
         data/crystal_gap2_semdiff_*.json records.",
        combined.len(),
        irinst_census().len(),
        irinst_census().len() - combined.len()
    );
    assert!(
        !combined.is_empty(),
        "the battery must exercise at least one IRInst form"
    );
}

/// The `IRInst` forms the WIDE chains' committed fixtures exercise, derived
/// from the fixture text like [`exercised_forms`] — the same never-rounded-up
/// posture, over the widened needle set.
fn wide_exercised_forms() -> BTreeSet<&'static str> {
    let mut forms = BTreeSet::new();
    for chain in wide_chains() {
        for (file, _) in chain.fixtures {
            let text = fixture(file);
            for (needle, form) in [
                (" = load ", "load"),
                (" = extractfield ", "extractfield"),
                ("switch ", "switch"),
                ("br bb", "br"),
                (" = const ", "const_"),
                ("ret ", "ret"),
                (" = icmp ", "icmp"),
                (" = and ", "binop"),
                (" = or ", "binop"),
                (" = shl ", "binop"),
                (" = lshr ", "binop"),
                (" = trunc ", "cast"),
                (" = zext ", "cast"),
                (" = sext ", "cast"),
                (" = bitcast ", "cast"),
                ("condbr ", "condbr"),
                (" = call @", "call"),
                ("store ", "store"),
                (" = gep ", "gep"),
                (" = insertfield ", "insertfield"),
                ("assert %", "assert"),
            ] {
                if text.contains(needle) {
                    forms.insert(form);
                }
            }
        }
    }
    forms
}

/// The E2 INSTRUMENT smoke for the wide lane — **no `Specification`, no
/// kernel**: it exercises only trust-ir's parser + interpreter over the
/// composed modules, so it is runnable on the 8 GB authoring box where spec
/// registration is not (the plan's §5/§6 split). What it pins:
///
/// * every chain that did NOT declare `e2_may_refuse` gets a non-fault answer
///   on every input (parse, signature reconstitution, callee-id fixup, direct
///   argument construction, and the per-input harnesses all actually work);
/// * wherever E2 and E3 both answered, they agree — the only value assertion
///   this smoke can make without hand-writing expectations;
/// * values and step counts are PRINTED per row, so the declared cost offsets
///   have a measured E2 half before the first kernel run.
///
/// It is NOT the differential: E1 — the kernel — is absent here, so nothing in
/// this test claims encoding agreement.
#[test]
fn crystal_a3_wide_e2_instrument_smoke() {
    for chain in wide_chains() {
        let fixture_texts: Vec<(String, &'static str)> = chain
            .fixtures
            .iter()
            .map(|(file, original)| (fixture(file), *original))
            .collect();
        eprintln!("\n=== W1 E2 smoke: {} ===", chain.name);
        for input in &chain.inputs {
            let (leg, notes) = wide_trust_leg(&chain, input, &fixture_texts);
            match &leg {
                Some((value, steps)) => {
                    eprintln!("  {:<32} -> {value} @{steps:?} steps", input.label);
                    assert!(
                        chain.e2_may_refuse.is_some() || !matches!(value, RunResult::Fault(_)),
                        "chain `{}` input `{}`: E2 faulted ({value}) on a lane that did \
                         not declare it may refuse",
                        chain.name,
                        input.label
                    );
                    if let Some(shipped) = &input.shipped {
                        if !matches!(value, RunResult::Fault(_)) {
                            assert_eq!(
                                value, shipped,
                                "chain `{}` input `{}`: E2 and the SHIPPED function \
                                 disagree",
                                chain.name, input.label
                            );
                        }
                    }
                }
                None => {
                    eprintln!("  {:<32} -> E2 refused", input.label);
                    for n in &notes {
                        eprintln!("      note: {n}");
                    }
                    assert!(
                        chain.e2_may_refuse.is_some(),
                        "chain `{}` input `{}`: an undeclared E2 refusal",
                        chain.name,
                        input.label
                    );
                }
            }
        }
    }
}

/// The W1 wide lane covers exactly the nine constructors the plan names —
/// pinned so the chain table cannot silently narrow (a dropped fixture would
/// shrink this set) and cannot silently claim more than the fixtures carry.
#[test]
fn crystal_a3_wide_lane_exercises_the_nine_w1_constructors() {
    let wide = wide_exercised_forms();
    for expected in [
        "icmp",
        "binop",
        "cast",
        "condbr",
        "call",
        "store",
        "gep",
        "insertfield",
        "assert",
    ] {
        assert!(
            wide.contains(expected),
            "the W1 chain fixtures no longer exercise `{expected}`; the wide lane's \
             +9 claim would be false. Exercised: {wide:?}"
        );
    }
}

// ═══════ the synthetic lanes (W2a; W2b and W2c via the same machinery) ═════
//
// Constructors no emitted body exercises, measured over AUTHORED
// micro-modules (`tests/fixtures/synth/`, Clean twins in
// `eval_ir_w2a_synth.rs` / `eval_ir_w2b_synth.rs` / `eval_ir_w2c_synth.rs`).
// Read `synth_chains.rs`'s module doc first: it records W2a's two DECLARED
// executor deltas (`undef` has no measurable E2 leg; `extractelement`
// out-of-bounds diverges by fault class), both measured at the pinned
// trust-ir rev, both asserted exactly rather than smoothed. `w2b_chains.rs`'s
// doc records the memory tranche's measured uninitialized-read fault-SITE
// split; `w2c_chains.rs`'s doc records the null-function-pointer fault-CODE
// split. All three lanes run through `measure_synth_lane` /
// `synth_e2_smoke_lane` below.

use clean_verify::ir_semdiff::synth::{
    e2_fault_class, synth_outcome_obligation, OutcomeClass, SynthOutcome,
};
use synth_chains::{synth_chains, SynthChain, SynthExpect, SynthInput};

/// The `IRInst` forms the SYNTHETIC fixtures exercise, derived from the
/// committed fixture text like [`exercised_forms`] — same never-rounded-up
/// posture. The bare `unreachable` terminator is matched per code line rather
/// than by substring, because the fixture's own function name contains the
/// word.
fn synth_exercised_forms() -> BTreeSet<&'static str> {
    let mut forms = BTreeSet::new();
    for chain in synth_chains() {
        for (file, _) in chain.fixtures {
            let text = fixture(file);
            for (needle, form) in [
                ("ret ", "ret"),
                (" = const ", "const_"),
                ("condbr ", "condbr"),
                (" = select ", "select"),
                (" = undef ", "undef"),
                (" = extractelement ", "extractelement"),
                (" = not ", "unop"),
                (" = ctpop ", "unop"),
            ] {
                if text.contains(needle) {
                    forms.insert(form);
                }
            }
            for line in text.lines() {
                if line.split(';').next().unwrap_or("").trim() == "unreachable" {
                    forms.insert("unreachable");
                }
            }
        }
    }
    forms
}

/// E2 for one synthetic input: compose (once per call — the modules are
/// three-instruction bodies), parse, execute with direct arguments. No
/// harness exists in this lane, so nothing is subtracted from the step count.
fn synth_trust_leg(
    chain: &SynthChain,
    input: &SynthInput,
    fixture_texts: &[(String, &'static str)],
) -> (RunResult, Option<u32>) {
    let module = wide_exec::build_wide_module(
        fixture_texts,
        chain.type_decls,
        chain.func_ids,
        &chain.sigs,
        None,
    )
    .unwrap_or_else(|e| panic!("synth chain `{}`: E2 module build failed: {e}", chain.name));
    let target = wide_exec::wide_target(&module, false)
        .unwrap_or_else(|e| panic!("synth chain `{}`: {e}", chain.name));
    wide_exec::run_wide(&module, target, input.trust_args.clone(), 0)
}

/// E1 value probe for a `Ret` row: candidates led by E2's live answer, then
/// the row's declared expectation, then the shared pool — the kernel
/// adjudicates by reducing `ir_eval`, so the ordering only decides which
/// question is asked first.
fn synth_clean_probe(
    spec: &mut Specification,
    chain: &SynthChain,
    input: &SynthInput,
    idx: usize,
    trust_answer: Option<&RunResult>,
    declared: &RunResult,
) -> (RunResult, Option<u32>) {
    let mut candidates: Vec<RunResult> = Vec::new();
    if let Some(a) = trust_answer {
        candidates.push(a.clone());
    }
    candidates.push(declared.clone());
    candidates.push(RunResult::Unit);
    candidates.push(RunResult::Bool(true));
    candidates.push(RunResult::Bool(false));
    for n in 0..=8u64 {
        candidates.push(RunResult::Int(n));
    }
    candidates.dedup();

    for fuel in 0..=MAX_IR_NUMERAL {
        for (c, cand) in candidates.iter().enumerate() {
            let Ok(src) = wide_value_obligation(
                &format!("sx_{}_i{idx}_f{fuel}_c{c}", chain.name),
                chain.clean_module,
                chain.clean_fid,
                fuel,
                &input.clean_tail,
                cand,
                chain.encoding,
            ) else {
                continue;
            };
            if spec
                .add_recursive_def(&src, "crystal A3 synth lane: kernel-checked value probe")
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

/// E1 outcome probe for a non-`Ret` row: the FULL `IROutcome` term is pinned
/// (fault constructor included), fuel from below. Returns the least accepted
/// fuel, or `None` when the kernel refuted the declared outcome at every
/// probed fuel — which the gate treats as a loud failure, never a shrug.
fn synth_outcome_probe(
    spec: &mut Specification,
    chain: &SynthChain,
    input: &SynthInput,
    idx: usize,
    outcome: &SynthOutcome,
) -> Option<u32> {
    for fuel in 0..=MAX_IR_NUMERAL {
        let Ok(src) = synth_outcome_obligation(
            &format!("sx_{}_i{idx}_f{fuel}_o", chain.name),
            chain.clean_module,
            chain.clean_fid,
            fuel,
            &input.clean_tail,
            outcome,
            chain.encoding,
        ) else {
            continue;
        };
        if spec
            .add_recursive_def(&src, "crystal A3 synth lane: kernel-checked outcome probe")
            .is_ok()
        {
            return Some(fuel);
        }
    }
    None
}

/// The wide tightness check, reused verbatim for synthetic rows: `fuel_out`
/// kernel-accepted one below the threshold.
fn synth_threshold_is_tight(
    spec: &mut Specification,
    chain: &SynthChain,
    input: &SynthInput,
    idx: usize,
    threshold: u32,
) -> bool {
    if threshold == 0 {
        return true;
    }
    let Ok(src) = wide_fuel_out_obligation(
        &format!("sx_{}_i{idx}_tight", chain.name),
        chain.clean_module,
        chain.clean_fid,
        threshold - 1,
        &input.clean_tail,
    ) else {
        return false;
    };
    spec.add_recursive_def(
        &src,
        "crystal A3 synth lane: the threshold is tight from below",
    )
    .is_ok()
}

/// Register a synthetic chain's module lines, once per SOURCE across the gate
/// run (the same discipline as [`register_wide_module`]).
fn register_synth_module(
    spec: &mut Specification,
    chain: &SynthChain,
    registered: &mut HashSet<&'static str>,
) {
    for def in chain.clean_defs {
        if registered.insert(*def) {
            spec.add_recursive_def(def, "crystal A3 synth lane: the chain's registered module")
                .unwrap_or_else(|e| {
                    panic!(
                        "synth chain `{}` module def failed to register: {e}",
                        chain.name
                    )
                });
        }
    }
}

/// The shared synthetic-lane measurement (W2a and W2b run it over their own
/// chain tables). Every chain, every input, both executors that exist for a
/// synthetic lane — `Ret` rows held to exact value agreement and the pinned
/// zero cost offset, `UbAgree` rows to outcome-class agreement with both
/// exact terms pinned, and every declared delta to EXACTLY its declaration.
/// E3 does not exist here and no row pretends otherwise.
fn measure_synth_lane(lane: &str, lane_chains: Vec<SynthChain>) {
    let mut spec = build_eval_ir_spec_with_stack();
    let mut registered: HashSet<&'static str> = HashSet::new();

    for chain in lane_chains {
        let fixture_texts: Vec<(String, &'static str)> = chain
            .fixtures
            .iter()
            .map(|(file, original)| (fixture(file), *original))
            .collect();
        register_synth_module(&mut spec, &chain, &mut registered);

        let mut rows: Vec<DiffRow> = Vec::new();
        let mut declared_deltas = 0usize;
        for (idx, input) in chain.inputs.iter().enumerate() {
            let (e2_value, e2_steps) = synth_trust_leg(&chain, input, &fixture_texts);
            let mut notes = vec![format!("input: {}", input.label)];
            let (trust_leg, clean_leg, tight) = match &input.expect {
                SynthExpect::Ret(declared) => {
                    let (cv, threshold) = synth_clean_probe(
                        &mut spec,
                        &chain,
                        input,
                        idx,
                        (!matches!(e2_value, RunResult::Fault(_))).then_some(&e2_value),
                        declared,
                    );
                    assert!(
                        !matches!(cv, RunResult::Fault(_)),
                        "{lane} chain `{}` input `{}`: Clean's kernel probe found no accepted \
                         value — the E1 leg may never be silently absent",
                        chain.name,
                        input.label
                    );
                    let tight = threshold.is_some_and(|t| {
                        synth_threshold_is_tight(&mut spec, &chain, input, idx, t)
                    });
                    (
                        Some((e2_value.clone(), e2_steps)),
                        Some((cv, threshold)),
                        tight,
                    )
                }
                SynthExpect::UbAgree(fault) => {
                    let RunResult::Fault(code) = &e2_value else {
                        panic!(
                            "{lane} chain `{}` input `{}`: E2 returned {e2_value} where \
                             undefined behavior was expected",
                            chain.name, input.label
                        );
                    };
                    assert_eq!(
                        e2_fault_class(code),
                        Some(OutcomeClass::Ub),
                        "{lane} chain `{}` input `{}`: E2 code `{code}` is not the UB class",
                        chain.name,
                        input.label
                    );
                    let outcome = SynthOutcome::Ub(*fault);
                    let threshold = synth_outcome_probe(&mut spec, &chain, input, idx, &outcome);
                    assert!(
                        threshold.is_some(),
                        "{lane} chain `{}` input `{}`: the kernel refuted the declared outcome \
                         `{outcome:?}` at every probed fuel",
                        chain.name,
                        input.label
                    );
                    let tight = threshold.is_some_and(|t| {
                        synth_threshold_is_tight(&mut spec, &chain, input, idx, t)
                    });
                    notes.push(format!(
                        "outcome-class agreement: clean pins {outcome:?}, e2 reported `{code}`"
                    ));
                    // Both legs recorded at the shared CLASS tag so the row
                    // compares; the exact terms live in the note above and in
                    // the kernel obligation itself.
                    (
                        Some((RunResult::Fault(OutcomeClass::Ub.tag().to_owned()), None)),
                        Some((
                            RunResult::Fault(OutcomeClass::Ub.tag().to_owned()),
                            threshold,
                        )),
                        tight,
                    )
                }
                SynthExpect::DeclaredDelta {
                    clean,
                    e2_code,
                    why,
                } => {
                    declared_deltas += 1;
                    let RunResult::Fault(code) = &e2_value else {
                        panic!(
                            "{lane} chain `{}` input `{}`: E2 returned {e2_value} where the \
                             declared delta expected fault `{e2_code}`. The divergence this \
                             row declares may have closed — re-measure before editing it.",
                            chain.name, input.label
                        );
                    };
                    assert_eq!(
                        code, e2_code,
                        "{lane} chain `{}` input `{}`: E2 faulted with a DIFFERENT code than \
                         the declared delta",
                        chain.name, input.label
                    );
                    let threshold = synth_outcome_probe(&mut spec, &chain, input, idx, clean);
                    assert!(
                        threshold.is_some(),
                        "{lane} chain `{}` input `{}`: the kernel refuted the declared outcome \
                         `{clean:?}` at every probed fuel",
                        chain.name,
                        input.label
                    );
                    let tight = threshold.is_some_and(|t| {
                        synth_threshold_is_tight(&mut spec, &chain, input, idx, t)
                    });
                    notes.push(format!("DECLARED DELTA: {why}"));
                    // Legs recorded verbatim and deliberately unequal, so the
                    // row renders as the disagreement it is.
                    (
                        Some((RunResult::Fault((*e2_code).to_owned()), None)),
                        Some((
                            RunResult::Fault(format!("clean:{:?}", clean.class())),
                            threshold,
                        )),
                        tight,
                    )
                }
            };
            notes.push(format!("E3 absent: {}", chain.shipped_absent));
            rows.push(DiffRow {
                chain: chain.name.to_owned(),
                tag: u32::try_from(idx).expect("input count fits u32"),
                trust: trust_leg,
                clean: clean_leg,
                threshold_tight: tight,
                shipped: None,
                notes,
            });
        }

        let report = summarize(
            chain.name,
            chain.enum_model,
            chain.total_domain,
            chain.expected_cost_offset,
            rows,
        );
        eprintln!("\n=== {lane} {} ===", report.chain);
        for row in &report.rows {
            eprintln!("{}", row.render());
            for note in &row.notes {
                eprintln!("      note: {note}");
            }
        }
        eprintln!("  {}", report.summary());

        // Verdicts. Disagreements must be EXACTLY the declared deltas; every
        // threshold must be pinned from below; and every priced row must sit
        // at the declared offset.
        assert_eq!(
            report.disagreed, declared_deltas,
            "{lane} chain `{}`: {} disagreement(s) against {} declared delta(s) — an \
             undeclared divergence (or a declared one that vanished)",
            report.chain, report.disagreed, declared_deltas
        );
        assert_eq!(
            report.loose_thresholds, 0,
            "{lane} chain `{}`: {} loose threshold(s) — an upper bound is not a cost",
            report.chain, report.loose_thresholds
        );
        for row in &report.rows {
            // The clean-minus-trust offset, recomputed from the row's own legs
            // (`DiffRow::cost_offset` is crate-private); a fault leg carries no
            // step count, so fault rows are unpriced by shape and skip this.
            let priced = match (&row.trust, &row.clean) {
                (Some((_, Some(steps))), Some((_, Some(threshold)))) => {
                    Some(i64::from(*threshold) - i64::from(*steps))
                }
                _ => None,
            };
            if let Some(offset) = priced {
                assert_eq!(
                    offset, chain.expected_cost_offset,
                    "{lane} chain `{}` input {}: cost offset {offset:+} vs pinned {:+}",
                    report.chain, row.tag, chain.expected_cost_offset
                );
            }
        }
    }
}

/// **The W2a gate.** The five constructors no emitted body exercises, run
/// through [`measure_synth_lane`]'s contract (exact `Ret` agreement + pinned
/// zero cost offset, class-compared `UbAgree`, the two declared deltas
/// asserted exactly).
#[test]
fn crystal_a3_semdiff_synth_measures_encoding_agreement() {
    measure_synth_lane("W2a", synth_chains());

    let combined: BTreeSet<&'static str> = exercised_forms()
        .union(&wide_exercised_forms())
        .copied()
        .collect::<BTreeSet<_>>()
        .union(&synth_exercised_forms())
        .copied()
        .collect();
    eprintln!(
        "\nThis is a MEASUREMENT, not a proof. Original + W1 + W2a chains exercise \
         {}/{} IRInst forms; the other {} are untouched by this battery. A synthetic \
         row measures E1/E2 agreement on authored text — never a producer's body — \
         and the committed MEASURED fraction stays whatever the last minted \
         data/crystal_gap2_semdiff_*.json records.",
        combined.len(),
        irinst_census().len(),
        irinst_census().len() - combined.len()
    );
}

/// **The W2b gate.** The memory tranche — `alloca`, `ptrdata`, `ptrmetadata`,
/// `ptrfromparts` — through the same [`measure_synth_lane`] contract. One
/// non-`Ret` row (`alloca`'s uninitialized read) compares at outcome class;
/// `w2b_chains.rs`'s module doc records the measured fault-SITE split it sits
/// on.
#[test]
fn crystal_a3_semdiff_w2b_measures_encoding_agreement() {
    measure_synth_lane("W2b", w2b_chains::w2b_chains());

    let combined: BTreeSet<&'static str> = exercised_forms()
        .union(&wide_exercised_forms())
        .copied()
        .collect::<BTreeSet<_>>()
        .union(&synth_exercised_forms())
        .copied()
        .collect::<BTreeSet<_>>()
        .union(&w2b_exercised_forms())
        .copied()
        .collect();
    eprintln!(
        "\nThis is a MEASUREMENT, not a proof. Original + W1 + W2a + W2b chains \
         exercise {}/{} IRInst forms; the other {} are untouched by this battery. A \
         synthetic row measures E1/E2 agreement on authored text — never a producer's \
         body — and the committed MEASURED fraction stays whatever the last minted \
         data/crystal_gap2_semdiff_*.json records.",
        combined.len(),
        irinst_census().len(),
        irinst_census().len() - combined.len()
    );
}

/// **The synthetic-lane E2 instrument smoke** — no `Specification`, no
/// kernel: trust-ir's parser + interpreter over the composed synthetic
/// modules, runnable on the 8 GB authoring box (the plan's §5/§6 split).
/// What it pins:
///
/// * every `Ret` row gets E2's exact answer — asserted against the AUTHORED
///   expectation, which for a synthetic module is the honest comparison this
///   smoke can make (there is no shipped function to cross-check);
/// * every `UbAgree` row faults with the UB class;
/// * every DECLARED delta reproduces EXACTLY — a vanished delta (an
///   interpreter that starts executing `undef`, or reclassifies the OOB read)
///   fails loudly instead of silently widening agreement;
/// * values and step counts are PRINTED per row, so the declared zero cost
///   offsets have a measured E2 half before the first kernel run.
///
/// It is NOT the differential: E1 is absent here, so nothing in this test
/// claims encoding agreement. Shared by the W2a and W2b smoke tests.
fn synth_e2_smoke_lane(lane: &str, lane_chains: Vec<SynthChain>) {
    for chain in lane_chains {
        let fixture_texts: Vec<(String, &'static str)> = chain
            .fixtures
            .iter()
            .map(|(file, original)| (fixture(file), *original))
            .collect();
        eprintln!("\n=== {lane} E2 smoke: {} ===", chain.name);
        for input in &chain.inputs {
            let (value, steps) = synth_trust_leg(&chain, input, &fixture_texts);
            eprintln!("  {:<34} -> {value} @{steps:?} steps", input.label);
            match &input.expect {
                SynthExpect::Ret(declared) => {
                    assert_eq!(
                        &value, declared,
                        "chain `{}` input `{}`: E2 disagrees with the authored expectation",
                        chain.name, input.label
                    );
                }
                SynthExpect::UbAgree(_) => {
                    let RunResult::Fault(code) = &value else {
                        panic!(
                            "chain `{}` input `{}`: E2 returned {value} where undefined \
                             behavior was expected",
                            chain.name, input.label
                        );
                    };
                    assert_eq!(
                        e2_fault_class(code),
                        Some(OutcomeClass::Ub),
                        "chain `{}` input `{}`: E2 code `{code}` is not the UB class",
                        chain.name,
                        input.label
                    );
                }
                SynthExpect::DeclaredDelta { e2_code, why, .. } => {
                    let RunResult::Fault(code) = &value else {
                        panic!(
                            "chain `{}` input `{}`: E2 returned {value} where the declared \
                             delta expected fault `{e2_code}` — the divergence may have \
                             closed; re-measure before editing the declaration",
                            chain.name, input.label
                        );
                    };
                    assert_eq!(
                        code, e2_code,
                        "chain `{}` input `{}`: E2 faulted with a different code than the \
                         declared delta",
                        chain.name, input.label
                    );
                    eprintln!("      declared delta: {why}");
                }
            }
        }
    }
}

/// The W2a smoke: [`synth_e2_smoke_lane`] over the W2a chain table.
#[test]
fn crystal_a3_synth_e2_instrument_smoke() {
    synth_e2_smoke_lane("W2a", synth_chains());
}

/// The W2b smoke: [`synth_e2_smoke_lane`] over the memory-tranche table.
#[test]
fn crystal_a3_w2b_e2_instrument_smoke() {
    synth_e2_smoke_lane("W2b", w2b_chains::w2b_chains());
}

/// The W2a synthetic lane covers exactly the five constructors the plan names
/// — the same pin discipline as the W1 test above, over the synthetic
/// fixtures.
#[test]
fn crystal_a3_synth_lane_exercises_the_five_w2a_constructors() {
    let synth = synth_exercised_forms();
    for expected in ["select", "undef", "unreachable", "extractelement", "unop"] {
        assert!(
            synth.contains(expected),
            "the W2a synthetic fixtures no longer exercise `{expected}`; the lane's +5 \
             claim would be false. Exercised: {synth:?}"
        );
    }
}

/// The `IRInst` forms the W2b synthetic fixtures exercise, derived from the
/// committed fixture text like [`synth_exercised_forms`] — same
/// never-rounded-up posture. Every needle carries the ` = ` binding prefix or
/// a trailing space so a directive comment or a function name (the files are
/// named after their constructors) cannot satisfy it.
fn w2b_exercised_forms() -> BTreeSet<&'static str> {
    let mut forms = BTreeSet::new();
    for chain in w2b_chains::w2b_chains() {
        for (file, _) in chain.fixtures {
            let text = fixture(file);
            for (needle, form) in [
                (" = alloca ", "alloca"),
                (" = ptr_data ", "ptrdata"),
                (" = ptr_metadata ", "ptrmetadata"),
                (" = ptr_from_parts ", "ptrfromparts"),
                (" = load ", "load"),
                ("store ", "store"),
                ("condbr ", "condbr"),
                ("ret ", "ret"),
            ] {
                if text.contains(needle) {
                    forms.insert(form);
                }
            }
        }
    }
    forms
}

/// The W2b synthetic lane covers exactly the four memory constructors the
/// plan names (§5 W2b) — the lane's +4 pin.
#[test]
fn crystal_a3_w2b_lane_exercises_the_four_w2b_constructors() {
    let w2b = w2b_exercised_forms();
    for expected in ["alloca", "ptrdata", "ptrmetadata", "ptrfromparts"] {
        assert!(
            w2b.contains(expected),
            "the W2b synthetic fixtures no longer exercise `{expected}`; the lane's +4 \
             claim would be false. Exercised: {w2b:?}"
        );
    }
}

/// **The W2c gate.** The call+module tranche — `callindirect`, `globaladdr` —
/// through the same [`measure_synth_lane`] contract. One declared delta
/// (`callindirect`'s null-callee row diverges by fault CODE; `w2c_chains.rs`'s
/// module doc records the measurement); every other row is exact `Ret`
/// agreement at the pinned zero cost offset.
#[test]
fn crystal_a3_semdiff_w2c_measures_encoding_agreement() {
    measure_synth_lane("W2c", w2c_chains::w2c_chains());

    let combined: BTreeSet<&'static str> = exercised_forms()
        .union(&wide_exercised_forms())
        .copied()
        .collect::<BTreeSet<_>>()
        .union(&synth_exercised_forms())
        .copied()
        .collect::<BTreeSet<_>>()
        .union(&w2b_exercised_forms())
        .copied()
        .collect::<BTreeSet<_>>()
        .union(&w2c_exercised_forms())
        .copied()
        .collect();
    eprintln!(
        "\nThis is a MEASUREMENT, not a proof. Original + W1 + W2a + W2b + W2c chains \
         exercise {}/{} IRInst forms; the other {} are untouched by the lanes ABOVE \
         (overflow has its own W3 lane below since 2026-08-25; fcmp is the plan's W4 \
         float lane). A synthetic row measures E1/E2 agreement on authored text — never \
         a producer's body — and the committed MEASURED fraction stays whatever the last \
         minted data/crystal_gap2_semdiff_*.json records.",
        combined.len(),
        irinst_census().len(),
        irinst_census().len() - combined.len(),
    );
}

/// The W2c smoke: [`synth_e2_smoke_lane`] over the call+module-tranche table.
#[test]
fn crystal_a3_w2c_e2_instrument_smoke() {
    synth_e2_smoke_lane("W2c", w2c_chains::w2c_chains());
}

/// The `IRInst` forms the W2c synthetic fixtures exercise, derived from the
/// committed fixture text like [`synth_exercised_forms`] — same
/// never-rounded-up posture. Every needle carries the ` = ` binding prefix or
/// a trailing space so a directive comment or a function name (the files are
/// named after their constructors) cannot satisfy it.
fn w2c_exercised_forms() -> BTreeSet<&'static str> {
    let mut forms = BTreeSet::new();
    for chain in w2c_chains::w2c_chains() {
        for (file, _) in chain.fixtures {
            let text = fixture(file);
            for (needle, form) in [
                (" = call_indirect ", "callindirect"),
                (" = global_addr ", "globaladdr"),
                (" = const ", "const_"),
                (" = load ", "load"),
                ("store ", "store"),
                ("condbr ", "condbr"),
                ("ret ", "ret"),
            ] {
                if text.contains(needle) {
                    forms.insert(form);
                }
            }
        }
    }
    forms
}

/// The W2c synthetic lane covers exactly the two call+module constructors the
/// plan names (§5 W2c) — the lane's +2 pin, completing the synthetic tranches:
/// only `overflow` (W3) and `fcmp` (W4) remain without battery rows.
#[test]
fn crystal_a3_w2c_lane_exercises_the_two_w2c_constructors() {
    let w2c = w2c_exercised_forms();
    for expected in ["callindirect", "globaladdr"] {
        assert!(
            w2c.contains(expected),
            "the W2c synthetic fixtures no longer exercise `{expected}`; the lane's +2 \
             claim would be false. Exercised: {w2c:?}"
        );
    }
}

/// **The W3 gate.** The overflow value domain — `synth_overflow_u8`,
/// `synth_overflow_i8` — through the same [`measure_synth_lane`] contract.
/// NO declared delta: every row is exact multi-value `Ret` agreement
/// ([`RunResult::Many`], the six-value ret of three (value, flag) pairs) at
/// the pinned zero cost offset. This is also the first battery measurement of
/// the machine's positional multi-value return (`ir_ret_to`).
#[test]
fn crystal_a3_semdiff_w3_measures_encoding_agreement() {
    measure_synth_lane("W3", w3_chains::w3_chains());

    let combined: BTreeSet<&'static str> = exercised_forms()
        .union(&wide_exercised_forms())
        .copied()
        .collect::<BTreeSet<_>>()
        .union(&synth_exercised_forms())
        .copied()
        .collect::<BTreeSet<_>>()
        .union(&w2b_exercised_forms())
        .copied()
        .collect::<BTreeSet<_>>()
        .union(&w2c_exercised_forms())
        .copied()
        .collect::<BTreeSet<_>>()
        .union(&w3_exercised_forms())
        .copied()
        .collect();
    eprintln!(
        "\nThis is a MEASUREMENT, not a proof. Original + W1 + W2a + W2b + W2c + W3 \
         chains exercise {}/{} IRInst forms (fcmp gained its own W4 lane below on \
         2026-08-25). A synthetic row measures E1/E2 agreement on authored text — never \
         a producer's body — and the committed MEASURED fraction stays whatever the last \
         minted data/crystal_gap2_semdiff_*.json records.",
        combined.len(),
        irinst_census().len(),
    );
}

/// The W3 smoke: [`synth_e2_smoke_lane`] over the overflow chain tables.
#[test]
fn crystal_a3_w3_e2_instrument_smoke() {
    synth_e2_smoke_lane("W3", w3_chains::w3_chains());
}

/// The `IRInst` forms the W3 synthetic fixtures exercise, derived from the
/// committed fixture text like [`synth_exercised_forms`] — same
/// never-rounded-up posture. All three `OverflowOp` mnemonics map to the one
/// `overflow` constructor, and each needle carries the ` = ` binding prefix
/// so a directive comment or the files' own names cannot satisfy it.
fn w3_exercised_forms() -> BTreeSet<&'static str> {
    let mut forms = BTreeSet::new();
    for chain in w3_chains::w3_chains() {
        for (file, _) in chain.fixtures {
            let text = fixture(file);
            for (needle, form) in [
                (" = add.overflow ", "overflow"),
                (" = sub.overflow ", "overflow"),
                (" = mul.overflow ", "overflow"),
                ("ret ", "ret"),
            ] {
                if text.contains(needle) {
                    forms.insert(form);
                }
            }
        }
    }
    forms
}

/// The W3 lane covers exactly the constructor the plan names (§5 W3) — the
/// lane's +1 pin: after it only `fcmp` lacked battery rows (its W4 lane is
/// below), and all three checked-arithmetic operators are present in the
/// fixtures (the needles are per-operator, so losing one would drop the
/// form).
#[test]
fn crystal_a3_w3_lane_exercises_the_overflow_constructor() {
    let w3 = w3_exercised_forms();
    assert!(
        w3.contains("overflow"),
        "the W3 synthetic fixtures no longer exercise `overflow`; the lane's +1 claim \
         would be false. Exercised: {w3:?}"
    );
    for chain in w3_chains::w3_chains() {
        for (file, _) in chain.fixtures {
            let text = fixture(file);
            for op in ["add.overflow", "sub.overflow", "mul.overflow"] {
                assert!(
                    text.contains(&format!(" = {op} ")),
                    "{file} lost its `{op}` node; the lane's all-three-operators claim \
                     would be false"
                );
            }
        }
    }
}

/// **The W4 gate.** The float-comparison domain — `synth_fcmp` — through the
/// same [`measure_synth_lane`] contract. NO declared delta: comparison is
/// TOTAL on classified binary64 operands (a NaN produces an ANSWER on both
/// executors — ordered false, unordered true), so every row is exact
/// twelve-value `Ret` agreement ([`RunResult::Many`]) at the pinned zero
/// cost offset. The lane completing means every `IRInst` constructor now has
/// battery rows — the coverage test above pins the exercised set against the
/// DERIVED census, with the two Phase-B forms owed by name.
#[test]
fn crystal_a3_semdiff_w4_measures_encoding_agreement() {
    measure_synth_lane("W4", w4_chains::w4_chains());

    let combined: BTreeSet<&'static str> = exercised_forms()
        .union(&wide_exercised_forms())
        .copied()
        .collect::<BTreeSet<_>>()
        .union(&synth_exercised_forms())
        .copied()
        .collect::<BTreeSet<_>>()
        .union(&w2b_exercised_forms())
        .copied()
        .collect::<BTreeSet<_>>()
        .union(&w2c_exercised_forms())
        .copied()
        .collect::<BTreeSet<_>>()
        .union(&w3_exercised_forms())
        .copied()
        .collect::<BTreeSet<_>>()
        .union(&w4_exercised_forms())
        .copied()
        .collect();
    eprintln!(
        "\nThis is a MEASUREMENT, not a proof. Original + W1 + W2a + W2b + W2c + W3 + W4 \
         chains exercise {}/{} IRInst forms — every constructor the THIR lowerer \
         produces. The two the trust-ir bridge produces (`borrow`, `copy`) are owed by \
         the Phase-B derived-bundle chain and are named in OWED_BY_THE_LZD_CHAIN. A \
         synthetic row measures E1/E2 agreement on authored text — never a producer's \
         body — and the committed MEASURED fraction stays whatever the last minted \
         data/crystal_gap2_semdiff_*.json records.",
        combined.len(),
        irinst_census().len(),
    );
}

/// The W4 smoke: [`synth_e2_smoke_lane`] over the fcmp chain table.
#[test]
fn crystal_a3_w4_e2_instrument_smoke() {
    synth_e2_smoke_lane("W4", w4_chains::w4_chains());
}

/// The `IRInst` forms the W4 synthetic fixture exercises, derived from the
/// committed fixture text like [`synth_exercised_forms`] — same
/// never-rounded-up posture. All twelve `FCmpOp` mnemonics map to the one
/// `fcmp` constructor, and the needle carries the ` = fcmp ` binding prefix
/// so a directive comment or the file's own name cannot satisfy it.
fn w4_exercised_forms() -> BTreeSet<&'static str> {
    let mut forms = BTreeSet::new();
    for chain in w4_chains::w4_chains() {
        for (file, _) in chain.fixtures {
            let text = fixture(file);
            for (needle, form) in [(" = fcmp ", "fcmp"), ("ret ", "ret")] {
                if text.contains(needle) {
                    forms.insert(form);
                }
            }
        }
    }
    forms
}

/// The W4 lane covers exactly the constructor the plan names (§5 W4) — the
/// final +1 pin, and all twelve comparison predicates are present in the
/// fixture (the needles are per-operator, so losing one would break the
/// lane's whole-split claim even though the constructor form survives).
#[test]
fn crystal_a3_w4_lane_exercises_the_fcmp_constructor() {
    let w4 = w4_exercised_forms();
    assert!(
        w4.contains("fcmp"),
        "the W4 synthetic fixture no longer exercises `fcmp`; the lane's +1 claim \
         would be false. Exercised: {w4:?}"
    );
    for chain in w4_chains::w4_chains() {
        for (file, _) in chain.fixtures {
            let text = fixture(file);
            for op in [
                "oeq", "one", "olt", "ole", "ogt", "oge", "ueq", "une", "ult", "ule", "ugt", "uge",
            ] {
                assert!(
                    text.contains(&format!(" = fcmp {op} f64 ")),
                    "{file} lost its `fcmp {op}` node; the lane's all-twelve-predicates \
                     claim would be false"
                );
            }
        }
    }
}

// ══════════════════════════ the float-RESIDUE lane ══════════════════════════

/// **The float-residue gate.** The three residue chains — `synth_fsign`,
/// `synth_fround`, `synth_fminmax` — through the same [`measure_synth_lane`]
/// contract. NO declared delta IN THE ROWS: every row is exact multi-value
/// `Ret` agreement on `RunResult::Float` bit patterns at the pinned zero
/// cost offset. The wave's divergences are CELL-shaped (rounding-on-NaN,
/// minmax's both-NaN and opposite-zero cells, and the whole-operator
/// `frem`/`fsqrt`/fp-cast refusals) and deliberately have no battery row —
/// they are kernel-witnessed refusals, PENDING-file records and adequacy-grid
/// deltas instead (`wfr_chains.rs` module doc).
#[test]
fn crystal_a3_semdiff_wfr_measures_encoding_agreement() {
    measure_synth_lane("WFR", wfr_chains::wfr_chains());
    eprintln!(
        "\nThis is a MEASUREMENT, not a proof. The float-residue chains measure the seven \
         answering residue OPERATORS (fneg/fabs, ffloor/fceil/ftrunc, fmin/fmax) inside \
         the already-exercised `unop`/`binop` constructors — the constructor ladder \
         is untouched by design, and the committed MEASURED fraction stays whatever the \
         last minted data/crystal_gap2_semdiff_*.json records."
    );
}

/// The float-residue smoke: [`synth_e2_smoke_lane`] over the residue chain
/// tables — E2 only, runnable on the authoring box.
#[test]
fn crystal_a3_wfr_e2_instrument_smoke() {
    synth_e2_smoke_lane("WFR", wfr_chains::wfr_chains());
}

/// The residue lane covers exactly the seven answering operators (the wave's
/// +7 claim, at OPERATOR granularity — the needles are per-mnemonic with the
/// ` = ` binding prefix, so a directive comment or a file name cannot
/// satisfy them and losing any one operator fails the pin even though the
/// `unop`/`binop` constructor forms survive).
#[test]
fn crystal_a3_wfr_lane_exercises_the_seven_residue_operators() {
    let mut found: BTreeSet<&'static str> = BTreeSet::new();
    for chain in wfr_chains::wfr_chains() {
        for (file, _) in chain.fixtures {
            let text = fixture(file);
            for op in ["fneg", "fabs", "ffloor", "fceil", "ftrunc", "fmin", "fmax"] {
                if text.contains(&format!(" = {op} f64 ")) {
                    found.insert(op);
                }
            }
        }
    }
    assert_eq!(
        found.len(),
        7,
        "the float-residue fixtures must exercise all seven answering operators; \
         found only {found:?}"
    );
}

// ═══════════════════ the WAT byte-profile atomic lane ═══════════════════

/// **The WAT gate.** Both sequential atomic fetch-add constructors, E1 on the
/// ByteV1 machine (`ir_byte_run_v1` over an authored `IRByteContextV1`) and E2
/// on trust-ir's interpreter: exact two-value `Ret` agreement (the returned
/// old word and the reloaded new word, wrapping rows included) at the pinned
/// zero cost offset, plus the uninitialized-read row at outcome class. No
/// declared delta. `wat_chains.rs`'s module doc says what this does not
/// measure (concurrency, a producer's body).
#[test]
fn crystal_a3_semdiff_wat_measures_encoding_agreement() {
    clean_verify::test_utils::run_with_stack(|| {
        wat_chains::measure_wat_lane(wat_chains::wat_chains());
    });
    eprintln!(
        "\nThis is a MEASUREMENT, not a proof. The WAT chains exercise the two sequential \
         atomic fetch-add constructors on authored text, through the ByteV1 machine; the \
         committed MEASURED fraction stays whatever the last minted \
         data/crystal_gap2_semdiff_*.json records."
    );
}

/// The WAT falsifier: a twin that fetch-adds the wrong SSA value must lose
/// the honest answer and keep its own (`wat_chains.rs`).
#[test]
fn crystal_a3_wat_lane_refuses_a_wrong_operand_twin() {
    clean_verify::test_utils::run_with_stack(wat_chains::wat_wrong_operand_twin_is_refused);
}

/// The WAT smoke: E2 alone against the authored expectations, no kernel.
#[test]
fn crystal_a3_wat_e2_instrument_smoke() {
    wat_chains::wat_e2_smoke(&wat_chains::wat_chains());
}

/// The WAT lane covers exactly the two constructors it was added for — each
/// credited only when its fixture carries the trust-ir operation AND its
/// Clean twin carries the matching `IRInst` constructor.
#[test]
fn crystal_a3_wat_lane_exercises_the_two_atomic_constructors() {
    let wat = wat_chains::wat_exercised_forms();
    for expected in [
        "atomic_fetch_add_relaxed_u64_seq",
        "atomic_fetch_add_relaxed_usize_seq",
    ] {
        assert!(
            wat.contains(expected),
            "the WAT fixtures no longer exercise `{expected}`; the lane's +2 claim would be \
             false. Exercised: {wat:?}"
        );
    }
}
