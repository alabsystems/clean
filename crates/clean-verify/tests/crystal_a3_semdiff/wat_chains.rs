// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The **WAT byte-profile atomic chains** — battery rows for the two `IRInst`
//! constructors appended on 2026-09-24 (`atomic_fetch_add_relaxed_u64_seq`,
//! `6e8241b2a`; `atomic_fetch_add_relaxed_usize_seq`, `6a687ae8d`), which
//! reached the census with neither a fixture nor an owed row.
//!
//! ## Why this lane's E1 is NOT `ir_eval`
//!
//! Every other synthetic lane measures Clean through the legacy cell-addressed
//! `ir_eval`. That machine REFUSES both atomic constructors outright —
//! `IROutcome.unmodelled IRFault.width_bounded`, kernel-witnessed by
//! `ir_exec_atomic_fetch_add_relaxed_u64_seq_unmodelled` and its usize twin
//! (`eval_ir_machine.rs`) — so a legacy row could only ever record a refusal
//! against trust-ir's answer. The ONLY Clean machine that executes them is the
//! ByteV1 profile (`ir_byte_exec_v1`, `eval_ir_byte_machine.rs`), so that is
//! what E1 runs here: `ir_byte_run_v1` from `ir_byte_init_v1`, over a
//! hand-authored `IRByteContextV1` (module + layouts + signature + binding +
//! one site per node) that [`clean_context`] generates with the fixture's SSA
//! ids. The obligation is the WHOLE outcome, `ir_byte_outcome_v1`, discharged
//! by `Eq.refl` — the kernel adjudicates by running the machine.
//!
//! ## What a green row measures, and what it does not
//!
//! **Does:** for the same authored module text, Clean's ByteV1 kernel run and
//! trust-ir's reference interpreter (`Inst::AtomicRMW` with `AtomicRMWOp::Add`:
//! load old, wrapping add, store, return old — `interpret.rs`, trust-ir
//! `5dbbf17`) return the same OLD word and leave the same NEW word behind (the
//! body reloads the slot and returns it), at the same step count; and both
//! refuse the fetch-add whose read half meets a fresh, never-stored slot at
//! the UB class (Clean `ub uninit` at the atomic's checked load; trust-ir's
//! STRICT atomic load of uninitialized bytes, `undefined_behavior`).
//!
//! **Does not:** concurrency. trust-ir's interpreter is single-threaded (every
//! ordering collapses to sequential consistency) and ByteV1's fetch-add is the
//! SEQUENTIAL primitive (`eval_ir_byte_atomic.rs`: "not a concurrent memory
//! model"); neither executor here can observe an interleaving, so these rows
//! say nothing about atomicity. Nor do they bind a PRODUCER: the module is
//! [`EnumModel::Synthetic`], authored for this differential, E3 absent by
//! construction ([`SYNTHETIC_NO_E3`]), and the ByteV1 context is authored, not
//! reflected — exactly the posture of the W2a-W4 lanes. Only the `usize` width
//! 64 executes in ByteV1 (other widths are refused, `eval_ir_byte_usize.rs`),
//! which is the width trust-ir's interpreter gives `usize` on this target.
//!
//! Cost offsets are DECLARED 0: both executors count one step per executed
//! instruction (alloca, condbr, store, fetch-add, load, ret = 6 on the
//! initialized arm), and E1's least fuel is pinned from below by a
//! kernel-accepted `fuel_out` one step short.

use std::collections::{BTreeSet, HashSet};

use clean_verify::ir_semdiff::synth::{e2_fault_class, OutcomeClass};
use clean_verify::ir_semdiff::{summarize, DiffRow, EnumModel, RunResult};
use clean_verify::spec::Specification;
use trust_ir::interpret::InterpretValue;
use trust_ir::ty::Ty;

use super::synth_chains::SYNTHETIC_NO_E3;
use super::wide_exec::{self, SigSpec};

/// The machine word a chain's atomic operates on — the ONE place the u64 and
/// usize chains differ, so the two Clean twins and the two fixtures cannot
/// drift apart in anything but the word type and the constructor.
#[derive(Clone, Copy, Debug)]
pub enum WatWord {
    /// `u64` / `IRTy.uint_ 64` / `atomic_fetch_add_relaxed_u64_seq`.
    U64,
    /// `usize` / `IRTy.usize_ 64` / `atomic_fetch_add_relaxed_usize_seq 64`.
    Usize64,
}

impl WatWord {
    fn clean_ty(self) -> &'static str {
        match self {
            WatWord::U64 => "(IRTy.uint_ 64)",
            WatWord::Usize64 => "(IRTy.usize_ 64)",
        }
    }

    /// The Clean constructor application, pointer then increment SSA id.
    fn clean_fetch_add(self, pointer: u64, value: u64) -> String {
        match self {
            WatWord::U64 => format!("IRInst.atomic_fetch_add_relaxed_u64_seq {pointer} {value}"),
            WatWord::Usize64 => {
                format!("IRInst.atomic_fetch_add_relaxed_usize_seq 64 {pointer} {value}")
            }
        }
    }

    /// The `IRInst` constructor NAME this word's chain exercises.
    pub fn constructor(self) -> &'static str {
        match self {
            WatWord::U64 => "atomic_fetch_add_relaxed_u64_seq",
            WatWord::Usize64 => "atomic_fetch_add_relaxed_usize_seq",
        }
    }

    /// The trust-ir text spelling of the same operation in the fixture — the
    /// coverage needle, carried with the ` = ` binding prefix so a comment or
    /// the function's own name cannot satisfy it.
    pub fn fixture_needle(self) -> &'static str {
        match self {
            WatWord::U64 => " = atomicrmw add relaxed u64 ptr ",
            WatWord::Usize64 => " = atomicrmw add relaxed usize ptr ",
        }
    }

    fn trust_ty(self) -> Ty {
        match self {
            WatWord::U64 => Ty::U64,
            WatWord::Usize64 => Ty::Usize,
        }
    }
}

/// One argument, rendered for BOTH executors from the same value.
#[derive(Clone, Copy, Debug)]
pub enum WatArg {
    /// A machine word of the chain's [`WatWord`] type.
    Word(u64),
    /// The arm selector.
    Bool(bool),
}

/// What one row expects of the two executors that exist for it.
pub enum WatExpect {
    /// Both return this value at the declared zero cost offset.
    Ret(RunResult),
    /// Both halt with undefined behavior: E1 pins `IROutcome.ub <fault>`
    /// exactly, E2 must report the UB class. Compared at outcome CLASS, with
    /// both exact terms in the row's notes (the W2a/W2b convention).
    UbAgree(&'static str),
}

/// One measured input.
pub struct WatInput {
    /// Human-readable label, printed with the row.
    pub label: &'static str,
    /// The arguments, in parameter order.
    pub args: [WatArg; 3],
    /// What this row expects.
    pub expect: WatExpect,
}

/// One byte-profile atomic chain.
pub struct WatChain {
    /// Short name, used in output and generated def names.
    pub name: &'static str,
    /// The committed synthetic fixture under `tests/fixtures/`.
    pub fixture: &'static str,
    /// The function's printed name inside that fixture.
    pub printed: &'static str,
    /// The word type the atomic operates on.
    pub word: WatWord,
    /// The reconstituted trust-ir signature.
    pub sig: SigSpec,
    /// The inputs.
    pub inputs: Vec<WatInput>,
}

/// The declared clean-minus-trust cost offset on value-returning rows.
pub const WAT_EXPECTED_COST_OFFSET: i64 = 0;

/// The fuel probed from below for every row: generous for a six-instruction
/// body, small enough that a run that never halts is a loud failure.
const WAT_MAX_FUEL: u32 = 16;

/// The two chains, in measurement order.
pub fn wat_chains() -> Vec<WatChain> {
    vec![
        chain(
            "wat_u64",
            "synth/synth_atomic_u64.trust-ir.txt",
            "@synth::atomic_u64_probe",
            WatWord::U64,
            928,
        ),
        chain(
            "wat_usize",
            "synth/synth_atomic_usize.trust-ir.txt",
            "@synth::atomic_usize_probe",
            WatWord::Usize64,
            929,
        ),
    ]
}

/// `(start, increment)` pairs for the initialized arm. The expectation is the
/// host's wrapping arithmetic, which is the semantics both executors claim
/// (trust-ir: the wrapping integer `BinOp::Add`; ByteV1: `ir_wrap 64`).
const WAT_INITIALIZED_ROWS: &[(&str, u64, u64)] = &[
    ("5 + 3: old 5 returned, 8 written", 5, 3),
    ("0 + 0: the zero word round-trips", 0, 0),
    ("MAX + 1: the written word wraps to 0", u64::MAX, 1),
    (
        "2^63 + 2^63: the carry out of bit 63 is dropped",
        1 << 63,
        1 << 63,
    ),
    ("MAX + MAX: wraps to MAX - 1", u64::MAX, u64::MAX),
    ("0 + MAX: no wrap at the top", 0, u64::MAX),
    (
        "0x0123456789abcdef + 0x1111111111111111: eight distinct bytes",
        0x0123_4567_89ab_cdef,
        0x1111_1111_1111_1111,
    ),
];

fn chain(
    name: &'static str,
    fixture: &'static str,
    printed: &'static str,
    word: WatWord,
    functy: u32,
) -> WatChain {
    let mut inputs: Vec<WatInput> = WAT_INITIALIZED_ROWS
        .iter()
        .map(|(label, start, delta)| WatInput {
            label,
            args: [
                WatArg::Word(*start),
                WatArg::Word(*delta),
                WatArg::Bool(true),
            ],
            expect: WatExpect::Ret(RunResult::Many(vec![
                RunResult::Int(*start),
                RunResult::Int(start.wrapping_add(*delta)),
            ])),
        })
        .collect();
    inputs.push(WatInput {
        label: "fresh slot, never stored: the read half is UB",
        args: [WatArg::Word(7), WatArg::Word(1), WatArg::Bool(false)],
        expect: WatExpect::UbAgree("IRFault.uninit"),
    });
    let t = word.trust_ty();
    WatChain {
        name,
        fixture,
        printed,
        word,
        sig: (
            functy,
            vec![t.clone(), t.clone(), Ty::Bool],
            vec![t.clone(), t],
        ),
        inputs,
    }
}

// ─────────────────────────── the Clean twin ───────────────────────────

fn list(ty: &str, items: &[String]) -> String {
    items
        .iter()
        .rev()
        .fold(format!("(@IRList.nil {ty})"), |tail, item| {
            format!("(@IRList.cons {ty} {item} {tail})")
        })
}

fn nats(ids: &[u64]) -> String {
    list(
        "Nat",
        &ids.iter().map(u64::to_string).collect::<Vec<String>>(),
    )
}

/// One node of the twin: the instruction, its result ids, and the result
/// TYPES its byte site declares.
struct TwinNode {
    inst: String,
    results: Vec<u64>,
    types: Vec<&'static str>,
}

fn node(inst: String, results: &[u64], types: &[&'static str]) -> TwinNode {
    TwinNode {
        inst,
        results: results.to_vec(),
        types: types.to_vec(),
    }
}

/// The name the chain's registered context constant carries.
pub fn clean_context_name(chain: &WatChain) -> String {
    format!("{}_ctx", chain.name)
}

/// The Clean twin of the fixture, as ONE registered `IRByteContextV1`
/// definition: function 0 with parameters (start %0, increment %1, selector
/// %2), the same three blocks and the same SSA ids as the trust-ir text, and
/// the catalog ByteV1 checks against — the word/pointer/bool layouts, the
/// exact signature, a local C-convention binding, and one site per node
/// carrying that node's result types.
pub fn clean_context(chain: &WatChain) -> String {
    let w = chain.word.clean_ty();
    let blocks: [(u64, Vec<TwinNode>); 3] = [
        (
            0,
            vec![
                node(
                    format!("IRInst.alloca {w} (@IROption.none Nat)"),
                    &[3],
                    &["IRTy.ptr_"],
                ),
                node(
                    "IRInst.condbr 2 1 (@IRList.nil Nat) 2 (@IRList.nil Nat)".to_owned(),
                    &[],
                    &[],
                ),
            ],
        ),
        (
            1,
            vec![
                node(format!("IRInst.store {w} 3 0 Bool.false"), &[], &[]),
                node(chain.word.clean_fetch_add(3, 1), &[4], &[w]),
                node(format!("IRInst.load {w} 3 Bool.false"), &[5], &[w]),
                node(format!("IRInst.ret {}", nats(&[4, 5])), &[], &[]),
            ],
        ),
        (
            2,
            vec![
                node(chain.word.clean_fetch_add(3, 1), &[6], &[w]),
                node(format!("IRInst.ret {}", nats(&[6, 6])), &[], &[]),
            ],
        ),
    ];
    let mut block_terms = Vec::new();
    let mut sites = Vec::new();
    for (id, nodes) in &blocks {
        let node_terms: Vec<String> = nodes
            .iter()
            .map(|n| format!("(IRNode.mk ({}) {})", n.inst, nats(&n.results)))
            .collect();
        block_terms.push(format!(
            "(IRBlock.mk {id} (@IRList.nil Nat) {})",
            list("IRNode", &node_terms)
        ));
        for (pc, n) in nodes.iter().enumerate() {
            let types: Vec<String> = n.types.iter().map(|t| (*t).to_owned()).collect();
            sites.push(format!(
                "(IRByteSiteV1.mk 0 {id} {pc} 0 1 {})",
                list("IRTy", &types)
            ));
        }
    }
    let func = format!(
        "(IRFunc.mk 0 {} 0 {})",
        nats(&[0, 1, 2]),
        list("IRBlock", &block_terms)
    );
    let layouts = list(
        "IRByteLayoutV1",
        &[
            "(IRByteLayoutV1.mk IRTy.bool_ 1 1 (@IRList.nil IRTy) (@IRList.nil Nat))".to_owned(),
            "(IRByteLayoutV1.mk IRTy.ptr_ 8 8 (@IRList.nil IRTy) (@IRList.nil Nat))".to_owned(),
            format!("(IRByteLayoutV1.mk {w} 8 8 (@IRList.nil IRTy) (@IRList.nil Nat))"),
        ],
    );
    let signature = format!(
        "(IRByteSignatureV1.mk 0 {} {} Bool.false)",
        list(
            "IRTy",
            &[w.to_owned(), w.to_owned(), "IRTy.bool_".to_owned()]
        ),
        list("IRTy", &[w.to_owned(), w.to_owned()])
    );
    format!(
        "def {} : IRByteContextV1 := IRByteContextV1.mk (IRModule.mk {} (@IRList.nil IRGlobal)) \
         {layouts} {} {} {}",
        clean_context_name(chain),
        list("IRFunc", &[func]),
        list("IRByteSignatureV1", &[signature]),
        list(
            "IRByteFunctionV1",
            &["(IRByteFunctionV1.mk 0 0 4096 1 Bool.false)".to_owned()]
        ),
        list("IRByteSiteV1", &sites),
    )
}

/// The provider for imported calls — this module imports nothing, so any
/// provider call would be a stuck run, never an answer.
const WAT_NO_IMPORT: &str = "def wat_no_import : IRByteProvidersV1 Nat := \
     fun (_ : Nat) (_ : IRList IRScalar) (mem : IRByteMemoryV1) (host : Nat) => \
     @IRByteImportResultV1.mk Nat (IROutcome.stuck IRFault.no_func) mem host";

fn clean_args(args: &[WatArg; 3]) -> String {
    let scalars: Vec<String> = args
        .iter()
        .map(|a| match a {
            WatArg::Word(n) => format!("(IRScalar.int_ {n})"),
            WatArg::Bool(b) => format!("(IRScalar.bool_ Bool.{b})"),
        })
        .collect();
    list("IRScalar", &scalars)
}

fn trust_args(word: WatWord, args: &[WatArg; 3]) -> Vec<InterpretValue> {
    args.iter()
        .map(|a| match a {
            WatArg::Word(n) => InterpretValue::int(word.trust_ty(), i128::from(*n))
                .expect("u64/usize is an integer type"),
            WatArg::Bool(b) => InterpretValue::bool(*b),
        })
        .collect()
}

/// The `IROutcome.ret` payload for a `Ret` expectation — raw decimal
/// literals (ByteV1 carries no `ir_d<N>` numeral pool and needs none).
fn clean_ret(result: &RunResult) -> Option<String> {
    let RunResult::Many(values) = result else {
        return None;
    };
    let mut scalars = Vec::new();
    for v in values {
        let RunResult::Int(n) = v else {
            return None;
        };
        scalars.push(format!("(IRScalar.int_ {n})"));
    }
    Some(format!("(IROutcome.ret {})", list("IRScalar", &scalars)))
}

/// The E1 run: `ir_byte_outcome_v1` of `fuel` ByteV1 steps from the actual
/// local entry, over empty caller memory and a zero host.
fn byte_outcome(ctx: &str, fuel: u32, args: &[WatArg; 3]) -> String {
    format!(
        "ir_byte_outcome_v1 Nat (ir_byte_run_v1 Nat {ctx} wat_no_import {fuel} \
         (ir_byte_init_v1 Nat {ctx} 0 {} (ir_byte_memory_empty_v1 64) 0))",
        clean_args(args)
    )
}

fn obligation(name: &str, actual: &str, outcome: &str) -> String {
    format!("def {name} : @Eq IROutcome ({actual}) {outcome} := @Eq.refl IROutcome {outcome}")
}

/// The least fuel at which the kernel accepts `outcome` for a run of the
/// context `ctx` on `args`, probed from below. `prefix` keeps every probe's
/// definition name unique across the gate run.
fn least_fuel(
    spec: &mut Specification,
    ctx: &str,
    prefix: &str,
    args: &[WatArg; 3],
    outcome: &str,
) -> Option<u32> {
    (0..=WAT_MAX_FUEL).find(|fuel| {
        let src = obligation(
            &format!("{prefix}_f{fuel}"),
            &byte_outcome(ctx, *fuel, args),
            outcome,
        );
        spec.add_recursive_def(
            &src,
            "crystal A3 WAT lane: kernel-checked ByteV1 outcome probe",
        )
        .is_ok()
    })
}

/// Is `threshold` NEEDED — is the run still `fuel_out` one step below it?
fn threshold_is_tight(
    spec: &mut Specification,
    chain: &WatChain,
    input: &WatInput,
    tag: &str,
    threshold: u32,
) -> bool {
    if threshold == 0 {
        return true;
    }
    let src = obligation(
        &format!("wat_{}_{tag}_tight", chain.name),
        &byte_outcome(&clean_context_name(chain), threshold - 1, &input.args),
        "IROutcome.fuel_out",
    );
    spec.add_recursive_def(
        &src,
        "crystal A3 WAT lane: the threshold is tight from below",
    )
    .is_ok()
}

/// E2: trust-ir's parser and reference interpreter over the composed fixture.
pub fn wat_trust_leg(chain: &WatChain, input: &WatInput) -> (RunResult, Option<u32>) {
    let texts = vec![(super::fixture(chain.fixture), chain.printed)];
    let module =
        wide_exec::build_wide_module(&texts, "", &[0], std::slice::from_ref(&chain.sig), None)
            .unwrap_or_else(|e| panic!("WAT chain `{}`: E2 module build failed: {e}", chain.name));
    let target = wide_exec::wide_target(&module, false)
        .unwrap_or_else(|e| panic!("WAT chain `{}`: {e}", chain.name));
    wide_exec::run_wide(&module, target, trust_args(chain.word, &input.args), 0)
}

/// The ByteV1 specification with every chain's context registered.
fn wat_spec(chains: &[WatChain]) -> Specification {
    let mut spec = clean_verify::eval_ir::build_byte_prelude_spec_v1_with_stack()
        .expect("the production ByteV1 vocabulary must build");
    spec.add_recursive_def(WAT_NO_IMPORT, "crystal A3 WAT lane: no-import provider")
        .unwrap_or_else(|e| panic!("wat_no_import failed to register: {e}"));
    let mut registered: HashSet<String> = HashSet::new();
    for chain in chains {
        if registered.insert(clean_context_name(chain)) {
            spec.add_recursive_def(
                &clean_context(chain),
                "crystal A3 WAT lane: the chain's authored ByteV1 Clean twin",
            )
            .unwrap_or_else(|e| {
                panic!(
                    "WAT chain `{}`: the ByteV1 context failed to register: {e}",
                    chain.name
                )
            });
        }
    }
    spec
}

/// Measure every row of every chain, E1 against E2, and hold the verdicts:
/// zero disagreements, zero loose thresholds, every priced row at the
/// declared zero offset.
pub fn measure_wat_lane(chains: Vec<WatChain>) {
    let mut spec = wat_spec(&chains);
    for chain in &chains {
        let mut rows: Vec<DiffRow> = Vec::new();
        for (idx, input) in chain.inputs.iter().enumerate() {
            let (e2_value, e2_steps) = wat_trust_leg(chain, input);
            let mut notes = vec![format!("input: {}", input.label)];
            let tag = format!("i{idx}");
            let (trust_leg, clean_leg, tight) = match &input.expect {
                WatExpect::Ret(declared) => {
                    // E2's live answer is asked first; the kernel decides.
                    let mut candidates: Vec<RunResult> = Vec::new();
                    if !matches!(e2_value, RunResult::Fault(_)) {
                        candidates.push(e2_value.clone());
                    }
                    candidates.push(declared.clone());
                    candidates.dedup();
                    let mut found: Option<(RunResult, u32)> = None;
                    for (c, cand) in candidates.iter().enumerate() {
                        let Some(outcome) = clean_ret(cand) else {
                            continue;
                        };
                        if let Some(fuel) = least_fuel(
                            &mut spec,
                            &clean_context_name(chain),
                            &format!("wat_{}_{tag}_c{c}", chain.name),
                            &input.args,
                            &outcome,
                        ) {
                            found = Some((cand.clone(), fuel));
                            break;
                        }
                    }
                    let (cv, threshold) = found.unwrap_or_else(|| {
                        panic!(
                            "WAT chain `{}` input `{}`: Clean's ByteV1 kernel run accepted no \
                             candidate at any fuel <= {WAT_MAX_FUEL} — the E1 leg may never be \
                             silently absent",
                            chain.name, input.label
                        )
                    });
                    let tight = threshold_is_tight(&mut spec, chain, input, &tag, threshold);
                    (
                        Some((e2_value.clone(), e2_steps)),
                        Some((cv, Some(threshold))),
                        tight,
                    )
                }
                WatExpect::UbAgree(fault) => {
                    let RunResult::Fault(code) = &e2_value else {
                        panic!(
                            "WAT chain `{}` input `{}`: E2 returned {e2_value} where undefined \
                             behavior was expected",
                            chain.name, input.label
                        );
                    };
                    assert_eq!(
                        e2_fault_class(code),
                        Some(OutcomeClass::Ub),
                        "WAT chain `{}` input `{}`: E2 code `{code}` is not the UB class",
                        chain.name,
                        input.label
                    );
                    let outcome = format!("(IROutcome.ub {fault})");
                    let threshold = least_fuel(
                        &mut spec,
                        &clean_context_name(chain),
                        &format!("wat_{}_{tag}", chain.name),
                        &input.args,
                        &outcome,
                    );
                    let threshold = threshold.unwrap_or_else(|| {
                        panic!(
                            "WAT chain `{}` input `{}`: the kernel refuted `{outcome}` at every \
                             fuel <= {WAT_MAX_FUEL}",
                            chain.name, input.label
                        )
                    });
                    let tight = threshold_is_tight(&mut spec, chain, input, &tag, threshold);
                    notes.push(format!(
                        "outcome-class agreement: clean pins {outcome}, e2 reported `{code}`"
                    ));
                    let ub = RunResult::Fault(OutcomeClass::Ub.tag().to_owned());
                    (Some((ub.clone(), None)), Some((ub, Some(threshold))), tight)
                }
            };
            notes.push(format!("E3 absent: {SYNTHETIC_NO_E3}"));
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
            EnumModel::Synthetic,
            false,
            WAT_EXPECTED_COST_OFFSET,
            rows,
        );
        eprintln!(
            "\n=== WAT {} ({}) ===",
            report.chain,
            chain.word.constructor()
        );
        for row in &report.rows {
            eprintln!("{}", row.render());
            for note in &row.notes {
                eprintln!("      note: {note}");
            }
        }
        eprintln!("  {}", report.summary());
        assert_eq!(
            report.disagreed, 0,
            "WAT chain `{}`: {} disagreement(s) — this lane declares no executor delta",
            report.chain, report.disagreed
        );
        assert_eq!(
            report.loose_thresholds, 0,
            "WAT chain `{}`: {} loose threshold(s) — an upper bound is not a cost",
            report.chain, report.loose_thresholds
        );
        for row in &report.rows {
            if let (Some((_, Some(steps))), Some((_, Some(threshold)))) = (&row.trust, &row.clean) {
                let offset = i64::from(*threshold) - i64::from(*steps);
                assert_eq!(
                    offset, WAT_EXPECTED_COST_OFFSET,
                    "WAT chain `{}` input {}: cost offset {offset:+} vs pinned {:+}",
                    report.chain, row.tag, WAT_EXPECTED_COST_OFFSET
                );
            }
        }
    }
}

/// FALSIFICATION. A lane that cannot go red is not evidence, so the E1 leg is
/// shown to DISCRIMINATE the atomic's operands: a twin whose fetch-add reads
/// the start word `%0` as its increment (where the fixture says `%1`) is
/// registered beside the honest one, and on the `5 + 3` row the kernel must
/// REFUSE the honest answer `[5, 8]` at every probed fuel while ACCEPTING the
/// mutant's own `[5, 10]` at the honest fuel — so the refusal is the operand,
/// not a malformed twin. Run for both words.
pub fn wat_wrong_operand_twin_is_refused() {
    let chains = wat_chains();
    let mut spec = wat_spec(&chains);
    for chain in &chains {
        let honest = clean_context(chain);
        let wrong = chain.word.clean_fetch_add(3, 0);
        assert_eq!(
            honest.matches(&chain.word.clean_fetch_add(3, 1)).count(),
            2,
            "WAT chain `{}`: the twin no longer fetch-adds %3 by %1 on both arms",
            chain.name
        );
        let ctx = format!("{}_wrong_operand", clean_context_name(chain));
        let mutant = honest
            .replacen(&clean_context_name(chain), &ctx, 1)
            .replace(&chain.word.clean_fetch_add(3, 1), &wrong);
        spec.add_recursive_def(&mutant, "crystal A3 WAT lane: wrong-operand MUTANT twin")
            .unwrap_or_else(|e| {
                panic!(
                    "WAT chain `{}`: the mutant twin failed to register: {e}",
                    chain.name
                )
            });
        let args = [WatArg::Word(5), WatArg::Word(3), WatArg::Bool(true)];
        let honest_answer = RunResult::Many(vec![RunResult::Int(5), RunResult::Int(8)]);
        let mutant_answer = RunResult::Many(vec![RunResult::Int(5), RunResult::Int(10)]);
        let refused = least_fuel(
            &mut spec,
            &ctx,
            &format!("wat_{}_mut_honest", chain.name),
            &args,
            &clean_ret(&honest_answer).expect("a two-word ret"),
        );
        assert_eq!(
            refused, None,
            "WAT chain `{}`: the wrong-operand twin was accepted at the HONEST answer — \
             E1 cannot see which SSA value the fetch-add reads",
            chain.name
        );
        let accepted = least_fuel(
            &mut spec,
            &ctx,
            &format!("wat_{}_mut_own", chain.name),
            &args,
            &clean_ret(&mutant_answer).expect("a two-word ret"),
        );
        assert_eq!(
            accepted,
            Some(6),
            "WAT chain `{}`: the mutant twin must still run to its own answer at the honest \
             fuel, or the refusal above proves only that the mutant was malformed",
            chain.name
        );
    }
}

/// E2 alone, against the AUTHORED expectations — no kernel, no
/// `Specification`. Values and step counts are printed per row so the
/// declared zero offset has a measured E2 half on any box.
pub fn wat_e2_smoke(chains: &[WatChain]) {
    for chain in chains {
        eprintln!("\n=== WAT E2 smoke: {} ===", chain.name);
        for input in &chain.inputs {
            let (value, steps) = wat_trust_leg(chain, input);
            eprintln!("  {:<62} -> {value} @{steps:?} steps", input.label);
            match &input.expect {
                WatExpect::Ret(declared) => assert_eq!(
                    &value, declared,
                    "chain `{}` input `{}`: E2 disagrees with the authored expectation",
                    chain.name, input.label
                ),
                WatExpect::UbAgree(_) => {
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
            }
        }
    }
}

/// The `IRInst` forms the WAT fixtures exercise, derived from the committed
/// fixture text (never-rounded-up, like every other lane). The atomic form is
/// credited only when the fixture carries the trust-ir operation AND the
/// chain's Clean twin carries the matching `IRInst` constructor, so neither
/// half can be credited without the other.
pub fn wat_exercised_forms() -> BTreeSet<&'static str> {
    let mut forms = BTreeSet::new();
    for chain in wat_chains() {
        let text = super::fixture(chain.fixture);
        if text.contains(chain.word.fixture_needle())
            && clean_context(&chain).contains(&format!("IRInst.{} ", chain.word.constructor()))
        {
            forms.insert(chain.word.constructor());
        }
        for (needle, form) in [
            (" = alloca ", "alloca"),
            ("condbr ", "condbr"),
            ("store ", "store"),
            (" = load ", "load"),
            ("ret ", "ret"),
        ] {
            if text.contains(needle) {
                forms.insert(form);
            }
        }
    }
    forms
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The twin's SSA ids are the fixture's: every `%N` the trust-ir text
    /// binds or reads is an id the generated context mentions, and the two
    /// chains' twins differ ONLY in the word type and the constructor.
    #[test]
    fn test_the_twins_differ_only_in_the_word() {
        let chains = wat_chains();
        let u64_ctx = clean_context(&chains[0]);
        let usize_ctx = clean_context(&chains[1]);
        let normalized = usize_ctx
            .replace("wat_usize_ctx", "wat_u64_ctx")
            .replace("IRTy.usize_ 64", "IRTy.uint_ 64")
            .replace(
                "atomic_fetch_add_relaxed_usize_seq 64",
                "atomic_fetch_add_relaxed_u64_seq",
            );
        assert_eq!(normalized, u64_ctx);
        assert_eq!(
            u64_ctx
                .matches("IRInst.atomic_fetch_add_relaxed_u64_seq 3 1")
                .count(),
            2,
            "both arms of the twin must fetch-add through %3 by %1"
        );
    }

    /// The initialized rows' expectations really wrap where the labels say.
    #[test]
    fn test_the_wrapping_rows_wrap() {
        let wrapped: Vec<u64> = WAT_INITIALIZED_ROWS
            .iter()
            .map(|(_, a, d)| a.wrapping_add(*d))
            .collect();
        assert_eq!(wrapped[2], 0);
        assert_eq!(wrapped[3], 0);
        assert_eq!(wrapped[4], u64::MAX - 1);
        assert_eq!(wrapped[6], 0x1234_5678_9abc_df00);
    }
}
