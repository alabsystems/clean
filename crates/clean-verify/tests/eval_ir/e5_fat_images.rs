// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal E5** (decision memo `docs/handoff/2026-09-23-crystal-decision-memo.md` §23): the
//! wide-pointer kinds, typed metadata, the vtable image and the refused wide `icmp`, measured
//! against trust-ir's REFERENCE INTERPRETER on real bodies of the m0off callee sidecar.
//!
//! The fixture `tests/fixtures/e5/e5_m0off_slices.trust-ir.txt` holds four slices of real bodies
//! -- `Environment::get_const`'s D14 read, the `Arc<str>` deref and the `Arc::ptr_eq` fast path of
//! `<Name as PartialEq>::eq`, and `<NameInner as Clone>::clone`'s container-length data read --
//! verbatim instruction lines put in trust-ir's own canonical form, beside SYNTHETIC drivers that
//! give the reference interpreter a buffer of markers and a vtable. Three legs over one fixture:
//!
//! * **E2**, the reference: every driver is RUN by `trust_ir::interpret`, and what it returns is
//!   the answer the other two legs must reproduce -- read off the run, never typed here.
//! * **Readers A and B**: the committed cores (`*.core.txt`) are what the projector
//!   (`scripts/crystal_a2_project`, reader A) made of each slice, reading the fixture's binary
//!   encoding `e5_m0off_slices.trust-ir.bin` (the projector reads trust-ir binary only; its own
//!   test binds that binary to this text through trust-ir's canonical printer); Clean's own text
//!   reader (`ir_mint`, reader B) must read the same slice to the same core.
//! * **E1**, EvalIR: each committed core is MINTED (`ir_mint::mint`) and registered, and the
//!   kernel RUNS the machine on it (`ir_eval .. = ..` by `Eq.refl`) to the answer E2 computed --
//!   every slice but the whole D14 one, whose `0 - align` mask would cost the kernel ~2^63
//!   subtraction steps in `ir_nat_bitop_go`; its two halves (the vtable read and the rebuild) are
//!   run instead. A wrong answer -- another slot, another vtable, an answer where the reference
//!   refuses, a read over a heap with no image -- is registered too and must be REJECTED, so the
//!   agreement is not vacuous.

use clean_kernel::Name;
use clean_verify::ir_mint::{self, SelfFunc};
use clean_verify::spec::{Specification, E5_NAMES};
use clean_verify::test_utils::build_eval_ir_spec_with_stack;
use clean_verify::vacuity_firewall::env_knows;
use trust_ir::interpret::{InterpretErrorCode, InterpretValueKind, Interpreter};

const FIXTURE: &str = include_str!("../fixtures/e5/e5_m0off_slices.trust-ir.txt");

/// `(slice function, committed reader-A core, the crate struct ids its core's first-use indices
/// name, in order)`.
const SLICES: &[(&str, &str, &[u32])] = &[
    (
        "e5::get_const_d14",
        include_str!("../fixtures/e5/e5_get_const_d14.core.txt"),
        &[53],
    ),
    (
        "e5::get_const_vtable_read",
        include_str!("../fixtures/e5/e5_get_const_vtable_read.core.txt"),
        &[53],
    ),
    (
        "e5::get_const_rebuild",
        include_str!("../fixtures/e5/e5_get_const_rebuild.core.txt"),
        &[],
    ),
    (
        "e5::name_eq_arc_str_deref",
        include_str!("../fixtures/e5/e5_name_eq_arc_str_deref.core.txt"),
        &[90],
    ),
    (
        "e5::name_eq_ptr_eq",
        include_str!("../fixtures/e5/e5_name_eq_ptr_eq.core.txt"),
        &[90],
    ),
    (
        "e5::nameinner_clone_data",
        include_str!("../fixtures/e5/e5_nameinner_clone_data.core.txt"),
        &[90, 78],
    ),
];

/// The marker base the drivers write at byte offset 0 of their buffer (`0x1000 + offset`).
const MARKER_BASE: u128 = 0x1000;

/// What one E2 driver returned: an integer, a Bool, or a type error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum E2 {
    Int(u128),
    Bool(bool),
    TypeError,
}

fn e2_runs() -> Vec<(String, E2)> {
    let module = trust_ir::parser::parse_module(FIXTURE).expect("the E5 fixture parses");
    let interp = Interpreter::with_module(&module);
    let mut out = Vec::new();
    for f in module
        .functions
        .iter()
        .filter(|f| f.name.contains("::drive_"))
    {
        let got = match interp.execute_function(f, Vec::new()) {
            Ok(o) => match o.returns.as_slice() {
                [v] => match v.kind {
                    InterpretValueKind::Int(i) => E2::Int(i.raw),
                    InterpretValueKind::Bool(b) => E2::Bool(b),
                    ref other => panic!("{}: returned {other:?}", f.name),
                },
                other => panic!("{}: returned {other:?}", f.name),
            },
            Err(e) if e.code == InterpretErrorCode::TypeError => E2::TypeError,
            Err(e) => panic!("{}: {:?} {}", f.name, e.code, e.message),
        };
        out.push((f.name.clone(), got));
    }
    out
}

fn e2(runs: &[(String, E2)], driver: &str) -> E2 {
    runs.iter()
        .find(|(n, _)| n == driver)
        .map(|(_, v)| *v)
        .unwrap_or_else(|| panic!("no E2 run for {driver}"))
}

/// A byte offset from a marker the reference loaded.
fn offset_of(v: E2) -> u128 {
    match v {
        E2::Int(m) => m.checked_sub(MARKER_BASE).expect("a marker"),
        E2::Bool(b) => panic!("expected a marker, got Bool({b})"),
        E2::TypeError => panic!("expected a marker, got a type error"),
    }
}

/// E2: the reference interpreter, on the real slices. These are the MEASURED answers; E1 below
/// is held to them.
#[test]
fn e5_reference_interpreter_runs_the_real_slices() {
    let runs = e2_runs();
    assert_eq!(runs.len(), 13, "{runs:?}");
    // D14 whole: round_up(16, align) with the align LOADED from vtable slot 2 (+16) ...
    assert_eq!(offset_of(e2(&runs, "e5::drive_d14_align8")), 16);
    assert_eq!(offset_of(e2(&runs, "e5::drive_d14_align16")), 16);
    assert_eq!(offset_of(e2(&runs, "e5::drive_d14_align32")), 32);
    // ... its two halves: the vtable read returns slot 2's word, and the rebuild keeps the data
    // pointer it is given and the vtable it is given (read back through the new trait object).
    for align in [8u128, 16, 32] {
        assert_eq!(
            e2(&runs, &format!("e5::drive_vtable_read_align{align}")),
            E2::Int(align)
        );
    }
    assert_eq!(offset_of(e2(&runs, "e5::drive_rebuild_data")), 16);
    assert_eq!(e2(&runs, "e5::drive_rebuild_vtable_align"), E2::Int(16));
    // `Arc<str>` deref: the str starts 16 bytes into the ArcInner, and its length is the
    // container pointer's metadata.
    assert_eq!(offset_of(e2(&runs, "e5::drive_arc_str_data")), 16);
    assert_eq!(e2(&runs, "e5::drive_arc_str_len"), E2::Int(5));
    // NameInner::clone's data read: the container header itself.
    assert_eq!(offset_of(e2(&runs, "e5::drive_nameinner_clone_data")), 0);
    // The reference refuses the wide-pointer comparison but computes the thin
    // control as an actual Bool, never an integer encoding.
    assert_eq!(e2(&runs, "e5::drive_ptr_eq"), E2::TypeError);
    assert_eq!(e2(&runs, "e5::drive_control_thin_icmp"), E2::Bool(true));
}

/// The canonical text of one function of the fixture, from its `fn` header to its closing brace.
fn function_text(name: &str) -> String {
    let header = format!("fn @\"{name}\"(");
    let at = FIXTURE
        .find(&header)
        .unwrap_or_else(|| panic!("{name} not in the fixture"));
    let end = FIXTURE[at..].find("\n}\n").expect("a closing brace") + at + 3;
    FIXTURE[at..end].to_string()
}

/// Readers A and B agree on every slice: Clean's text reader reads the fixture to the core the
/// projector committed.
#[test]
fn e5_reader_b_reads_each_slice_as_reader_a_projected_it() {
    for (name, core_a, _) in SLICES {
        let (core_b, _) =
            ir_mint::read_emitted_with_pins(&function_text(name), SelfFunc::Unpinned, Some(64))
                .unwrap_or_else(|e| panic!("reader B refuses {name}: {e}"));
        let printed = ir_mint::print(&core_b).expect("a core prints");
        assert_eq!(&printed, core_a, "{name}: reader B disagrees with reader A");
    }
    // The images this slice set exists for, present in the committed cores.
    let all: String = SLICES.iter().map(|(_, c, _)| *c).collect();
    for image in [
        "(extractfield (containervtable) ",
        "(ptrmetadata (containervtable) (ptr) ",
        "(load (uint 64) ",
        "(ptrfromparts (fatdyn 265360036) (ptr) ",
        "(copy (fatdyn 265360036) ",
        "(ptrdata (containerlen) ",
        "(ptrmetadata (containerlen) (uint 64) ",
        "(icmp eq (containerlen) ",
    ] {
        assert!(all.contains(image), "no committed core carries `{image}`");
    }
}

/// The E5 stage: registered, and resting on nothing.
#[test]
fn e5_stage_is_registered_with_an_empty_axiom_closure() {
    let spec = build_eval_ir_spec_with_stack();
    for name in E5_NAMES {
        assert!(env_knows(spec.env(), name), "{name} is not registered");
        let key = Name::from_string(name);
        let domain = spec
            .env()
            .axiom_deps(&key)
            .unwrap_or_else(|| panic!("{name} has no constant entry"));
        let foundational = spec
            .env()
            .foundational_axiom_deps(&key)
            .unwrap_or_else(|| panic!("{name} has no constant entry"));
        assert!(
            domain.is_empty() && foundational.is_empty(),
            "{name} rests on {domain:?} / {foundational:?}"
        );
    }
}

/// Mint a committed core under `prefix` with the struct lane `structs`, and register it.
fn register_slice(spec: &mut Specification, prefix: &str, core: &str, structs: &[u32]) {
    let rows: Vec<String> = structs
        .iter()
        .enumerate()
        .map(|(k, id)| {
            format!(r#"{{"canonical": {k}, "crate_id": {id}, "alias": "{prefix}_s{k}"}}"#)
        })
        .collect();
    // The mint reads the aggregate aliases and the (empty) callee lane; the table's `body` and
    // `interface` are required by its parser and pinned to what the fixture's header prints: the
    // default linkage and calling convention, and no producer clause.
    let tags = ir_mint::tags::parse(&format!(
        r#"{{"body": "{prefix}", "enums": [], "structs": [{}], "funcs": [],
            "interface": {{"linkage": "{}", "calling_conv": "{}", "functy": 0,
                           "producer": null, "params": [], "block_params": [],
                           "aligns": [], "clauses": []}}}}"#,
        rows.join(", "),
        ir_mint::DEFAULT_LINKAGE,
        ir_mint::DEFAULT_CALLING_CONV
    ))
    .expect("the slice's tag table parses");
    let sx = ir_mint::parse(core).expect("a committed core parses");
    let script = ir_mint::mint(&sx, prefix, &tags)
        .unwrap_or_else(|e| panic!("{prefix}: mint refuses: {e}"))
        .text();
    for line in script.lines().map(str::trim).filter(|l| !l.is_empty()) {
        spec.add_recursive_def(line, "crystal E5 test: a minted slice")
            .unwrap_or_else(|e| panic!("{prefix}: `{line}` does not register: {e}"));
    }
}

/// `ir_eval <fuel> <module> ir_d0 <args> <heap> ir_d0 = <expected>`, by `Eq.refl`: the kernel runs
/// the machine.
fn run_claim(name: &str, module: &str, args: &str, heap: &str, expected: &str) -> String {
    format!(
        "def {name} : Eq IROutcome (ir_eval ir_d40 {module} ir_d0 {args} {heap} ir_d0) {expected} \
         := Eq.refl IROutcome {expected}"
    )
}

/// The wide value `NonNull { pointer: fat(d, m) }`, the struct a slice's parameter carries.
fn nonnull(d: u128, m: u128) -> String {
    format!("(IRScalar.aggv (IRScalar.vcons (IRScalar.fat_ {d} {m}) IRScalar.vnil))")
}

fn one(v: &str) -> String {
    format!("(IRList.cons IRScalar {v} (IRList.nil IRScalar))")
}

/// The data address and the vtable address of the E1 runs; the heap holds only the vtable image.
const DATA: u128 = 200;
const VTABLE: u128 = 100;

/// E1: EvalIR runs every minted slice to the answer E2 computed, and refuses each near miss.
#[test]
fn e5_evalir_runs_each_minted_slice_to_the_reference_answer() {
    let runs = e2_runs();
    let mut spec = build_eval_ir_spec_with_stack();
    let prefixes = [
        "ir_e5t_d14",
        "ir_e5t_vtr",
        "ir_e5t_rb",
        "ir_e5t_str",
        "ir_e5t_eq",
        "ir_e5t_ni",
    ];
    for ((_, core, structs), prefix) in SLICES.iter().zip(prefixes) {
        register_slice(&mut spec, prefix, core, structs);
    }
    let empty = "(IRList.nil IRMemSlot)";
    let mut accept: Vec<String> = Vec::new();
    let mut reject: Vec<(String, &str)> = Vec::new();

    // D14 over `Arc<dyn ConstantSource>` = `{ NonNull { fat(data, vtable) }, PhantomData, Global }`,
    // with the vtable IMAGE in the heap at VTABLE: [drop = null, size = 24, align]. The WHOLE slice
    // is not run here, and that is a measured cost, not a gap in the image: its round-up masks
    // with `0 - align`, a word near 2^64, and EvalIR's bitwise AND halves its operands by
    // repeated subtraction (`ir_nat_bitop_go` -> `ir_nat_div x 2`), so the kernel would take
    // ~2^63 steps. Its two halves ARE run: the vtable read (every E5 construct but the rebuild)
    // and the rebuild; the arithmetic between them is EvalIR's existing wrapping binops.
    let arc = format!(
        "(IRScalar.aggv (IRScalar.vcons {} (IRScalar.vcons (IRScalar.aggv IRScalar.vnil) \
         (IRScalar.vcons (IRScalar.aggv IRScalar.vnil) IRScalar.vnil))))",
        nonnull(DATA, VTABLE)
    );
    for align in [8u128, 16, 32] {
        let E2::Int(word) = e2(&runs, &format!("e5::drive_vtable_read_align{align}")) else {
            panic!("the vtable read returns an integer")
        };
        let heap = format!(
            "(ir_vtable_cells {VTABLE} IRScalar.nullptr_ 24 {align} (IRList.nil IRScalar))"
        );
        accept.push(run_claim(
            &format!("ir_e5t_vtable_read_align{align}"),
            "ir_e5t_vtr_module",
            &one(&arc),
            &heap,
            &format!(
                "(IROutcome.ret {})",
                one(&format!("(IRScalar.int_ {word})"))
            ),
        ));
        reject.push((
            run_claim(
                &format!("ir_e5t_vtable_read_align{align}_size"),
                "ir_e5t_vtr_module",
                &one(&arc),
                &heap,
                &format!("(IROutcome.ret {})", one("(IRScalar.int_ 24)")),
            ),
            "the size slot where the align slot is read",
        ));
    }
    // Without the image the align word is not there: the load halts, never guesses.
    reject.push((
        run_claim(
            "ir_e5t_vtable_read_no_image",
            "ir_e5t_vtr_module",
            &one(&arc),
            empty,
            &format!("(IROutcome.ret {})", one("(IRScalar.int_ 16)")),
        ),
        "a vtable read over a heap with no image",
    ));
    // The rebuild: the new trait object is (the data pointer given, the SAME vtable).
    let rb_off = offset_of(e2(&runs, "e5::drive_rebuild_data"));
    assert_eq!(e2(&runs, "e5::drive_rebuild_vtable_align"), E2::Int(16));
    let rb_args = format!(
        "(IRList.cons IRScalar (IRScalar.ptr_ {}) {})",
        DATA + 16,
        one(&format!("(IRScalar.ptr_ {VTABLE})"))
    );
    accept.push(run_claim(
        "ir_e5t_rebuild",
        "ir_e5t_rb_module",
        &rb_args,
        empty,
        &format!(
            "(IROutcome.ret {})",
            one(&format!("(IRScalar.fat_ {} {VTABLE})", DATA + rb_off))
        ),
    ));
    reject.push((
        run_claim(
            "ir_e5t_rebuild_other_vtable",
            "ir_e5t_rb_module",
            &rb_args,
            empty,
            &format!(
                "(IROutcome.ret {})",
                one(&format!("(IRScalar.fat_ {} {})", DATA + rb_off, VTABLE + 8))
            ),
        ),
        "a rebuilt trait object over another vtable",
    ));

    // `Arc<str>` deref: the str is (data + 16, len).
    let str_off = offset_of(e2(&runs, "e5::drive_arc_str_data"));
    let E2::Int(len) = e2(&runs, "e5::drive_arc_str_len") else {
        panic!("the str length is an integer")
    };
    accept.push(run_claim(
        "ir_e5t_str_deref",
        "ir_e5t_str_module",
        &one(&nonnull(DATA, len)),
        empty,
        &format!(
            "(IROutcome.ret {})",
            one(&format!("(IRScalar.fat_ {} {len})", DATA + str_off))
        ),
    ));

    // `icmp eq` on the container pointers: a type error, as in the reference.
    assert_eq!(e2(&runs, "e5::drive_ptr_eq"), E2::TypeError);
    let fat = nonnull(DATA, len);
    accept.push(run_claim(
        "ir_e5t_ptr_eq_refused",
        "ir_e5t_eq_module",
        &format!("(IRList.cons IRScalar {fat} {})", one(&fat)),
        empty,
        "(IROutcome.type_error IRFault.not_int)",
    ));
    reject.push((
        run_claim(
            "ir_e5t_ptr_eq_answers",
            "ir_e5t_eq_module",
            &format!("(IRList.cons IRScalar {fat} {})", one(&fat)),
            empty,
            &format!("(IROutcome.ret {})", one("(IRScalar.bool_ Bool.true)")),
        ),
        "an answer where the reference refuses",
    ));

    // NameInner::clone's data read: the header address itself.
    let ni_off = offset_of(e2(&runs, "e5::drive_nameinner_clone_data"));
    accept.push(run_claim(
        "ir_e5t_nameinner_data",
        "ir_e5t_ni_module",
        &one(&nonnull(DATA, 3)),
        empty,
        &format!(
            "(IROutcome.ret {})",
            one(&format!("(IRScalar.ptr_ {})", DATA + ni_off))
        ),
    ));

    for claim in &accept {
        let t = std::time::Instant::now();
        spec.add_recursive_def(
            claim,
            "crystal E5 test: an EvalIR run held to the reference",
        )
        .unwrap_or_else(|e| panic!("EvalIR does not reach the reference's answer:\n{claim}\n{e}"));
        eprintln!(
            "e5 E1 accepted in {:.3}s: {}",
            t.elapsed().as_secs_f64(),
            &claim[..60.min(claim.len())]
        );
    }
    for (claim, what) in &reject {
        let t = std::time::Instant::now();
        assert!(
            spec.add_recursive_def(claim, "crystal E5 test: a near miss that must be rejected")
                .is_err(),
            "the kernel ACCEPTED {what}, so the agreement above is vacuous:\n{claim}"
        );
        eprintln!(
            "e5 E1 rejected in {:.3}s: {what}",
            t.elapsed().as_secs_f64()
        );
    }
}
