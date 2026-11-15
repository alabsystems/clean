// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A2 — the MINT gate for `ir_its`, the FIRST chain cut from a body of
//! `TypeChecker::infer_type`'s DERIVED CLOSURE.**
//!
//! Same three readers and the same questions as `crystal_a2_mint.rs`; read that
//! file's header and `src/ir_mint/mod.rs` for what this establishes and what it
//! does not.
//!
//! **This file closes a residual that was stated when `ir_its` landed.** A4 and
//! A5 (`eval_ir_its.rs`, clean `3acce3947`) were registered with the module
//! header saying, in as many words, that the three-reader gate did not exist and
//! that the core module's fidelity therefore rested on reader A plus a HAND
//! reading of the emitted text — and that a hand reading is not a gate. It is a
//! gate now.
//!
//! # What is new in kind here
//!
//! * **The first chain whose dump is not the crate module** -- and this one held
//!   up under the gate. Every earlier core
//!   is cut from `clean_kernel.trust-ir.bin`; this one is function index 102 of
//!   `dump-infertype-O3-part/callees/clean_kernel.callees.trust-ir.bin`, the
//!   callee sidecar's partial bundle for `infer_type`.
//! * **Two `usize` sites, pinned through the tag table.** NOT the first -- an
//!   earlier draft of this header and of `eval_ir_its.rs` said "the first `usize`
//!   in a committed core module" and that is false (`ir_ni` has `sites: 1`,
//!   `ir_lzd` has `isize_sites: 2`). **Writing this gate is what found it**: both
//!   readers refuse `usize` without a pinned width, `a2project` via
//!   `--usize-bits` and reader B via the tag table's `usize` lane, and reader B
//!   refused this fixture outright until that lane existed. So the "first"
//!   claim, and the claim that reader A and the emitted text agreed, were both
//!   made about a body reader B had never read. That is the difference between a
//!   hand reading and a gate, measured on this chain.
//! * **The first body with NO calling-convention keyword** in its header, where
//!   every crate-module chain prints `rustcc`, and the first whose `#producer`
//!   says `trust-ir` rather than `trust`. Both are the sidecar lane showing
//!   through — these bodies are derived from monomorphized upstream MIR, not
//!   lowered from this crate's THIR — and both are pinned by M7/M10 so a body
//!   that drifted back to the crate lane would be refused here.
//! * **The first minted `copy`.** It is not decoration: a transcription that
//!   dropped it would answer 2 and take two steps, and `ir_its_exact` pins three.
//!
//! # What this gate does NOT establish
//!
//! That the body is interesting. It is the smallest body in a 2,388-function
//! bundle and deliberately the easiest one there. What the gate establishes is
//! that the term A4 and A5 are about IS the emitted body, by three readers that
//! do not share a path.

use clean_verify::ir_mint::{self, SelfFunc, Sx};

const PREFIX: &str = "ir_its";
const MODULE_CONST: &str = "ir_its_module";
// Reader B's input lives beside reader A's projection in `generated/`, NOT in
// `tests/fixtures/`, and that is a DELIBERATE deviation with a structural
// reason rather than a convenience.
//
// `crystal-fixture-pins` requires every `tests/fixtures/*.trust-ir.txt` to carry
// a row in the current rebaseline record, so a fixture cannot "arrive
// uncompared". The sanctioned way to add one is a `chain_additions` entry in a
// NEW rebaseline — and chain 18's own `reason` states that record's premise:
// "two new fixtures pinned byte-exactly from this dump; every retained fixture
// is byte-identical to the SAME dump (strict freshness exit 0)".
//
// That premise cannot hold here. Every other fixture is cut from the crate
// module's dump; this body is cut from the callee sidecar's partial bundle for
// `infer_type`, a SECOND dump which contains none of them. Minting a rebaseline
// that declared this addition would have to assert strict freshness over
// retained fixtures against a dump they do not appear in.
//
// So the fixture-pin gate keeps its invariant over `tests/fixtures/` COMPLETELY
// UNCHANGED, and the property it protects — a committed reader-B input traceable
// to a recorded dump measurement — is carried here by a stronger, chain-local
// pair: `ir_its.core.prov.json` names the dump path and its sha256, and M2 below
// proves reader A and reader B agree about the body. What would retire the
// deviation is a fixture-pin record that admits MORE THAN ONE dump; that is an
// owner decision and is catalogued in docs/JUSTIFIED_EXCEPTIONS.md.
const FIXTURE: &str = include_str!("../src/spec/core_spec/generated/ir_its.emitted.txt");

fn tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_ITS_TAGS).expect("the committed tag table must parse")
}

fn core_a() -> Sx {
    ir_mint::parse(ir_mint::IR_ITS_CORE).expect("the committed core module must parse")
}

fn core_b() -> Sx {
    // Reader B resolves `usize` through the tag table's pin, exactly as `ir_ni`
    // does. A bare `read_emitted` REFUSES this body -- see
    // `m9_reader_b_refuses_usize_without_a_pin`, which is the arm that found the
    // gap: until this gate existed, "reader A and the emitted text agree" was a
    // HAND reading, and reader B had never read the fixture at all.
    ir_mint::read_emitted_with_pins(FIXTURE, SelfFunc::Unpinned, Some(64))
        .expect("reader B must read the committed emitted trust-ir under the pin")
        .0
}

fn canon(sx: &Sx) -> String {
    ir_mint::print(sx).expect("a core module must print")
}

// ────────────────────────────────────────────────────────────────────────────
// M1 — the committed core is canonical, and it is THIS body.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m1_committed_core_round_trips_its_printer() {
    let a = core_a();
    assert_eq!(
        canon(&a),
        ir_mint::IR_ITS_CORE,
        "the committed core module is not what its own canonical printer produces"
    );
    let text = ir_mint::IR_ITS_CORE;
    assert!(
        text.contains("(const (uint 64) (int 2))"),
        "the committed core must carry the array length as a width-64 constant — the `usize` \
         resolved under the pinned target width:\n{text}"
    );
    assert!(
        text.contains("(copy (uint 64) 0)"),
        "and the COPY, which is not decoration: without it the body is two steps, and \
         ir_its_exact pins three:\n{text}"
    );
    assert!(
        text.contains("(ret (vals 1))"),
        "and the return of the copy, not of the constant:\n{text}"
    );
    assert!(
        !text.contains("(switch") && !text.contains("(condbr") && !text.contains("(call "),
        "one block, no control flow, no call — which is why A4 needs no activation induction"
    );
    assert!(
        text.contains("(params)\n      (entry 0)"),
        "and ZERO function parameters — the emptiness is the pin, and it is what lets A4 \
         quantify over nothing but the heap and the fuel:\n{text}"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M2 — reader B equals reader A, EXACTLY: empty ledger.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m2_reader_b_equals_reader_a_with_an_empty_ledger() {
    let (masked, ledger) =
        ir_mint::mask_text_unwitnessed(&core_a()).expect("reader A's module must mask");
    assert_eq!(
        canon(&masked),
        canon(&core_b()),
        "the artifact BINARY (reader A, via a2project over the infer_type callee bundle) and \
         the emitted TEXT (reader B) disagree about this body. Until this file existed, that \
         agreement was a HAND reading."
    );
    assert!(
        ledger.is_empty(),
        "no `switch` means no unwitnessed slot — the emitted text fully determines the core \
         module: {ledger:?}"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M3 — `mint` of the committed core IS the committed, registered script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m3_mint_reproduces_the_registered_script() {
    let minted = ir_mint::mint(&core_a(), PREFIX, &tags())
        .expect("mint")
        .text();
    assert_eq!(
        minted,
        ir_mint::IR_ITS_DEFS,
        "minting the committed core does not reproduce the committed script that \
         `eval_ir_its.rs` replays — so the three lines A4 and A5 are proved over are not the \
         lines this core mints to"
    );
    assert_eq!(
        minted.lines().filter(|l| !l.trim().is_empty()).count(),
        3,
        "three definitions: the block, the function, the module"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M4 — reader C: the ELABORATED term decodes back to the committed core.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m4_the_registered_kernel_term_decodes_to_the_committed_core() {
    let spec = clean_verify::test_utils::shared_spec();
    let decoded = ir_mint::decode(spec.env(), MODULE_CONST, &tags()).expect("decode ir_its_module");
    assert_eq!(
        canon(&decoded),
        ir_mint::IR_ITS_CORE,
        "the ELABORATED term registered under `{MODULE_CONST}` does not decode to the committed \
         core module. This is the check that keeps `mint` out of the trusted base: reader C \
         never sees the minter's output, and it is what makes A4/A5 theorems about the EMITTED \
         body rather than about whatever the minter happened to write."
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M7 — the tag table still matches the artifact.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m7_the_tag_table_still_matches_the_artifact() {
    assert!(
        FIXTURE.contains("(functy.110)"),
        "the emitted body must still carry signature index 110; if it does not, the artifact \
         was re-interned and this table needs a one-line REVIEWED re-pin"
    );
    assert!(
        ir_mint::IR_ITS_TAGS.contains("\"functy\": 110"),
        "and the committed table must record it"
    );
    assert!(
        !FIXTURE.contains("enum.") && !FIXTURE.contains("struct."),
        "this body names no aggregate; the empty enums/structs lanes are a measurement"
    );
    assert!(
        !FIXTURE.contains("call "),
        "and it calls nothing, which is what makes the empty `funcs` lane admissible"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M9 — the `usize` resolution is RECORDED, with its site count, not assumed.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m9_reader_b_refuses_usize_without_a_pin() {
    let e = ir_mint::read_emitted(FIXTURE)
        .map(|_| ())
        .expect_err("reader B must REFUSE `usize` when no width is pinned");
    let msg = format!("{e}");
    assert!(
        msg.contains("TARGET-DEPENDENT"),
        "and the refusal must say why rather than merely failing: {msg}"
    );
}

#[test]
fn m9_the_target_width_is_recorded_rather_than_assumed() {
    assert!(
        FIXTURE.contains("const usize 2"),
        "the emitted text says `usize`, not a fixed width — which is the whole reason \
         a2project refuses to project this body without being told the target"
    );
    assert!(
        ir_mint::IR_ITS_PROVENANCE.contains("\"usize_bits\": 64"),
        "reader A must RECORD the width it was given"
    );
    assert!(
        ir_mint::IR_ITS_PROVENANCE.contains("\"usize_sites_resolved\": 2"),
        "and how many sites it resolved with it — 2 here, the const and the copy. A recorded \
         count is what makes a silently-changed width visible."
    );
    assert!(
        ir_mint::IR_ITS_TAGS.contains("\"sites\": 2"),
        "and the tag table's `usize` lane must pin the SITE COUNT -- two here, the const and \
         the copy. The count is what catches a u64-for-usize swap, which the resolved core \
         text cannot: both spell (uint 64)."
    );
    assert!(
        ir_mint::IR_ITS_TAGS.contains("erasure_note"),
        "and it must say out loud what the resolution erases"
    );
    assert!(
        ir_mint::IR_ITS_CORE.contains("(uint 64)"),
        "and the committed core must be the RESOLVED form, so nothing downstream re-decides it"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M11 — the SIDECAR LANE's two interface differences are pinned.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m11_the_sidecar_lane_interface_is_pinned() {
    assert!(
        FIXTURE.starts_with("fn @"),
        "this body's header carries NO calling-convention keyword, where every crate-module \
         chain prints `rustcc`. A body that drifted back to the crate lane would start \
         `rustcc fn @` and must be refused here:\n{FIXTURE}"
    );
    assert!(
        FIXTURE.contains("; #producer: trust-ir"),
        "and its producer stamp is `trust-ir`, not `trust` — the sidecar bundle's own"
    );
    assert!(
        ir_mint::IR_ITS_TAGS.contains("\"calling_conv\": \"ccc\"")
            && ir_mint::IR_ITS_TAGS.contains("\"producer\": \"trust-ir\""),
        "and the committed table must pin both, so the difference is a claim rather than an \
         accident nobody wrote down"
    );
    assert!(
        ir_mint::IR_ITS_PROVENANCE.contains("dump-infertype-O3-part"),
        "reader A must record that the dump is the infer_type callee bundle and not the crate \
         module — the provenance IS the point of this chain"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M8 — the mint DISCRIMINATES: a one-token counterfactual is a different core.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m8_the_mint_discriminates_a_one_token_counterfactual() {
    // A body that returns the CONSTANT instead of the COPY: same answer, one
    // fewer step. If the mint could not see the difference, `ir_its_exact`'s
    // three-step pin would be proving something about a body we did not emit.
    let twin = FIXTURE.replace("ret %1", "ret %0");
    let b = ir_mint::read_emitted_with_pins(&twin, SelfFunc::Unpinned, Some(64))
        .expect("the counterfactual must still read under the pin")
        .0;
    assert_ne!(
        canon(&b),
        canon(&core_b()),
        "returning the constant rather than the copy must produce a DIFFERENT core module"
    );

    // And a body whose array length is 4 rather than 2.
    let wider = FIXTURE.replace("const usize 2", "const usize 4");
    let w = ir_mint::read_emitted_with_pins(&wider, SelfFunc::Unpinned, Some(64))
        .expect("the wider twin must still read under the pin")
        .0;
    assert_ne!(
        canon(&w),
        canon(&core_b()),
        "a `[Level; 4]` backing array must produce a DIFFERENT core module — otherwise \
         `smallvec_level2_array_size` would be silently reusable for a type it is false of"
    );
}
