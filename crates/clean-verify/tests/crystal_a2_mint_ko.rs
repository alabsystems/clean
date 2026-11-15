// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A2 — the MINT gate for the `kind_ord` chain,
//! `level::Level::kind_ord`.**
//!
//! Same three readers and the same questions as `crystal_a2_mint.rs`; read
//! that file's header and `src/ir_mint/mod.rs` for what this establishes and
//! what it does not. This is the SEVENTH chain the mint machinery covers and
//! the second complete chain of the crystal, migrated off its hand
//! transcription on 2026-08-21.
//!
//! **The migration diff, printed before adoption** (the rule the flagship's
//! wrong exhaustive flag made mandatory: a divergence is a FINDING): SIX of
//! the ten lines diverged, all ONE notation class — the hand blocks named the
//! shared `ir_tU8` alias where the mint inlines `(IRTy.uint_ ir_d8)`, and the
//! two are definitionally equal (`ir_tU8 := IRTy.uint_ ir_d8`). The other four
//! lines (`ir_ko_tenum`, `ir_ko_b6`, `ir_ko_func`, `ir_ko_module`) minted
//! byte-identical. NO semantic divergence; every downstream `ir_ko_*` theorem
//! kept proving unchanged, the five executed arm witnesses included.
//!
//! **What is new here relative to the six earlier minted chains:**
//!
//! * The first minted chain whose unwitnessed ledger is NON-EMPTY since the
//!   flagship: the body dispatches, so `Switch.exhaustive_enum_unreachable`
//!   occurs exactly once and M2 compares under the one-entry declared mask.
//!   (The float tranche's ledgers are empty; `ir_pv` has one switch too, but
//!   this chain's committed core was cut by the gate's FIRST landing and had
//!   never been minted.)
//! * The aggregate alias exercises `mint::interning_id`'s POOL arm: `Level`
//!   was `enum.2` on all four recorded dumps and is `enum.3` since the
//!   2026-10-07 rebaseline — inside `ir_d0..ir_d16` either way — so the
//!   alias reads `IRTy.enum_ ir_d3` where `ir_pv_tprio` reads a literal
//!   `135`. M3 pins the spelling in both directions.
//! * The join block binds a `u8` — the first minted chain whose block
//!   parameter row carries an integer width, which is the M10 slot an
//!   `f32`-class twin would hide in.

use clean_verify::ir_mint::{self, Sx};

#[allow(dead_code)]
use crate::emitted_cfg;

use emitted_cfg::{assert_lanes, parse_clean, parse_emitted};

const PREFIX: &str = "ir_ko";
const MODULE_CONST: &str = "ir_ko_module";
const FIXTURE: &str = include_str!("fixtures/level_kind_ord.trust-ir.txt");

fn tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_KO_TAGS).expect("the committed tag table must parse")
}

fn core_a() -> Sx {
    ir_mint::parse(ir_mint::IR_KO_CORE).expect("the committed core module must parse")
}

fn core_b() -> Sx {
    ir_mint::read_emitted(FIXTURE).expect("reader B must read the committed emitted trust-ir")
}

fn canon(sx: &Sx) -> String {
    ir_mint::print(sx).expect("a core module must print")
}

// ────────────────────────────────────────────────────────────────────────────
// M1 — the committed core is canonical, and it is the five-answer dispatch.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m1_committed_core_round_trips_its_printer() {
    let a = core_a();
    assert_eq!(
        canon(&a),
        ir_mint::IR_KO_CORE,
        "the committed core module is not what its own canonical printer produces"
    );
    // COVERAGE DENOMINATOR: two empty modules round-trip too.
    let text = ir_mint::IR_KO_CORE;
    assert!(
        text.contains("(load (enum 0) 0 false)"),
        "the committed core must carry the receiver load:\n{text}"
    );
    assert!(
        text.contains("(extractfield (uint 8) 2 0)"),
        "and the discriminant read at field 0:\n{text}"
    );
    assert!(
        text.contains(
            "(switch 3 5 (args) (cases (case 0 1 (args)) (case 1 2 (args)) (case 2 3 (args)) \
             (case 3 4 (args))) false)"
        ),
        "and the four-case switch whose DEFAULT edge carries the reachable Param arm, \
         exhaustive flag measured FALSE:\n{text}"
    );
    for n in 0..5 {
        assert!(
            text.contains(&format!("(const (uint 8) (int {n}))")),
            "and the five distinct u8 answers, {n} included:\n{text}"
        );
    }
    assert!(
        !text.contains("(call "),
        "this body calls nothing; a core module with a call is not it"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M2 — reader B (the emitted TEXT) equals reader A (the artifact BINARY),
// modulo the declared one-entry ledger.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m2_reader_b_equals_reader_a_modulo_the_declared_ledger() {
    let (masked, ledger) =
        ir_mint::mask_text_unwitnessed(&core_a()).expect("reader A's module must mask");
    assert_eq!(
        canon(&masked),
        canon(&core_b()),
        "the artifact BINARY (reader A) and the emitted TEXT (reader B) disagree about this body"
    );
    assert_eq!(
        ledger.len(),
        1,
        "exactly one slot the emitted text cannot show: {ledger:?}"
    );
    assert_eq!(
        ledger[0].inst, "switch",
        "and it is `Switch.exhaustive_enum_unreachable`, which trust-ir's Display never prints"
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
        ir_mint::IR_KO_DEFS,
        "the committed definition script is not what `mint` produces from the committed core \
         module. The committed script is the one `eval_ir_kind_ord.rs` REGISTERS, so a \
         difference here means the proved module is again hand-edited."
    );
    assert!(
        ir_mint::IR_KO_RECORD.contains(&ir_mint::digest(&minted)),
        "the mint record's defs digest does not match the minted script"
    );
    assert!(
        ir_mint::IR_KO_RECORD.contains(&ir_mint::digest(ir_mint::IR_KO_CORE)),
        "the mint record's core digest does not match the committed core module"
    );
}

/// **`mint::interning_id`'s POOL arm, pinned on a real chain.** `ir_pv` pins
/// the literal arm (`IRTy.enum_ 127`); this chain is the sibling fact that an
/// id AT OR BELOW 16 still renders through the atom pool — which is what kept
/// every pre-`Arg::Data` artifact byte-identical when the policy split.
#[test]
fn m3_the_alias_renders_through_the_pool() {
    let lines = ir_mint::mint(&core_a(), PREFIX, &tags())
        .expect("mint")
        .lines;
    assert_eq!(
        lines.first().map(String::as_str),
        Some("def ir_ko_tenum : IRTy := IRTy.enum_ ir_d3"),
        "crate id 3 is inside ir_d0..ir_d16 and must render as `ir_d3`"
    );
    assert!(
        !ir_mint::IR_KO_DEFS.contains("IRTy.enum_ 3"),
        "and NOT as a bare literal, which would be a different (also-elaborable) spelling \
         than the one the M3 byte-equality pins"
    );
    // The width datum renders through the pool too: 8 <= 16.
    assert!(
        ir_mint::IR_KO_DEFS.contains("(IRTy.uint_ ir_d8)"),
        "the u8 width must spell ir_d8:\n{}",
        ir_mint::IR_KO_DEFS
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M5 — the A1 lane comparator, unchanged, over the MINTED script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m5_the_a1_comparator_agrees_over_the_minted_script() {
    let emitted = parse_emitted(FIXTURE);
    let clean = parse_clean(ir_mint::IR_KO_DEFS, "def ir_ko_b");
    assert_lanes(&emitted, &clean, "ir_ko (minted)");
    assert_eq!(emitted.blocks, clean.blocks);
    assert_eq!(emitted.cases, clean.cases);
    assert_eq!(emitted.default, clean.default);
    assert_eq!(emitted.int_consts, clean.int_consts);
    assert!(
        emitted.cases.len() == 4 && !emitted.int_consts.is_empty(),
        "coverage denominator: two empty lane sets compare equal, and this body has four \
         explicit cases and five integer constants"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M7 — the tag table still records the interning id the artifact names.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m7_the_tag_table_still_matches_the_artifact() {
    assert!(
        FIXTURE.contains("load enum.3, ptr %0"),
        "the emitted body must still name enum.3; if it does not, the artifact was re-interned \
         and this table needs a one-line REVIEWED re-pin — which is a different thing from the \
         proved module having stopped matching"
    );
    assert!(
        ir_mint::IR_KO_TAGS.contains("\"crate_id\": 3"),
        "and the committed table must record it"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M10 — the interface: accepted under the pin, refused one token off it.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m10_the_committed_fixture_projects_under_its_pinned_interface() {
    let p = ir_mint::project(FIXTURE, &tags())
        .unwrap_or_else(|e| panic!("the committed fixture must project: {e}"));
    // The core module is UNCHANGED by this lane: the projection is reader B's
    // core, which carries `?` in the one slot the emitted text cannot witness,
    // so it is compared against the MASKED committed core — exactly M2's
    // comparison, restated here as the claim boundary that the interface lane
    // checks the module rather than changing it.
    let (masked, _) =
        ir_mint::mask_text_unwitnessed(&core_a()).expect("the committed core must mask");
    assert_eq!(
        canon(&p.core),
        canon(&masked),
        "projecting under the interface pin must produce the committed core (masked)"
    );
    let tys: Vec<&str> = p.interface.params.iter().map(|s| s.ty.as_str()).collect();
    assert_eq!(tys, ["ptr"], "one parameter: the &Level receiver");
    let joins: Vec<(u32, &str)> = p
        .interface
        .block_params
        .iter()
        .map(|s| (s.block, s.ty.as_str()))
        .collect();
    assert_eq!(
        joins,
        [(6, "u8")],
        "the join binds a u8 — the width is the semantic payload of this row"
    );
    assert_eq!(
        p.interface.aligns,
        ["load:None"],
        "one memory instruction, the receiver load"
    );
}

/// The pins BITE: a widened join, a receiver that is not a pointer, a foreign
/// calling convention and a moved `functy` are each refused, and the refusal
/// names the slot. The core module alone separates NONE of the first two.
#[test]
fn m10_the_interface_pins_bite() {
    let t = tags();
    for (from, to, slot) in [
        ("bb6(%1: u8):", "bb6(%1: u32):", "block parameter"),
        ("bb0(%0: ptr):", "bb0(%0: f64):", "parameter"),
        ("rustcc fn @", "ccc fn @", "calling convention"),
        ("(functy.278)", "(functy.279)", "signature index"),
    ] {
        let mutated = FIXTURE.replace(from, to);
        assert_ne!(mutated, FIXTURE, "the mutation must bite: {from}");
        let e = ir_mint::project(&mutated, &t).map(|_| ()).expect_err(
            "a body whose interface is not the pinned one must be REFUSED, never accepted",
        );
        assert!(
            format!("{e}").contains(slot),
            "the refusal must name the drifted slot ({slot}): {e}"
        );
    }
}

// ────────────────────────────────────────────────────────────────────────────
// M8 — the mint discriminates this chain from its skeleton-sibling.
// ────────────────────────────────────────────────────────────────────────────

/// `has_cubical_layer` and `kind_ord` share the load/extractfield/switch/join
/// skeleton; a mint that keyed on the skeleton would produce one module for
/// both. Digests, scripts and the constant lane must all separate them.
#[test]
fn m8_the_mint_discriminates_the_skeleton_siblings() {
    assert_ne!(
        ir_mint::digest(ir_mint::IR_KO_CORE),
        ir_mint::digest(ir_mint::IR_H2_CORE),
        "ir_ko and ir_h2 must not share a core digest"
    );
    assert_ne!(ir_mint::IR_KO_DEFS, ir_mint::IR_H2_DEFS);
    assert!(
        ir_mint::IR_KO_DEFS.contains("IRConst.int_")
            && !ir_mint::IR_KO_DEFS.contains("IRConst.bool_"),
        "kind_ord answers in u8 constants"
    );
    assert!(
        ir_mint::IR_H2_DEFS.contains("IRConst.bool_")
            && !ir_mint::IR_H2_DEFS.contains("IRConst.int_"),
        "has_cubical_layer answers in Bool constants"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M4 — reader C: the ELABORATED KERNEL TERM decodes back to the committed
// core. The expensive check (one full Specification build), LAST.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m4_the_registered_kernel_term_decodes_to_the_committed_core() {
    let spec = clean_verify::test_utils::shared_spec();
    let decoded = ir_mint::decode(spec.env(), MODULE_CONST, &tags()).expect("decode ir_ko_module");
    assert_eq!(
        canon(&decoded),
        ir_mint::IR_KO_CORE,
        "the ELABORATED term registered under `{MODULE_CONST}` does not decode to the committed \
         core module. This is the check that keeps `mint` out of the trusted base: reader C \
         never sees the minter's output — and on this chain it is also what pins that the \
         registered term's inlined `(IRTy.uint_ ir_d8)` IS the u8 the hand alias denoted."
    );
}
