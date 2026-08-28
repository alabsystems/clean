// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A2 — the MINT gate for the `bvar_in_range` chain,
//! `expr::bvar_in_range`.**
//!
//! Same three readers and the same questions as `crystal_a2_mint.rs`; read
//! that file's header and `src/ir_mint/mod.rs` for what this establishes and
//! what it does not. This is the ELEVENTH chain the mint machinery covers and
//! the FIFTH complete chain of the crystal, migrated off its hand
//! transcription on 2026-08-21 — the first minted body that BRANCHES on a
//! value it computed.
//!
//! **The migration diff, printed before adoption** (the rule the flagship's
//! wrong exhaustive flag made mandatory: a divergence is a FINDING): FIVE of
//! the nine lines diverged, TWO notation classes, both definitionally equal —
//! `ir_br_b0`/`b1`/`b2`/`b4` inline `(IRTy.uint_ 32)` where the hand lines
//! named `ir_br_tu32` (which deltas to `IRTy.uint_ ir_d32`, and `ir_d32`
//! computes to the literal 32), and `ir_br_func` spells its three-parameter
//! list as the raw `IRList.cons Nat` spine where the hand line named `ir_nl3`
//! (which deltas to exactly that spine). `ir_br_b3`, `ir_br_b5`, `ir_br_b6`
//! and `ir_br_module` minted byte-identical. NO semantic divergence; every
//! downstream `ir_br_*` theorem kept proving unchanged, the four path
//! witnesses and five concrete executions included.
//!
//! **What is new here relative to the ten earlier minted chains:**
//!
//! * The first minted body with a `condbr` — two of them, nested, which is
//!   the lane the A1 comparator gained for this chain in the first place.
//!   Both are fully printed by the emitted text, so the unwitnessed ledger is
//!   EMPTY: the float-tranche posture, reached for the first time by a body
//!   with control flow.
//! * The first minted chain whose width renders as a LITERAL: 32 is outside
//!   the `ir_d0..ir_d16` atom pool, so `mint` spells `(IRTy.uint_ 32)` where
//!   `ir_ko` spells `(IRTy.uint_ ir_d8)` — `nat_data`'s other arm, pinned by
//!   M3's byte-equality below.
//! * Three by-value integer parameters — the widest interface params lane yet
//!   pinned, and the slot a `u16`/`u64` twin (same CFG, different function)
//!   would hide in.

use clean_verify::ir_mint::{self, Sx};

#[allow(dead_code)]
#[path = "crystal_a1_lineage/emitted_cfg.rs"]
mod emitted_cfg;

use emitted_cfg::{assert_lanes, parse_clean, parse_emitted};

const PREFIX: &str = "ir_br";
const MODULE_CONST: &str = "ir_br_module";
const FIXTURE: &str = include_str!("fixtures/bvar_in_range.trust-ir.txt");

fn tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_BR_TAGS).expect("the committed tag table must parse")
}

fn core_a() -> Sx {
    ir_mint::parse(ir_mint::IR_BR_CORE).expect("the committed core module must parse")
}

fn core_b() -> Sx {
    ir_mint::read_emitted(FIXTURE).expect("reader B must read the committed emitted trust-ir")
}

fn canon(sx: &Sx) -> String {
    ir_mint::print(sx).expect("a core module must print")
}

// ────────────────────────────────────────────────────────────────────────────
// M1 — the committed core is canonical, and it is the two-condbr short
// circuit.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m1_committed_core_round_trips_its_printer() {
    let a = core_a();
    assert_eq!(
        canon(&a),
        ir_mint::IR_BR_CORE,
        "the committed core module is not what its own canonical printer produces"
    );
    // COVERAGE DENOMINATOR: two empty modules round-trip too.
    let text = ir_mint::IR_BR_CORE;
    assert!(
        text.contains("(const (uint 32) (int 4294967295))"),
        "the committed core must carry the u32::MAX sentinel:\n{text}"
    );
    assert_eq!(
        text.matches("(condbr ").count(),
        2,
        "TWO conditional branches — the emitted short circuit:\n{text}"
    );
    assert_eq!(
        text.matches("(icmp ").count(),
        4,
        "four comparisons: eq, uge, uge, ult:\n{text}"
    );
    assert!(
        text.contains("(icmp eq (uint 32) 2 5)")
            && text.contains("(icmp uge (uint 32) 0 1)")
            && text.contains("(icmp ult (uint 32) 0 2)"),
        "and they are the emitted ones:\n{text}"
    );
    assert!(
        !text.contains("(switch") && !text.contains("(call "),
        "no switch and no call in this body; a core module with either is not it"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M2 — reader B (the emitted TEXT) equals reader A (the artifact BINARY),
// EXACTLY: no switch means no slot the text cannot show.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m2_reader_b_equals_reader_a_with_an_empty_ledger() {
    let (masked, ledger) =
        ir_mint::mask_text_unwitnessed(&core_a()).expect("reader A's module must mask");
    assert_eq!(
        canon(&masked),
        canon(&core_b()),
        "the artifact BINARY (reader A) and the emitted TEXT (reader B) disagree about this body"
    );
    assert!(
        ledger.is_empty(),
        "no `switch` means no unwitnessed slot — a condbr prints both targets. A non-empty \
         ledger here means the body stopped being the two-condbr shape: {ledger:?}"
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
        ir_mint::IR_BR_DEFS,
        "the committed definition script is not what `mint` produces from the committed core \
         module. The committed script is the one `eval_ir_bvar_range.rs` REGISTERS, so a \
         difference here means the proved module is again hand-edited."
    );
    assert!(
        ir_mint::IR_BR_RECORD.contains(&ir_mint::digest(&minted)),
        "the mint record's defs digest does not match the minted script"
    );
    assert!(
        ir_mint::IR_BR_RECORD.contains(&ir_mint::digest(ir_mint::IR_BR_CORE)),
        "the mint record's core digest does not match the committed core module"
    );
}

/// **`nat_data`'s LITERAL arm, pinned on a real chain.** `ir_ko` pins the pool
/// arm (`IRTy.uint_ ir_d8`); this chain is the sibling fact that a width above
/// 16 renders as a decimal literal — and that the sentinel constant stays the
/// literal the emitted `IRInst.const_` materialises, which is the whole reason
/// this chain could be registered at all (see `ir_br_c1`'s rationale).
#[test]
fn m3_the_width_and_the_sentinel_render_as_literals() {
    assert!(
        ir_mint::IR_BR_DEFS.contains("(IRTy.uint_ 32)"),
        "32 is outside ir_d0..ir_d16 and must render as the literal:\n{}",
        ir_mint::IR_BR_DEFS
    );
    assert!(
        !ir_mint::IR_BR_DEFS.contains("ir_d32"),
        "and NOT through a named width constant, which would be a different (also-elaborable) \
         spelling than the one the M3 byte-equality pins"
    );
    assert!(
        ir_mint::IR_BR_DEFS.contains("(IRConst.int_ 4294967295)"),
        "the u32::MAX sentinel is the literal the emitted body materialises:\n{}",
        ir_mint::IR_BR_DEFS
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M5 — the A1 lane comparator, unchanged, over the MINTED script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m5_the_a1_comparator_agrees_over_the_minted_script() {
    let emitted = parse_emitted(FIXTURE);
    let clean = parse_clean(ir_mint::IR_BR_DEFS, "def ir_br_b");
    assert_lanes(&emitted, &clean, "ir_br (minted)");
    assert_eq!(emitted.blocks, clean.blocks);
    assert_eq!(emitted.condbrs, clean.condbrs);
    assert_eq!(emitted.icmps, clean.icmps);
    assert_eq!(emitted.int_consts, clean.int_consts);
    assert!(
        emitted.condbrs.len() == 2 && emitted.icmps.len() == 4,
        "coverage denominator: two empty lane sets compare equal, and this body has two \
         condbrs and comparisons in four blocks"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M7 — the tag table still records the interning ids the artifact names.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m7_the_tag_table_still_matches_the_artifact() {
    assert!(
        FIXTURE.contains("fn @expr::bvar_in_range(functy.467)"),
        "the emitted body must still carry signature index 467; if it does not, the artifact \
         was re-interned and this table needs a one-line REVIEWED re-pin — which is a \
         different thing from the proved module having stopped matching"
    );
    assert!(
        ir_mint::IR_BR_TAGS.contains("\"functy\": 467"),
        "and the committed table must record it"
    );
    assert!(
        !FIXTURE.contains("enum.") && !FIXTURE.contains("struct."),
        "this body names no aggregate; the empty enums/structs lanes are a measurement"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M10 — the interface: accepted under the pin, refused one token off it.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m10_the_committed_fixture_projects_under_its_pinned_interface() {
    let p = ir_mint::project(FIXTURE, &tags())
        .unwrap_or_else(|e| panic!("the committed fixture must project: {e}"));
    let (masked, _) =
        ir_mint::mask_text_unwitnessed(&core_a()).expect("the committed core must mask");
    assert_eq!(
        canon(&p.core),
        canon(&masked),
        "projecting under the interface pin must produce the committed core (masked)"
    );
    let tys: Vec<&str> = p.interface.params.iter().map(|s| s.ty.as_str()).collect();
    assert_eq!(
        tys,
        ["u32", "u32", "u32"],
        "three by-value u32 parameters: idx, start, end"
    );
    let joins: Vec<(u32, &str)> = p
        .interface
        .block_params
        .iter()
        .map(|s| (s.block, s.ty.as_str()))
        .collect();
    assert_eq!(
        joins,
        [(3, "bool"), (6, "bool")],
        "two chained joins, both Bool — the two-join graph is the short circuit"
    );
    assert!(
        p.interface.aligns.is_empty(),
        "no memory instruction in this body"
    );
}

/// The pins BITE: a widened parameter, a widened join, a foreign calling
/// convention and a moved `functy` are each refused, and the refusal names
/// the slot. The core module alone separates NONE of the first two.
#[test]
fn m10_the_interface_pins_bite() {
    let t = tags();
    for (from, to, slot) in [
        ("%1: u32, %2: u32):", "%1: u32, %2: u64):", "parameter"),
        ("bb3(%3: bool):", "bb3(%3: u32):", "block parameter"),
        ("rustcc fn @", "ccc fn @", "calling convention"),
        ("(functy.467)", "(functy.468)", "signature index"),
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
// M8 — the mint discriminates this chain from its condbr-sibling.
// ────────────────────────────────────────────────────────────────────────────

/// `bvar_in_range` and `is_valid_char` are the only two condbr-carrying
/// chained bodies, with the same seven-block two-join skeleton; a mint that
/// keyed on the skeleton would produce one module for both. The cores must
/// differ, and the sibling's fixture must not be ACCEPTED under this chain's
/// pin — the name is the first slot the projection refuses on.
#[test]
fn m8_the_mint_discriminates_the_condbr_siblings() {
    const SIBLING: &str = include_str!("fixtures/is_valid_char.trust-ir.txt");
    let sib = ir_mint::read_emitted(SIBLING).expect("reader B must read the sibling fixture");
    assert_ne!(
        ir_mint::digest(&canon(&core_b())),
        ir_mint::digest(&canon(&sib)),
        "ir_br and the is_valid_char sibling must not share a core digest"
    );
    let e = ir_mint::project(SIBLING, &tags())
        .map(|_| ())
        .expect_err("the sibling fixture must be REFUSED under this chain's pin, never accepted");
    assert!(
        format!("{e}").contains("expr::bvar_in_range"),
        "and the refusal must name the pinned body: {e}"
    );
    assert!(
        ir_mint::IR_BR_DEFS.contains("IRICmpOp.eq_")
            && ir_mint::IR_BR_DEFS.contains("IRICmpOp.uge"),
        "bvar_in_range compares with eq and uge, which the ult-only sibling never does"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M4 — reader C: the ELABORATED KERNEL TERM decodes back to the committed
// core. The expensive check (one full Specification build), LAST.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m4_the_registered_kernel_term_decodes_to_the_committed_core() {
    let spec = clean_verify::test_utils::shared_spec();
    let decoded = ir_mint::decode(spec.env(), MODULE_CONST, &tags()).expect("decode ir_br_module");
    assert_eq!(
        canon(&decoded),
        ir_mint::IR_BR_CORE,
        "the ELABORATED term registered under `{MODULE_CONST}` does not decode to the committed \
         core module. This is the check that keeps `mint` out of the trusted base: reader C \
         never sees the minter's output — and on this chain it is also what pins that the \
         registered term's inlined `(IRTy.uint_ 32)` IS the u32 the hand alias denoted."
    );
}
