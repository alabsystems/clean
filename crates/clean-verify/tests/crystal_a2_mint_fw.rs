// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A2 — the MINT gate for the `with` chain,
//! `flat::types::FlatFlags::with`.**
//!
//! Same three readers and the same questions as `crystal_a2_mint.rs`; read
//! that file's header and `src/ir_mint/mod.rs` for what this establishes and
//! what it does not. This is the TENTH chain the mint machinery covers,
//! migrated off its hand transcription on 2026-08-21.
//!
//! **The migration diff, printed before adoption** (a divergence is a
//! FINDING): ONE of the four lines diverged, THREE notation classes in it,
//! all definitionally equal — `ir_fw_b0` inlines `(IRTy.uint_ ir_d8)` where
//! the hand line named `ir_tU8` (three slots), spells the template as the raw
//! `(IRConst.aggv (IRConst.vcons (IRConst.int_ ir_d0) IRConst.vnil))` spine
//! where the hand line named `ir_cvar ir_d0`, and names its OWN
//! `ir_fw_tflags` alias where the hand line borrowed the sibling chain's
//! `ir_fc_tflags` (both delta to `IRTy.struct_ 815`). `ir_fw_func` and
//! `ir_fw_module` minted byte-identical; the `ir_fw_tflags` alias line is
//! minted-only. NO semantic divergence.
//!
//! **What is new here relative to the nine earlier minted chains:**
//!
//! * The first minted chain whose STRUCT the module ITSELF names — the
//!   template `const struct.815 { 0 }` and the insertfield — so the tag
//!   table's struct row is a REAL aggregate row (its sibling `contains` pins
//!   the same crate entry interface-only), and M4 is the first read-back of a
//!   struct alias out of a registered term.
//! * The first minted chain that is NOT in the producer A/B record: its mint
//!   record states ONE reader-A dump, not three, and says so.
//! * The first minted WRITE lane: the insertfield's field index, source and
//!   value ride the shape table through M3/M4 for the first time.

use clean_verify::ir_mint::{self, Sx};

#[allow(dead_code)]
use crate::emitted_cfg;

use emitted_cfg::{assert_lanes, parse_clean, parse_emitted};

const PREFIX: &str = "ir_fw";
const MODULE_CONST: &str = "ir_fw_module";
const FIXTURE: &str = include_str!("fixtures/flat_flags_with.trust-ir.txt");

fn tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_FW_TAGS).expect("the committed tag table must parse")
}

fn core_a() -> Sx {
    ir_mint::parse(ir_mint::IR_FW_CORE).expect("the committed core module must parse")
}

fn core_b() -> Sx {
    ir_mint::read_emitted(FIXTURE).expect("reader B must read the committed emitted trust-ir")
}

fn canon(sx: &Sx) -> String {
    ir_mint::print(sx).expect("a core module must print")
}

// ────────────────────────────────────────────────────────────────────────────
// M1 — the committed core is canonical, and it is the or/template/write body.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m1_committed_core_round_trips_its_printer() {
    let a = core_a();
    assert_eq!(
        canon(&a),
        ir_mint::IR_FW_CORE,
        "the committed core module is not what its own canonical printer produces"
    );
    let text = ir_mint::IR_FW_CORE;
    assert!(
        text.contains("(extractfield (uint 8) 0 0)")
            && text.contains("(extractfield (uint 8) 1 0)"),
        "field 0 of BOTH by-value arguments:\n{text}"
    );
    assert!(
        text.contains("(binop or (uint 8) 2 3)"),
        "the OR — the sibling's graph with the read half swapped for a write half:\n{text}"
    );
    assert!(
        text.contains("(const (struct 0) (agg (int 0)))")
            && text.contains("(insertfield (struct 0) 5 0 4)"),
        "the TEMPLATE and the WRITE at field 0:\n{text}"
    );
    assert!(
        text.contains("(ret (vals 6))"),
        "the body returns the WRITTEN aggregate %6:\n{text}"
    );
    assert!(
        !text.contains("(switch ") && !text.contains("(load ") && !text.contains("(call "),
        "straight line, no memory, no callee"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M2 — reader B equals reader A EXACTLY: the ledger is empty (no switch).
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m2_reader_b_equals_reader_a_with_an_empty_ledger() {
    let (masked, ledger) =
        ir_mint::mask_text_unwitnessed(&core_a()).expect("reader A's module must mask");
    assert!(
        ledger.is_empty(),
        "no switch, so nothing the emitted text cannot witness: {ledger:?}"
    );
    assert_eq!(
        canon(&masked),
        canon(&core_b()),
        "the artifact BINARY (reader A) and the emitted TEXT (reader B) disagree about this body"
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
        ir_mint::IR_FW_DEFS,
        "the committed definition script is not what `mint` produces from the committed core \
         module. The committed script is the one `eval_ir_flat_flags_with.rs` REGISTERS, so a \
         difference here means the proved module is again hand-edited."
    );
    assert!(
        ir_mint::IR_FW_RECORD.contains(&ir_mint::digest(&minted)),
        "the mint record's defs digest does not match the minted script"
    );
    assert!(
        ir_mint::IR_FW_RECORD.contains(&ir_mint::digest(ir_mint::IR_FW_CORE)),
        "the mint record's core digest does not match the committed core module"
    );
    // The chain's OWN alias — where the hand transcription borrowed the
    // sibling's. Both delta to the same type; the mint keeps namespaces per
    // chain, so a re-interning of one chain is one reviewed re-pin.
    assert_eq!(
        ir_mint::mint(&core_a(), PREFIX, &tags())
            .expect("mint")
            .lines
            .first()
            .map(String::as_str),
        Some("def ir_fw_tflags : IRTy := IRTy.struct_ 815"),
    );
    assert!(
        !ir_mint::IR_FW_DEFS.contains("ir_fc_tflags"),
        "the minted script must not lean on the sibling chain's namespace"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M5 — the A1 lane comparator, unchanged, over the MINTED script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m5_the_a1_comparator_agrees_over_the_minted_script() {
    let emitted = parse_emitted(FIXTURE);
    let clean = parse_clean(ir_mint::IR_FW_DEFS, "def ir_fw_b");
    assert_lanes(&emitted, &clean, "ir_fw (minted)");
    assert_eq!(emitted.blocks, clean.blocks);
    assert_eq!(emitted.binops, clean.binops);
    assert_eq!(emitted.insertfields, clean.insertfields);
    assert_eq!(emitted.agg_consts, clean.agg_consts);
    assert!(
        !emitted.insertfields.is_empty() && !emitted.agg_consts.is_empty(),
        "coverage denominator: the write lane and the template are the body"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M7 — the tag table still records the interning id the artifact names.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m7_the_tag_table_still_matches_the_artifact() {
    assert!(
        FIXTURE.contains("const struct.815 { 0 }") && FIXTURE.contains("insertfield struct.815"),
        "the emitted body must still name struct.815 in its instructions; if not, the artifact \
         was re-interned and this table needs a one-line REVIEWED re-pin"
    );
    assert!(
        FIXTURE.contains("bb0(%0: struct.815, %1: struct.815):"),
        "and both parameters must still be the same struct"
    );
    assert!(
        ir_mint::IR_FW_TAGS.contains("\"crate_id\": 815"),
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
    // No switch, so the projection is exact against the committed core.
    assert_eq!(
        canon(&p.core),
        ir_mint::IR_FW_CORE,
        "projecting under the interface pin must produce the committed core"
    );
    let tys: Vec<&str> = p.interface.params.iter().map(|s| s.ty.as_str()).collect();
    assert_eq!(
        tys,
        ["struct#0", "struct#0"],
        "two by-value copies of the SAME canonical struct — and the same index the body's own \
         const and insertfield name"
    );
    assert!(
        p.interface.block_params.is_empty() && p.interface.aligns.is_empty(),
        "no join and no memory instruction — measured, not assumed"
    );
}

/// The pins BITE, exactly as on the sibling chain.
#[test]
fn m10_the_interface_pins_bite() {
    let t = tags();
    for (from, to, slot) in [
        (
            "bb0(%0: struct.815, %1: struct.815):",
            "bb0(%0: struct.815, %1: struct.999):",
            "parameter",
        ),
        (
            "bb0(%0: struct.815, %1: struct.815):",
            "bb0(%0: u32, %1: struct.815):",
            "parameter",
        ),
        ("rustcc fn @", "ccc fn @", "calling convention"),
        ("(functy.460)", "(functy.461)", "signature index"),
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
// M8 — the mint discriminates the flat siblings.
// ────────────────────────────────────────────────────────────────────────────

/// `contains` and `with` are one struct apart in source and share the
/// read-read-binop prefix; the mint must separate them everywhere it can.
#[test]
fn m8_the_mint_discriminates_the_flat_siblings() {
    assert_ne!(
        ir_mint::digest(ir_mint::IR_FW_CORE),
        ir_mint::digest(ir_mint::IR_FC_CORE),
        "ir_fw and ir_fc must not share a core digest"
    );
    assert_ne!(ir_mint::IR_FW_DEFS, ir_mint::IR_FC_DEFS);
    assert!(
        ir_mint::IR_FW_DEFS.contains("IRBinOp.or_")
            && !ir_mint::IR_FW_DEFS.contains("IRBinOp.and_"),
        "with is the OR half"
    );
    assert!(
        ir_mint::IR_FW_DEFS.contains("IRInst.insertfield")
            && !ir_mint::IR_FC_DEFS.contains("IRInst.insertfield"),
        "with rebuilds the struct; contains computes a Bool"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M4 — reader C: the ELABORATED KERNEL TERM decodes back to the committed
// core. The expensive check (one full Specification build), LAST.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m4_the_registered_kernel_term_decodes_to_the_committed_core() {
    let spec = clean_verify::test_utils::shared_spec();
    let decoded = ir_mint::decode(spec.env(), MODULE_CONST, &tags()).expect("decode ir_fw_module");
    assert_eq!(
        canon(&decoded),
        ir_mint::IR_FW_CORE,
        "the ELABORATED term registered under `{MODULE_CONST}` does not decode to the committed \
         core module — and on this chain it is the first read-back of a STRUCT alias and a \
         WRITE instruction out of a registered term."
    );
}
