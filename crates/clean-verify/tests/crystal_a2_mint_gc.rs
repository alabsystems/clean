// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A2 — the MINT gate for the `get_char_val_trunc` chain,
//! `env::native_reducers_beq_shortcircuit::get_char_val::{closure#0}`.**
//!
//! Same three readers and the same questions as `crystal_a2_mint.rs`; read
//! that file's header and `src/ir_mint/mod.rs` for what this establishes and
//! what it does not. This is the THIRTEENTH chain the mint machinery covers,
//! migrated off its hand transcription on 2026-08-21 — the first minted body
//! whose whole content is a CAST, and the first with a UNIT parameter.
//!
//! **The migration diff, printed before adoption** (the rule the flagship's
//! wrong exhaustive flag made mandatory: a divergence is a FINDING): ONE of
//! the three lines diverged, ONE notation class, definitionally equal —
//! `ir_gc_b0` inlines `(IRTy.uint_ 64)` and `(IRTy.uint_ 32)` where the hand
//! line reused the `ir_vc_tu64` / `ir_br_tu32` aliases. `ir_gc_func` and
//! `ir_gc_module` minted byte-identical. NO semantic divergence; every
//! downstream `ir_gc_*` theorem kept proving unchanged, the four boundary
//! witnesses (2^32-1 / 2^32 / collapse pair) included.

use clean_verify::ir_mint::{self, Sx};

#[allow(dead_code)]
#[path = "crystal_a1_lineage/emitted_cfg.rs"]
mod emitted_cfg;

use emitted_cfg::{assert_lanes, parse_clean, parse_emitted};

const PREFIX: &str = "ir_gc";
const MODULE_CONST: &str = "ir_gc_module";
const FIXTURE: &str = include_str!("fixtures/get_char_val_trunc.trust-ir.txt");

fn tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_GC_TAGS).expect("the committed tag table must parse")
}

fn core_a() -> Sx {
    ir_mint::parse(ir_mint::IR_GC_CORE).expect("the committed core module must parse")
}

fn core_b() -> Sx {
    ir_mint::read_emitted(FIXTURE).expect("reader B must read the committed emitted trust-ir")
}

fn canon(sx: &Sx) -> String {
    ir_mint::print(sx).expect("a core module must print")
}

// ────────────────────────────────────────────────────────────────────────────
// M1 — the committed core is canonical, and it is one trunc and a ret.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m1_committed_core_round_trips_its_printer() {
    let a = core_a();
    assert_eq!(
        canon(&a),
        ir_mint::IR_GC_CORE,
        "the committed core module is not what its own canonical printer produces"
    );
    let text = ir_mint::IR_GC_CORE;
    assert!(
        text.contains("(cast trunc (uint 64) (uint 32) 1)"),
        "the committed core must carry the u64→u32 trunc of %1:\n{text}"
    );
    assert!(
        text.contains("(ret (vals 2))"),
        "and return the truncated value, not the argument:\n{text}"
    );
    assert!(
        !text.contains("(switch") && !text.contains("(condbr") && !text.contains("(call "),
        "one block, no control flow, no call; a core module with any is not it"
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
        "the artifact BINARY (reader A) and the emitted TEXT (reader B) disagree about this body"
    );
    assert!(
        ledger.is_empty(),
        "no `switch` means no unwitnessed slot: {ledger:?}"
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
        ir_mint::IR_GC_DEFS,
        "the committed definition script is not what `mint` produces from the committed core \
         module. The committed script is the one `eval_ir_trunc.rs` REGISTERS, so a difference \
         here means the proved module is again hand-edited."
    );
    assert!(
        ir_mint::IR_GC_RECORD.contains(&ir_mint::digest(&minted)),
        "the mint record's defs digest does not match the minted script"
    );
    assert!(
        ir_mint::IR_GC_RECORD.contains(&ir_mint::digest(ir_mint::IR_GC_CORE)),
        "the mint record's core digest does not match the committed core module"
    );
    assert!(
        ir_mint::IR_GC_DEFS.contains("(IRTy.uint_ 64) (IRTy.uint_ 32)")
            && !ir_mint::IR_GC_DEFS.contains("(IRTy.uint_ 32) (IRTy.uint_ 64)"),
        "source width then destination width — the reverse is a widening, which faults:\n{}",
        ir_mint::IR_GC_DEFS
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M5 — the A1 lane comparator, unchanged, over the MINTED script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m5_the_a1_comparator_agrees_over_the_minted_script() {
    let emitted = parse_emitted(FIXTURE);
    let clean = parse_clean(ir_mint::IR_GC_DEFS, "def ir_gc_b");
    assert_lanes(&emitted, &clean, "ir_gc (minted)");
    assert_eq!(emitted.blocks, clean.blocks);
    assert!(
        !emitted.casts.is_empty(),
        "coverage denominator: two empty lane sets compare equal, and this body IS a cast"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M7 — the tag table still records the interning ids the artifact names.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m7_the_tag_table_still_matches_the_artifact() {
    assert!(
        FIXTURE.contains("(functy.370)"),
        "the emitted body must still carry signature index 370; if it does not, the artifact \
         was re-interned and this table needs a one-line REVIEWED re-pin"
    );
    assert!(
        ir_mint::IR_GC_TAGS.contains("\"functy\": 370"),
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
        ["()", "u64"],
        "the UNIT closure environment and the u64 operand — the first row is the only witness \
         anywhere that the environment is empty, because the core module holds only the SSA id"
    );
    assert!(p.interface.block_params.is_empty(), "one block, no joins");
    assert!(
        p.interface.aligns.is_empty(),
        "no memory instruction in this body"
    );
}

/// The pins BITE: a pointer environment, a narrowed operand, a foreign
/// calling convention and a moved `functy` are each refused, and the refusal
/// names the slot. The FIRST row is the one this chain exists to pin: a twin
/// whose environment captures a pointer is one core module with this body.
#[test]
fn m10_the_interface_pins_bite() {
    let t = tags();
    for (from, to, slot) in [
        (
            "bb0(%0: (), %1: u64):",
            "bb0(%0: ptr, %1: u64):",
            "parameter",
        ),
        (
            "bb0(%0: (), %1: u64):",
            "bb0(%0: (), %1: u32):",
            "parameter",
        ),
        ("rustcc fn @", "ccc fn @", "calling convention"),
        ("(functy.370)", "(functy.371)", "signature index"),
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
// M8 — the mint discriminates this chain from the other one-block computers.
// ────────────────────────────────────────────────────────────────────────────

/// The float tranche and this chain share the one-block compute-and-return
/// skeleton; a mint keyed on the skeleton would produce one module for all
/// five. Digests and the instruction must separate them.
#[test]
fn m8_the_mint_discriminates_the_one_block_siblings() {
    assert_ne!(
        ir_mint::digest(ir_mint::IR_GC_CORE),
        ir_mint::digest(ir_mint::IR_FA_CORE),
        "ir_gc and ir_fa must not share a core digest"
    );
    assert!(
        ir_mint::IR_GC_DEFS.contains("IRInst.cast")
            && !ir_mint::IR_GC_DEFS.contains("IRInst.binop"),
        "this body casts and computes nothing"
    );
    assert!(
        ir_mint::IR_FA_DEFS.contains("IRInst.binop")
            && !ir_mint::IR_FA_DEFS.contains("IRInst.cast"),
        "the float sibling computes and casts nothing"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M4 — reader C: the ELABORATED KERNEL TERM decodes back to the committed
// core. The expensive check (one full Specification build), LAST.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m4_the_registered_kernel_term_decodes_to_the_committed_core() {
    let spec = clean_verify::test_utils::shared_spec();
    let decoded = ir_mint::decode(spec.env(), MODULE_CONST, &tags()).expect("decode ir_gc_module");
    assert_eq!(
        canon(&decoded),
        ir_mint::IR_GC_CORE,
        "the ELABORATED term registered under `{MODULE_CONST}` does not decode to the committed \
         core module. This is the check that keeps `mint` out of the trusted base: reader C \
         never sees the minter's output."
    );
}
