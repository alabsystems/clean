// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A2 — the MINT gate for the `strict_monads` chain,
//! `env::Environment::set_lean4_core_strict_monads`.**
//!
//! Same three readers and the same questions as `crystal_a2_mint.rs`; read
//! that file's header and `src/ir_mint/mod.rs` for what this establishes and
//! what it does not. This is the SEVENTEENTH chain the mint machinery covers,
//! and until 2026-08-22 it was a NAMED REFUSAL: its `insertfield` writes
//! FIELD 81 of the Environment struct, and the minter's structural-slot rule
//! refused every numeral above the `ir_d0..ir_d16` atom pool.
//!
//! **How the refusal was converted**: a field index is a position within a
//! TYPE, not within the module — the same side of the structural/datum line
//! as the type's own width — so `shape.rs` reclassifies the two field slots
//! (`extractfield`, `insertfield`) as `Arg::Data`: rendered through the pool
//! at 16 and below (every previously minted artifact byte-identical, held by
//! every chain's M3 in this same suite), and as the bare decimal literal
//! above it — exactly the spelling the HAND transcription of this very body
//! already used and its downstream theorems already prove against. SSA ids,
//! block ids and function ids stay pool-bounded and still refuse loudly:
//! see `a_structural_numeral_above_the_pool_still_refuses`.
//!
//! **The migration diff, printed before adoption**: ONE of the four lines
//! diverged, ONE notation class, definitionally equal — `ir_sm_b0`'s
//! four-node list is the raw `IRList.cons IRNode` spine where the hand line
//! spelled a `cons`+`ir_bd3` hybrid. `ir_sm_tenv`, `ir_sm_func` and
//! `ir_sm_module` minted byte-identical — the literal 81 included. NO
//! semantic divergence; every downstream `ir_sm_*` theorem kept proving
//! unchanged.
//!
//! This chain also forced reader B's `store` arm into existence — the first
//! chained body that writes MEMORY (`flat_flags_with` writes an aggregate in
//! a register). Until 2026-08-22 the emitted-text reader refused the fixture
//! fail-closed with the instruction named, the recorded posture for a
//! mnemonic outside the reader.

use clean_verify::ir_mint::{self, Sx};

#[allow(dead_code)]
use crate::emitted_cfg;

use emitted_cfg::{assert_lanes, parse_clean, parse_emitted};

const PREFIX: &str = "ir_sm";
const MODULE_CONST: &str = "ir_sm_module";
const FIXTURE: &str = include_str!("fixtures/strict_monads.trust-ir.txt");

fn tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_SM_TAGS).expect("the committed tag table must parse")
}

fn core_a() -> Sx {
    ir_mint::parse(ir_mint::IR_SM_CORE).expect("the committed core module must parse")
}

fn core_b() -> Sx {
    ir_mint::read_emitted(FIXTURE).expect("reader B must read the committed emitted trust-ir")
}

fn canon(sx: &Sx) -> String {
    ir_mint::print(sx).expect("a core module must print")
}

// ────────────────────────────────────────────────────────────────────────────
// M1 — the committed core is canonical: load, write field 83, store, ret.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m1_committed_core_round_trips_its_printer() {
    let a = core_a();
    assert_eq!(
        canon(&a),
        ir_mint::IR_SM_CORE,
        "the committed core module is not what its own canonical printer produces"
    );
    let text = ir_mint::IR_SM_CORE;
    assert!(
        text.contains("(load (struct 0) 0 false)"),
        "the committed core must read the whole Environment through the receiver:\n{text}"
    );
    assert!(
        text.contains("(insertfield (struct 0) 2 83 1)"),
        "and write FIELD 83 (81 until the 2026-10-07 re-derivation) — the numeral this chain's refusal was named for:\n{text}"
    );
    assert!(
        text.contains("(store (struct 0) 0 3 false)"),
        "and store the updated value back through the receiver:\n{text}"
    );
    assert!(text.contains("(ret (vals))"), "and return VOID:\n{text}");
}

// ────────────────────────────────────────────────────────────────────────────
// M2 — reader B equals reader A, EXACTLY: empty ledger. This is the lane
// that could not run before the `store` arm existed.
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

/// Reader B's new arm is fail-closed in both trailing-operand directions,
/// like `load`'s: an unknown trailing operand and a doubled `align` refuse.
#[test]
fn reader_b_store_arm_refuses_malformed_tails() {
    let junk = FIXTURE.replace(
        "store struct.586 %3, ptr %0",
        "store struct.586 %3, ptr %0, banana",
    );
    assert_ne!(junk, FIXTURE);
    let e = ir_mint::read_emitted(&junk)
        .map(|_| ())
        .expect_err("an unknown trailing operand on a store must refuse");
    assert!(
        format!("{e}").contains("store"),
        "the refusal must name the instruction: {e}"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M3 — `mint` of the committed core IS the committed, registered script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m3_mint_reproduces_the_registered_script() {
    let minted = ir_mint::mint(&core_a(), PREFIX, &tags())
        .expect("mint no longer refuses this body")
        .text();
    assert_eq!(
        minted,
        ir_mint::IR_SM_DEFS,
        "the committed definition script is not what `mint` produces from the committed core \
         module. The committed script is the one `eval_ir_strict_monads.rs` REGISTERS, so a \
         difference here means the proved module is again hand-edited."
    );
    assert!(
        ir_mint::IR_SM_RECORD.contains(&ir_mint::digest(&minted)),
        "the mint record's defs digest does not match the minted script"
    );
    assert!(
        ir_mint::IR_SM_RECORD.contains(&ir_mint::digest(ir_mint::IR_SM_CORE)),
        "the mint record's core digest does not match the committed core module"
    );
}

/// **The converted refusal, pinned from both sides.** The field index mints
/// as the bare literal 83 (81 before the 2026-10-07 re-derivation) — a datum above the pool — and a field index AT the
/// pool still renders through it, so the reclassification changed exactly the
/// artifacts it had to and no others.
#[test]
fn m3_the_field_index_renders_as_the_literal() {
    assert!(
        ir_mint::IR_SM_DEFS.contains("ir_sm_tenv ir_d2 83 ir_d1"),
        "field 83 must be the bare literal, the spelling the hand transcription proved \
         against:\n{}",
        ir_mint::IR_SM_DEFS
    );
    assert!(
        !ir_mint::IR_SM_DEFS.contains("ir_d83"),
        "and NOT a pool atom the specification does not register"
    );
    // The pool arm, on the sibling that exercises it: ir_fw's insertfield
    // writes field 0.
    assert!(
        ir_mint::IR_FW_DEFS.contains("IRInst.insertfield ir_fw_tflags ir_d5 ir_d0 ir_d4"),
        "a field index at or below 16 still renders through the pool — byte-identity of every \
         earlier minted artifact is the reclassification's own regression gate:\n{}",
        ir_mint::IR_FW_DEFS
    );
}

/// **The structural rule survives.** Reclassifying the field slots must NOT
/// have widened the pool for genuine module positions: an SSA id above the
/// pool still refuses, naming the atom pool.
#[test]
fn a_structural_numeral_above_the_pool_still_refuses() {
    // The committed core with its insertfield RESULT (an SSA position) forged
    // to 131 — one above `mint::MAX_STRUCTURAL_ATOM`. It was 81 until
    // 2026-09-20: the 2026-09-16 widening to ir_d0..ir_d130 made 81 a numeral
    // the minter ACCEPTS, so this pin stopped refusing and nothing said so.
    // If it stops refusing again the pool has widened again — move the
    // specimen, never loosen the assertion.
    let forged = ir_mint::IR_SM_CORE.replace("(results 3)", "(results 131)");
    assert_ne!(forged, ir_mint::IR_SM_CORE, "the forgery must bite");
    let sx = ir_mint::parse(&forged).expect("the forged core still parses");
    let e = ir_mint::mint(&sx, PREFIX, &tags())
        .map(|_| ())
        .expect_err("an SSA id above the pool must still refuse");
    assert!(
        format!("{e}").contains("atom pool"),
        "the refusal must still be the atom pool, not something else: {e}"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M5 — the A1 lane comparator, unchanged, over the MINTED script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m5_the_a1_comparator_agrees_over_the_minted_script() {
    let emitted = parse_emitted(FIXTURE);
    let clean = parse_clean(ir_mint::IR_SM_DEFS, "def ir_sm_b");
    assert_lanes(&emitted, &clean, "ir_sm (minted)");
    assert_eq!(emitted.blocks, clean.blocks);
    assert!(
        !emitted.insertfields.is_empty() && !emitted.stores.is_empty(),
        "coverage denominator: this body IS a write, twice over"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M7 — the tag table still records the interning ids the artifact names.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m7_the_tag_table_still_matches_the_artifact() {
    assert!(
        FIXTURE.contains("(functy.385)"),
        "the emitted body must still carry signature index 385; if it does not, the artifact \
         was re-interned and this table needs a one-line REVIEWED re-pin"
    );
    assert!(
        ir_mint::IR_SM_TAGS.contains("\"functy\": 385"),
        "and the committed table must record it"
    );
    assert!(
        FIXTURE.matches("struct.586").count() == 3,
        "all three instructions name the SAME struct — the row is REAL, not interface-only"
    );
    assert!(
        ir_mint::IR_SM_TAGS.contains("\"crate_id\": 586"),
        "and the committed table pins that id"
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
    assert_eq!(tys, ["ptr", "bool"], "the &mut receiver and the flag");
    assert_eq!(
        p.interface.aligns,
        ["load:None", "store:None"],
        "BOTH memory instructions' align slots are read and compared — the store one for the \
         first time anywhere"
    );
}

/// The pins BITE: a by-value receiver, an aligned store, a foreign calling
/// convention and a moved `functy` are each refused, and the refusal names
/// the slot.
#[test]
fn m10_the_interface_pins_bite() {
    let t = tags();
    for (from, to, slot) in [
        (
            "bb0(%0: ptr, %1: bool):",
            "bb0(%0: struct.586, %1: bool):",
            "parameter",
        ),
        (
            "store struct.586 %3, ptr %0",
            "store struct.586 %3, ptr %0, align 8",
            "align",
        ),
        ("rustcc fn @", "ccc fn @", "calling convention"),
        ("(functy.385)", "(functy.386)", "signature index"),
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
// M8 — the mint discriminates this chain from the other WRITE chain.
// ────────────────────────────────────────────────────────────────────────────

/// `ir_fw` also ends in an insertfield-shaped write — but into a register
/// aggregate it then RETURNS, where this body writes MEMORY and returns void.
#[test]
fn m8_the_mint_discriminates_the_write_siblings() {
    assert_ne!(
        ir_mint::digest(ir_mint::IR_SM_CORE),
        ir_mint::digest(ir_mint::IR_FW_CORE),
        "ir_sm and ir_fw must not share a core digest"
    );
    assert!(
        ir_mint::IR_SM_DEFS.contains("IRInst.store") && ir_mint::IR_SM_DEFS.contains("ret ir_nl0"),
        "this body writes memory and returns nothing"
    );
    assert!(
        !ir_mint::IR_FW_DEFS.contains("IRInst.store"),
        "the register-write sibling never touches memory"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M4 — reader C: the ELABORATED KERNEL TERM decodes back to the committed
// core. The expensive check (one full Specification build), LAST.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m4_the_registered_kernel_term_decodes_to_the_committed_core() {
    let spec = clean_verify::test_utils::shared_spec();
    let decoded = ir_mint::decode(spec.env(), MODULE_CONST, &tags()).expect("decode ir_sm_module");
    assert_eq!(
        canon(&decoded),
        ir_mint::IR_SM_CORE,
        "the ELABORATED term registered under `{MODULE_CONST}` does not decode to the committed \
         core module. This is the check that keeps `mint` out of the trusted base: reader C \
         never sees the minter's output — and on this chain it is also what pins that the \
         registered term's literal 83 IS the field the artifact writes."
    );
}
