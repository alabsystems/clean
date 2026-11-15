// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A2 — the MINT gate for the `contains` chain,
//! `flat::types::FlatFlags::contains`.**
//!
//! Same three readers and the same questions as `crystal_a2_mint.rs`; read
//! that file's header and `src/ir_mint/mod.rs` for what this establishes and
//! what it does not. This is the NINTH chain the mint machinery covers,
//! migrated off its hand transcription on 2026-08-21.
//!
//! **The migration diff, printed before adoption** (a divergence is a
//! FINDING): ONE of the four lines diverged, one notation class — `ir_fc_b0`
//! inlines `(IRTy.uint_ ir_d8)` in its five typed slots where the hand line
//! named the `ir_tU8` alias, definitionally equal. `ir_fc_tflags` — the
//! interface-only struct pin the hand transcription ALREADY registered for
//! exactly the purpose the tag table now owns — minted BYTE-IDENTICAL, as did
//! `ir_fc_func` and `ir_fc_module`. NO semantic divergence.
//!
//! **What is new here relative to the eight earlier minted chains:**
//!
//! * The first minted chain whose interface pins a BY-VALUE STRUCT — twice:
//!   both parameters are the SAME canonical struct (`struct#0`), and that
//!   sameness is the pin's semantic payload. The module's instructions name
//!   no aggregate at all (both extractfields read the u8 payload off the
//!   by-value SSA arguments), so like `ir_fs_tsrc` the row is INTERFACE-ONLY
//!   — `Tags::canon_ty`'s `struct` arm gets its first committed exercise.
//! * The first minted chain with NO constant of any kind: the answer is
//!   COMPUTED (and → eq), so the mint's binop/icmp rows carry the whole body.

use clean_verify::ir_mint::{self, Sx};

#[allow(dead_code)]
use crate::emitted_cfg;

use emitted_cfg::{assert_lanes, parse_clean, parse_emitted};

const PREFIX: &str = "ir_fc";
const MODULE_CONST: &str = "ir_fc_module";
const FIXTURE: &str = include_str!("fixtures/flat_flags_contains.trust-ir.txt");

fn tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_FC_TAGS).expect("the committed tag table must parse")
}

fn core_a() -> Sx {
    ir_mint::parse(ir_mint::IR_FC_CORE).expect("the committed core module must parse")
}

fn core_b() -> Sx {
    ir_mint::read_emitted(FIXTURE).expect("reader B must read the committed emitted trust-ir")
}

fn canon(sx: &Sx) -> String {
    ir_mint::print(sx).expect("a core module must print")
}

// ────────────────────────────────────────────────────────────────────────────
// M1 — the committed core is canonical, and it is the and/eq subset test.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m1_committed_core_round_trips_its_printer() {
    let a = core_a();
    assert_eq!(
        canon(&a),
        ir_mint::IR_FC_CORE,
        "the committed core module is not what its own canonical printer produces"
    );
    let text = ir_mint::IR_FC_CORE;
    assert!(
        text.contains("(extractfield (uint 8) 0 0)")
            && text.contains("(extractfield (uint 8) 1 0)"),
        "field 0 of BOTH by-value arguments:\n{text}"
    );
    assert!(
        text.contains("(binop and (uint 8) 2 3)") && text.contains("(icmp eq (uint 8) 4 5)"),
        "the subset test: self.0 & other.0 == other.0:\n{text}"
    );
    assert!(
        !text.contains("(const ") && !text.contains("(switch ") && !text.contains("(load "),
        "no constant, no dispatch, no memory — the answer is computed"
    );
    assert!(!text.contains("(call "), "this body calls nothing");
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
        ir_mint::IR_FC_DEFS,
        "the committed definition script is not what `mint` produces from the committed core \
         module. The committed script is the one `eval_ir_contains.rs` REGISTERS, so a \
         difference here means the proved module is again hand-edited."
    );
    assert!(
        ir_mint::IR_FC_RECORD.contains(&ir_mint::digest(&minted)),
        "the mint record's defs digest does not match the minted script"
    );
    assert!(
        ir_mint::IR_FC_RECORD.contains(&ir_mint::digest(ir_mint::IR_FC_CORE)),
        "the mint record's core digest does not match the committed core module"
    );
    // The interface-only alias: BYTE-IDENTICAL to the pin the hand
    // transcription already registered, and a literal (815 > 16; 1017 before the 2026-10-07 rebaseline).
    assert_eq!(
        ir_mint::mint(&core_a(), PREFIX, &tags())
            .expect("mint")
            .lines
            .first()
            .map(String::as_str),
        Some("def ir_fc_tflags : IRTy := IRTy.struct_ 815"),
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M5 — the A1 lane comparator, unchanged, over the MINTED script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m5_the_a1_comparator_agrees_over_the_minted_script() {
    let emitted = parse_emitted(FIXTURE);
    let clean = parse_clean(ir_mint::IR_FC_DEFS, "def ir_fc_b");
    assert_lanes(&emitted, &clean, "ir_fc (minted)");
    assert_eq!(emitted.blocks, clean.blocks);
    assert_eq!(emitted.binops, clean.binops);
    assert_eq!(emitted.icmps, clean.icmps);
    assert_eq!(emitted.extracts, clean.extracts);
    assert!(
        !emitted.binops.is_empty() && !emitted.icmps.is_empty(),
        "coverage denominator: the whole body is one binop and one icmp"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M7 — the tag table still records the interning id the artifact names.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m7_the_tag_table_still_matches_the_artifact() {
    assert!(
        FIXTURE.contains("bb0(%0: struct.815, %1: struct.815):"),
        "both parameters must still be struct.815; if not, the artifact was re-interned and \
         this table needs a one-line REVIEWED re-pin"
    );
    assert!(
        ir_mint::IR_FC_TAGS.contains("\"crate_id\": 815"),
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
    // No switch, so the projection is exact against the committed core — no
    // mask needed, unlike the ko/fs chains.
    assert_eq!(
        canon(&p.core),
        ir_mint::IR_FC_CORE,
        "projecting under the interface pin must produce the committed core"
    );
    let tys: Vec<&str> = p.interface.params.iter().map(|s| s.ty.as_str()).collect();
    assert_eq!(
        tys,
        ["struct#0", "struct#0"],
        "two by-value copies of the SAME canonical struct — the sameness is the pin"
    );
    assert!(
        p.interface.block_params.is_empty() && p.interface.aligns.is_empty(),
        "no join and no memory instruction — measured, not assumed"
    );
}

/// The pins BITE: a different struct in EITHER slot, a non-struct argument, a
/// foreign calling convention and a moved `functy` are each refused, and the
/// refusal names the slot.
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
        ("(functy.459)", "(functy.460)", "signature index"),
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
// M8 — the mint discriminates this chain from every other minted chain.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m8_the_mint_discriminates_across_the_minted_set() {
    for (who, core) in [
        ("ir_h2", ir_mint::IR_H2_CORE),
        ("ir_ko", ir_mint::IR_KO_CORE),
        ("ir_fs", ir_mint::IR_FS_CORE),
        ("ir_pv", ir_mint::IR_PV_CORE),
        ("ir_fa", ir_mint::IR_FA_CORE),
    ] {
        assert_ne!(
            ir_mint::digest(ir_mint::IR_FC_CORE),
            ir_mint::digest(core),
            "ir_fc and {who} must not share a core digest"
        );
    }
    // The nearest FUTURE sibling is `FlatFlags::with` (or/insertfield over the
    // same struct); until it mints, the committed separation is against the
    // emitted text: `contains` computes and returns a Bool, `with` rebuilds
    // the struct. Pin the halves of that separation this chain owns.
    assert!(
        ir_mint::IR_FC_DEFS.contains("IRBinOp.and_")
            && !ir_mint::IR_FC_DEFS.contains("IRBinOp.or_"),
        "contains is the AND half"
    );
    assert!(
        !ir_mint::IR_FC_DEFS.contains("IRInst.insertfield"),
        "contains rebuilds nothing"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M4 — reader C: the ELABORATED KERNEL TERM decodes back to the committed
// core. The expensive check (one full Specification build), LAST.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m4_the_registered_kernel_term_decodes_to_the_committed_core() {
    let spec = clean_verify::test_utils::shared_spec();
    let decoded = ir_mint::decode(spec.env(), MODULE_CONST, &tags()).expect("decode ir_fc_module");
    assert_eq!(
        canon(&decoded),
        ir_mint::IR_FC_CORE,
        "the ELABORATED term registered under `{MODULE_CONST}` does not decode to the committed \
         core module. This is the check that keeps `mint` out of the trusted base: reader C \
         never sees the minter's output."
    );
}
