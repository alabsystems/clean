// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A2 — the MINT gate for the `meta_tag_shl` chain,
//! `tc::local_context::LocalContext::push_low_local::META_TAG::{const-init}`.**
//!
//! Same three readers and the same questions as `crystal_a2_mint.rs`; read
//! that file's header and `src/ir_mint/mod.rs` for what this establishes and
//! what it does not. This is the FOURTEENTH chain the mint machinery covers,
//! migrated off its hand transcription on 2026-08-21 — the first minted body
//! with an ASSERT (the panic arm), and the CTFE seam's chain.
//!
//! **The migration diff, printed before adoption** (the rule the flagship's
//! wrong exhaustive flag made mandatory: a divergence is a FINDING): ONE of
//! the three lines diverged, THREE notation classes in it, all definitionally
//! equal — `ir_mt_b0` spells its nine-node body as the raw `IRList.cons
//! IRNode` spine where the hand line named `ir_mt_bd9`, inlines
//! `(IRTy.uint_ 64)` / `(IRTy.int_ 32)` / `(IRTy.uint_ 32)` where the hand
//! line named `ir_vc_tu64` / `ir_mt_ti32` / `ir_br_tu32`, and spells the 1
//! constant `(IRConst.int_ ir_d1)` where the hand line wrote the literal.
//! `ir_mt_func` and `ir_mt_module` minted byte-identical. NO semantic
//! divergence; every downstream `ir_mt_*` theorem kept proving unchanged,
//! the out-of-bounds and negative-shift counterfactuals included (both stay
//! HAND-authored on purpose: they are counterfactuals, not the artifact).
//!
//! **What is new here relative to the thirteen earlier minted chains:**
//!
//! * The first minted `assert` — the node prints no result, no type and no
//!   target, and its `#proof: shift_in_range` clause is pinned as a clause
//!   KIND (the only chained body carrying one).
//! * The first minted `i32` — a SIGNED type, `(IRTy.int_ 32)`, whose
//!   signedness is load-bearing twice (the bitcast zero-reads the pattern for
//!   the range check; the sext sign-extends it for the shift).
//! * The first minted body with NO parameters at all: the interface pin is
//!   the EMPTINESS, which is the slot a twin that smuggled the shift amount
//!   in as an argument would hide in.

use clean_verify::ir_mint::{self, Sx};

#[allow(dead_code)]
use crate::emitted_cfg;

use emitted_cfg::{assert_lanes, parse_clean, parse_emitted};

const PREFIX: &str = "ir_mt";
const MODULE_CONST: &str = "ir_mt_module";
const FIXTURE: &str = include_str!("fixtures/meta_tag_shl.trust-ir.txt");

fn tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_MT_TAGS).expect("the committed tag table must parse")
}

fn core_a() -> Sx {
    ir_mint::parse(ir_mint::IR_MT_CORE).expect("the committed core module must parse")
}

fn core_b() -> Sx {
    ir_mint::read_emitted(FIXTURE).expect("reader B must read the committed emitted trust-ir")
}

fn canon(sx: &Sx) -> String {
    ir_mint::print(sx).expect("a core module must print")
}

// ────────────────────────────────────────────────────────────────────────────
// M1 — the committed core is canonical, and it is the guarded shift.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m1_committed_core_round_trips_its_printer() {
    let a = core_a();
    assert_eq!(
        canon(&a),
        ir_mint::IR_MT_CORE,
        "the committed core module is not what its own canonical printer produces"
    );
    let text = ir_mint::IR_MT_CORE;
    assert!(
        text.contains("(assert 4)"),
        "the committed core must carry the range-check ASSERT — the panic arm:\n{text}"
    );
    assert!(
        text.contains("(cast bitcast (int 32) (uint 32) 1)")
            && text.contains("(cast sext (int 32) (uint 64) 1)"),
        "and the two casts of the SAME operand with different opcodes:\n{text}"
    );
    assert!(
        text.contains("(binop shl (uint 64) 0 5)"),
        "and the shift itself:\n{text}"
    );
    for k in ["(int 1)", "(int 63)", "(int 64)"] {
        assert!(
            text.contains(k),
            "and the three constants, {k} included:\n{text}"
        );
    }
    assert!(
        !text.contains("(switch") && !text.contains("(condbr") && !text.contains("(call "),
        "one block, no control flow, no call"
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
        "no `switch` means no unwitnessed slot — the assert prints completely: {ledger:?}"
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
        ir_mint::IR_MT_DEFS,
        "the committed definition script is not what `mint` produces from the committed core \
         module. The committed script is the one `eval_ir_meta_tag.rs` REGISTERS, so a \
         difference here means the proved module is again hand-edited."
    );
    assert!(
        ir_mint::IR_MT_RECORD.contains(&ir_mint::digest(&minted)),
        "the mint record's defs digest does not match the minted script"
    );
    assert!(
        ir_mint::IR_MT_RECORD.contains(&ir_mint::digest(ir_mint::IR_MT_CORE)),
        "the mint record's core digest does not match the committed core module"
    );
    assert!(
        ir_mint::IR_MT_DEFS.contains("(IRTy.int_ 32)"),
        "the SIGNED i32 must render — the first minted signed type:\n{}",
        ir_mint::IR_MT_DEFS
    );
    assert!(
        ir_mint::IR_MT_DEFS.contains("(IRConst.int_ ir_d1)")
            && ir_mint::IR_MT_DEFS.contains("(IRConst.int_ 63)"),
        "a datum at or below 16 renders through the pool and one above it as the literal — \
         both arms of `nat_data`, in one line:\n{}",
        ir_mint::IR_MT_DEFS
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M5 — the A1 lane comparator, unchanged, over the MINTED script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m5_the_a1_comparator_agrees_over_the_minted_script() {
    let emitted = parse_emitted(FIXTURE);
    let clean = parse_clean(ir_mint::IR_MT_DEFS, "def ir_mt_b");
    assert_lanes(&emitted, &clean, "ir_mt (minted)");
    assert_eq!(emitted.blocks, clean.blocks);
    assert_eq!(emitted.asserts, clean.asserts);
    assert_eq!(emitted.int_consts, clean.int_consts);
    assert_eq!(emitted.casts, clean.casts);
    assert!(
        !emitted.asserts.is_empty() && !emitted.casts.is_empty(),
        "coverage denominator: this body carries the assert and two casts"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M7 — the tag table still records the interning ids the artifact names.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m7_the_tag_table_still_matches_the_artifact() {
    assert!(
        FIXTURE.contains("(functy.116)"),
        "the emitted body must still carry signature index 116; if it does not, the artifact \
         was re-interned and this table needs a one-line REVIEWED re-pin"
    );
    assert!(
        ir_mint::IR_MT_TAGS.contains("\"functy\": 116"),
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
    assert!(
        p.interface.params.is_empty() && p.interface.block_params.is_empty(),
        "a const-initializer takes NOTHING — the emptiness IS the pin"
    );
    assert!(
        p.interface.aligns.is_empty(),
        "no memory instruction in this body"
    );
    assert!(
        p.interface.clauses.contains("proof") && !p.interface.clauses.contains("names"),
        "the only chained body with a `proof` clause and without `names`: {:?}",
        p.interface.clauses
    );
}

/// The pins BITE: a smuggled parameter, a foreign calling convention, a moved
/// `functy` and a dropped `#proof` clause are each refused, and the refusal
/// names the slot.
#[test]
fn m10_the_interface_pins_bite() {
    let t = tags();
    for (from, to, slot) in [
        ("bb0:", "bb0(%9: u64):", "parameter"),
        ("rustcc fn @", "ccc fn @", "calling convention"),
        ("(functy.116)", "(functy.117)", "signature index"),
        (
            "assert %4  ; #proof: shift_in_range  ; #loc: 254 157 30",
            "assert %4  ; #loc: 254 157 30",
            "annotation clause kinds",
        ),
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
// M8 — the mint discriminates the shipped body from its counterfactuals.
// ────────────────────────────────────────────────────────────────────────────

/// The registered OOB counterfactual (`ir_mt_oob_*`, shift amount 64) differs
/// from the shipped body in ONE constant, and it stays HAND-authored on
/// purpose — it is a counterfactual, not the artifact. The mint must separate
/// the two: minting a core with the counterfactual's constant must produce a
/// different script than the committed one.
#[test]
fn m8_the_mint_discriminates_the_shipped_body_from_the_counterfactual() {
    let oob_core = ir_mint::IR_MT_CORE.replace("(int 63)", "(int 64)");
    assert_ne!(oob_core, ir_mint::IR_MT_CORE, "the mutation must bite");
    let sx = ir_mint::parse(&oob_core).expect("the counterfactual core must still parse");
    let minted = ir_mint::mint(&sx, PREFIX, &tags()).expect("mint").text();
    assert_ne!(
        minted,
        ir_mint::IR_MT_DEFS,
        "one moved constant must move the minted script"
    );
    assert!(
        minted.contains("(IRConst.int_ 64)"),
        "and move it to exactly the counterfactual's spelling"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M4 — reader C: the ELABORATED KERNEL TERM decodes back to the committed
// core. The expensive check (one full Specification build), LAST.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m4_the_registered_kernel_term_decodes_to_the_committed_core() {
    let spec = clean_verify::test_utils::shared_spec();
    let decoded = ir_mint::decode(spec.env(), MODULE_CONST, &tags()).expect("decode ir_mt_module");
    assert_eq!(
        canon(&decoded),
        ir_mint::IR_MT_CORE,
        "the ELABORATED term registered under `{MODULE_CONST}` does not decode to the committed \
         core module. This is the check that keeps `mint` out of the trusted base: reader C \
         never sees the minter's output — and on this chain it is also what pins that the \
         registered `(IRTy.int_ 32)` IS the signed type the hand alias denoted."
    );
}
