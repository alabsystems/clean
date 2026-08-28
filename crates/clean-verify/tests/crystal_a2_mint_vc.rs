// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A2 — the MINT gate for the `is_valid_char` chain,
//! `env::native_reducers_char::is_valid_char`.**
//!
//! Same three readers and the same questions as `crystal_a2_mint.rs`; read
//! that file's header and `src/ir_mint/mod.rs` for what this establishes and
//! what it does not. This is the TWELFTH chain the mint machinery covers,
//! migrated off its hand transcription on 2026-08-21 — `ir_br`'s condbr
//! sibling, at width 64.
//!
//! **The migration diff, printed before adoption** (the rule the flagship's
//! wrong exhaustive flag made mandatory: a divergence is a FINDING): THREE of
//! the nine lines diverged, ONE notation class, definitionally equal —
//! `ir_vc_b0`/`b1`/`b4` inline `(IRTy.uint_ 64)` where the hand lines named
//! `ir_vc_tu64` (which deltas to `IRTy.uint_ ir_d64`, and `ir_d64` computes
//! to the literal 64). The other six lines minted byte-identical. NO semantic
//! divergence; every downstream `ir_vc_*` theorem kept proving unchanged,
//! the surrogate-range path witnesses included.
//!
//! **What is new here relative to `ir_br`:** the constant-on-the-LEFT icmp
//! (`icmp ult u64 %5, %0` — no other chained body compares a materialized
//! constant as the left operand), pinned below at the minted spelling.

use clean_verify::ir_mint::{self, Sx};

#[allow(dead_code)]
#[path = "crystal_a1_lineage/emitted_cfg.rs"]
mod emitted_cfg;

use emitted_cfg::{assert_lanes, parse_clean, parse_emitted};

const PREFIX: &str = "ir_vc";
const MODULE_CONST: &str = "ir_vc_module";
const FIXTURE: &str = include_str!("fixtures/is_valid_char.trust-ir.txt");

fn tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_VC_TAGS).expect("the committed tag table must parse")
}

fn core_a() -> Sx {
    ir_mint::parse(ir_mint::IR_VC_CORE).expect("the committed core module must parse")
}

fn core_b() -> Sx {
    ir_mint::read_emitted(FIXTURE).expect("reader B must read the committed emitted trust-ir")
}

fn canon(sx: &Sx) -> String {
    ir_mint::print(sx).expect("a core module must print")
}

// ────────────────────────────────────────────────────────────────────────────
// M1 — the committed core is canonical, and it is the surrogate-range
// dispatch.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m1_committed_core_round_trips_its_printer() {
    let a = core_a();
    assert_eq!(
        canon(&a),
        ir_mint::IR_VC_CORE,
        "the committed core module is not what its own canonical printer produces"
    );
    let text = ir_mint::IR_VC_CORE;
    for k in [55296u32, 57343, 1114112] {
        assert!(
            text.contains(&format!("(const (uint 64) (int {k}))")),
            "the committed core must carry the {k} bound:\n{text}"
        );
    }
    assert_eq!(
        text.matches("(condbr ").count(),
        2,
        "TWO conditional branches:\n{text}"
    );
    assert!(
        text.contains("(icmp ult (uint 64) 5 0)"),
        "and the constant-on-the-LEFT comparison, which no other chained body has:\n{text}"
    );
    assert!(
        !text.contains("(switch") && !text.contains("(call "),
        "no switch and no call in this body; a core module with either is not it"
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
        ir_mint::IR_VC_DEFS,
        "the committed definition script is not what `mint` produces from the committed core \
         module. The committed script is the one `eval_ir_valid_char.rs` REGISTERS, so a \
         difference here means the proved module is again hand-edited."
    );
    assert!(
        ir_mint::IR_VC_RECORD.contains(&ir_mint::digest(&minted)),
        "the mint record's defs digest does not match the minted script"
    );
    assert!(
        ir_mint::IR_VC_RECORD.contains(&ir_mint::digest(ir_mint::IR_VC_CORE)),
        "the mint record's core digest does not match the committed core module"
    );
    assert!(
        ir_mint::IR_VC_DEFS.contains("(IRTy.uint_ 64)") && !ir_mint::IR_VC_DEFS.contains("ir_d64"),
        "64 is outside ir_d0..ir_d16 and must render as the literal, not the named width:\n{}",
        ir_mint::IR_VC_DEFS
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M5 — the A1 lane comparator, unchanged, over the MINTED script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m5_the_a1_comparator_agrees_over_the_minted_script() {
    let emitted = parse_emitted(FIXTURE);
    let clean = parse_clean(ir_mint::IR_VC_DEFS, "def ir_vc_b");
    assert_lanes(&emitted, &clean, "ir_vc (minted)");
    assert_eq!(emitted.blocks, clean.blocks);
    assert_eq!(emitted.condbrs, clean.condbrs);
    assert_eq!(emitted.icmps, clean.icmps);
    assert_eq!(emitted.int_consts, clean.int_consts);
    assert!(
        emitted.condbrs.len() == 2 && emitted.icmps.len() == 3,
        "coverage denominator: two condbrs and comparisons in three blocks"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M7 — the tag table still records the interning ids the artifact names.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m7_the_tag_table_still_matches_the_artifact() {
    assert!(
        FIXTURE.contains("fn @env::native_reducers_char::is_valid_char(functy.377)"),
        "the emitted body must still carry signature index 377; if it does not, the artifact \
         was re-interned and this table needs a one-line REVIEWED re-pin"
    );
    assert!(
        ir_mint::IR_VC_TAGS.contains("\"functy\": 377"),
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
    assert_eq!(tys, ["u64"], "one by-value u64 parameter: the code point");
    let joins: Vec<(u32, &str)> = p
        .interface
        .block_params
        .iter()
        .map(|s| (s.block, s.ty.as_str()))
        .collect();
    assert_eq!(
        joins,
        [(3, "bool"), (6, "bool")],
        "two chained joins, both Bool"
    );
    assert!(
        p.interface.aligns.is_empty(),
        "no memory instruction in this body"
    );
}

/// The pins BITE: a narrowed parameter, a widened join, a foreign calling
/// convention and a moved `functy` are each refused, and the refusal names
/// the slot.
#[test]
fn m10_the_interface_pins_bite() {
    let t = tags();
    for (from, to, slot) in [
        ("bb0(%0: u64):", "bb0(%0: u32):", "parameter"),
        ("bb6(%2: bool):", "bb6(%2: u8):", "block parameter"),
        ("rustcc fn @", "ccc fn @", "calling convention"),
        ("(functy.377)", "(functy.378)", "signature index"),
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

/// `is_valid_char` and `bvar_in_range` share the seven-block two-join condbr
/// skeleton; a mint that keyed on the skeleton would produce one module for
/// both. Digests, scripts and the width must all separate them.
#[test]
fn m8_the_mint_discriminates_the_condbr_siblings() {
    assert_ne!(
        ir_mint::digest(ir_mint::IR_VC_CORE),
        ir_mint::digest(ir_mint::IR_BR_CORE),
        "ir_vc and ir_br must not share a core digest"
    );
    assert_ne!(ir_mint::IR_VC_DEFS, ir_mint::IR_BR_DEFS);
    assert!(
        !ir_mint::IR_VC_DEFS.contains("IRICmpOp.eq_")
            && !ir_mint::IR_VC_DEFS.contains("IRICmpOp.uge"),
        "is_valid_char compares with ult alone, where its sibling uses eq and uge"
    );
    assert!(
        ir_mint::IR_VC_DEFS.contains("(IRTy.uint_ 64)")
            && ir_mint::IR_BR_DEFS.contains("(IRTy.uint_ 32)"),
        "and the two bodies work at different widths"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M4 — reader C: the ELABORATED KERNEL TERM decodes back to the committed
// core. The expensive check (one full Specification build), LAST.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m4_the_registered_kernel_term_decodes_to_the_committed_core() {
    let spec = clean_verify::test_utils::shared_spec();
    let decoded = ir_mint::decode(spec.env(), MODULE_CONST, &tags()).expect("decode ir_vc_module");
    assert_eq!(
        canon(&decoded),
        ir_mint::IR_VC_CORE,
        "the ELABORATED term registered under `{MODULE_CONST}` does not decode to the committed \
         core module. This is the check that keeps `mint` out of the trusted base: reader C \
         never sees the minter's output."
    );
}
