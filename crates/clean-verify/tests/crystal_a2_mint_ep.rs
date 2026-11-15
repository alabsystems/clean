// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A2 — the MINT gate for the `expr_path_step_clone` chain,
//! `<tc::expr_location::ExprPathStep as std::clone::Clone>::clone`.**
//!
//! Same three readers and the same questions as `crystal_a2_mint.rs`; read
//! that file's header and `src/ir_mint/mod.rs` for what this establishes and
//! what it does not. This is the FIFTEENTH chain the mint machinery covers,
//! migrated off its hand transcription on 2026-08-21 — and the chain whose
//! enum id is the ORIGINAL SPECIMEN of the whole-crate drift class the tag
//! table exists for: observed at 181/181/176 over the producer A/B record's
//! three dumps, 182 on the 2026-08-21 laneREG dump, and pinned at the
//! fixture-era 225 (184 before the 2026-10-07 rebaseline) that readers B and C are compared against.
//!
//! **The migration diff, printed before adoption** (the rule the flagship's
//! wrong exhaustive flag made mandatory: a divergence is a FINDING): TWELVE
//! of the sixteen lines diverged, TWO notation classes, both definitionally
//! equal — `ir_ep_b0` inlines `(IRTy.uint_ ir_d8)` where the hand line named
//! `ir_tU8`, and `ir_ep_b1`..`b11` spell each arm constant as the raw
//! `(IRConst.aggv (IRConst.vcons (IRConst.int_ ir_dK) IRConst.vnil))` spine
//! where the hand lines named `ir_cvar ir_dK`. `ir_ep_tstep` (the 184 pin, 225 since the 2026-10-07 rebaseline, now
//! owned by the tag table), `ir_ep_b12`, `ir_ep_func` and `ir_ep_module`
//! minted byte-identical. NO semantic divergence; every downstream `ir_ep_*`
//! theorem kept proving unchanged, all eleven executed arm witnesses and the
//! junk-payload witness included.
//!
//! **What is new here relative to the fourteen earlier minted chains:** the
//! first minted chain whose JOIN binds an AGGREGATE (`bb12(%1: enum.225)`),
//! whose canonical pin `enum#0` is what `Tags::canon_ty`'s own doc cites; and
//! the widest minted module yet (13 blocks, 16 lines, an 11-arm dispatch).

use clean_verify::ir_mint::{self, Sx};

#[allow(dead_code)]
use crate::emitted_cfg;

use emitted_cfg::{assert_lanes, parse_clean, parse_emitted};

const PREFIX: &str = "ir_ep";
const MODULE_CONST: &str = "ir_ep_module";
const FIXTURE: &str = include_str!("fixtures/expr_path_step_clone.trust-ir.txt");

fn tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_EP_TAGS).expect("the committed tag table must parse")
}

fn core_a() -> Sx {
    ir_mint::parse(ir_mint::IR_EP_CORE).expect("the committed core module must parse")
}

fn core_b() -> Sx {
    ir_mint::read_emitted(FIXTURE).expect("reader B must read the committed emitted trust-ir")
}

fn canon(sx: &Sx) -> String {
    ir_mint::print(sx).expect("a core module must print")
}

// ────────────────────────────────────────────────────────────────────────────
// M1 — the committed core is canonical, and it is the eleven-arm dispatch.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m1_committed_core_round_trips_its_printer() {
    let a = core_a();
    assert_eq!(
        canon(&a),
        ir_mint::IR_EP_CORE,
        "the committed core module is not what its own canonical printer produces"
    );
    let text = ir_mint::IR_EP_CORE;
    assert!(
        text.contains("(load (enum 0) 0 false)"),
        "the committed core must carry the receiver load:\n{text}"
    );
    assert!(
        text.contains("(extractfield (uint 8) 2 0)"),
        "and the discriminant read at field 0:\n{text}"
    );
    assert_eq!(
        text.matches("(case ").count(),
        10,
        "TEN explicit switch cases, 0..9 — tag 10 rides the default:\n{text}"
    );
    for k in 0..11 {
        assert!(
            text.contains(&format!("(const (enum 0) (agg (int {k})))")),
            "and the eleven distinct aggregate arm constants, tag {k} included:\n{text}"
        );
    }
    assert!(
        !text.contains("(call "),
        "all eleven variants are fieldless, so clone calls nothing"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M2 — reader B equals reader A, modulo the declared one-entry ledger.
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
        ir_mint::IR_EP_DEFS,
        "the committed definition script is not what `mint` produces from the committed core \
         module. The committed script is the one `eval_ir_path_step.rs` REGISTERS, so a \
         difference here means the proved module is again hand-edited."
    );
    assert!(
        ir_mint::IR_EP_RECORD.contains(&ir_mint::digest(&minted)),
        "the mint record's defs digest does not match the minted script"
    );
    assert!(
        ir_mint::IR_EP_RECORD.contains(&ir_mint::digest(ir_mint::IR_EP_CORE)),
        "the mint record's core digest does not match the committed core module"
    );
}

/// **`mint::interning_id`'s LITERAL arm, on the drift class's original
/// specimen.** 225 (184 before the 2026-10-07 rebaseline) is outside `ir_d0..ir_d16`, so the alias spells the
/// literal — and the literal is the FIXTURE-ERA id, which none of the four
/// recorded artifact dumps carries (181/181/176/182): the tag table, not the
/// module and not the freshest dump, owns the pin.
#[test]
fn m3_the_alias_renders_the_fixture_era_literal() {
    let lines = ir_mint::mint(&core_a(), PREFIX, &tags())
        .expect("mint")
        .lines;
    assert_eq!(
        lines.first().map(String::as_str),
        Some("def ir_ep_tstep : IRTy := IRTy.enum_ 225"),
        "crate id 225 is outside ir_d0..ir_d16 and must render as the literal"
    );
    assert!(
        !ir_mint::IR_EP_DEFS.contains("IRTy.enum_ 182")
            && !ir_mint::IR_EP_DEFS.contains("IRTy.enum_ 181"),
        "and NOT as any of the drifted artifact-side ids"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M5 — the A1 lane comparator, unchanged, over the MINTED script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m5_the_a1_comparator_agrees_over_the_minted_script() {
    let emitted = parse_emitted(FIXTURE);
    let clean = parse_clean(ir_mint::IR_EP_DEFS, "def ir_ep_b");
    assert_lanes(&emitted, &clean, "ir_ep (minted)");
    assert_eq!(emitted.blocks, clean.blocks);
    assert_eq!(emitted.cases, clean.cases);
    assert_eq!(emitted.default, clean.default);
    assert_eq!(emitted.agg_consts, clean.agg_consts);
    assert!(
        emitted.cases.len() == 10 && !emitted.agg_consts.is_empty(),
        "coverage denominator: ten explicit cases and eleven aggregate constants"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M7 — the tag table still records the interning ids the artifact names.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m7_the_tag_table_still_matches_the_artifact() {
    assert!(
        FIXTURE.contains("load enum.225, ptr %0"),
        "the emitted body must still name enum.225; if it does not, the artifact was \
         re-interned and this table needs a one-line REVIEWED re-pin — which, on THIS chain, \
         has already been warranted four times by four dumps (181/181/176/182)"
    );
    assert!(
        ir_mint::IR_EP_TAGS.contains("\"crate_id\": 225"),
        "and the committed table must record it"
    );
    assert!(
        FIXTURE.contains("(functy.903)") && ir_mint::IR_EP_TAGS.contains("\"functy\": 903"),
        "same for the signature index"
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
    assert_eq!(tys, ["ptr"], "one parameter: the &ExprPathStep receiver");
    let joins: Vec<(u32, &str)> = p
        .interface
        .block_params
        .iter()
        .map(|s| (s.block, s.ty.as_str()))
        .collect();
    assert_eq!(
        joins,
        [(12, "enum#0")],
        "the join binds the AGGREGATE, canonicalized through the tag table — the raw token has \
         been observed at four different crate ids for this one unchanged body"
    );
    assert_eq!(
        p.interface.aligns,
        ["load:None"],
        "one memory instruction, the receiver load"
    );
}

/// The pins BITE: a receiver that is not a pointer, a join bound at a FOREIGN
/// enum id (the drift trap: an id the table does not list canonicalizes to
/// `enum#?`, which is not the pinned `enum#0`), a foreign calling convention
/// and a moved `functy` are each refused, and the refusal names the slot.
#[test]
fn m10_the_interface_pins_bite() {
    let t = tags();
    for (from, to, slot) in [
        ("bb0(%0: ptr):", "bb0(%0: u64):", "parameter"),
        (
            "bb12(%1: enum.225):",
            "bb12(%1: enum.181):",
            "block parameter",
        ),
        ("rustcc fn @", "ccc fn @", "calling convention"),
        ("(functy.903)", "(functy.904)", "signature index"),
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
// M8 — the mint discriminates this chain from its dispatch-siblings.
// ────────────────────────────────────────────────────────────────────────────

/// `expr_path_step_clone`, `kind_ord` and `has_cubical_layer` share the
/// load/extractfield/switch/join skeleton; a mint that keyed on the skeleton
/// would produce one module for all three. Digests, scripts and the constant
/// lane must all separate them.
#[test]
fn m8_the_mint_discriminates_the_dispatch_siblings() {
    for (other, name) in [
        (ir_mint::IR_KO_CORE, "ir_ko"),
        (ir_mint::IR_H2_CORE, "ir_h2"),
    ] {
        assert_ne!(
            ir_mint::digest(ir_mint::IR_EP_CORE),
            ir_mint::digest(other),
            "ir_ep and {name} must not share a core digest"
        );
    }
    assert!(
        ir_mint::IR_EP_DEFS.contains("IRConst.aggv")
            && !ir_mint::IR_KO_DEFS.contains("IRConst.aggv"),
        "expr_path_step_clone answers in AGGREGATES where kind_ord answers in u8 scalars"
    );
    assert_eq!(
        ir_mint::IR_EP_DEFS.matches("def ir_ep_b").count(),
        13,
        "thirteen blocks — the widest minted module"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M4 — reader C: the ELABORATED KERNEL TERM decodes back to the committed
// core. The expensive check (one full Specification build), LAST.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m4_the_registered_kernel_term_decodes_to_the_committed_core() {
    let spec = clean_verify::test_utils::shared_spec();
    let decoded = ir_mint::decode(spec.env(), MODULE_CONST, &tags()).expect("decode ir_ep_module");
    assert_eq!(
        canon(&decoded),
        ir_mint::IR_EP_CORE,
        "the ELABORATED term registered under `{MODULE_CONST}` does not decode to the committed \
         core module. This is the check that keeps `mint` out of the trusted base: reader C \
         never sees the minter's output — and on this chain it is also what pins that the \
         registered `IRTy.enum_ 225` maps back through the tag table to the canonical enum#0 \
         the core module carries."
    );
}
