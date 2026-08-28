// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A2 — the MINT gate for the `from_source_system` chain,
//! `mode::CleanMode::from_source_system`.**
//!
//! Same three readers and the same questions as `crystal_a2_mint.rs`; read
//! that file's header and `src/ir_mint/mod.rs` for what this establishes and
//! what it does not. This is the EIGHTH chain the mint machinery covers and
//! the third complete chain of the crystal, migrated off its hand
//! transcription on 2026-08-21.
//!
//! **The migration diff, printed before adoption** (the rule the flagship's
//! wrong exhaustive flag made mandatory: a divergence is a FINDING): THIRTEEN
//! of the seventeen module lines diverged, in TWO notation classes, both
//! definitionally equal — `ir_fs_b0`'s extractfield type inlines
//! `(IRTy.uint_ ir_d8)` where the hand line named `ir_tU8`, and the twelve
//! arm constants spell the raw `(IRConst.aggv (IRConst.vcons (IRConst.int_
//! ir_dN) IRConst.vnil))` spine where the hand lines named `ir_cvar ir_dN`.
//! The other four lines minted byte-identical, ONE line is minted-only (the
//! `ir_fs_tsrc` interface alias), and NO semantic divergence was found: every
//! downstream `ir_fs_*` theorem kept proving unchanged.
//!
//! **What is new here relative to the seven earlier minted chains:**
//!
//! * The first minted chain whose ARGUMENT is a by-value ENUM. The parameter
//!   type the interface pins is `enum#1` — resolved through the tag table's
//!   INTERFACE-ONLY SourceSystem row (canonical 1, fixture-era crate id 178),
//!   the first such row in the tree. The pin has already survived one real
//!   re-interning in RECORDED form: reader A's 2026-08-21 dump carries the
//!   same type at `enum.176` with the instruction text byte-identical.
//! * Both arms of `mint::interning_id` land on ONE chain: `ir_fs_tmode` spells
//!   13 as `ir_d13` (inside the pool), `ir_fs_tsrc` spells 178 as a literal.
//! * The first minted chain with AGGREGATE constants, so M3/M4 are the first
//!   check that the shape table's `agg` constant row round-trips through the
//!   minter AND back out of the elaborated term.

use clean_verify::ir_mint::{self, Sx};

#[allow(dead_code)]
#[path = "crystal_a1_lineage/emitted_cfg.rs"]
mod emitted_cfg;

use emitted_cfg::{assert_lanes, parse_clean, parse_emitted};

const PREFIX: &str = "ir_fs";
const MODULE_CONST: &str = "ir_fs_module";
const FIXTURE: &str = include_str!("fixtures/from_source_system.trust-ir.txt");

fn tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_FS_TAGS).expect("the committed tag table must parse")
}

fn core_a() -> Sx {
    ir_mint::parse(ir_mint::IR_FS_CORE).expect("the committed core module must parse")
}

fn core_b() -> Sx {
    ir_mint::read_emitted(FIXTURE).expect("reader B must read the committed emitted trust-ir")
}

fn canon(sx: &Sx) -> String {
    ir_mint::print(sx).expect("a core module must print")
}

// ────────────────────────────────────────────────────────────────────────────
// M1 — the committed core is canonical, and it is the twelve-arm dispatch.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m1_committed_core_round_trips_its_printer() {
    let a = core_a();
    assert_eq!(
        canon(&a),
        ir_mint::IR_FS_CORE,
        "the committed core module is not what its own canonical printer produces"
    );
    // COVERAGE DENOMINATOR: two empty modules round-trip too.
    let text = ir_mint::IR_FS_CORE;
    assert!(
        text.contains("(extractfield (uint 8) 0 0)"),
        "the discriminant is read off the SSA VALUE %0 — no load, the argument is by value:\n{text}"
    );
    assert!(
        text.contains("(case 9 10 (args)) (case 11 11 (args))"),
        "eleven explicit cases with the HOLE AT TEN — tag 10 (PVS) rides the default:\n{text}"
    );
    assert!(!text.contains("(case 10 "), "no explicit case for tag 10");
    assert!(
        text.contains("(const (enum 0) (agg (int 0)))"),
        "the arms are AGGREGATE constants:\n{text}"
    );
    assert!(
        !text.contains("(load ") && !text.contains("(call "),
        "this body loads nothing and calls nothing"
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
        ir_mint::IR_FS_DEFS,
        "the committed definition script is not what `mint` produces from the committed core \
         module. The committed script is the one `eval_ir_from_source.rs` REGISTERS, so a \
         difference here means the proved module is again hand-edited."
    );
    assert!(
        ir_mint::IR_FS_RECORD.contains(&ir_mint::digest(&minted)),
        "the mint record's defs digest does not match the minted script"
    );
    assert!(
        ir_mint::IR_FS_RECORD.contains(&ir_mint::digest(ir_mint::IR_FS_CORE)),
        "the mint record's core digest does not match the committed core module"
    );
}

/// **Both arms of `mint::interning_id` on one chain.** 13 is inside the
/// `ir_d0..ir_d16` atom pool and must spell `ir_d13`; 178 is outside it and
/// must spell a decimal literal — the ir_pv precedent, now with its control on
/// the same script.
#[test]
fn m3_the_aliases_exercise_both_interning_arms() {
    let lines = ir_mint::mint(&core_a(), PREFIX, &tags())
        .expect("mint")
        .lines;
    assert_eq!(
        lines.first().map(String::as_str),
        Some("def ir_fs_tmode : IRTy := IRTy.enum_ ir_d13"),
        "crate id 13 is inside the pool and must render as `ir_d13`"
    );
    assert_eq!(
        lines.get(1).map(String::as_str),
        Some("def ir_fs_tsrc : IRTy := IRTy.enum_ 178"),
        "crate id 178 is outside the pool and must render as a literal — the INTERFACE-ONLY \
         SourceSystem alias, registered so the parameter pin is an elaborated term"
    );
    assert!(
        !ir_mint::IR_FS_DEFS.contains("ir_d178") && !ir_mint::IR_FS_DEFS.contains("IRTy.enum_ 13"),
        "and never the other arm's spelling:\n{}",
        ir_mint::IR_FS_DEFS
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M5 — the A1 lane comparator, unchanged, over the MINTED script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m5_the_a1_comparator_agrees_over_the_minted_script() {
    let emitted = parse_emitted(FIXTURE);
    let clean = parse_clean(ir_mint::IR_FS_DEFS, "def ir_fs_b");
    assert_lanes(&emitted, &clean, "ir_fs (minted)");
    assert_eq!(emitted.blocks, clean.blocks);
    assert_eq!(emitted.cases, clean.cases);
    assert_eq!(emitted.default, clean.default);
    assert_eq!(emitted.agg_consts, clean.agg_consts);
    assert!(
        emitted.cases.len() == 11 && !emitted.agg_consts.is_empty(),
        "coverage denominator: eleven explicit cases and twelve aggregate constants"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M7 — the tag table still records the interning ids the artifact names.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m7_the_tag_table_still_matches_the_artifact() {
    assert!(
        FIXTURE.contains("const enum.13 { 0 }"),
        "the emitted body must still name enum.13; if it does not, the artifact was re-interned \
         and this table needs a one-line REVIEWED re-pin"
    );
    assert!(
        FIXTURE.contains("bb0(%0: enum.178):"),
        "and the entry parameter must still be enum.178 — this is the FIXTURE-ERA pin the \
         canonical `enum#1` resolves through; reader A's 2026-08-21 dump already carries 176, \
         RECORDED in ir_fs.mint.json and compared against nothing"
    );
    assert!(
        ir_mint::IR_FS_TAGS.contains("\"crate_id\": 13")
            && ir_mint::IR_FS_TAGS.contains("\"crate_id\": 178"),
        "and the committed table must record both"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M10 — the interface: accepted under the pin, refused one token off it.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m10_the_committed_fixture_projects_under_its_pinned_interface() {
    let p = ir_mint::project(FIXTURE, &tags())
        .unwrap_or_else(|e| panic!("the committed fixture must project: {e}"));
    // The projection is reader B's core, which carries `?` in the one slot the
    // emitted text cannot witness (the switch's exhaustive flag), so it is
    // compared against the MASKED committed core — M2's comparison, restated
    // as the claim boundary that this lane checks the module, not changes it.
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
        ["enum#1"],
        "one parameter, a BY-VALUE enum, canonicalized through the SourceSystem row — \
         producer-invariant and still not `enum#?`"
    );
    let joins: Vec<(u32, &str)> = p
        .interface
        .block_params
        .iter()
        .map(|s| (s.block, s.ty.as_str()))
        .collect();
    assert_eq!(
        joins,
        [(13, "enum#0")],
        "the join binds the RESULT enum by value"
    );
    assert!(
        p.interface.aligns.is_empty(),
        "no memory instruction — measured, not assumed"
    );
}

/// The pins BITE: a different argument enum, a non-enum argument, a widened
/// join, a foreign calling convention and a moved `functy` are each refused,
/// and the refusal names the slot. The core module alone separates NONE of the
/// first three — two by-value-enum twins project to one core module, which is
/// exactly why the SourceSystem row exists.
#[test]
fn m10_the_interface_pins_bite() {
    let t = tags();
    for (from, to, slot) in [
        ("bb0(%0: enum.178):", "bb0(%0: enum.999):", "parameter"),
        ("bb0(%0: enum.178):", "bb0(%0: u32):", "parameter"),
        ("bb13(%1: enum.13):", "bb13(%1: u32):", "block parameter"),
        ("rustcc fn @", "ccc fn @", "calling convention"),
        ("(functy.554)", "(functy.555)", "signature index"),
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
// M8 — the mint discriminates this chain from its dispatch siblings.
// ────────────────────────────────────────────────────────────────────────────

/// `kind_ord` and `from_source_system` are both switch-dispatch bodies whose
/// arms materialise constants; the constant LANE is what separates them
/// (scalar u8 against aggregate enum), and the mint must too.
#[test]
fn m8_the_mint_discriminates_the_dispatch_siblings() {
    assert_ne!(
        ir_mint::digest(ir_mint::IR_FS_CORE),
        ir_mint::digest(ir_mint::IR_KO_CORE),
        "ir_fs and ir_ko must not share a core digest"
    );
    assert_ne!(ir_mint::IR_FS_DEFS, ir_mint::IR_KO_DEFS);
    assert!(
        ir_mint::IR_FS_DEFS.contains("IRConst.aggv")
            && !ir_mint::IR_KO_DEFS.contains("IRConst.aggv"),
        "from_source_system answers in aggregates; kind_ord answers in scalars"
    );
    assert!(
        ir_mint::IR_FS_DEFS.contains("IRInst.extractfield (IRTy.uint_ ir_d8) ir_d0 ir_d0")
            && ir_mint::IR_KO_DEFS.contains("IRInst.extractfield (IRTy.uint_ ir_d8) ir_d2 ir_d0"),
        "and the extractfield OPERAND separates by-value from loaded: %0 against %2"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M4 — reader C: the ELABORATED KERNEL TERM decodes back to the committed
// core. The expensive check (one full Specification build), LAST.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m4_the_registered_kernel_term_decodes_to_the_committed_core() {
    let spec = clean_verify::test_utils::shared_spec();
    let decoded = ir_mint::decode(spec.env(), MODULE_CONST, &tags()).expect("decode ir_fs_module");
    assert_eq!(
        canon(&decoded),
        ir_mint::IR_FS_CORE,
        "the ELABORATED term registered under `{MODULE_CONST}` does not decode to the committed \
         core module. This is the check that keeps `mint` out of the trusted base: reader C \
         never sees the minter's output — and on this chain it is also the first read-back of \
         an AGGREGATE constant spine out of a registered term."
    );
}
