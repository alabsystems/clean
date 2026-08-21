// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A2 — the MINT gate for the `gep` chain,
//! `env::types::SimpPriority::value`.**
//!
//! Same three readers and the same questions as `crystal_a2_mint.rs`; read that
//! file's header and `src/ir_mint/mod.rs` for what this establishes and what it
//! does not. This file is the second chain the mint machinery covers, and it
//! exists as its own test binary rather than as a module of the first because
//! the first is already at the 500-line convention and because a second chain
//! is the only way to tell "the minter works" from "the minter reproduces the
//! one module it was written against".
//!
//! **What is new here, and it is the reason this chain could not have been
//! minted a day ago:**
//!
//! * Its enum is interned at **127** and its widths are **32** and **64**, all
//!   outside the registered `ir_d0..ir_d16` atom pool. `mint::nat` REFUSES a
//!   numeral above the pool and must go on doing so — every slot it guards is a
//!   position in the module — but a bit width and a constant VALUE are not
//!   positions. `shape::Arg::Data` is that split, and `m3` below is what pins
//!   it: the minted script says `IRTy.uint_ 32` and `IRConst.int_ 1000`, and
//!   `m4` reads them back out of the ELABORATED TERM through `ExprKind::Lit`.
//! * `Tags::alias_defs` used to format every interning id as `ir_d{id}`
//!   unconditionally. At 127 that mints `IRTy.enum_ ir_d127` — a constant the
//!   specification does not declare — and nothing in `ir_mint` would have
//!   caught it; it would have surfaced as an elaboration failure at
//!   registration, in a different file, with no mention of the tag table.
//!   `m7_alias` is the regression pin.
//! * It carries a **`gep`**, which no earlier minted chain does, so `m3`/`m4`
//!   are the first check that the shape table's `gep` row round-trips.

use clean_verify::ir_mint::{self, Sx};

#[allow(dead_code)]
#[path = "crystal_a1_lineage/emitted_cfg.rs"]
mod emitted_cfg;

use emitted_cfg::{assert_lanes, parse_clean, parse_emitted};

const PREFIX: &str = "ir_pv";
const MODULE_CONST: &str = "ir_pv_module";
const FIXTURE: &str = include_str!("fixtures/simp_priority_value.trust-ir.txt");

fn tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_PV_TAGS).expect("the committed tag table must parse")
}

fn core_a() -> Sx {
    ir_mint::parse(ir_mint::IR_PV_CORE).expect("the committed core module must parse")
}

fn core_b() -> Sx {
    ir_mint::read_emitted(FIXTURE).expect("reader B must read the committed emitted trust-ir")
}

fn canon(sx: &Sx) -> String {
    ir_mint::print(sx).expect("a core module must print")
}

// ────────────────────────────────────────────────────────────────────────────
// M1 — the committed core is canonical, and it is not empty.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m1_committed_core_round_trips_its_printer() {
    let a = core_a();
    assert_eq!(
        canon(&a),
        ir_mint::IR_PV_CORE,
        "the committed core module is not what its own canonical printer produces"
    );
    // COVERAGE DENOMINATOR: two empty modules round-trip too.
    let text = ir_mint::IR_PV_CORE;
    assert!(
        text.contains("(gep (int 8) 0 (idx 5) true)"),
        "the committed core must carry the GEP this chain exists for:\n{text}"
    );
    assert!(
        text.contains("(load (uint 32) 6 false)"),
        "and the load THROUGH the gep's result %6:\n{text}"
    );
    assert!(
        text.contains("(const (uint 32) (int 1000))"),
        "and the Default arm's 1000:\n{text}"
    );
    assert!(
        !text.contains("(call "),
        "this body calls nothing; a core module with a call is not it"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M2 — reader B (the emitted TEXT) equals reader A (the artifact BINARY),
// modulo the declared unwitnessed ledger.
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
        ir_mint::IR_PV_DEFS,
        "the committed definition script is not what `mint` produces from the committed core \
         module. The committed script is the one `eval_ir_priority.rs` REGISTERS, so a difference \
         here means the proved module is again hand-edited."
    );
    assert!(
        ir_mint::IR_PV_RECORD.contains(&ir_mint::digest(&minted)),
        "the mint record's defs digest does not match the minted script"
    );
    assert!(
        ir_mint::IR_PV_RECORD.contains(&ir_mint::digest(ir_mint::IR_PV_CORE)),
        "the mint record's core digest does not match the committed core module"
    );
}

/// **The numeral policy, pinned in both directions.**
///
/// A datum outside the atom pool renders as a decimal literal; a POSITION
/// outside it is still a refusal. Both halves matter: dropping the second would
/// let a `(func 20 …)` mint a numeral the specification never introduced.
#[test]
fn m3_data_render_as_literals_and_positions_still_refuse() {
    let script = ir_mint::IR_PV_DEFS;
    for expect in [
        "IRTy.enum_ 127",
        "IRTy.uint_ 32",
        "IRTy.int_ 64",
        "IRConst.int_ 1000",
    ] {
        assert!(
            script.contains(expect),
            "the minted script must carry `{expect}` — a machine DATUM above the atom pool, \
             rendered as a decimal Nat literal:\n{script}"
        );
    }
    for expect in ["IRTy.int_ ir_d8", "IRConst.int_ ir_d4", "ir_d0", "ir_d7"] {
        assert!(
            script.contains(expect),
            "and everything at or below 16 must still render through the pool, so every artifact \
             minted before `Arg::Data` existed is byte-identical after it: `{expect}` is missing\n\
             {script}"
        );
    }
    assert!(
        !script.contains("ir_d127") && !script.contains("ir_d32") && !script.contains("ir_d64"),
        "and NOT as `ir_d127` / `ir_d32` / `ir_d64`. The first names a constant the \
         specification does not declare at all; the other two are declared, but as `Nat.add` \
         terms that `ir_mint::decode`'s delta+beta reducer cannot peel to `Nat.succ`, so reader \
         C would refuse the very module it is meant to read back.\n{script}"
    );

    // The refusal half, on a real body: `level_is_zero`'s SSA ids run to 20.
    let lz = ir_mint::parse(ir_mint::IR_LZ_CORE).expect("the lz core parses");
    let lz_tags = ir_mint::tags::parse(ir_mint::IR_LZ_TAGS).expect("the lz tag table parses");
    let e = ir_mint::mint(&lz, "ir_lz", &lz_tags)
        .expect_err("a POSITION above the pool must still refuse");
    assert!(
        format!("{e}").contains("atom pool"),
        "and the refusal must still name the atom pool: {e}"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M4 — the elaborated kernel term decodes back to the same core module.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m4_the_registered_kernel_term_decodes_to_the_committed_core() {
    let spec = clean_verify::test_utils::shared_spec();
    let decoded = ir_mint::decode(spec.env(), MODULE_CONST, &tags()).expect("decode ir_pv_module");
    assert_eq!(
        canon(&decoded),
        ir_mint::IR_PV_CORE,
        "the ELABORATED term registered under `{MODULE_CONST}` does not decode to the committed \
         core module. This is the check that keeps `mint` out of the trusted base: reader C never \
         sees the minter's output — and on this chain it is also the check that a `Nat` LITERAL \
         in the registered term reads back as the number it is."
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M5 — the A1 lane comparator, unchanged, over the MINTED script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m5_the_a1_comparator_agrees_over_the_minted_script() {
    let emitted = parse_emitted(FIXTURE);
    let clean = parse_clean(ir_mint::IR_PV_DEFS, "def ir_pv_b");
    assert_lanes(&emitted, &clean, "ir_pv (minted)");
    assert_eq!(emitted.blocks, clean.blocks);
    assert_eq!(emitted.cases, clean.cases);
    assert_eq!(emitted.default, clean.default);
    assert!(
        !emitted.geps.is_empty(),
        "coverage denominator: two empty gep lanes compare equal, and this body has one"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M7 — the tag table still records the interning id the artifact names, and
// the ALIAS it mints is a term the specification can elaborate.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m7_the_tag_table_still_matches_the_artifact() {
    assert!(
        FIXTURE.contains("load enum.127, ptr %0"),
        "the emitted body must still name enum.127; if it does not, the artifact was re-interned \
         and this table needs a one-line REVIEWED re-pin — which is a different thing from the \
         proved module having stopped matching"
    );
    assert!(
        ir_mint::IR_PV_TAGS.contains("\"crate_id\": 127"),
        "and the committed table must record it"
    );
}

/// **The fail-open `Tags::alias_defs` had until 2026-08-20.**
///
/// At any interning id above 16 it minted `ir_d{id}` — a constant the
/// specification does not declare. Nothing in `ir_mint` read the alias, so the
/// defect could only surface at registration, as an unknown identifier, in a
/// file that does not mention tag tables. This chain is the first with such an
/// id, so this is where the pin goes.
#[test]
fn m7_alias_the_interning_id_is_a_term_the_spec_can_elaborate() {
    let a = ir_mint::mint(&core_a(), PREFIX, &tags())
        .expect("the committed module must mint")
        .lines;
    assert_eq!(
        a.first().map(String::as_str),
        Some("def ir_pv_tprio : IRTy := IRTy.enum_ 127"),
        "the alias must name the crate id as a LITERAL, not as `ir_d127`"
    );
    // Exercise the other arm through the same public behavior, without making
    // the implementation helper part of `ir_mint`'s external API.
    let small_id = ir_mint::IR_PV_TAGS.replace("\"crate_id\": 127", "\"crate_id\": 13");
    assert_ne!(
        small_id,
        ir_mint::IR_PV_TAGS,
        "the fixture rewrite must bite"
    );
    let small_tags =
        ir_mint::tags::parse(&small_id).expect("the rewritten tag table must still parse");
    let small = ir_mint::mint(&core_a(), PREFIX, &small_tags)
        .expect("the same core under the small-id table must mint")
        .lines;
    assert_eq!(
        small.first().map(String::as_str),
        Some("def ir_pv_tprio : IRTy := IRTy.enum_ ir_d13"),
        "and at or below 16 it is still the atom pool, which is what keeps `ir_h2.defs.txt` \
         byte-identical across this change"
    );
}
