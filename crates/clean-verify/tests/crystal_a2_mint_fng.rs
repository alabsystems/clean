// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! The A2 mint gate for `ir_fng` — `reduce_float_neg::{closure#0}`, the only
//! chained body whose emitted instruction is a `unop`.
//!
//! WHY A SEPARATE FILE, and not a row in `crystal_a2_mint_floats.rs`. That gate
//! is written for the ONE-BINOP shape: its M1 asserts
//! `(binop {op} (float 64) 1 2)` against every row. This body emits
//! `(fcmp oeq (float 64) 1 2)`, so adding it there would fail M1 — and the only
//! way to make it pass would be to weaken an assertion that is doing real work
//! for the four binop chains. A gate is not a place to make room.
//!
//! NO COMMITTED FIXTURE, AND WHY — the one thing this gate cannot check.
//! Reader B reads a fixture in `tests/fixtures/`, and a fixture there needs a
//! row in the record `CURRENT_REBASELINE` names. Measured 2026-09-20: the dump
//! this chain was cut from is a LATER NUMBERING ERA than the committed set —
//! `crystal_fixture_freshness.py` reports `FRESH: no chained body's instructions
//! have moved`, and simultaneously that functy/loc-file/type-table/callee/global
//! indices all moved. Giving this fixture a row means re-pointing
//! `CURRENT_REBASELINE`, which re-pins all 22 fixtures to that era and would
//! move `ir_hlb.tags.json`'s pinned `functy 435` (this dump says 364) out from
//! under its own gate. That is a reviewed owner operation, so the fixture is NOT
//! committed and the reader-A/reader-B agreement (M2) is NOT claimed here. What
//! remains is reader A's projection, which the mint reproduces byte for byte.
//!
//! WHAT THIS CHAIN IS, stated so it cannot inflate. `fcmp` already has battery
//! rows from the W4 SYNTHETIC lane (`w4_chains.rs`), which covers all twelve
//! `FCmpOp` predicates over authored micro-modules. This adds nothing to that
//! coverage. What it adds is the KIND of evidence for one predicate: `oeq` at
//! binary64 is now witnessed by an emitted body from the shipped kernel rather
//! than by a module an author wrote. It is NOT A0-eligible — the body's
//! `derived_mir` verdict is `unsupported` — and it is not a claim about
//! `Level::is_zero`'s refusing gates.

use clean_verify::ir_mint::{self, Sx};

const PREFIX: &str = "ir_fng";

fn core_a() -> Sx {
    ir_mint::parse(ir_mint::IR_FNG_CORE).expect("the committed core module must parse")
}

/// M1 — the committed core is canonical, and it is the one-`fcmp` body.
#[test]
fn m1_committed_core_round_trips_its_printer() {
    assert_eq!(
        ir_mint::print(&core_a()).expect("a core module must print"),
        ir_mint::IR_FNG_CORE,
        "the committed core module is not what its own canonical printer produces"
    );
    // COVERAGE DENOMINATOR: an empty module round-trips too, so pin the content.
    assert!(
        ir_mint::IR_FNG_CORE.contains("(unop fneg (float 64) 1)"),
        "the committed core must carry the one fneg this chain exists for:\n{}",
        ir_mint::IR_FNG_CORE
    );
    assert!(
        ir_mint::IR_FNG_CORE.contains("(ret (vals 2))"),
        "and the ret of ITS RESULT, not an operand:\n{}",
        ir_mint::IR_FNG_CORE
    );
    // The predicate is load-bearing: `oeq` and `une` are different programs on
    // a NaN operand, and both print as an `fcmp` of the same shape.
    for wrong in ["(unop fabs ", "(unop not ", "(binop fsub "] {
        assert!(
            !ir_mint::IR_FNG_CORE.contains(wrong),
            "the committed core carries `{wrong}`, which is a different operator -- `fabs` and a `0 - x` subtraction agree with `fneg` on almost every value"
        );
    }
    for absent in ["(call ", "(switch ", "(load ", "(store ", "(fcmp "] {
        assert!(
            !ir_mint::IR_FNG_CORE.contains(absent),
            "this body has no `{absent}`; a core module with one is not it"
        );
    }
}

/// M3 — the mint reproduces the committed script. This is the fail-closed one:
/// the committed script is what the spec stage registers, so a difference here
/// means the proved module was hand-edited.
#[test]
fn m3_mint_reproduces_the_registered_script() {
    let minted = ir_mint::mint(&core_a(), PREFIX, &tags())
        .expect("mint must accept the committed core and tags")
        .text();
    assert_eq!(
        minted,
        ir_mint::IR_FNG_DEFS,
        "the committed definition script is not what `mint` produces from the committed core \
         module"
    );
    assert!(
        ir_mint::IR_FNG_RECORD.contains(&ir_mint::digest(&minted)),
        "the mint record's defs digest does not match the minted script"
    );
    assert!(
        ir_mint::IR_FNG_RECORD.contains(&ir_mint::digest(ir_mint::IR_FNG_CORE)),
        "the mint record's core digest does not match the committed core module"
    );
    // No aggregate, no alias: the script's first line is the entry block.
    assert!(
        minted.starts_with("def ir_fng_b0 : IRBlock"),
        "an aggregate alias appeared in a chain whose aggregate lanes are measured empty:\n{minted}"
    );
}

/// The `functy` pin is 319 and NOT `ir_fa`'s 381, and that is a measurement:
/// the four `f64 -> f64` closures share one signature entry, while this body
/// returns `bool`.
#[test]
fn the_functy_pin_is_this_body_s_own_signature() {
    assert!(
        ir_mint::IR_FNG_TAGS.contains("\"functy\": 318"),
        "the tag table's functy pin moved; 318 is this signature's own entry, not ir_fa's 381 or ir_fbq's 319"
    );
}

fn tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_FNG_TAGS).expect("the committed tag table must parse")
}
