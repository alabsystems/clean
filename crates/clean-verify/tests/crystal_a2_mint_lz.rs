// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A2 — the MINT gate for the DESIGNATED TARGET,
//! `level::Level::is_zero`, and the wall it machine-checks.**
//!
//! Same three readers and the same questions as `crystal_a2_mint.rs`; read
//! that file's header and `src/ir_mint/mod.rs` for what this establishes and
//! what it does not. This chain is different from the seventeen before it in
//! one way that is the whole point of the file: its minted module
//! (`ir_lz_module`, registered 2026-08-22 by `eval_ir_level_minted.rs`) is
//! NOT the module the chain's A4/A5 theorems are about. Those theorems —
//! `ir_lzm_correct`, `ir_lzm_machine_sound` — quantify over the hand
//! SEMANTIC MODEL `ir_lzm_module`, which until 2026-08-22 carried the chain's
//! name and differs from the emitted body in FOUR classes:
//!
//! 1. the switch: five arms + `unreachable` default + flag TRUE in the model,
//!    four arms + `IMax` on the default edge + flag FALSE as emitted;
//! 2. per-arm `ret` in the model, `br` to a `bool`-parameter join as emitted;
//! 3. the deref INLINED as `extractfield` + null-check + `assert` in the model,
//!    `gep` + `call <LevelArc as Deref>::deref` as emitted;
//! 4. three emitted-only blocks — 10 against 7.
//!
//! `the_wall_between_the_model_and_the_minted_module` prints that diff
//! verbatim (reader C's decode of BOTH registered terms against reader A's
//! projection) and fails if the model ever silently agrees with the artifact
//! or the minted module ever silently disagrees with it. Over the minted
//! module the A4 sentence is REFUTED — kernel-checked as
//! `ir_lz_minted_refutes_a4_on_max` — because the module calls a function it
//! does not define. Decision memo:
//! `designs/2026-08-22-is-zero-model-vs-minted-decision.md`.
//!
//! **What this gate does NOT cover, and why.** `has_cubical_layer`'s gate
//! carries the producer A/B record (M6) and the mutation matrix; this chain
//! postdates the A/B record (two reader-A dumps, `ir_lz.a152.prov.json` and
//! `ir_lz.b039.prov.json`, one core digest) and the mutation matrix is
//! chain-generic. The callee-identity lane — the only lane this body needs
//! that no other body does — stays in `crystal_a2_mint/callee_identity.rs`.

use clean_verify::ir_mint::{self, Sx};
use clean_verify::vacuity_firewall::env_knows;

#[allow(dead_code)]
#[path = "crystal_a1_lineage/emitted_cfg.rs"]
mod emitted_cfg;

use emitted_cfg::{assert_lanes, parse_clean, parse_emitted};

const PREFIX: &str = "ir_lz";
const MINTED_MODULE: &str = "ir_lz_module";
const MODEL_MODULE: &str = "ir_lzm_module";
const FIXTURE: &str = include_str!("fixtures/level_is_zero.trust-ir.txt");

fn tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_LZ_TAGS).expect("the committed tag table must parse")
}

fn core_a() -> Sx {
    ir_mint::parse(ir_mint::IR_LZ_CORE).expect("the committed core module must parse")
}

/// Reader B, told which crate id is the body's own (this is the one chain
/// where that matters: the text names its callees by whole-crate index).
fn core_b() -> Sx {
    ir_mint::read_emitted_with_self(FIXTURE, tags().self_func())
        .expect("reader B must read the committed emitted trust-ir")
        .0
}

fn canon(sx: &Sx) -> String {
    ir_mint::print(sx).expect("a core module must print")
}

// ────────────────────────────────────────────────────────────────────────────
// M1 — the committed core is canonical, and it is the branching, calling body.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m1_committed_core_round_trips_its_printer() {
    let a = core_a();
    assert_eq!(
        canon(&a),
        ir_mint::IR_LZ_CORE,
        "the committed core module is not what its own canonical printer produces"
    );
    let text = ir_mint::IR_LZ_CORE;
    assert_eq!(text.matches("(block ").count(), 10, "ten blocks");
    assert!(
        text.contains("(call 1 (args 9))") && text.contains("(call 0 (args 12))"),
        "is_zero calls its deref callee (foreign, index 1) and then itself (index 0):\n{text}"
    );
    assert_eq!(text.matches("(call 1 ").count(), 3, "three deref calls");
    assert_eq!(text.matches("(call 0 ").count(), 3, "three self-calls");
    assert_eq!(text.matches("(gep ").count(), 3, "three geps");
    assert!(
        text.contains("(case 2 4 (args))) false)"),
        "the switch's exhaustive flag is the MEASURED false:\n{text}"
    );
    assert!(
        !text.contains("unreachable") && !text.contains("assert"),
        "no trap and no assert anywhere in the emitted body"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M2 — reader B equals reader A modulo the one slot the text cannot show.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m2_reader_b_equals_reader_a_modulo_the_switch_flag() {
    let (masked, ledger) =
        ir_mint::mask_text_unwitnessed(&core_a()).expect("reader A's module must mask");
    assert_eq!(
        canon(&masked),
        canon(&core_b()),
        "the artifact BINARY (reader A) and the emitted TEXT (reader B) disagree about this body"
    );
    assert_eq!(ledger.len(), 1, "exactly one unwitnessed slot: {ledger:?}");
    assert_eq!(
        ledger[0].to_string(),
        "bb0#2 switch arg4",
        "the switch's exhaustive flag, third node of the entry block"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M3 — `mint` of the committed core IS the committed, REGISTERED script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m3_mint_reproduces_the_registered_script() {
    let minted = ir_mint::mint(&core_a(), PREFIX, &tags())
        .expect("the ir_d0..ir_d63 pool mints the designated target")
        .text();
    assert_eq!(
        minted,
        ir_mint::IR_LZ_DEFS,
        "the committed definition script is not what `mint` produces from the committed core \
         module. The committed script is the one `eval_ir_level_minted.rs` REGISTERS, so a \
         difference here means the minted module is hand-edited."
    );
    assert!(
        ir_mint::IR_LZ_RECORD.contains(&ir_mint::digest(&minted)),
        "the mint record's defs digest does not match the minted script"
    );
    assert!(
        ir_mint::IR_LZ_RECORD.contains(&ir_mint::digest(ir_mint::IR_LZ_CORE)),
        "the mint record's core digest does not match the committed core module"
    );
    assert!(
        minted.contains("ir_d20"),
        "the atom the old pool lacked is exercised:\n{minted}"
    );
    assert!(
        minted.contains("IRInst.call ir_d1") && minted.contains("IRInst.call ir_d0"),
        "both callees mint, self at 0 and the deref at 1:\n{minted}"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M5 — the A1 lane comparator, unchanged, over the MINTED script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m5_the_a1_comparator_agrees_over_the_minted_script() {
    let emitted = parse_emitted(FIXTURE);
    let clean = parse_clean(ir_mint::IR_LZ_DEFS, "def ir_lz_b");
    assert_lanes(&emitted, &clean, "ir_lz (minted)");
    assert_eq!(emitted.blocks, clean.blocks);
    assert_eq!(emitted.cases, clean.cases);
    assert_eq!(emitted.default, clean.default);
    assert_eq!(emitted.param_blocks, clean.param_blocks);
    assert_eq!(emitted.blocks.len(), 10, "coverage denominator");
}

// ────────────────────────────────────────────────────────────────────────────
// M7 — the tag table still records the interning ids the artifact names.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m7_the_tag_table_still_matches_the_artifact() {
    assert!(
        FIXTURE.contains("(functy.0)"),
        "the emitted body must still carry signature index 0; if it does not, the artifact was \
         re-interned and this table needs a one-line REVIEWED re-pin"
    );
    assert!(ir_mint::IR_LZ_TAGS.contains("\"functy\": 0"));
    assert_eq!(FIXTURE.matches("enum.2").count(), 1, "one load of enum.2");
    assert!(ir_mint::IR_LZ_TAGS.contains("\"crate_id\": 2"));
    for (id, count) in [(3905u32, 3usize), (3894, 3)] {
        assert_eq!(
            FIXTURE.matches(&format!("@func.{id}(")).count(),
            count,
            "@func.{id} is called {count} times in the fixture"
        );
        assert!(
            ir_mint::IR_LZ_TAGS.contains(&format!("\"crate_id\": {id}")),
            "and the committed table pins it"
        );
    }
}

// ────────────────────────────────────────────────────────────────────────────
// M8 — the mint discriminates this body from every chain that calls nothing.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m8_the_mint_discriminates_the_calling_body() {
    for (name, other) in [
        ("ir_h2", ir_mint::IR_H2_CORE),
        ("ir_ko", ir_mint::IR_KO_CORE),
        ("ir_fs", ir_mint::IR_FS_CORE),
    ] {
        assert_ne!(
            ir_mint::digest(ir_mint::IR_LZ_CORE),
            ir_mint::digest(other),
            "ir_lz and {name} must not share a core digest"
        );
    }
    assert!(ir_mint::IR_LZ_DEFS.contains("IRInst.call"));
    for (name, defs) in [
        ("ir_h2", ir_mint::IR_H2_DEFS),
        ("ir_ko", ir_mint::IR_KO_DEFS),
        ("ir_fs", ir_mint::IR_FS_DEFS),
    ] {
        assert!(
            !defs.contains("IRInst.call"),
            "{name} calls nothing; is_zero is the only minted body that does"
        );
    }
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
    assert_eq!(tys, ["ptr"], "the &Level receiver");
    let joins: Vec<(u32, &str)> = p
        .interface
        .block_params
        .iter()
        .map(|s| (s.block, s.ty.as_str()))
        .collect();
    assert_eq!(
        joins,
        [(6, "bool"), (9, "bool")],
        "the two join blocks' bool parameters — the class-2 divergence from the model"
    );
    assert_eq!(p.interface.aligns, ["load:None"]);
}

/// The pins BITE: a by-value receiver, an aligned load, a foreign calling
/// convention and a moved `functy` are each refused, and the refusal names
/// the slot.
#[test]
fn m10_the_interface_pins_bite() {
    let t = tags();
    for (from, to, slot) in [
        ("bb0(%0: ptr):", "bb0(%0: enum.2):", "parameter"),
        (
            "load enum.2, ptr %0",
            "load enum.2, ptr %0, align 8",
            "align",
        ),
        ("rustcc fn @", "ccc fn @", "calling convention"),
        ("(functy.0)", "(functy.1)", "signature index"),
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
// M4 + THE WALL — reader C over BOTH registered terms. One full Specification
// build, LAST.
// ────────────────────────────────────────────────────────────────────────────

/// The registered MINTED term decodes to the committed core (M4 for the
/// designated target, for the first time), and the registered MODEL does NOT
/// — the four-class divergence, printed verbatim.
#[test]
fn the_wall_between_the_model_and_the_minted_module() {
    let spec = clean_verify::test_utils::shared_spec();
    let t = tags();

    // M4: the minted module IS the artifact projection.
    let minted = ir_mint::decode(spec.env(), MINTED_MODULE, &t)
        .unwrap_or_else(|e| panic!("decode {MINTED_MODULE}: {e}"));
    assert_eq!(
        canon(&minted),
        ir_mint::IR_LZ_CORE,
        "the ELABORATED term registered under `{MINTED_MODULE}` does not decode to the \
         committed core module. This is the check that keeps `mint` out of the trusted base: \
         reader C never sees the minter's output."
    );

    // THE WALL: the model is a different program, and it stays one until the
    // A4/A5 theorems are restated — deliberately, never discovered green.
    let model = ir_mint::decode(spec.env(), MODEL_MODULE, &t)
        .unwrap_or_else(|e| panic!("decode {MODEL_MODULE}: {e}"));
    let hand = canon(&model);
    assert_ne!(
        hand,
        ir_mint::IR_LZ_CORE,
        "the hand model `{MODEL_MODULE}` and the emitted body have AGREED — the A4/A5 theorems \
         are then about the artifact and this wall, `crystal_a1_lineage/level_is_zero.rs`, and \
         the status page's link-4 row must all move together, deliberately"
    );
    let mut report = String::from(
        "\nlevel_is_zero MINTED (ir_lz_module, == reader A) vs MODEL (ir_lzm_module) — \
         core-module line diff:\n",
    );
    for d in diff_lines(ir_mint::IR_LZ_CORE, &hand) {
        report.push_str(&d);
        report.push('\n');
    }
    println!("{report}");

    // The four classes are visible in the decoded model, not only in prose.
    assert!(hand.contains("(unreachable)") && !ir_mint::IR_LZ_CORE.contains("(unreachable)"));
    assert!(hand.contains("(assert ") && !ir_mint::IR_LZ_CORE.contains("(assert "));
    assert!(!hand.contains("(gep ") && !hand.contains("(call 1 "));
    assert_eq!(hand.matches("(block ").count(), 7);
}

/// The kernel-checked facts about the minted module are registered: three
/// constant-arm returns, two STUCK recursive arms, the represented-input
/// witness, and the refutation of A4 over it.
#[test]
fn the_stuck_witnesses_and_the_refutation_are_registered() {
    let spec = clean_verify::test_utils::shared_spec();
    for name in [
        "ir_lz_on_zero",
        "ir_lz_on_succ",
        "ir_lz_on_param",
        "ir_lz_on_max_stuck",
        "ir_lz_on_imax_stuck",
        "encodes_live_ref_maxzz_witness",
        "ir_lz_minted_refutes_a4_on_max",
        // and the model's theorems, under their honest names
        "ir_lzm_correct",
        "ir_lzm_machine_sound",
        "ir_lzm_never_faults",
    ] {
        assert!(
            env_knows(spec.env(), name),
            "{name} must be registered — the spec built, so it elaborated and kernel-checked"
        );
    }
    for gone in ["ir_lz_correct", "ir_lz_machine_sound", "ir_lz_cost"] {
        assert!(
            !env_knows(spec.env(), gone),
            "{gone} is the old name of a MODEL theorem; it must not reappear under the chain's \
             prefix, where a reader would take it for a theorem about the emitted body"
        );
    }
}

/// A minimal two-column line diff: `-` minted/emitted-only, `+` model-only.
fn diff_lines(a: &str, b: &str) -> Vec<String> {
    let al: Vec<&str> = a.lines().collect();
    let bl: Vec<&str> = b.lines().collect();
    let mut out = Vec::new();
    let (mut i, mut j) = (0usize, 0usize);
    while i < al.len() || j < bl.len() {
        match (al.get(i), bl.get(j)) {
            (Some(x), Some(y)) if x == y => {
                out.push(format!("  {x}"));
                i += 1;
                j += 1;
            }
            (Some(x), Some(y)) => {
                let x_in_b = bl[j..].iter().position(|l| l == x);
                let y_in_a = al[i..].iter().position(|l| l == y);
                match (x_in_b, y_in_a) {
                    (Some(xb), Some(ya)) if ya <= xb => {
                        out.push(format!("- {}", al[i]));
                        i += 1;
                    }
                    (Some(_), _) => {
                        out.push(format!("+ {}", bl[j]));
                        j += 1;
                    }
                    (None, Some(_)) => {
                        out.push(format!("- {}", al[i]));
                        i += 1;
                    }
                    (None, None) => {
                        out.push(format!("- {x}"));
                        out.push(format!("+ {y}"));
                        i += 1;
                        j += 1;
                    }
                }
            }
            (Some(x), None) => {
                out.push(format!("- {x}"));
                i += 1;
            }
            (None, Some(y)) => {
                out.push(format!("+ {y}"));
                j += 1;
            }
            (None, None) => {}
        }
    }
    out
}
