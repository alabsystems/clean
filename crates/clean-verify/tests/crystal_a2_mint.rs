// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A2 — the MINT gate: the proved module is GENERATED from the
//! emitted artifact, and three independent readers agree on it.**
//!
//! A1 asked whether a hand transcription still matched the artifact. This gate
//! asks a different question — whether the registered module is a transcription
//! at all — and answers it by generating the module and checking the generation
//! from three directions. `src/ir_mint/mod.rs` states what that does and does
//! not establish; read it before quoting this gate.
//!
//! ## The checks, and what each one can see that the others cannot
//!
//! | | check | catches |
//! |---|---|---|
//! | **M1** | the committed core module round-trips its own canonical printer byte for byte | a reader that dropped a field: it could not print the field back |
//! | **M2** | reader B (the emitted TEXT, read in this crate) equals reader A (the artifact BINARY, read by `scripts/crystal_a2_project`) modulo the declared unwitnessed ledger | any disagreement between the artifact and the text about anything the text prints |
//! | **M3** | `mint` of the committed core is byte-equal to the committed, REGISTERED definition script | a non-deterministic or edited generation; the committed script is the one `eval_ir_mode.rs` registers |
//! | **M4** | reader C — the ELABORATED KERNEL TERM registered under `ir_h2_module` — decodes back to the committed core | a minter defect: reader C never sees the minter's output |
//! | **M5** | the A1 lane comparator, unchanged, over the MINTED script against the emitted text | anything the lane set catches that the core form's own equality would not phrase the same way |
//! | **M6** | the producer A/B record: three real dumps, every `func_id` moved, one `enum` id moved, every core digest identical | a normalization that does not actually absorb renumbering |
//! | **M7** | the committed tag table still records the crate-level interning ids the artifact names | a re-interning — reported as a stale PIN, not as a module that stopped matching |
//! | **M8** | the function's own id and its callee ids are ONE namespace, and the `funcs` pin says which function each index is | two functions denoted by one numeral: `is_zero(deref(p))` and `deref(is_zero(p))` projected to the SAME core module until 2026-08-20 |
//! | **M9** | every field the artifact carries and the core module does not is listed in `data/crystal_mint_blind_slots.json`, anchored to the line that erases it | an erasure nobody wrote down — which is how M8's collision survived M1 through M7 |
//! | **M11** | `Switch.exhaustive_enum_unreachable` and `CallIndirect`'s signature and convention operands cannot change the machine's step, at every module, state and operand list | an erasure justified by a comment: every "nothing dispatches on the flag" claim rested on reading one line of `ir_exec` |
//! | **M10** | the artifact's INTERFACE — the function's name, every parameter's TYPE, every `align` operand, the KINDS of annotation clause — equals the chain's pinned table | `bb0(%0: ptr)` against `bb0(%0: Rc<enum.13>)`: a `&CleanMode` against an `Rc<CleanMode>`, where the entry `load` reads the discriminant in one and the refcount header in the other, and which were ONE core module until 2026-08-20 |
//!
//! **M7 is the split, and it is the point.** `enum.13` is a crate table entry;
//! it moves under a producer change with no instruction changed
//! (`expr_path_step_clone`'s moved 181 → 176 over the three dumps M6 records).
//! The core module the digest is taken over carries the canonical FIRST-USE
//! index instead, and the crate id lives in `generated/ir_h2.tags.json`, which
//! the minter reads to emit `def ir_h2_tmode : IRTy := IRTy.enum_ ir_d13` — so
//! the REGISTERED term still names it, exactly as the 2026-08-19 `load_tys`
//! lane requires. The gate therefore still stops on a re-interning, but M7 says
//! *which* thing moved: a one-line reviewed re-pin, not a re-transcription.
//!
//! **M2 is blind in exactly one slot and says so.**
//! `Switch.exhaustive_enum_unreachable` is never printed by trust-ir's
//! `Display`, so reader B writes `?` there and the mask makes the comparison
//! exact rather than lenient. That slot has one in-repo witness — reader A —
//! and the mutation matrix below shows M3/M4 catching a change there while M2
//! cannot. It is the cell that no text-anchored gate can cover, and it is the
//! cell where the hand transcription was WRONG (`Bool.true` against a measured
//! `false` on three producers and four sibling chains).
//!
//! ## Falsification
//!
//! `mutation::mutation_matrix` perturbs the artifact and asserts the gate
//! REJECTS, one row per perturbation kind, printing every verdict — and it
//! FAILS if any row passes every check. Its last row is the negative control
//! that matters most in practice: pure `enum`/`functy`/`#loc` renumbering must
//! NOT fire, because a gate that alarms on re-interning gets switched off
//! within a week, taking the real check with it.

use clean_verify::ir_mint::{self, Sx};

// The A1 lane comparator, INCLUDED UNCHANGED. It is reader D of this gate: it
// reads the emitted text on one side and Clean spec source on the other, and
// neither path goes through the minter. Most of its surface is unused here, so
// the include is dead-code-allowed rather than trimmed — trimming it would fork
// the comparator, which is the one thing it must not do.
#[allow(dead_code)]
#[path = "crystal_a1_lineage/emitted_cfg.rs"]
mod emitted_cfg;

use emitted_cfg::{assert_lanes, parse_clean, parse_emitted};

// The falsification battery: one row per perturbation kind, each asserted to be
// REJECTED, plus the negative control that pure crate-level renumbering is NOT.
// Split out because the gate and its falsification are two readable halves, and
// because this file was over the 500-line convention with both in it.
#[path = "crystal_a2_mint/mutation.rs"]
mod mutation;

// M8 — callee identity. `level_is_zero` is the only chained body that calls
// anything, and the 2026-08-20 namespace collision lived there: the function's
// own id and its callee ids were two counters both starting at 0, so one
// numeral denoted two functions. This lane carries the constructed
// counterexample and the pin that closes it.
#[path = "crystal_a2_mint/callee_identity.rs"]
mod callee_identity;

// M9 — the blind-slot list: every field the artifact carries and the core
// module does not, in one committed file, anchored to the source line that
// erases it.
#[path = "crystal_a2_mint/blind_slots.rs"]
mod blind_slots;

// M10 — the interface lane: the function's NAME, every parameter's TYPE, every
// `align` operand and the KINDS of annotation clause, compared against the
// chain's pinned table. Four of the five constructed witnesses in
// `data/crystal_mint_blind_slots.json` stop being accepted here.
#[path = "crystal_a2_mint/interface.rs"]
mod interface;

// M11 — the three operands `ir_exec` drops, proved inert. The justification a
// row that stays an ERASURE owes: a kernel-checked theorem, to the standard
// `ir_ty_is_agg_enum_any` set, instead of a comment.
#[path = "crystal_a2_mint/inertness.rs"]
mod inertness;

pub(crate) const PREFIX: &str = "ir_h2";
const MODULE_CONST: &str = "ir_h2_module";
pub(crate) const FIXTURE: &str = include_str!("fixtures/has_cubical_layer.trust-ir.txt");
pub(crate) const PRODUCER_AB: &str =
    include_str!("../src/spec/core_spec/generated/ir_mint.producer_ab.json");

pub(crate) fn tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_H2_TAGS).expect("the committed tag table must parse")
}

fn core_a() -> Sx {
    ir_mint::parse(ir_mint::IR_H2_CORE).expect("the committed core module must parse")
}

pub(crate) fn core_b() -> Sx {
    ir_mint::read_emitted(FIXTURE).expect("reader B must read the committed emitted trust-ir")
}

pub(crate) fn canon(sx: &Sx) -> String {
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
        ir_mint::IR_H2_CORE,
        "the committed core module is not in canonical form. print(parse(x)) == x is the witness \
         that the reader dropped nothing: a field it failed to read is a field it cannot print \
         back."
    );

    // COVERAGE DENOMINATOR. Two empty modules compare equal, so pin what the
    // artifact actually contains before comparing anything to it.
    let mut blocks = 0usize;
    let mut insts = 0usize;
    ir_mint::core::for_each_inst(&a, |_, _, _| {
        insts += 1;
        Ok(())
    })
    .expect("walk");
    for f in a.tagged("module").expect("module")[0]
        .tagged("funcs")
        .expect("funcs")
    {
        blocks += f.tagged("func").expect("func")[3]
            .tagged("blocks")
            .expect("blocks")
            .len();
    }
    assert_eq!(blocks, 5, "has_cubical_layer emits five blocks");
    assert_eq!(insts, 10, "has_cubical_layer emits ten instructions");
    assert!(
        canon(&a).contains("(load (enum 0) 0 false)"),
        "the core form names the aggregate by its CANONICAL first-use index, never by the crate \
         table entry — that is what keeps a re-interning out of the module's identity"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M2 — readers A and B agree, and the blindness is declared, not tolerated.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m2_binary_and_text_readers_agree_modulo_a_declared_ledger() {
    let (masked, ledger) = ir_mint::mask_text_unwitnessed(&core_a()).expect("mask");
    let names: Vec<String> = ledger.iter().map(ToString::to_string).collect();
    assert_eq!(
        names,
        vec!["bb0#2 switch arg4".to_string()],
        "the set of fields the emitted TEXT cannot witness must be exactly the declared one. If \
         this grew, a new blind slot appeared and the gate must name it rather than absorb it."
    );
    assert_eq!(
        canon(&masked),
        canon(&core_b()),
        "reader A (the artifact BINARY, via the offline projector) and reader B (the emitted \
         TEXT, read in this crate) disagree. Masked slots: {names:?}"
    );
}

#[test]
fn m2_the_blind_slot_is_the_one_the_hand_transcription_got_wrong() {
    // Not decoration: this is the measured defect the mint mechanism found.
    // The artifact says `false`; `SRC_IR_H2_B0` said `Bool.true`.
    let a = canon(&core_a());
    assert!(
        a.contains("(cases (case 2 1 (args)) (case 3 2 (args))) false)"),
        "the artifact's switch must carry exhaustive_enum_unreachable = false; the committed core \
         says otherwise:\n{a}"
    );
    assert!(
        ir_mint::IR_H2_DEFS.contains("Bool.true"),
        "the minted script should still carry a Bool.true somewhere (the two const arms)"
    );
    let b0 = ir_mint::IR_H2_DEFS
        .lines()
        .find(|l| l.starts_with("def ir_h2_b0 "))
        .expect("a minted b0");
    assert!(
        ir_mint::IR_H2_DEFS.contains("def ir_h2_tmode : IRTy := IRTy.enum_ ir_d13"),
        "the minted script must carry the 2026-08-19 load-type correction, derived from the \
         committed tag table rather than repaired by hand"
    );
    assert!(
        b0.contains("IRInst.load ir_h2_tmode ir_d0 Bool.false"),
        "…and the entry block must load through it:\n{b0}"
    );
    assert!(
        b0.ends_with("Bool.false)))"),
        "the minted b0's switch must end in the measured exhaustive flag, not the transcribed \
         one:\n{b0}"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M3 — the registered script is what `mint` produces, byte for byte.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m3_mint_reproduces_the_registered_script() {
    let minted = ir_mint::mint(&core_a(), PREFIX, &tags())
        .expect("mint")
        .text();
    assert_eq!(
        minted,
        ir_mint::IR_H2_DEFS,
        "the committed definition script is not what `mint` produces from the committed core \
         module. The committed script is the one `eval_ir_mode.rs` REGISTERS, so a difference \
         here means the proved module is again hand-edited."
    );
    assert!(
        ir_mint::IR_H2_RECORD.contains(&ir_mint::digest(&minted)),
        "the mint record's defs digest does not match the minted script"
    );
    assert!(
        ir_mint::IR_H2_RECORD.contains(&ir_mint::digest(ir_mint::IR_H2_CORE)),
        "the mint record's core digest does not match the committed core module"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M4 — the elaborated kernel term decodes back to the same core module.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m4_the_registered_kernel_term_decodes_to_the_committed_core() {
    let spec = clean_verify::test_utils::shared_spec();
    let decoded = ir_mint::decode(spec.env(), MODULE_CONST, &tags()).expect("decode ir_h2_module");
    assert_eq!(
        canon(&decoded),
        ir_mint::IR_H2_CORE,
        "the ELABORATED term registered under `{MODULE_CONST}` does not decode to the committed \
         core module. This is the check that keeps `mint` out of the trusted base: reader C never \
         sees the minter's output."
    );
}

#[test]
fn m4_decode_discriminates_between_two_registered_modules() {
    // Negative control for reader C. A decoder that returned a constant, or
    // that read the wrong constant, would pass M4 and be useless.
    let spec = clean_verify::test_utils::shared_spec();
    let h2 = ir_mint::decode(spec.env(), MODULE_CONST, &tags()).expect("decode ir_h2_module");
    // `ir_ko_module` loads `enum.2` (Level). Decoding it under h2's tag table
    // must REFUSE rather than silently renumber, so the control is run under a
    // table that lists Level's id and nothing else.
    let ko_tags = ir_mint::tags::parse(
        r#"{"body":"t","interface":{"linkage":"external","calling_conv":"rustcc","functy":0,"producer":null,"params":[],"block_params":[],"aligns":[],"clauses":[]},"enums":[{"canonical":0,"crate_id":2,"alias":"ir_ko_tenum"}],"structs":[],"funcs":[]}"#,
    )
    .expect("a one-row table");
    assert!(
        ir_mint::decode(spec.env(), "ir_ko_module", &tags()).is_err(),
        "decoding a module that names an unlisted crate id must refuse, not renumber"
    );
    let ko = ir_mint::decode(spec.env(), "ir_ko_module", &ko_tags).expect("decode ir_ko_module");
    assert_ne!(
        canon(&h2),
        canon(&ko),
        "reader C returned the same core module for two different registered modules"
    );
    // And it really did read `level_kind_ord`: that body's answers are u8
    // constants, not bools.
    assert!(
        canon(&ko).contains("(const (uint 8)"),
        "ir_ko_module should decode with u8 constants:\n{}",
        canon(&ko)
    );
}

#[test]
fn m4_decode_is_fail_closed_on_an_absent_constant() {
    let spec = clean_verify::test_utils::shared_spec();
    let e = ir_mint::decode(spec.env(), "ir_no_such_module", &tags()).expect_err("must refuse");
    assert!(
        format!("{e}").contains("is not a constant"),
        "unexpected refusal: {e}"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M5 — the A1 lane comparator, unchanged, over the MINTED script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m5_the_lane_comparator_agrees_with_the_minted_script() {
    // The WHOLE minted script, aliases included: `parse_clean`'s `load_tys`
    // lane resolves `ir_h2_tmode` through the alias definitions, so filtering
    // them out would leave that lane comparing an unresolved name.
    let minted_blocks = ir_mint::IR_H2_DEFS.to_string();
    let emitted = parse_emitted(FIXTURE);
    let clean = parse_clean(&minted_blocks, "def ir_h2_b");
    assert_lanes(&emitted, &clean, "has_cubical_layer (minted)");
}

// ────────────────────────────────────────────────────────────────────────────
// M7 — the tag table still describes the artifact.
//
// This is the check that keeps the two questions apart. "Does the proved module
// denote the same program?" is M1..M5 and it does not depend on a crate table
// entry. "Which crate table entry did this build name?" is here, and it is the
// one that moves under a producer change. A re-interning must land HERE, as a
// one-line reviewed update, and not there, as a proof about a different
// program.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m7_the_tag_table_still_describes_the_artifact() {
    let t = tags();
    let (_, observed) = ir_mint::read_emitted_with_tags(FIXTURE).expect("reader B");
    assert_eq!(
        observed.enums.len(),
        t.enums.len(),
        "the emitted body names {} enum(s); the tag table lists {}",
        observed.enums.len(),
        t.enums.len()
    );
    for (canonical, crate_id) in observed.enums.iter().enumerate() {
        let idx = u32::try_from(canonical).expect("small");
        let (recorded, alias) = t.enum_alias(idx).expect("a listed canonical index");
        assert_eq!(
            recorded, crate_id,
            "TAG DRIFT, not a module change: canonical enum {idx} (`{alias}`) is recorded as \
             crate id {recorded} and the emitted body names {crate_id}. The proved module is \
             unaffected — re-pin the table in `generated/ir_h2.tags.json` after checking the \
             artifact, exactly as `data/crystal_enum_tag_pin.json` is re-pinned."
        );
    }
    assert!(
        observed.structs.is_empty() && t.structs.is_empty(),
        "this body names no struct"
    );

    // …and reader A's independent record of the same ids.
    let rec: serde_json::Value =
        serde_json::from_str(PRODUCER_AB).expect("the producer A/B record must parse");
    let row = rec["rows"]
        .as_array()
        .expect("rows")
        .iter()
        .find(|r| r["chain"] == "has_cubical_layer")
        .expect("the width-one chain");
    for per_producer in row["crate_enum_ids_seen"].as_array().expect("ids") {
        let ids: Vec<u32> = per_producer
            .as_array()
            .expect("one list per producer")
            .iter()
            .map(|v| u32::try_from(v.as_u64().expect("id")).expect("small"))
            .collect();
        assert_eq!(
            ids, observed.enums,
            "reader A and reader B disagree about the crate-level enum ids of this body"
        );
    }
}

// ────────────────────────────────────────────────────────────────────────────
// M6 — the renumbering fact, measured rather than asserted.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m6_the_core_digest_is_invariant_across_three_real_producers() {
    let rec: serde_json::Value =
        serde_json::from_str(PRODUCER_AB).expect("the producer A/B record must parse");
    let rows = rec["rows"].as_array().expect("rows");
    assert!(
        rows.len() >= 11,
        "the A/B record must cover every chained body, found {}",
        rows.len()
    );
    let producers = rec["producers"].as_array().expect("producers");
    assert_eq!(producers.len(), 3, "three producers");

    let mut moved_func_ids = 0usize;
    let mut moved_enum_ids = 0usize;
    for row in rows {
        let digests = row["core_digest"]
            .as_array()
            .expect("core_digest per producer");
        assert_eq!(digests.len(), 3, "one digest per producer");
        assert!(
            digests.windows(2).all(|w| w[0] == w[1]),
            "core digest moved across producers for {}: {digests:?}",
            row["chain"]
        );
        let fids = row["artifact_func_id"].as_array().expect("func ids");
        if !fids.windows(2).all(|w| w[0] == w[1]) {
            moved_func_ids += 1;
        }
        let eids = row["crate_enum_ids_seen"].as_array().expect("enum ids");
        if !eids.windows(2).all(|w| w[0] == w[1]) {
            moved_enum_ids += 1;
        }
    }
    assert_eq!(
        moved_func_ids,
        rows.len(),
        "this is not an A/B at all unless the crate-level numbering actually moved: only \
         {moved_func_ids} of {} rows saw their func_id move",
        rows.len()
    );
    assert!(
        moved_enum_ids >= 1,
        "the enum re-interning drift class (CRYSTAL_STATUS records enum176 vs enum181) must be \
         exercised by at least one row"
    );
    // The width-one chain's digest is the one this gate is built on.
    let h2 = rows
        .iter()
        .find(|r| r["chain"] == "has_cubical_layer")
        .expect("the width-one chain must be in the record");
    let expected = ir_mint::digest(ir_mint::IR_H2_CORE);
    assert_eq!(
        h2["clean_core_digest"].as_str(),
        Some(expected.as_str()),
        "the committed core module is not the object the A/B measured"
    );
}
