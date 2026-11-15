// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A2 — the MINT gate for the `node_id_index` chain,
//! `cert::builder::state::NodeId::index`.**
//!
//! Same three readers and the same questions as `crystal_a2_mint.rs`; read
//! that file's header and `src/ir_mint/mod.rs` for what this establishes and
//! what it does not. This is the SIXTEENTH chain the mint machinery covers,
//! and until 2026-08-22 it was a NAMED REFUSAL: reader A had no Clean IRTy
//! image for `trust_ir::Ty::Usize`, and refusing was correct — `usize` is
//! TARGET-DEPENDENT, and an image that silently assumed 64 bits would have
//! baked a word-size assumption into a committed core module.
//!
//! **How the refusal was converted, without the silent assumption**: the
//! width is a PINNED TARGET FACT. `generated/ir_ni.tags.json` carries a
//! `usize` lane — bits 64 (the recorded aarch64-apple-darwin producer, the
//! same fact `node_id_index.lineage.json` pins), and the exact SITE COUNT
//! (one). Reader A resolves only under `--usize-bits 64` and records the
//! resolution in provenance; reader B resolves only through the tag table's
//! lane; both keep refusing, by name, without the pin. The resolved core
//! spells the site as the plain `(uint 64)` — reader C, the elaborated kernel
//! term, could never reproduce a distinction Clean's `IRTy` does not have —
//! so what the resolution ERASES is checked at the pinned site count instead:
//! see `the_u64_twin_is_the_recorded_erasure_and_the_site_count_refuses_it`.
//!
//! **The migration diff, printed before adoption** (the rule the flagship's
//! wrong exhaustive flag made mandatory: a divergence is a FINDING): ONE of
//! the four lines diverged, TWO notation classes, both definitionally equal —
//! `ir_ni_b0` inlines `(IRTy.uint_ 32)` where the hand line BORROWED the
//! sibling `ir_br_tu32` alias, and `(IRTy.uint_ 64)` where the hand line
//! named `ir_ni_tusize` (the theorem-side alias, which stays registered and
//! keeps stating the cast-semantics theorems). `ir_ni_tself`, `ir_ni_func`
//! and `ir_ni_module` minted byte-identical. NO semantic divergence; every
//! downstream `ir_ni_*` theorem kept proving unchanged, the four boundary
//! witnesses and the sext contrast included.

use clean_verify::ir_mint::{self, SelfFunc, Sx};

#[allow(dead_code)]
use crate::emitted_cfg;

use emitted_cfg::{assert_lanes, parse_clean, parse_emitted};

const PREFIX: &str = "ir_ni";
const MODULE_CONST: &str = "ir_ni_module";
const FIXTURE: &str = include_str!("fixtures/node_id_index.trust-ir.txt");

fn tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_NI_TAGS).expect("the committed tag table must parse")
}

fn core_a() -> Sx {
    ir_mint::parse(ir_mint::IR_NI_CORE).expect("the committed core module must parse")
}

/// Reader B over the committed fixture, THROUGH the pinned usize width — the
/// only way this fixture reads at all.
fn core_b() -> Sx {
    ir_mint::read_emitted_with_pins(FIXTURE, SelfFunc::Unpinned, Some(64))
        .expect("reader B must read the committed emitted trust-ir under the pin")
        .0
}

fn canon(sx: &Sx) -> String {
    ir_mint::print(sx).expect("a core module must print")
}

// ────────────────────────────────────────────────────────────────────────────
// M1 — the committed core is canonical: one field read, one zext, one ret.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m1_committed_core_round_trips_its_printer() {
    let a = core_a();
    assert_eq!(
        canon(&a),
        ir_mint::IR_NI_CORE,
        "the committed core module is not what its own canonical printer produces"
    );
    let text = ir_mint::IR_NI_CORE;
    assert!(
        text.contains("(extractfield (uint 32) 0 0)"),
        "the committed core must read field 0 of the by-value receiver:\n{text}"
    );
    assert!(
        text.contains("(cast zext (uint 32) (uint 64) 1)"),
        "and zero-extend it at the RESOLVED usize width:\n{text}"
    );
    assert!(
        text.contains("(ret (vals 2))"),
        "and return the extended value:\n{text}"
    );
    assert!(
        !text.contains("usize"),
        "the RESOLVED core must not carry the token — the resolution is the tag table's, and \
         reader C could never reproduce it:\n{text}"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// The REFUSAL, kept: no pin, no image. This is the fail-closed half the
// conversion was required to preserve.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn usize_without_the_pin_is_still_refused_by_name() {
    let e = ir_mint::read_emitted(FIXTURE)
        .map(|_| ())
        .expect_err("reader B must refuse `usize` when no width is pinned");
    let msg = format!("{e}");
    assert!(
        msg.contains("usize") && msg.contains("TARGET-DEPENDENT"),
        "the refusal must name the type and the reason: {msg}"
    );
    assert!(
        msg.contains("tag-table") || msg.contains("tag table"),
        "…and the repair — the tag table's usize lane: {msg}"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// The image DISCRIMINATES: u32-vs-usize is two core modules.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn the_resolved_image_discriminates_u32_from_usize() {
    let twin = FIXTURE.replace("zext u32 %1 to usize", "zext u32 %1 to u32");
    assert_ne!(twin, FIXTURE, "the mutation must bite");
    let (sx, _) = ir_mint::read_emitted_with_pins(&twin, SelfFunc::Unpinned, Some(64))
        .expect("the u32 twin reads — it needs no pin at all");
    assert_ne!(
        canon(&sx),
        canon(&core_b()),
        "a body zero-extending to u32 and one zero-extending to usize must NOT project to one \
         core module — (uint 32) vs the resolved (uint 64)"
    );
}

/// **The erasure, stated as a measurement.** A twin spelling `u64` where the
/// body spells `usize` projects to the SAME resolved core — that is what
/// resolving costs, said out loud — and the pinned SITE COUNT is the check
/// that refuses it: the twin's observed count is 0, the pin says 1.
#[test]
fn the_u64_twin_is_the_recorded_erasure_and_the_site_count_refuses_it() {
    let twin = FIXTURE.replace("zext u32 %1 to usize", "zext u32 %1 to u64");
    assert_ne!(twin, FIXTURE, "the mutation must bite");
    let (sx, observed) = ir_mint::read_emitted_with_pins(&twin, SelfFunc::Unpinned, Some(64))
        .expect("the u64 twin reads");
    assert_eq!(
        canon(&sx),
        canon(&core_b()),
        "the RESOLVED cores are identical — this equality is the declared erasure, and if it \
         ever fails the erasure note in the tag table is stale"
    );
    assert_eq!(observed.usize_seen, 0, "the twin resolved nothing");
    let e = ir_mint::project(&twin, &tags())
        .map(|_| ())
        .expect_err("the interface pin must refuse the twin at the site count");
    assert!(
        format!("{e}").contains("usize site"),
        "the refusal must name the usize-sites slot: {e}"
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
        "the artifact BINARY (reader A, resolved under --usize-bits 64) and the emitted TEXT \
         (reader B, resolved through the tag table) disagree about this body"
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
        ir_mint::IR_NI_DEFS,
        "the committed definition script is not what `mint` produces from the committed core \
         module. The committed script is the one `eval_ir_node_id_index.rs` REGISTERS, so a \
         difference here means the proved module is again hand-edited."
    );
    assert!(
        ir_mint::IR_NI_RECORD.contains(&ir_mint::digest(&minted)),
        "the mint record's defs digest does not match the minted script"
    );
    assert!(
        ir_mint::IR_NI_RECORD.contains(&ir_mint::digest(ir_mint::IR_NI_CORE)),
        "the mint record's core digest does not match the committed core module"
    );
    assert!(
        ir_mint::IR_NI_DEFS.contains("(IRTy.uint_ 32) (IRTy.uint_ 64)")
            && !ir_mint::IR_NI_DEFS.contains("ir_ni_tusize"),
        "the minted script inlines the resolved widths; the theorem-side alias stays in the \
         eval file and OUT of the module's identity:\n{}",
        ir_mint::IR_NI_DEFS
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M5 — the A1 lane comparator, unchanged, over the MINTED script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m5_the_a1_comparator_agrees_over_the_minted_script() {
    let mut emitted = parse_emitted(FIXTURE);
    // The same two-step resolution the A1 gate performs (its raw parse
    // carries the loud `?usize` token; see crystal_a1_lineage/node_id_index.rs
    // for the assertion that it is EXACTLY that before any resolution).
    let mut resolved = 0usize;
    for slot in emitted.cast_tys.values_mut() {
        for t in slot.iter_mut() {
            assert_eq!(t.3, "?usize", "the raw parse must carry the loud token");
            t.3 = "uint64".to_string();
            resolved += 1;
        }
    }
    assert_eq!(
        resolved, 1,
        "exactly one usize site — the tag table's pinned count"
    );
    let clean = parse_clean(ir_mint::IR_NI_DEFS, "def ir_ni_b");
    assert_lanes(&emitted, &clean, "ir_ni (minted)");
    assert_eq!(emitted.blocks, clean.blocks);
    assert!(
        !emitted.casts.is_empty(),
        "coverage denominator: two empty lane sets compare equal, and this body IS a cast"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M7 — the tag table still records the interning ids the artifact names.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m7_the_tag_table_still_matches_the_artifact() {
    assert!(
        FIXTURE.contains("(functy.85)"),
        "the emitted body must still carry signature index 85; if it does not, the artifact \
         was re-interned and this table needs a one-line REVIEWED re-pin"
    );
    assert!(
        ir_mint::IR_NI_TAGS.contains("\"functy\": 85"),
        "and the committed table must record it"
    );
    assert!(
        FIXTURE.contains("bb0(%0: struct.210):"),
        "the receiver is struct.210 BY VALUE — NodeId, not its unchained twin ExtensionIdx \
         (struct.848)"
    );
    assert!(
        ir_mint::IR_NI_TAGS.contains("\"crate_id\": 210"),
        "and the committed table pins that id in its interface-only struct row"
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
    assert_eq!(
        tys,
        ["struct#0"],
        "ONE by-value struct parameter, canonicalized through the tag table"
    );
    assert!(p.interface.block_params.is_empty(), "one block, no joins");
    assert!(
        p.interface.aligns.is_empty(),
        "no memory instruction in this body — the by-value receiver arrives in a register \
         aggregate"
    );
}

/// The pins BITE: a pointer receiver, the TWIN's struct id, a foreign calling
/// convention and a moved `functy` are each refused, and the refusal names
/// the slot. The second row is the one this chain exists to pin: the
/// unchained twin `ExtensionIdx::index` is THIS body at struct.848.
#[test]
fn m10_the_interface_pins_bite() {
    let t = tags();
    for (from, to, slot) in [
        ("bb0(%0: struct.210):", "bb0(%0: ptr):", "parameter"),
        ("bb0(%0: struct.210):", "bb0(%0: struct.848):", "parameter"),
        ("rustcc fn @", "ccc fn @", "calling convention"),
        ("(functy.85)", "(functy.86)", "signature index"),
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
// M8 — the mint discriminates this chain from its cast sibling.
// ────────────────────────────────────────────────────────────────────────────

/// `ir_gc` is the OTHER one-block single-cast body — trunc u64→u32, the exact
/// reverse seam. Digests, opcode and direction must all separate them.
#[test]
fn m8_the_mint_discriminates_the_cast_siblings() {
    assert_ne!(
        ir_mint::digest(ir_mint::IR_NI_CORE),
        ir_mint::digest(ir_mint::IR_GC_CORE),
        "ir_ni and ir_gc must not share a core digest"
    );
    assert!(
        ir_mint::IR_NI_DEFS.contains("IRCastOp.zext")
            && !ir_mint::IR_NI_DEFS.contains("IRCastOp.trunc"),
        "this body widens"
    );
    assert!(
        ir_mint::IR_GC_DEFS.contains("IRCastOp.trunc")
            && !ir_mint::IR_GC_DEFS.contains("IRCastOp.zext"),
        "the sibling narrows"
    );
    assert!(
        ir_mint::IR_NI_DEFS.contains("IRInst.extractfield"),
        "and only this body reads a field first"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M4 — reader C: the ELABORATED KERNEL TERM decodes back to the committed
// core. The expensive check (one full Specification build), LAST.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m4_the_registered_kernel_term_decodes_to_the_committed_core() {
    let spec = clean_verify::test_utils::shared_spec();
    let decoded = ir_mint::decode(spec.env(), MODULE_CONST, &tags()).expect("decode ir_ni_module");
    assert_eq!(
        canon(&decoded),
        ir_mint::IR_NI_CORE,
        "the ELABORATED term registered under `{MODULE_CONST}` does not decode to the committed \
         core module. This is the check that keeps `mint` out of the trusted base: reader C \
         never sees the minter's output — and on this chain it is also what pins that the \
         registered term's inlined (IRTy.uint_ 64) IS the resolved usize the tag table declares."
    );
}
