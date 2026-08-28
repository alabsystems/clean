// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A2 — the MINT gate for the FIRST COMPLETE CHAIN,
//! `expr::meta::ExprMeta::has_loose_bvars` calling
//! `expr::meta::ExprMeta::loose_bvar_range`.**
//!
//! Same three readers and the same questions as `crystal_a2_mint.rs`; read that
//! file's header and `src/ir_mint/mod.rs` for what this establishes and what it
//! does not. This is the EIGHTEENTH chain and the last one to migrate: until
//! 2026-08-23 it was the programme's one hand transcription, and it was the
//! strongest chain in it — A0 6-of-6 and A6 4-of-4, the body that earns the
//! sentence "one function of the shipping kernel, proved end-to-end".
//!
//! # THE MIGRATION DIFF, PRINTED BEFORE ADOPTION
//!
//! FOUR of the six lines minted BYTE-IDENTICAL — `ir_hlb_tself`, `ir_hlb_func`,
//! `ir_lbr_func` and, notably, `ir_hlb_module` itself, so the two-function list
//! order and both own ids were already right. TWO lines differ, both block
//! bodies:
//!
//! ```text
//! ir_hlb_b0
//!   hand:   … (IRInst.const_ ir_br_tu32 (IRConst.int_ 0)) …
//!   minted: … (IRInst.const_ (IRTy.uint_ 32) (IRConst.int_ ir_d0)) …
//!   hand:   … (ir_bd3 A B C) …
//!   minted: … (IRList.cons IRNode A (IRList.cons IRNode B (IRList.cons IRNode C
//!               (IRList.nil IRNode)))) …
//!
//! ir_lbr_b0
//!   hand:   … (ir_mt_bd9 A B C D E F G H I) …
//!   minted: … the same nine nodes as a raw IRList.cons spine …
//!   hand:   … ir_vc_tu64 … ir_br_tu32 …          (4 and 5 occurrences)
//!   minted: … (IRTy.uint_ 64) … (IRTy.uint_ 32) …
//! ```
//!
//! **THREE notation classes, NO semantic divergence.** (1) BORROWED SIBLING
//! TYPE ALIASES: the hand lines named `ir_br_tu32` (registered by the
//! `bvar_in_range` chain) and `ir_vc_tu64` (by `is_valid_char`) — this chain
//! owned neither, the `flat_flags_with` borrowing again. (2) BORROWED NODE-LIST
//! BUILDERS: `ir_bd3` and the `meta_tag` chain's `ir_mt_bd9`, where
//! `ir_mint::node_list` has builders at 1/2/3/6 nodes and neither 4 nor 9 is
//! one of them. (3) THE ATOM POOL: the hand `(IRConst.int_ 0)` against the
//! mint's `(IRConst.int_ ir_d0)`, the data cutoff at 16 that leaves the
//! callee's 44 and 64 bare on both sides.
//!
//! That the three are notation and not meaning is not asserted here, it is
//! CHECKED: [`the_hand_transcription_and_the_mint_are_the_same_program`]
//! unfolds each alias by its REGISTERED definition on both sides and requires
//! byte identity, and prints the verbatim diff first.
//!
//! # What is new in kind, relative to the seventeen earlier minted chains
//!
//! * **The only core module with TWO functions.** Reader A projected both
//!   bodies in one pass (`a2project … --with …`) under ONE interning namespace,
//!   so the caller's `(call 1 …)` and the callee's `(func 1 …)` are the same
//!   numeral BY CONSTRUCTION — the 2026-08-20 `level_is_zero` collision refused
//!   at the source of the numbering rather than by two hands agreeing.
//! * **`extra_bodies`**: the tag table names the second body, its Clean name
//!   prefix and its own interface, and `mint` refuses a module whose function
//!   list is not exactly the declared bodies in declared order.
//! * **Reader B reads TWO fixtures.** `split_bodies` cuts the text into exactly
//!   the declared number of bodies and refuses the surplus by name, which is
//!   the 2026-08-20 tail rule generalised rather than relaxed.
//! * It is what separates this chain from `ir_lz`, whose `funcs` lane also has
//!   two rows: there the second function is CALLED and not DEFINED, so
//!   `ir_call_exec` goes `stuck no_func` and A4 is refuted. Here it is defined,
//!   the call resolves, and A4 holds.

use clean_verify::ir_mint::{self, Sx};

#[allow(dead_code)]
#[path = "crystal_a1_lineage/emitted_cfg.rs"]
mod emitted_cfg;

use emitted_cfg::{assert_lanes, parse_clean, parse_emitted};

const PREFIX: &str = "ir_hlb";
const MODULE_CONST: &str = "ir_hlb_module";
const CALLER: &str = include_str!("fixtures/has_loose_bvars.trust-ir.txt");
const CALLEE: &str = include_str!("fixtures/loose_bvar_range_callee.trust-ir.txt");

/// The two emitted bodies in MODULE ORDER — caller then callee. The order is
/// not a formatting choice: it is the order `ir_func_find` walks, and the tag
/// table's `funcs`/`extra_bodies` lanes pin it by name, so a swapped
/// concatenation is refused rather than silently read.
fn fixture() -> String {
    format!("{CALLER}{CALLEE}")
}

fn tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_HLB_TAGS).expect("the committed tag table must parse")
}

fn core_a() -> Sx {
    ir_mint::parse(ir_mint::IR_HLB_CORE).expect("the committed core module must parse")
}

/// Reader B over BOTH fixtures, told the chain's function namespace.
fn core_b() -> Sx {
    ir_mint::project(&fixture(), &tags())
        .expect("reader B must read the two committed emitted bodies")
        .core
}

fn canon(sx: &Sx) -> String {
    ir_mint::print(sx).expect("a core module must print")
}

/// ONE definition line of the minted script, by name.
///
/// The A1 comparator splits its input on the block marker and reads everything
/// after it, so handing it the whole script would let the CALLEE's block leak
/// into the CALLER's lanes — a hazard no one-block chain has. Selecting the one
/// line is what keeps the two comparisons independent.
fn def_line(name: &str) -> &'static str {
    let prefix = format!("def {name} ");
    ir_mint::IR_HLB_DEFS
        .lines()
        .map(str::trim)
        .find(|l| l.starts_with(&prefix))
        .unwrap_or_else(|| panic!("the minted script must define {name}"))
}

// The MIGRATION record: the hand transcription this mint replaced, kept
// verbatim, and the machine-checked proof that the two are one program. Split
// out because the gate and the migration are two readable halves and because
// this file was over the 500-line convention with both in it.
#[path = "crystal_a2_mint/hlb_migration.rs"]
mod hlb_migration;

// ────────────────────────────────────────────────────────────────────────────
// M1 — the committed core is canonical, and it is the TWO-FUNCTION call body.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m1_committed_core_round_trips_its_printer() {
    assert_eq!(
        canon(&core_a()),
        ir_mint::IR_HLB_CORE,
        "the committed core module is not what its own canonical printer produces"
    );
    let text = ir_mint::IR_HLB_CORE;
    assert_eq!(
        text.matches("(func ").count(),
        2,
        "TWO functions — the only committed core module that has more than one:\n{text}"
    );
    assert!(
        text.contains("(func 0\n") && text.contains("(func 1\n"),
        "the caller at canonical 0 and the callee at 1, in module order:\n{text}"
    );
    assert_eq!(
        text.matches("(call ").count(),
        1,
        "exactly one call in the whole module"
    );
    assert!(
        text.contains("(call 1 (args 0))"),
        "and it targets canonical index 1 — the callee's OWN id, one namespace:\n{text}"
    );
    assert!(
        text.contains("(assert 4)") && text.contains("(cast trunc (uint 64) (uint 32) 6)"),
        "the callee's assert and its closing trunc:\n{text}"
    );
    assert!(
        !text.contains("(switch ") && !text.contains("(load ") && !text.contains("(gep "),
        "no dispatch and no memory anywhere: ExprMeta is a u64 newtype passed by value"
    );
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
        "neither body has a switch, so nothing the emitted text cannot witness: {ledger:?}"
    );
    assert_eq!(
        canon(&masked),
        canon(&core_b()),
        "the artifact BINARY (reader A) and the two emitted TEXTS (reader B) disagree about this \
         module"
    );
}

/// Reader B is TOTAL over its input: a third body, or a swapped pair, is
/// refused by name rather than dropped or misread.
#[test]
fn m2_reader_b_refuses_a_surplus_body_and_a_swapped_pair() {
    let t = tags();
    let e = ir_mint::project(&format!("{CALLER}{CALLEE}{CALLEE}"), &t)
        .map(|_| ())
        .expect_err("a third body must be REFUSED, never dropped unread");
    assert!(
        format!("{e}").contains("function bod"),
        "the refusal must name the surplus: {e}"
    );
    let e = ir_mint::project(&format!("{CALLEE}{CALLER}"), &t)
        .map(|_| ())
        .expect_err("the bodies in the wrong module order must be REFUSED");
    assert!(
        format!("{e}").contains("loose_bvar_range") || format!("{e}").contains("has_loose_bvars"),
        "the refusal must name the function that is in the wrong slot: {e}"
    );
    let e = ir_mint::project(CALLER, &t)
        .map(|_| ())
        .expect_err("the caller ALONE is not this chain's module");
    assert!(
        format!("{e}").contains("function bod"),
        "the refusal must say how many bodies the table declares: {e}"
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
        ir_mint::IR_HLB_DEFS,
        "the committed definition script is not what `mint` produces from the committed core \
         module. The committed script is the one `eval_ir_has_loose_bvars.rs` REGISTERS, so a \
         difference here means the proved module is again hand-edited."
    );
    assert!(
        ir_mint::IR_HLB_RECORD.contains(&ir_mint::digest(&minted)),
        "the mint record's defs digest does not match the minted script"
    );
    assert!(
        ir_mint::IR_HLB_RECORD.contains(&ir_mint::digest(ir_mint::IR_HLB_CORE)),
        "the mint record's core digest does not match the committed core module"
    );
    // The second body's name prefix comes from the TABLE, not from the minter.
    assert!(
        minted.contains("def ir_lbr_b0 ") && minted.contains("def ir_lbr_func "),
        "the callee's definitions carry the tag table's `ir_lbr` prefix"
    );
    assert!(
        ir_mint::IR_HLB_TAGS.contains("\"prefix\": \"ir_lbr\""),
        "…and the table is where that prefix is pinned"
    );
}

/// The declared-bodies rule BITES: a module whose function list is not exactly
/// the tag table's bodies, in order, is refused rather than minted.
#[test]
fn m3_the_declared_bodies_rule_bites() {
    let t = tags();
    let one = ir_mint::parse(&ir_mint::IR_HLB_CORE.replace(
        "    (func 1\n      (params 0)\n      (entry 0)\n",
        "    (funcX 1\n      (params 0)\n      (entry 0)\n",
    ));
    // A malformed second function is a refusal at parse or at mint; either way
    // it never mints a one-function module in silence.
    let refused = match one {
        Err(e) => format!("{e}"),
        Ok(sx) => match ir_mint::mint(&sx, PREFIX, &t) {
            Err(e) => format!("{e}"),
            Ok(s) => panic!("a module whose second function is not a `func` minted: {s:?}"),
        },
    };
    assert!(!refused.is_empty(), "the refusal must say something");
}

// ────────────────────────────────────────────────────────────────────────────
// M5 — the A1 lane comparator, unchanged, over the MINTED script, both bodies.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m5_the_a1_comparator_agrees_over_the_minted_script() {
    let caller = parse_emitted(CALLER);
    let clean = parse_clean(def_line("ir_hlb_b0"), "def ir_hlb_b");
    assert_lanes(&caller, &clean, "ir_hlb (minted, caller)");
    assert_eq!(caller.blocks, clean.blocks);
    assert_eq!(caller.icmps, clean.icmps);

    let callee = parse_emitted(CALLEE);
    let lbr = parse_clean(def_line("ir_lbr_b0"), "def ir_lbr_b");
    assert_lanes(&callee, &lbr, "ir_lbr (minted, callee)");
    assert_eq!(callee.blocks, lbr.blocks);
    assert_eq!(callee.icmps, lbr.icmps);
    assert_eq!(callee.extracts, lbr.extracts);
    assert_eq!(callee.binops, lbr.binops);
    assert!(
        !callee.extracts.is_empty() && !callee.binops.is_empty(),
        "coverage denominator: the callee reads a field and shifts it"
    );
    // The two comparisons are INDEPENDENT: parsing one body must not pick up
    // the other's instructions out of the shared script.
    assert!(
        clean.extracts.is_empty() && clean.binops.is_empty() && clean.asserts.is_empty(),
        "the caller's parse must not absorb the callee's extractfield/lshr/assert"
    );
    assert!(
        lbr.order != clean.order,
        "…and the two bodies must not parse to the same instruction order"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M7 — the tag table still records what the artifact names.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m7_the_tag_table_still_matches_the_artifact() {
    assert!(
        CALLER.contains("bb0(%0: struct.29):") && CALLEE.contains("bb0(%0: struct.29):"),
        "both receivers must still be struct.29; if not, the artifact was re-interned and this \
         table needs a one-line REVIEWED re-pin"
    );
    assert!(
        ir_mint::IR_HLB_TAGS.contains("\"crate_id\": 29"),
        "and the committed table must record it"
    );
    assert!(
        CALLER.contains("call @func.3657("),
        "the caller's one call must still name @func.3657"
    );
    assert!(
        ir_mint::IR_HLB_TAGS.contains("\"crate_id\": 3657")
            && ir_mint::IR_HLB_TAGS.contains("\"crate_id\": 3658"),
        "…and the funcs lane must pin BOTH ids: the callee's, and the caller's own, which the \
         emitted text names nowhere at all"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M10 — the interface: accepted under the pins, refused one token off them —
// on EITHER body, which is what an `extra_bodies` interface is for.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m10_both_bodies_project_under_their_pinned_interfaces() {
    let p = ir_mint::project(&fixture(), &tags())
        .unwrap_or_else(|e| panic!("the committed fixtures must project: {e}"));
    assert_eq!(
        canon(&p.core),
        ir_mint::IR_HLB_CORE,
        "projecting under the interface pins must produce the committed core"
    );
    assert_eq!(p.interfaces.len(), 2, "one interface per body");
    assert_eq!(
        p.interfaces[0].function_name,
        "expr::meta::ExprMeta::has_loose_bvars"
    );
    assert_eq!(
        p.interfaces[1].function_name,
        "expr::meta::ExprMeta::loose_bvar_range"
    );
    for (i, iface) in p.interfaces.iter().enumerate() {
        let tys: Vec<&str> = iface.params.iter().map(|s| s.ty.as_str()).collect();
        assert_eq!(
            tys,
            ["struct#0"],
            "body {i} takes ONE by-value receiver at the SAME canonical struct"
        );
        assert!(
            iface.block_params.is_empty() && iface.aligns.is_empty(),
            "body {i}: no join and no memory instruction — measured, not assumed"
        );
    }
    assert!(
        p.interfaces[1].clauses.contains("proof"),
        "only the CALLEE carries `#proof: shift_in_range`"
    );
    assert!(
        !p.interfaces[0].clauses.contains("proof"),
        "and the caller does not — the per-body pin is what separates them"
    );
    // The observed function lanes: the caller witnesses both ids, the callee
    // only its own. A pre-seeded sibling the body never calls is NOT reported.
    assert_eq!(p.bodies[0].funcs.len(), 2, "caller: self plus its callee");
    assert_eq!(
        p.bodies[1].funcs.len(),
        1,
        "callee: itself, and it calls none"
    );
}

/// The pins BITE, on both bodies and in both directions.
#[test]
fn m10_the_interface_pins_bite() {
    let t = tags();
    for (from, to, slot) in [
        ("(functy.435)", "(functy.436)", "signature index"),
        ("(functy.433)", "(functy.434)", "signature index"),
        (
            "rustcc fn @expr::meta::ExprMeta::has",
            "ccc fn @expr::meta::ExprMeta::has",
            "calling convention",
        ),
        (
            "rustcc fn @expr::meta::ExprMeta::loose",
            "ccc fn @expr::meta::ExprMeta::loose",
            "calling convention",
        ),
        (
            "bb0(%0: struct.29):\n    %1 = call",
            "bb0(%0: u64):\n    %1 = call",
            "parameter",
        ),
        (
            "bb0(%0: struct.29):\n    %1 = extractfield",
            "bb0(%0: struct.999):\n    %1 = extractfield",
            "parameter",
        ),
        (
            "call @func.3657(%0)",
            "call @func.9999(%0)",
            "not in the chain's tag table",
        ),
    ] {
        let mutated = fixture().replace(from, to);
        assert_ne!(mutated, fixture(), "the mutation must bite: {from}");
        let e = ir_mint::project(&mutated, &t).map(|_| ()).expect_err(
            "a body whose interface is not the pinned one must be REFUSED, never accepted",
        );
        assert!(
            format!("{e}").contains(slot),
            "the refusal must name the drifted slot ({slot}): {e}"
        );
    }
    // The `#proof` clause is pinned PER BODY: moving it to the caller is a
    // different interface on both, and the projection refuses.
    let moved = fixture().replace("  ; #proof: shift_in_range", "");
    let e = ir_mint::project(&moved, &t)
        .map(|_| ())
        .expect_err("dropping the callee's proof clause must be refused");
    assert!(
        format!("{e}").contains("annotation clause kinds"),
        "the refusal must name the clause lane: {e}"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M8 — the mint discriminates this chain from every other minted chain.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m8_the_mint_discriminates_across_the_minted_set() {
    for (who, core) in [
        ("ir_h2", ir_mint::IR_H2_CORE),
        ("ir_lz", ir_mint::IR_LZ_CORE),
        ("ir_ko", ir_mint::IR_KO_CORE),
        ("ir_mt", ir_mint::IR_MT_CORE),
        ("ir_gc", ir_mint::IR_GC_CORE),
    ] {
        assert_ne!(
            ir_mint::digest(ir_mint::IR_HLB_CORE),
            ir_mint::digest(core),
            "ir_hlb and {who} must not share a core digest"
        );
    }
    // The nearest neighbour is `ir_lz`: the only OTHER chain whose module
    // contains a `call`. The separation is the one that matters semantically —
    // there the callee is not defined, here it is.
    assert_eq!(
        ir_mint::IR_LZ_CORE.matches("(func ").count(),
        1,
        "ir_lz DEFINES one function and calls a second it does not define"
    );
    assert_eq!(
        ir_mint::IR_HLB_CORE.matches("(func ").count(),
        2,
        "ir_hlb defines both — which is why its A4 holds and ir_lz's is refuted"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M4 — reader C: the ELABORATED KERNEL TERM decodes back to the committed
// core. The expensive check (one full Specification build), LAST.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m4_the_registered_kernel_term_decodes_to_the_committed_core() {
    let spec = clean_verify::test_utils::shared_spec();
    let decoded = ir_mint::decode(spec.env(), MODULE_CONST, &tags()).expect("decode ir_hlb_module");
    assert_eq!(
        canon(&decoded),
        ir_mint::IR_HLB_CORE,
        "the ELABORATED term registered under `{MODULE_CONST}` does not decode to the committed \
         core module. This is the check that keeps `mint` out of the trusted base: reader C never \
         sees the minter's output — and on this chain it is also the only reader that sees BOTH \
         functions as one term."
    );
}
