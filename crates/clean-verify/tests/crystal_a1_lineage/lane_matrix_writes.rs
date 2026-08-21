// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Discrimination proofs for the two WRITE lanes** (`insertfields`,
//! `stores`), added 2026-08-20 AHEAD of the last three chains.
//!
//! Every earlier lane was added by the chain that needed it and proved
//! discriminating by the battery afterwards. These two land BEFORE their
//! chains, so the proof-by-mutation lands with them: for each lane, a
//! perturbation in that lane ALONE fails the compare — checked in the
//! strongest available form, whole-`Cfg` equality with ONLY the lane under
//! test cleared — in BOTH directions (artifact-side text mutated against an
//! unperturbed Clean transcription, and Clean-side source mutated against the
//! unperturbed artifact), while the unperturbed pair passes the full
//! `assert_lanes` gate.
//!
//! ## What this file does and does NOT establish
//!
//! * The emitted texts are the COMMITTED fixtures of two of the three
//!   remaining bodies (`flat_flags_with.trust-ir.txt`,
//!   `strict_monads.trust-ir.txt`). The Clean sides are TEST-LOCAL candidate
//!   transcriptions written for this file. **They are not registered spec
//!   definitions and no chain correspondence is claimed here** — the chains
//!   that register their `ir_fw_*` / `ir_sm_*` modules own that gate, and the
//!   helper arities they need (`ir_bd4`, `ir_d81`) are their build items, not
//!   facts this file asserts.
//! * Nothing here claims interpreter agreement for these bodies. The
//!   producer's interpreter differential is NOT-RUN (0 samples) on all three
//!   remaining bodies; the chain evidence is agreed + markers_exact +
//!   flip-lineage equality, and this file is about the CFG gate only.
//! * Emptiness on every matrix chain is asserted here explicitly, and
//!   independently by the pinned matrix: neither lane is in any `nonempty`
//!   row, so a registered fixture growing a write instruction fails the matrix
//!   by name. (The float chains that gate outside the matrix compare the two
//!   lanes empty-vs-empty through their own `assert_lanes` calls.)

use super::*;

/// The candidate Clean-side transcription of
/// `fixtures/flat_flags_with.trust-ir.txt` (`flat::types::FlatFlags::with`) —
/// TEST-LOCAL, see the module doc.
const CAND_FW_B0: &str = "def ir_fw_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd6 (ir_nd1 \
     (IRInst.extractfield (IRTy.uint_ 8) ir_d0 ir_d0) ir_d2) (ir_nd1 (IRInst.extractfield \
     (IRTy.uint_ 8) ir_d1 ir_d0) ir_d3) (ir_nd1 (IRInst.binop IRBinOp.or_ (IRTy.uint_ 8) ir_d2 \
     ir_d3) ir_d4) (ir_nd1 (IRInst.const_ (IRTy.struct_ 1017) (ir_cvar ir_d0)) ir_d5) (ir_nd1 \
     (IRInst.insertfield (IRTy.struct_ 1017) ir_d5 ir_d0 ir_d4) ir_d6) (ir_nd (IRInst.ret \
     (ir_nl1 ir_d6))))";
const CAND_FW_FUNC: &str = "def ir_fw_func : IRFunc := IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1) \
     ir_d0 (ir_blk ir_fw_b0 ir_blk0)";

/// The candidate Clean-side transcription of
/// `fixtures/strict_monads.trust-ir.txt`
/// (`env::Environment::set_lean4_core_strict_monads`) — TEST-LOCAL.
const CAND_SM_B0: &str = "def ir_sm_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd4 (ir_nd1 \
     (IRInst.load (IRTy.struct_ 441) ir_d0 Bool.false) ir_d2) (ir_nd1 (IRInst.insertfield \
     (IRTy.struct_ 441) ir_d2 ir_d81 ir_d1) ir_d3) (ir_nd (IRInst.store (IRTy.struct_ 441) \
     ir_d0 ir_d3 Bool.false)) (ir_nd (IRInst.ret ir_nl0)))";
const CAND_SM_FUNC: &str = "def ir_sm_func : IRFunc := IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1) \
     ir_d0 (ir_blk ir_sm_b0 ir_blk0)";

/// Whole-`Cfg` equality with ONLY the insertfield lane cleared: the proof that
/// a perturbation is invisible to every OTHER lane, stated over the shape
/// instead of over a hand-picked list of assertions that could omit one.
fn eq_except_insertfields(mut a: Cfg, mut b: Cfg, why: &str) {
    a.insertfields.clear();
    b.insertfields.clear();
    assert_eq!(
        a, b,
        "{why}: expected every lane EXCEPT insertfields to agree"
    );
}

/// The same, for the store lane.
fn eq_except_stores(mut a: Cfg, mut b: Cfg, why: &str) {
    a.stores.clear();
    b.stores.clear();
    assert_eq!(a, b, "{why}: expected every lane EXCEPT stores to agree");
}

/// The GATE itself — `assert_lanes`, the exact call every chain makes — must
/// go red on the mutated pair, and red in the NAMED lane. `assert_ne!` on the
/// lane field proves the parsers see the drift; this proves the comparator
/// REPORTS it, so a chain wired the normal way cannot pass over it.
fn gate_goes_red_in(a: &Cfg, b: &Cfg, lane_msg: &str, why: &str) {
    let err = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        assert_lanes(a, b, "mutation probe");
    }))
    .expect_err(&format!(
        "{why}: assert_lanes must FAIL on the mutated pair"
    ));
    let msg = err
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| err.downcast_ref::<&str>().map(|s| (*s).to_string()))
        .unwrap_or_default();
    assert!(
        msg.contains(lane_msg),
        "{why}: assert_lanes failed, but not in the expected lane — wanted {lane_msg:?}, got: \
         {msg}"
    );
}

/// The unperturbed pairs pass the FULL gate — every lane, the function
/// signature, and the totality equality. This is the green half every
/// mutation below is measured against.
#[test]
fn writes_lanes_agree_on_the_candidate_transcriptions() {
    let fw = parse_emitted(&fixture("flat_flags_with.trust-ir.txt"));
    let fw_clean = parse_clean(CAND_FW_B0, "def ir_fw_b");
    assert_lanes(&fw, &fw_clean, "flat_flags_with candidate");
    assert_entry_params(
        &fixture("flat_flags_with.trust-ir.txt"),
        CAND_FW_FUNC,
        "flat_flags_with candidate",
    );
    assert_eq!(
        fw.insertfields.get(&0),
        Some(&vec![(6, "struct1017".to_string(), 5, 0, 4)]),
        "the lane must actually be POPULATED on this body — an empty lane agreeing with an \
         empty lane is the vacuity mode this file exists to refuse"
    );

    let sm = parse_emitted(&fixture("strict_monads.trust-ir.txt"));
    let sm_clean = parse_clean(CAND_SM_B0, "def ir_sm_b");
    assert_lanes(&sm, &sm_clean, "strict_monads candidate");
    assert_entry_params(
        &fixture("strict_monads.trust-ir.txt"),
        CAND_SM_FUNC,
        "strict_monads candidate",
    );
    assert_eq!(
        sm.insertfields.get(&0),
        Some(&vec![(3, "struct441".to_string(), 2, 81, 1)]),
        "insertfield at FIELD 81 of Environment is the exact case the lane was cut for"
    );
    assert_eq!(
        sm.stores.get(&0),
        Some(&vec![(0, "struct441".to_string(), 3)]),
        "the store lane must be populated: (POINTER %0, struct441, value %3)"
    );
}

/// **INSERTFIELD, artifact direction and spec direction.** Each perturbation
/// leaves every other lane bit-identical (proved over the whole shape, not a
/// list) and fails in `insertfields` — so before 2026-08-20 every one of these
/// was a transcription the gate accepted.
#[test]
fn insertfield_lane_catches_what_every_old_lane_misses() {
    let text = fixture("flat_flags_with.trust-ir.txt");
    let clean = parse_clean(CAND_FW_B0, "def ir_fw_b");

    // Artifact mutations: FIELD INDEX, TYPE, inserted VALUE, source AGGREGATE.
    // The field index is the one the task exists for: writing field 1 instead
    // of field 0 of FlatFlags is a different function, and `order` sees the
    // same class binding the same result.
    for (from, to, what) in [
        (
            "insertfield struct.1017 %5, 0, %4",
            "insertfield struct.1017 %5, 1, %4",
            "FIELD INDEX 0 -> 1",
        ),
        (
            "insertfield struct.1017 %5, 0, %4",
            "insertfield struct.1018 %5, 0, %4",
            "TYPE struct.1017 -> struct.1018",
        ),
        (
            "insertfield struct.1017 %5, 0, %4",
            "insertfield struct.1017 %5, 0, %3",
            "inserted VALUE %4 -> %3",
        ),
        (
            "insertfield struct.1017 %5, 0, %4",
            "insertfield struct.1017 %1, 0, %4",
            "source AGGREGATE %5 -> %1",
        ),
    ] {
        assert!(
            text.contains(from),
            "fixture moved under the mutation {what}"
        );
        let mutated = parse_emitted(&text.replace(from, to));
        assert_ne!(
            mutated.insertfields, clean.insertfields,
            "{what}: the INSERTFIELD lane must see it"
        );
        gate_goes_red_in(&mutated, &clean, "INSERTFIELD lane differs", what);
        eq_except_insertfields(mutated, parse_emitted(&text), what);
    }

    // Spec mutation: the registered-side field index drifts. Same shape, other
    // direction.
    let drifted = parse_clean(
        &CAND_FW_B0.replace("ir_d5 ir_d0 ir_d4", "ir_d5 ir_d1 ir_d4"),
        "def ir_fw_b",
    );
    let emitted = parse_emitted(&text);
    assert_ne!(
        emitted.insertfields, drifted.insertfields,
        "Clean-side FIELD INDEX 0 -> 1: the INSERTFIELD lane must see it"
    );
    gate_goes_red_in(
        &emitted,
        &drifted,
        "INSERTFIELD lane differs",
        "Clean-side FIELD INDEX 0 -> 1",
    );
    eq_except_insertfields(emitted, drifted, "Clean-side FIELD INDEX 0 -> 1");
}

/// **STORE, artifact direction and spec direction.** A store binds no result,
/// so `order` records `("store", [])` and every operand was invisible: the
/// swap, the type and the value mutations here all leave every other lane
/// bit-identical. Outright DELETION is the one drift `order` already saw, and
/// that is measured below too rather than claimed either way.
#[test]
fn store_lane_catches_what_every_old_lane_misses() {
    let text = fixture("strict_monads.trust-ir.txt");
    let clean = parse_clean(CAND_SM_B0, "def ir_sm_b");
    let emitted = parse_emitted(&text);

    // Artifact mutations: operand SWAP (store the pointer through the value —
    // both parsers normalize to pointer-first exactly so this cannot hide),
    // the stored TYPE, and the stored VALUE (%2 is the pre-insertfield
    // Environment: storing it makes the whole body a no-op).
    for (from, to, what) in [
        (
            "store struct.441 %3, ptr %0",
            "store struct.441 %0, ptr %3",
            "ptr/value SWAP",
        ),
        (
            "store struct.441 %3, ptr %0",
            "store struct.442 %3, ptr %0",
            "TYPE struct.441 -> struct.442",
        ),
        (
            "store struct.441 %3, ptr %0",
            "store struct.441 %2, ptr %0",
            "stored VALUE %3 -> %2",
        ),
    ] {
        assert!(
            text.contains(from),
            "fixture moved under the mutation {what}"
        );
        let mutated = parse_emitted(&text.replace(from, to));
        assert_ne!(
            mutated.stores, clean.stores,
            "{what}: the STORE lane must see it"
        );
        gate_goes_red_in(&mutated, &clean, "STORE lane differs", what);
        eq_except_stores(mutated, parse_emitted(&text), what);
    }

    // Spec mutation: the registered store's POINTER drifts to the loaded
    // value's id — a store through a non-pointer, which `ir_store_exec` would
    // fault, and which no other lane distinguishes from the artifact.
    let drifted = parse_clean(
        &CAND_SM_B0.replace(
            "(IRTy.struct_ 441) ir_d0 ir_d3 Bool.false",
            "(IRTy.struct_ 441) ir_d1 ir_d3 Bool.false",
        ),
        "def ir_sm_b",
    );
    assert_ne!(
        emitted.stores, drifted.stores,
        "Clean-side POINTER ir_d0 -> ir_d1: the STORE lane must see it"
    );
    gate_goes_red_in(
        &emitted,
        &drifted,
        "STORE lane differs",
        "Clean-side POINTER drift",
    );
    eq_except_stores(parse_emitted(&text), drifted, "Clean-side POINTER drift");

    // DELETION, measured honestly: dropping the store is ALREADY visible to
    // `order` (its class list loses the entry) — the lane's contribution is
    // the operands and the type, which order structurally cannot carry.
    let deleted =
        parse_emitted(&text.replace("    store struct.441 %3, ptr %0  ; #loc: 368 3479 8\n", ""));
    assert_ne!(
        emitted.order, deleted.order,
        "deleting the store must already fail the ORDER lane — if this ever passes, the \
         doc-comment on Cfg::stores is overclaiming what order sees"
    );
    assert_ne!(
        emitted.stores, deleted.stores,
        "…and the STORE lane fails it too"
    );
}

/// The two refusals are refusals, not drops: a volatile store (either side)
/// and an aligned store PANIC instead of parsing to nothing on both sides and
/// comparing equal.
#[test]
fn volatile_and_align_stores_are_refused_not_dropped() {
    let text = fixture("strict_monads.trust-ir.txt");
    let volatile_emitted = text.replace("store struct.441 %3", "volatile store struct.441 %3");
    assert!(
        std::panic::catch_unwind(|| parse_emitted(&volatile_emitted)).is_err(),
        "an emitted VOLATILE store must be refused — the lane has no slot for the flag"
    );
    let aligned = text.replace(
        "store struct.441 %3, ptr %0",
        "store struct.441 %3, ptr %0, align 8",
    );
    assert!(
        std::panic::catch_unwind(|| parse_emitted(&aligned)).is_err(),
        "an emitted ALIGNED store must be refused — Clean's IRInst.store has no align operand"
    );
    let volatile_clean = CAND_SM_B0.replace("ir_d0 ir_d3 Bool.false", "ir_d0 ir_d3 Bool.true");
    assert!(
        std::panic::catch_unwind(|| parse_clean(&volatile_clean, "def ir_sm_b")).is_err(),
        "a registered VOLATILE store must be refused symmetrically, or a volatile pair could \
         agree by both sides dropping the flag"
    );
}

/// Empty-vs-empty on every MATRIX chain: none of those bodies contains an
/// insertfield or a store, so both new lanes must read empty on BOTH sides —
/// which is what keeps all existing chain gates green under the widened
/// shape, and it is checked rather than assumed. (The pinned matrix enforces
/// the same fact through each row's `nonempty` set; this is the statement of
/// it in the write lanes' own terms.)
#[test]
fn writes_lanes_are_empty_on_every_matrix_chain() {
    for ch in CHAINS {
        let emitted = parse_emitted(&fixture(ch.fixture));
        let clean = parse_clean(
            &clean_block_sources(ch.spec, ch.blocks_prefix),
            ch.block_marker,
        );
        for (side, cfg) in [("emitted", &emitted), ("Clean", &clean)] {
            assert!(
                cfg.insertfields.is_empty() && cfg.stores.is_empty(),
                "{}: the {side} side has a write instruction ({:?} / {:?}) that predates the \
                 write lanes — its chain's lane row and mutation coverage must be extended, not \
                 inherited",
                ch.who,
                cfg.insertfields,
                cfg.stores
            );
        }
    }
}
