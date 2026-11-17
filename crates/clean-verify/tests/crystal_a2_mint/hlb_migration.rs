// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **THE MIGRATION of chain 18 off its hand transcription (2026-08-23), and the
//! machine-checked verdict that the two are one program.**
//!
//! Split out of `crystal_a2_mint_hlb.rs` because the gate and the migration
//! record are two readable halves and because the file was over the 500-line
//! convention with both in it. Read that file's header first: it carries the
//! verbatim diff and the three notation classes.
//!
//! The `ir_lz` precedent is the standard this is held to. There the same
//! comparison found FOUR real divergence classes and the decision memo
//! (`designs/2026-08-22-is-zero-model-vs-minted-decision.md`) retired the hand
//! module to `ir_lzm_module` rather than adopting the minted side quietly.
//! Here every difference disappears under one delta step per registered alias.

use clean_verify::ir_mint;

// ────────────────────────────────────────────────────────────────────────────
// THE MIGRATION: the hand transcription this mint replaced, and the proof that
// the two are one program. Kept verbatim so the comparison is re-runnable and
// not a claim in a commit message.
// ────────────────────────────────────────────────────────────────────────────

/// The six lines `spec/core_spec/eval_ir_has_loose_bvars.rs` registered by hand
/// until 2026-08-23, in module order.
const HAND: [&str; 6] = [
    "def ir_hlb_tself : IRTy := IRTy.struct_ 29",
    "def ir_hlb_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (IRList.cons IRNode (ir_nd1 (IRInst.call ir_d1 (ir_nl1 ir_d0)) ir_d1) (ir_bd3 (ir_nd1 (IRInst.const_ ir_br_tu32 (IRConst.int_ 0)) ir_d2) (ir_nd1 (IRInst.icmp IRICmpOp.ugt ir_br_tu32 ir_d1 ir_d2) ir_d3) (ir_nd (IRInst.ret (ir_nl1 ir_d3)))))",
    "def ir_hlb_func : IRFunc := IRFunc.mk ir_d0 (ir_nl1 ir_d0) ir_d0 (ir_blk ir_hlb_b0 ir_blk0)",
    "def ir_lbr_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_mt_bd9 (ir_nd1 (IRInst.extractfield ir_vc_tu64 ir_d0 ir_d0) ir_d1) (ir_nd1 (IRInst.const_ ir_br_tu32 (IRConst.int_ 44)) ir_d2) (ir_nd1 (IRInst.const_ ir_br_tu32 (IRConst.int_ 64)) ir_d3) (ir_nd1 (IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d2 ir_d3) ir_d4) (ir_nd (IRInst.assert ir_d4)) (ir_nd1 (IRInst.cast IRCastOp.zext ir_br_tu32 ir_vc_tu64 ir_d2) ir_d5) (ir_nd1 (IRInst.binop IRBinOp.lshr ir_vc_tu64 ir_d1 ir_d5) ir_d6) (ir_nd1 (IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_br_tu32 ir_d6) ir_d7) (ir_nd (IRInst.ret (ir_nl1 ir_d7))))",
    "def ir_lbr_func : IRFunc := IRFunc.mk ir_d1 (ir_nl1 ir_d0) ir_d0 (ir_blk ir_lbr_b0 ir_blk0)",
    "def ir_hlb_module : IRModule := IRModule.mk (IRList.cons IRFunc ir_hlb_func (IRList.cons IRFunc ir_lbr_func (IRList.nil IRFunc))) (IRList.nil IRGlobal)",
];

/// Version 1 of the CURRENT source spelling for this historical fixture.
///
/// The existing struct-id transport happens first. This additional transport
/// only marks the complete IRList constructor prefixes used by HAND: nil at
/// IRFunc/IRGlobal and cons at IRNode/IRFunc. It preserves every supplied
/// argument and is neither a source parser nor a semantic normalization.
fn current_source_spelling_v1(line: &str) -> String {
    assert!(line.is_ascii() && line.starts_with("def "));
    assert!(!line.contains('"') && !line.contains('\\'));
    let mut out = line.to_owned();
    for (name, arity) in [("IRList.nil", 1usize), ("IRList.cons", 3usize)] {
        let head = format!("({name}");
        let mut cursor = 0;
        while let Some(relative) = out[cursor..].find(&head) {
            let start = cursor + relative;
            let after_head = start + head.len();
            let next = out.as_bytes().get(after_head).copied();
            // A longer qualified identifier is not this constructor.
            if next.is_some_and(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'\'')) {
                cursor = after_head;
                continue;
            }
            assert_eq!(next, Some(b' '), "v1 requires a complete grouped {name}");
            let (args, end) = split_args(&out, after_head + 1);
            assert!(end < out.len() && out.as_bytes()[end] == b')');
            assert_eq!(
                args.len(),
                arity,
                "v1 requires every original {name} argument"
            );
            assert!(
                matches!(
                    (name, args[0].as_str()),
                    ("IRList.nil", "IRFunc" | "IRGlobal") | ("IRList.cons", "IRNode" | "IRFunc")
                ),
                "v1 is closed to HAND's original constructor type arguments"
            );
            out.insert(start + 1, '@');
            cursor = start + 2;
        }
    }
    out
}

#[test]
fn current_source_spelling_v1_is_closed_and_argument_preserving() {
    for historical in HAND {
        let at_pin = historical.replace("IRTy.struct_ 29", "IRTy.struct_ 765");
        let current = current_source_spelling_v1(&at_pin);
        assert_eq!(current.replace("@IRList.", "IRList."), at_pin);
        assert_eq!(current_source_spelling_v1(&current), current);
    }
    let module = current_source_spelling_v1(HAND[5]);
    assert!(module.contains("(@IRList.cons IRFunc "));
    assert!(module.contains("(@IRList.nil IRGlobal)"));
    for other in [
        "def other : Type := (Other.IRList.nil IRFunc)",
        "def other : Type := (IRList.nilSuffix IRFunc)",
        "def other : Type := (@IRList.nil IRFunc)",
    ] {
        assert_eq!(current_source_spelling_v1(other), other);
    }
    for incomplete in [
        "def bad : Type := (IRList.nil)",
        "def bad : Type := (IRList.cons IRFunc f)",
        "def bad : Type := (IRList.cons IRFunc f (IRList.nil IRFunc)",
        "def bad : Type := (IRList.nil IRScalar)",
    ] {
        assert!(std::panic::catch_unwind(|| current_source_spelling_v1(incomplete)).is_err());
    }
}

/// The top-level arguments of `(head a b …)`, given the byte index just past
/// the head and its following space, and the index of the closing paren.
///
/// Byte indices throughout, which is sound because every spec source is ASCII —
/// `eval_ir_has_loose_bvars_tests.rs::test_sources_balanced_ascii` is the lane
/// that keeps it so, and it now covers the minted script too.
fn split_args(s: &str, from: usize) -> (Vec<String>, usize) {
    let b = s.as_bytes();
    let (mut i, mut depth, mut cur, mut out) = (from, 0i32, String::new(), Vec::new());
    while i < b.len() {
        match b[i] {
            b'(' => depth += 1,
            b')' if depth == 0 => break,
            b')' => depth -= 1,
            b' ' if depth == 0 => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
                i += 1;
                continue;
            }
            _ => {}
        }
        cur.push(char::from(b[i]));
        i += 1;
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    (out, i)
}

/// `(name a₁ … aₙ)` → the `IRList.cons` spine its REGISTERED definition unfolds
/// to (`eval_ir_crystal.rs` for `ir_bd1..ir_bd6`, `eval_ir_meta_tag.rs` for
/// `ir_mt_bd9`).
fn unfold_builder(mut s: String, name: &str, arity: usize) -> String {
    let head = format!("({name} ");
    while let Some(k) = s.find(&head) {
        let (args, end) = split_args(&s, k + head.len());
        assert_eq!(args.len(), arity, "{name} takes {arity} nodes: {args:?}");
        let mut spine = String::from("(@IRList.nil IRNode)");
        for a in args.iter().rev() {
            spine = format!("(@IRList.cons IRNode {a} {spine})");
        }
        s = format!("{}{spine}{}", &s[..k], &s[end + 1..]);
    }
    s
}

/// Unfold every registered alias either side may use, so what is left is the
/// same ground term or is not.
///
/// Each step is one DELTA step on a definition the specification registers, and
/// the source is named. Nothing here is a rewrite invented for the comparison.
fn unfold(line: &str) -> String {
    // `def ir_br_tu32 : IRTy := IRTy.uint_ ir_d32` (eval_ir_bvar_range.rs)
    // `def ir_vc_tu64 : IRTy := IRTy.uint_ ir_d64` (eval_ir_valid_char.rs)
    let mut s = line
        .replace("ir_br_tu32", "(IRTy.uint_ ir_d32)")
        .replace("ir_vc_tu64", "(IRTy.uint_ ir_d64)");
    for (name, arity) in [
        ("ir_mt_bd9", 9),
        ("ir_bd6", 6),
        ("ir_bd3", 3),
        ("ir_bd2", 2),
        ("ir_bd1", 1),
    ] {
        s = unfold_builder(s, name, arity);
    }
    // The atom pool `ir_d0..ir_d64`, longest first so `ir_d32` is never read as
    // `ir_d3` followed by a `2`.
    for n in (0..=64u32).rev() {
        s = s.replace(&format!("ir_d{n} "), &format!("{n} "));
        s = s.replace(&format!("ir_d{n})"), &format!("{n})"));
    }
    s
}

/// **THE FINDING, and it is the good one: the hand transcription and the mint
/// are the SAME PROGRAM.**
///
/// Every difference disappears under one delta step per registered alias, so
/// the sentence the truth-up's §6 attaches to this body survives the migration
/// intact.
#[test]
fn the_hand_transcription_and_the_mint_are_the_same_program() {
    let minted: Vec<&str> = ir_mint::IR_HLB_DEFS
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .collect();
    assert_eq!(minted.len(), HAND.len(), "six definitions either way");
    // HAND is verbatim, so its one crate-level id is the 2026-08-23 FIXTURE-ERA
    // struct id (29). The 2026-10-07 source-bound rebaseline re-pinned that
    // build fact to 765 (data/crystal_fixture_rebaseline_2026-10-07_047ebd051.json,
    // has_loose_bvars type-table-index struct.29 -> struct.765) with zero
    // instructions moved, so the comparison is taken against the hand line at
    // the CURRENT pin -- the ledger's mapping, applied once and named here.
    // Current-source v1 adds only explicit IRList constructor markers, after
    // the unchanged ledger-bound id map. The comparison/count below concern
    // this current representation, never byte equality of historical HAND.
    let hand_at_current_pin: Vec<String> = HAND
        .iter()
        .map(|h| h.replace("IRTy.struct_ 29", "IRTy.struct_ 765"))
        .map(|h| current_source_spelling_v1(&h))
        .collect();
    assert_ne!(
        hand_at_current_pin[0], HAND[0],
        "the re-pin must bite on the alias line, or this comparison is against nothing new"
    );
    let mut identical = 0;
    for (h, m) in hand_at_current_pin.iter().zip(&minted) {
        let name = h.split(' ').nth(1).unwrap_or("?");
        if h == m {
            identical += 1;
            println!("[{name}] BYTE-IDENTICAL");
        } else {
            println!("[{name}] DIFFERS\n  hand:   {h}\n  minted: {m}");
        }
        assert_eq!(
            unfold(h),
            unfold(m),
            "[{name}] the hand line and the minted line are NOT the same term after unfolding \
             every registered alias. That is a SEMANTIC divergence and the migration must stop: \
             follow the ir_lz decision structure (rebase the theorems, prove a refinement, or \
             retire the model), never adopt the minted side quietly"
        );
    }
    assert_eq!(
        identical, 4,
        "four lines minted byte-identical — ir_hlb_tself, ir_hlb_func, ir_lbr_func and the \
         two-function ir_hlb_module"
    );
    // The classes, pinned so a later mint that changed one of them says so.
    assert!(
        !ir_mint::IR_HLB_DEFS.contains("ir_br_tu32")
            && !ir_mint::IR_HLB_DEFS.contains("ir_vc_tu64"),
        "the mint borrows no sibling chain's type alias"
    );
    assert!(
        !ir_mint::IR_HLB_DEFS.contains("ir_mt_bd9") && !ir_mint::IR_HLB_DEFS.contains("ir_bd3"),
        "the mint borrows no sibling chain's node-list builder"
    );
    // NON-VACUITY, both ways. An `unfold` that returned its input, or that
    // collapsed everything, would make the equality above true and empty.
    assert_ne!(
        unfold(HAND[1]),
        HAND[1],
        "the unfolder must actually unfold the hand line"
    );
    assert_ne!(
        unfold(minted[1]),
        minted[1],
        "…and the minted line, whose ir_dN atoms are aliases too"
    );
    assert_ne!(
        unfold(&hand_at_current_pin[1]),
        hand_at_current_pin[1],
        "the unfolder must also unfold the current-source hand projection"
    );
    // And it must still SEPARATE two different programs: one operator moved on
    // either side, and the two no longer unfold to the same term.
    for (from, to) in [
        ("IRICmpOp.ugt", "IRICmpOp.ult"),
        ("IRInst.call ir_d1", "IRInst.call ir_d0"),
    ] {
        let mutated = HAND[1].replace(from, to);
        assert_ne!(mutated, HAND[1], "the mutation `{from}` must apply");
        assert_ne!(
            unfold(&mutated),
            unfold(minted[1]),
            "unfolding must not absorb a real change (`{from}` -> `{to}`)"
        );
        // Compare mutations in the SAME current spelling. A bare/@ difference
        // must not be what makes a semantic mutation appear detectable.
        let mutated_current = hand_at_current_pin[1].replace(from, to);
        assert_ne!(
            mutated_current, hand_at_current_pin[1],
            "the current mutation must apply"
        );
        assert_ne!(
            unfold(&mutated_current),
            unfold(minted[1]),
            "current-source unfolding must preserve the change (`{from}` -> `{to}`)"
        );
        let mutated_mint = minted[1].replace(from, to);
        assert_ne!(mutated_mint, minted[1], "the minted mutation must apply");
        assert_ne!(
            unfold(&hand_at_current_pin[1]),
            unfold(&mutated_mint),
            "the same mutation on the minted side must also remain visible"
        );
    }
    assert!(
        ir_mint::IR_HLB_DEFS.contains("(IRConst.int_ ir_d0)")
            && ir_mint::IR_HLB_DEFS.contains("(IRConst.int_ 44)"),
        "the data pool's cutoff at 16: 0 renders as an atom, 44 as a literal"
    );
}

/// The chain's PROVENANCE, at its real strength — two reader-A dumps, and the
/// record says two rather than the eleven original rows' three.
///
/// The second dump is the one that makes the caller's `(call 1 …)` a
/// producer-invariant fact rather than a numeral from one build: it moved ALL
/// FOUR of the chain's crate-level indices (func 3650/3649 -> 3665/3664, functy
/// 432/430 -> 438/436) and the core text did not move at all.
#[test]
fn the_mint_record_states_two_dumps_and_not_three() {
    let r = ir_mint::IR_HLB_RECORD;
    assert!(
        r.contains("\"producer_dumps_observed\": 2"),
        "the record must state TWO dumps"
    );
    for sha in [
        // laneREG wc-REG/dump_O3, 2026-08-21 — the projection this was minted from.
        "af1597c4dffc1f722044457232caeacdf7f02c74bcfe5db7ff95314314c6c4cc",
        // laneF8 wc-ctl/dump_O3, 2026-08-23 — the independent reproduction.
        "84b723b8bcf40c02427b13c007d530f28d23b2f504db168f1c7584472077db6e",
    ] {
        assert!(r.contains(sha), "the record must name the dump {sha}");
    }
    assert!(
        !r.contains("producer_dumps_observed\": 3"),
        "this chain postdates the producer A/B record and must not claim its three"
    );
    // The fixture era is a THIRD set of ids, and the tag table pins THOSE —
    // reader A's are recorded, never compared.
    assert!(
        ir_mint::IR_HLB_TAGS.contains("\"functy\": 410")
            && ir_mint::IR_HLB_TAGS.contains("\"functy\": 408"),
        "the interface pins are the FIXTURE-era signature indices"
    );
    assert!(
        r.contains("438") && r.contains("432"),
        "…and the record carries reader A's, from both dumps"
    );
}
