// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **M5 for `ir_lzc`: the A1 lane comparator, unchanged, over BOTH minted
//! bodies.**
//!
//! Split out of `crystal_a2_mint_lzc.rs` — read that file's header first for
//! what the chain is and what it does not claim.
//!
//! # Why each body is handed ONE definition line
//!
//! `parse_clean` splits its input on the block marker and reads everything
//! after each occurrence, so the LAST chunk runs to the end of what it was
//! given. Handing it the whole minted script would put the callee's six
//! `IRInst.…` nodes inside the root's `ir_lzc_b9` chunk — against an emitted
//! `bb9` that holds one `br` — and the comparison would fail on the wrong
//! lane with a message nobody can read. `crystal_a2_mint_hlb.rs` documents the
//! same hazard and works around it the same way; `ir_lz` never met it only
//! because its trailing `ir_lz_func` / `ir_lz_module` lines carry no `IRInst.`
//! token, and this chain's do.
//!
//! [`m5_the_a1_comparator_agrees_over_the_minted_script`] therefore runs a LEAK
//! DETECTOR — `ir_lzc_b9` parses to exactly one `br`, and no node anywhere in
//! the root's parse carries a class only the callee has — **before** it calls
//! `assert_lanes`. Ordering is the whole point of the detector, not decoration:
//! `assert_lanes` compares the `order` lane by name and ends in a whole-`Cfg`
//! equality, so it WOULD catch the same leak, but it reaches it on whichever
//! lane happens to differ first. Both faces were measured on 2026-09-10 by
//! mutating [`root_blocks`] to keep the whole script — the leak the paragraph
//! above describes. As the code stands the panic is this file's own
//! `ir_lzc_b9 must parse to exactly one `br`…`, naming the callee's definition
//! and the chunk it leaked into. With `assert_lanes` put back FIRST (the
//! previous ordering, restored for one run) the same mutation dies inside the
//! comparator instead: `ir_lzc (minted, root): RET lane differs: emitted
//! {6: [1]} vs Clean {6: [1], 9: [5]}` at
//! `crystal_a1_lineage/emitted_cfg.rs`, a message about return values that
//! names neither the callee nor the chunk. Detector first, so the leak is
//! diagnosed by name.
//!
//! # The two mnemonics that made this chain need a rename table
//!
//! `trust-ir` prints `global_addr` and `ptr_from_parts`; the registered
//! constructors are `IRInst.globaladdr` and `IRInst.ptrfromparts`. The order
//! lane compares CLEAN class names, so the emitted side renames — the table is
//! `CLASS_RENAMES` in `crystal_a1_lineage/emitted_cfg_parse_class.rs`, and
//! this is the first chain that reaches it.

use clean_verify::ir_mint;

use super::emitted_cfg::{assert_lanes, parse_clean, parse_emitted};
use super::{DEREF, IS_ZERO};

/// ONE definition line of the minted script, by name — the callee's block.
fn def_line(name: &str) -> &'static str {
    let prefix = format!("def {name} ");
    ir_mint::IR_LZC_DEFS
        .lines()
        .map(str::trim)
        .find(|l| l.starts_with(&prefix))
        .unwrap_or_else(|| panic!("the minted script must define {name}"))
}

/// The ROOT's ten block lines and nothing else, so the callee's definition
/// cannot leak into `ir_lzc_b9`'s chunk.
fn root_blocks() -> String {
    ir_mint::IR_LZC_DEFS
        .lines()
        .filter(|l| l.starts_with("def ir_lzc_b"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// The classes only the CALLEE's body has. None of them may appear anywhere in
/// the root's parse: each is the signature of a leak from the shared script.
///
/// `call` is deliberately NOT one of them, and measured rather than assumed:
/// the root calls the deref and calls ITSELF, so THREE of its blocks — `b4`,
/// `b5` and `b7`, two call nodes each, SIX in the whole root — carry a `call`
/// of their own, and a whole-root scan for one is red on a correct parse.
/// Both sides of that census, run 2026-09-10:
/// `awk '/^def ir_lzc_b/ {n=gsub(/IRInst.call/,"&"); if (n) print $2, n}'` over
/// `generated/ir_lzc.defs.txt` prints `ir_lzc_b4 2 / ir_lzc_b5 2 /
/// ir_lzc_b7 2`, and `grep -c "= call @func"` over
/// `tests/fixtures/level_is_zero.trust-ir.txt` is `6` (bb4, bb5, bb7).
/// The `call` leak is caught where it would actually land — the exact
/// `ir_lzc_b9` assertion below, that being the chunk a whole-script parse
/// appends the callee to.
const CALLEE_ONLY: &[&str] = &["globaladdr", "ptrfromparts"];

#[test]
fn m5_the_a1_comparator_agrees_over_the_minted_script() {
    // THE ROOT — the designated target, byte-frozen as `(func 0 …)` and
    // re-minted here under `ir_lzc_*` names. Same assertions as
    // `crystal_a2_mint_lz.rs`'s M5 over the same emitted body.
    let root_src = root_blocks();
    let emitted = parse_emitted(IS_ZERO);
    let clean = parse_clean(&root_src, "def ir_lzc_b");

    // THE LEAK DETECTOR, and it runs BEFORE the comparator on purpose.
    // `ir_lzc_b9` is the last block chunk, so a whole-script parse would absorb
    // `def ir_lad_b0`'s six nodes here; block 9 holds exactly one `br` and
    // nothing else. `assert_lanes` below would notice that too — it compares
    // the `order` lane by name and then the whole `Cfg` — but it fires on
    // whichever lane differs first, measured to be RET, with a message that
    // names neither the callee nor the chunk. Diagnose by name first, compare
    // second.
    assert_eq!(
        clean.order.get(&9).map(Vec::as_slice),
        Some(&[("br".to_string(), Vec::new())][..]),
        "ir_lzc_b9 must parse to exactly one `br`; anything else is the callee's definition \
         leaking into the root's last chunk"
    );
    // …and the same detector by CLASS rather than by chunk. Today's script puts
    // `def ir_lad_b0` after `def ir_lzc_b9` (`generated/ir_lzc.defs.txt` line
    // 14 of 16), so the assertion above is the one that fires on a whole-script
    // parse — measured, that is the panic. This loop is the net for a leak that
    // lands anywhere ELSE: a callee block emitted BETWEEN two root blocks would
    // be absorbed by the preceding chunk, leaving `ir_lzc_b9` correct and the
    // wrong program compared. Measured the same day by splicing
    // `def_line("ir_lad_b0")` in AHEAD of `def ir_lzc_b9`: `ir_lzc_b9` stays
    // exactly one `br` and this loop is what panics — `the root's parse carries
    // a `globaladdr` in bb8`. It costs one pass over ten short lanes.
    for (b, seq) in &clean.order {
        for (class, _) in seq {
            assert!(
                !CALLEE_ONLY.contains(&class.as_str()),
                "the root's parse carries a `{class}` in bb{b}: the callee's body leaked into \
                 the root's chunk, and every lane compared below is a lane of the wrong program"
            );
        }
    }

    assert_lanes(&emitted, &clean, "ir_lzc (minted, root)");
    assert_eq!(emitted.blocks, clean.blocks);
    assert_eq!(emitted.cases, clean.cases);
    assert_eq!(emitted.default, clean.default);
    assert_eq!(emitted.param_blocks, clean.param_blocks);
    assert_eq!(emitted.blocks.len(), 10, "coverage denominator");

    // THE CALLEE — the deref, one block, six instructions, and the first body
    // in this tree whose order lane carries the `globaladdr` CLASS. The lane
    // names the class and the bound id and nothing else: the GLOBAL INDEX falls
    // into the `_ => {}` arm of the value-lane match on both sides
    // (`emitted_cfg_parse.rs`, `emitted_cfg_parse_clean.rs`), and
    // `ptrfromparts` compares
    // neither its two types nor its two operands. Those slots ARE pinned, just
    // not here: M10 (`lzc_interface.rs`, `m10_the_interface_pins_bite`) refuses
    // `@global.4557 -> @global.9999` and `fatptr<str> -> fatptr<slice ty.0>` by
    // mutation, and M2 compares the FULL canonical print of reader A's module
    // against reader B's, both slots included. Read this lane for program
    // ORDER, never for operand identity.
    let callee = parse_emitted(DEREF);
    let lad = parse_clean(def_line("ir_lad_b0"), "def ir_lad_b");
    assert_lanes(&callee, &lad, "ir_lad (minted, callee)");
    assert_eq!(callee.blocks, lad.blocks);
    assert_eq!(callee.blocks, vec![0], "the deref has one block");
    assert_eq!(callee.rets, lad.rets);
    let want: Vec<(String, Vec<u32>)> = [
        ("call", vec![1u32]),
        ("globaladdr", vec![2]),
        ("const", vec![3]),
        ("ptrfromparts", vec![4]),
        ("call", vec![5]),
        ("ret", vec![]),
    ]
    .into_iter()
    .map(|(c, r)| (c.to_string(), r))
    .collect();
    for (side, cfg) in [("emitted", &callee), ("Clean", &lad)] {
        assert_eq!(
            cfg.order.get(&0).map(Vec::as_slice),
            Some(want.as_slice()),
            "{side}: the deref's bb0 must be exactly `call, globaladdr, const, ptrfromparts, \
             call, ret` with those bound ids. The two middle classes are the mnemonics whose \
             printed spelling carries an underscore the Clean constructor does not, so this is \
             also where `CLASS_RENAMES` stops being a comment"
        );
    }
    // …and the two comparisons are INDEPENDENT. Stated on the ONE key both
    // maps have: a whole-map `assert_ne!` cannot fail here, since the root's
    // key set is the ten blocks pinned above and the callee's is `[0]`, so the
    // maps differ by key set on every execution and the check would be dead.
    // Block 0 against block 0 can fail, and is what a second parse of the SAME
    // source would look like.
    assert_ne!(
        lad.order.get(&0),
        clean.order.get(&0),
        "the deref's bb0 and the root's bb0 must not parse to the same instruction \
         sequence — two parses of the same source would satisfy every assertion above"
    );
}
