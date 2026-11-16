// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for the GLOBALS LANE ([`super::mint_globals`]): minting a
//! `(globals …)` list, the three-way namespace check, and reader C's
//! read-back of the registered `IRList IRGlobal`.
//!
//! A sibling of [`super::tests`] rather than a section inside it, for the same
//! reason [`super::mint_globals`] is a sibling of [`super::mint`]: the lane is
//! one unit, and the file it would otherwise sit in is already over the
//! repository's 500-line cap.

use super::tests::GLOBALS_PROBE_HEAD;
use super::{core, mint, mint_globals, tags, Sx};

// ────────────────────────────────────────────────────────────────────────────
// Minting and decoding a module WITH a global list (the `ir_lzc` shape).
// ────────────────────────────────────────────────────────────────────────────

/// The smallest core module with a global in it: one function whose entry
/// block takes the address of global 0 (or, with `addresses` false, builds a
/// constant instead) and returns it, over the given `(globals …)` items.
fn one_global_core(addresses: bool, globals: &str) -> Sx {
    let first = if addresses {
        "(node (results 1) (globaladdr 0))"
    } else {
        "(node (results 1) (const (uint 8) (int 1)))"
    };
    core::parse(&format!(
        "(module (funcs (func 0 (params 0) (entry 0) (blocks (block 0 (params) (nodes {first} \
         (node (results) (ret (vals 1)))))))) (globals {globals}))"
    ))
    .expect("a hand core module parses")
}

/// A tag table whose `globals` lane pins exactly canonical global 0.
fn one_global_tags() -> tags::Tags {
    tags::parse(&format!(
        r#"{GLOBALS_PROBE_HEAD}[{{"canonical":0,"crate_id":4557,"name":"g","ty":"[u8 x 2]","linkage":"internal"}}]}}"#
    ))
    .expect("a one-global table parses")
}

/// The numeral policy, stated as an assertion on the minted text: the global's
/// INDEX is structural (`ir_d0`), its initializer bytes are data (`ir_d8` for
/// 8, the literal `108` for 108), the `IRGlobal` line lands after the aliases
/// and before the first block, and the module line carries the cons list.
/// The same module without a global keeps the literal `(@IRList.nil IRGlobal)`
/// and no `_g` line. M3 judges this explicit spelling and its decoded module.
#[test]
fn mint_a_module_with_one_global_states_the_numeral_policy() {
    let core = one_global_core(true, "(global 0 (agg (int 8) (int 108)))");
    let minted = mint(&core, "ir_gx", &one_global_tags()).expect("a module with one global mints");
    assert_eq!(
        minted.lines,
        vec![
            "def ir_gx_g0 : IRGlobal := IRGlobal.mk ir_d0 (IRConst.aggv (IRConst.vcons \
             (IRConst.int_ ir_d8) (IRConst.vcons (IRConst.int_ 108) IRConst.vnil)))"
                .to_string(),
            "def ir_gx_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_bd2 (ir_nd1 \
             (IRInst.globaladdr ir_d0) ir_d1) (ir_nd (IRInst.ret (ir_nl1 ir_d1))))"
                .to_string(),
            "def ir_gx_func : IRFunc := IRFunc.mk ir_d0 (ir_nl1 ir_d0) ir_d0 (ir_blk ir_gx_b0 \
             ir_blk0)"
                .to_string(),
            "def ir_gx_module : IRModule := IRModule.mk (@IRList.cons IRFunc ir_gx_func \
             (@IRList.nil IRFunc)) (@IRList.cons IRGlobal ir_gx_g0 (@IRList.nil IRGlobal))"
                .to_string(),
        ]
    );
    // The control: no global, no `_g` line, the nil literal, under a table
    // with no `globals` lane at all.
    let bare = mint(&one_global_core(false, ""), "ir_gx", &tags::Tags::default())
        .expect("a module without a global mints under a table without the lane");
    assert_eq!(bare.lines.len(), 3, "no IRGlobal line:\n{}", bare.text());
    assert!(bare.lines.iter().all(|l| !l.contains("IRGlobal.mk")));
    assert!(
        bare.lines[2].ends_with(" (@IRList.nil IRGlobal)"),
        "the empty global list must retain its explicit type argument:\n{}",
        bare.lines[2]
    );
    assert_eq!(
        mint_globals::GLOBAL.args.len(),
        2,
        "IRGlobal.mk : Nat → IRConst → IRGlobal"
    );
}

/// Reader C reads the REGISTERED term back: the minted script is elaborated
/// into the EvalIR specification and the elaborated `ir_gx_module` decodes to
/// exactly the hand core module, global list included. This is the check that
/// keeps `mint` out of the trusted base for a module with globals, as M4 does
/// for every chain without one.
#[test]
fn mint_and_decode_round_trip_a_module_with_one_global() {
    crate::test_utils::run_with_stack(|| {
        let core = one_global_core(true, "(global 0 (agg (int 8) (int 108)))");
        let t = one_global_tags();
        let minted = mint(&core, "ir_gx", &t).expect("mints");
        let mut spec = crate::eval_ir::build_spec_with_stack().expect("the EvalIR spec builds");
        for line in &minted.lines {
            spec.add_recursive_def(line, "ir_mint globals round-trip probe")
                .unwrap_or_else(|e| panic!("registering `{line}`: {e}"));
        }
        let decoded = super::decode(spec.env(), "ir_gx_module", &t)
            .expect("reader C decodes the registered module");
        let canonical = core::print(&decoded).expect("print");
        assert_eq!(
            canonical,
            core::print(&core).expect("print"),
            "the elaborated term does not decode to the module it was minted from"
        );
        assert!(
            canonical.contains("(globals (global 0 (agg (int 8) (int 108))))"),
            "the global list survives the round trip:\n{canonical}"
        );
        // Not a constant reader: a module registered with NO global decodes to
        // a module with none.
        let bare =
            mint(&one_global_core(false, ""), "ir_gy", &tags::Tags::default()).expect("mints");
        for line in &bare.lines {
            spec.add_recursive_def(line, "ir_mint globals round-trip control")
                .unwrap_or_else(|e| panic!("registering `{line}`: {e}"));
        }
        let bare_decoded =
            super::decode(spec.env(), "ir_gy_module", &tags::Tags::default()).expect("decodes");
        assert!(
            core::print(&bare_decoded)
                .expect("print")
                .contains("(globals)"),
            "reader C reads the empty list back as empty"
        );
    });
}

/// `(globaladdr k)` and `(global k …)` are one namespace: an address into an
/// entry the module does not declare is refused at mint, and the refusal names
/// the missing entry rather than something downstream.
#[test]
fn a_globaladdr_with_no_global_entry_is_refused() {
    let e = mint(&one_global_core(true, ""), "ir_gx", &one_global_tags())
        .expect_err("a `(globaladdr 0)` with no `(global 0 …)` must refuse");
    assert!(
        format!("{e}").contains("does not declare"),
        "the refusal names the missing entry: {e}"
    );
}

/// A global list entry that no instruction addresses is a cell the machine
/// would materialize for no reader, and it is refused rather than minted.
#[test]
fn a_global_no_instruction_addresses_is_refused() {
    let e = mint(
        &one_global_core(false, "(global 0 (agg (int 1)))"),
        "ir_gx",
        &one_global_tags(),
    )
    .expect_err("a `(global 0 …)` nothing addresses must refuse");
    assert!(
        format!("{e}").contains("no instruction addresses"),
        "the refusal says which direction failed: {e}"
    );
}

/// A global index is STRUCTURAL and renders through the `ir_d0..ir_d130` pool;
/// an index one above it refuses as the numeral, before the position check
/// could read the same numeral as an ordering fault. And the list must be dense
/// and in order, because its order is the one `ir_global_find` walks.
///
/// The index is DERIVED from the bound: it was a literal `64`, one above the
/// `ir_d63` pool it was written against, and the 2026-09-16 widening to
/// `ir_d130` (`9e1d4df2d`) made it a member, so this pin stopped refusing.
#[test]
fn a_global_index_above_the_atom_pool_is_refused() {
    let above_pool = mint::MAX_STRUCTURAL_ATOM + 1;
    let e = mint(
        &one_global_core(true, &format!("(global {above_pool} (agg (int 1)))")),
        "ir_gx",
        &one_global_tags(),
    )
    .expect_err("a global index one above MAX_STRUCTURAL_ATOM is outside the pool");
    assert!(
        matches!(e, super::MintError::Numeral(n) if n == above_pool),
        "expected Numeral({above_pool}), got: {e}"
    );
    let e = mint(
        &one_global_core(true, "(global 1 (agg (int 1)))"),
        "ir_gx",
        &one_global_tags(),
    )
    .expect_err("a list starting at 1 is not dense");
    assert!(
        format!("{e}").contains("out of order or not dense"),
        "unexpected refusal: {e}"
    );
}

/// The verifier's amendment: the minter consults the tag table's `globals`
/// lane for every declared AND every addressed index, exactly as
/// `check_func_namespace` consults `funcs` for every callee. A hand core that
/// never passes through `project` cannot mint a global whose name, type and
/// linkage nothing recorded.
#[test]
fn a_global_the_tag_table_does_not_pin_is_refused_at_mint() {
    let core = one_global_core(true, "(global 0 (agg (int 1)))");
    let e = mint(&core, "ir_gx", &tags::Tags::default())
        .expect_err("a global no row pins must refuse at mint, not only in project");
    assert!(
        format!("{e}").contains("not in the chain's tag table"),
        "the refusal is the pin's own: {e}"
    );
    // …and the same core under the pinned table mints (the positive control
    // for the refusal above).
    mint(&core, "ir_gx", &one_global_tags()).expect("pinned, it mints");
}

/// The chain this lane exists for: the committed `ir_lzc` core module — the
/// root, the deref body, and the one promoted string global — mints under its
/// committed tag table, with the global's 34 bytes as data, its index as
/// structure, and the two-function / one-global module line.
#[test]
fn the_lzc_core_mints_under_its_tag_table() {
    const LZC_CORE: &str = include_str!("../spec/core_spec/generated/ir_lzc.core.txt");
    let core = core::parse(LZC_CORE).expect("the committed lzc core parses");
    let t = tags::parse(super::IR_LZC_TAGS).expect("the lzc table");
    let minted = mint(&core, "ir_lzc", &t).expect("the lzc core mints");
    let g0 = minted
        .lines
        .iter()
        .find(|l| l.starts_with("def ir_lzc_g0 "))
        .expect("an IRGlobal line for the promoted string");
    assert!(
        g0.starts_with(
            "def ir_lzc_g0 : IRGlobal := IRGlobal.mk ir_d0 (IRConst.aggv (IRConst.vcons \
             (IRConst.int_ 108) (IRConst.vcons (IRConst.int_ 105) "
        ),
        "index structural, bytes data:\n{g0}"
    );
    assert_eq!(
        g0.matches("IRConst.vcons").count(),
        34,
        "34 bytes of `live LevelArc must contain a level`"
    );
    // Placement: after the alias, before the first block.
    assert_eq!(
        minted.lines[0], "def ir_lzc_tlevel : IRTy := IRTy.enum_ ir_d3",
        "the alias comes first"
    );
    assert!(minted.lines[1].starts_with("def ir_lzc_g0 "));
    assert!(minted.lines[2].starts_with("def ir_lzc_b0 "));
    // The deref body addresses it and builds the `&str` over it.
    let lad = minted
        .lines
        .iter()
        .find(|l| l.starts_with("def ir_lad_b0 "))
        .expect("the deref's entry block");
    assert!(
        lad.contains("(ir_nd1 (IRInst.globaladdr ir_d0) ir_d2)")
            && lad.contains(
                "(IRInst.ptrfromparts (IRTy.fatptr_ (IRTy.uint_ ir_d8)) (IRTy.uint_ 64) ir_d2 ir_d3)"
            ),
        "{lad}"
    );
    assert_eq!(
        minted.lines.last().map(String::as_str),
        Some(
            "def ir_lzc_module : IRModule := IRModule.mk (@IRList.cons IRFunc ir_lzc_func \
             (@IRList.cons IRFunc ir_lad_func (@IRList.nil IRFunc))) (@IRList.cons IRGlobal \
             ir_lzc_g0 (@IRList.nil IRGlobal))"
        )
    );
}
