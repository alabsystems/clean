// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for the mint pipeline. The end-to-end gate is
//! `tests/crystal_a2_mint.rs`; these are the properties of the pieces, and in
//! particular the NAME-PARITY test that is the standing mitigation for the
//! matched-pair residual named in the module docs.

use super::{core, mint, read_emitted, shape, tags, SelfFunc, Sx};

/// Every declared shape names a DISTINCT Clean constructor and a distinct core
/// mnemonic, in both directions.
///
/// This is the parity table the minter and the decoder share. If two rows named
/// one constructor, a matched pair of mistranslations would be structurally
/// possible rather than merely conceivable; if a row named a constructor the
/// specification does not declare, minting would produce an unelaborable term.
#[test]
fn shape_table_is_a_bijection_in_both_directions() {
    for (label, cores, cleans) in [
        (
            "IRInst",
            shape::INSTS.iter().map(|s| s.core).collect::<Vec<_>>(),
            shape::INSTS.iter().map(|s| s.clean).collect::<Vec<_>>(),
        ),
        (
            "IRTy",
            shape::TYS.iter().map(|s| s.core).collect(),
            shape::TYS.iter().map(|s| s.clean).collect(),
        ),
        (
            "IRConst",
            shape::CONSTS.iter().map(|s| s.core).collect(),
            shape::CONSTS.iter().map(|s| s.clean).collect(),
        ),
    ] {
        let mut cs = cores.clone();
        cs.sort_unstable();
        cs.dedup();
        assert_eq!(cs.len(), cores.len(), "{label}: duplicate core mnemonic");
        let mut ks = cleans.clone();
        ks.sort_unstable();
        ks.dedup();
        assert_eq!(
            ks.len(),
            cleans.len(),
            "{label}: duplicate Clean constructor"
        );
    }
    for alpha in ["binop", "unop", "overflow", "icmp", "fcmp", "cast"] {
        let rows = shape::alphabet(alpha);
        assert!(!rows.is_empty(), "{alpha}: no alphabet");
        let mut cs: Vec<_> = rows.iter().map(|(c, _)| *c).collect();
        cs.sort_unstable();
        cs.dedup();
        assert_eq!(cs.len(), rows.len(), "{alpha}: duplicate core operator");
        let mut ks: Vec<_> = rows.iter().map(|(_, k)| *k).collect();
        ks.sort_unstable();
        ks.dedup();
        assert_eq!(ks.len(), rows.len(), "{alpha}: duplicate Clean operator");
    }
}

/// The counts are the ones the `IRInst` / `IRTy` / operator inductives declare.
/// A constructor added to the specification without a row here is a silent
/// hole in the minter, so the number is pinned rather than derived.
#[test]
fn shape_table_covers_the_declared_alphabets() {
    assert_eq!(shape::INSTS.len(), 28, "IRInst has 28 constructors");
    assert_eq!(shape::TYS.len(), 18, "IRTy has 18 constructors");
    assert_eq!(shape::BINOP.len(), 20);
    assert_eq!(shape::UNOP.len(), 9);
    assert_eq!(shape::OVERFLOW.len(), 3);
    assert_eq!(shape::ICMP.len(), 10);
    assert_eq!(shape::FCMP.len(), 12);
    assert_eq!(shape::CAST.len(), 17);
}

#[test]
fn tag_table_parses_and_is_invertible() {
    let t = tags::parse(super::IR_H2_TAGS).expect("the committed tag table must parse");
    assert_eq!(t.enums.len(), 1, "one aggregate: CleanMode");
    assert_eq!(t.enums[&0], (13, "ir_h2_tmode".to_string()));
    assert_eq!(t.enum_canonical(13).expect("invertible"), 0);
    assert!(
        t.enum_canonical(176).is_err(),
        "an id the table does not list must REFUSE, not become a canonical index of its own"
    );
    assert!(
        t.enum_alias(1).is_err(),
        "an unlisted canonical index must refuse"
    );
    assert_eq!(
        t.alias_defs(),
        vec!["def ir_h2_tmode : IRTy := IRTy.enum_ ir_d13".to_string()]
    );
}

#[test]
fn tag_table_parser_is_fail_closed() {
    assert!(tags::parse("not json").is_err());
    assert!(
        tags::parse("{}").is_err(),
        "a missing `enums` array is not an empty one"
    );
    assert!(
        tags::parse(r#"{"enums":[],"structs":[]}"#).is_err(),
        "a missing `funcs` lane is not an empty one either. A table that omitted it would read as \
         `this body calls nothing`, which is the silent default the 2026-08-20 callee-namespace \
         collision lived in."
    );
    assert!(
        tags::parse(
            r#"{"body":"t","interface":{"linkage":"external","calling_conv":"rustcc","functy":0,"producer":null,"params":[],"block_params":[],"aligns":[],"clauses":[]},"enums":[],"structs":[],"funcs":[{"canonical":1,"crate_id":9,"name":"f"}]}"#
        )
        .is_err(),
        "the funcs lane must be DENSE from 0: canonical 0 is the function's own entry, and a hole \
         there is a callee index no row accounts for"
    );
    assert!(
        tags::parse(
            r#"{"body":"t","interface":{"linkage":"external","calling_conv":"rustcc","functy":0,"producer":null,"params":[],"block_params":[],"aligns":[],"clauses":[]},"enums":[],"structs":[],"funcs":[{"canonical":0,"crate_id":9,"name":"a"},{"canonical":1,"crate_id":9,"name":"b"}]}"#
        )
        .is_err(),
        "two canonical function indices claiming one crate id is not invertible"
    );
    assert!(
        tags::parse(r#"{"body":"t","interface":{"linkage":"external","calling_conv":"rustcc","functy":0,"producer":null,"params":[],"block_params":[],"aligns":[],"clauses":[]},"enums":[],"structs":[],"funcs":[{"canonical":0,"crate_id":9}]}"#).is_err(),
        "a funcs row must carry the NAME — the half that does not move under a re-interning, and \
         the only thing a reviewer can actually check"
    );
    assert!(
        tags::parse(r#"{"body":"t","interface":{"linkage":"external","calling_conv":"rustcc","functy":0,"producer":null,"params":[],"block_params":[],"aligns":[],"clauses":[]},"enums":[{"canonical":0,"crate_id":1,"alias":"a"},{"canonical":1,"crate_id":1,"alias":"b"}],"structs":[],"funcs":[]}"#)
            .is_err(),
        "two canonical indices claiming one crate id is not invertible"
    );
}

#[test]
fn core_text_round_trips_its_printer() {
    let sx = core::parse(super::IR_H2_CORE).expect("parse");
    assert_eq!(core::print(&sx).expect("print"), super::IR_H2_CORE);
}

#[test]
fn parser_is_fail_closed() {
    assert!(core::parse("(module").is_err(), "unclosed paren");
    assert!(core::parse("(module) (module)").is_err(), "trailing form");
    assert!(core::parse("").is_err(), "empty input");
    assert!(core::parse(")").is_err(), "stray close");
}

#[test]
fn mint_refuses_an_unwitnessed_flag() {
    let sx = read_emitted(include_str!(
        "../../tests/fixtures/has_cubical_layer.trust-ir.txt"
    ))
    .expect("reader B");
    let t = tags::parse(super::IR_H2_TAGS).expect("tag table");
    let e = mint(&sx, "ir_h2", &t).expect_err("a `?` flag must refuse to mint");
    assert!(
        format!("{e}").contains("unwitnessed"),
        "unexpected refusal: {e}"
    );
}

#[test]
fn mint_refuses_a_numeral_outside_the_atom_pool() {
    let sx = Sx::tag(
        "module",
        vec![
            Sx::tag(
                "funcs",
                vec![Sx::tag(
                    "func",
                    vec![
                        Sx::a("0"),
                        Sx::tag("params", vec![]),
                        Sx::tag("entry", vec![Sx::a("0")]),
                        Sx::tag(
                            "blocks",
                            vec![Sx::tag(
                                "block",
                                vec![
                                    Sx::a("0"),
                                    Sx::tag("params", vec![]),
                                    Sx::tag(
                                        "nodes",
                                        vec![Sx::tag(
                                            "node",
                                            vec![
                                                Sx::tag("results", vec![]),
                                                Sx::tag(
                                                    "ret",
                                                    vec![Sx::tag("vals", vec![Sx::a("99")])],
                                                ),
                                            ],
                                        )],
                                    ),
                                ],
                            )],
                        ),
                    ],
                )],
            ),
            Sx::tag("globals", vec![]),
        ],
    );
    let e = mint(&sx, "ir_x", &tags::Tags::default()).expect_err("99 is outside ir_d0..ir_d16");
    assert!(format!("{e}").contains("atom pool"), "unexpected: {e}");
}

#[test]
fn reader_b_refuses_an_unknown_instruction() {
    let text = "rustcc fn @x(functy.0) {\nbb0:\n    %1 = quantum_teleport u8 %0\n    ret %1\n}\n";
    let e = read_emitted(text).expect_err("an unknown printed form must refuse");
    assert!(format!("{e}").contains("no Clean image"), "unexpected: {e}");
}

#[test]
fn reader_b_reads_every_committed_chain_fixture_or_says_why() {
    // Coverage, printed rather than assumed. A fixture reader B cannot read is
    // recorded here with its refusal; it is never silently skipped.
    let fixtures: &[(&str, &str)] = &[
        (
            "has_cubical_layer",
            include_str!("../../tests/fixtures/has_cubical_layer.trust-ir.txt"),
        ),
        (
            "level_kind_ord",
            include_str!("../../tests/fixtures/level_kind_ord.trust-ir.txt"),
        ),
        (
            "from_source_system",
            include_str!("../../tests/fixtures/from_source_system.trust-ir.txt"),
        ),
        (
            "expr_path_step_clone",
            include_str!("../../tests/fixtures/expr_path_step_clone.trust-ir.txt"),
        ),
        (
            "level_is_zero",
            include_str!("../../tests/fixtures/level_is_zero.trust-ir.txt"),
        ),
        (
            "bvar_in_range",
            include_str!("../../tests/fixtures/bvar_in_range.trust-ir.txt"),
        ),
        (
            "flat_flags_contains",
            include_str!("../../tests/fixtures/flat_flags_contains.trust-ir.txt"),
        ),
        (
            "flat_flags_with",
            include_str!("../../tests/fixtures/flat_flags_with.trust-ir.txt"),
        ),
        (
            "float_div",
            include_str!("../../tests/fixtures/float_div.trust-ir.txt"),
        ),
        (
            "get_char_val_trunc",
            include_str!("../../tests/fixtures/get_char_val_trunc.trust-ir.txt"),
        ),
        (
            "is_valid_char",
            include_str!("../../tests/fixtures/is_valid_char.trust-ir.txt"),
        ),
        (
            "meta_tag_shl",
            include_str!("../../tests/fixtures/meta_tag_shl.trust-ir.txt"),
        ),
        (
            "strict_monads",
            include_str!("../../tests/fixtures/strict_monads.trust-ir.txt"),
        ),
    ];
    let mut report = String::from("\nreader B over the committed chain fixtures\n");
    let mut ok = 0usize;
    // `node_id_index` is read through its PIN, separately below: its body
    // contains `usize`, which reader B refuses by design until the chain's
    // tag table states the width. The pinned read is part of this
    // denominator, not an exemption from it.
    for (name, text) in fixtures {
        match read_emitted(text) {
            Ok(sx) => {
                core::print(&sx).expect("a read fixture must print");
                ok += 1;
                report.push_str(&format!("  {name:<22} READ\n"));
            }
            Err(e) => report.push_str(&format!("  {name:<22} REFUSED: {e}\n")),
        }
    }
    let ni_text = include_str!("../../tests/fixtures/node_id_index.trust-ir.txt");
    match super::emitted::read_with_pins(ni_text, SelfFunc::Unpinned, Some(64)) {
        Ok((sx, tags)) => {
            core::print(&sx).expect("a read fixture must print");
            assert_eq!(tags.usize_seen, 1, "one resolved usize site");
            ok += 1;
            report.push_str("  node_id_index          READ (usize pinned at 64)\n");
        }
        Err(e) => report.push_str(&format!("  node_id_index          REFUSED: {e}\n")),
    }
    // The CALL chain's two bodies are read through the chain's tag table, not
    // bare, and that is not a concession: its module holds TWO functions, so
    // reader B has to be told how many bodies the text carries and which
    // canonical index each occupies. Read bare, the pair would produce two
    // `(func 0 …)` modules — right for neither, and a module whose two
    // functions share an id is one `ir_func_find` cannot walk.
    let hlb = include_str!("../../tests/fixtures/has_loose_bvars.trust-ir.txt");
    let lbr = include_str!("../../tests/fixtures/loose_bvar_range_callee.trust-ir.txt");
    let ht = tags::parse(super::IR_HLB_TAGS).expect("the hlb tag table must parse");
    match super::project(&format!("{hlb}{lbr}"), &ht) {
        Ok(p) => {
            core::print(&p.core).expect("a read chain must print");
            assert_eq!(p.interfaces.len(), 2, "one interface per body");
            ok += 1;
            report.push_str("  has_loose_bvars+callee READ (two bodies, one module)\n");
        }
        Err(e) => report.push_str(&format!("  has_loose_bvars+callee REFUSED: {e}\n")),
    }
    println!("{report}");
    assert_eq!(
        ok,
        fixtures.len() + 2,
        "reader B must read every committed chain fixture:{report}"
    );
}

/// The CALL chain's tag table declares TWO bodies, and every lane the mint
/// needs for the second one is pinned rather than defaulted.
#[test]
fn the_hlb_tag_table_declares_two_bodies() {
    let t = tags::parse(super::IR_HLB_TAGS).expect("the hlb tag table must parse");
    assert_eq!(
        t.body_canonicals(),
        vec![0, 1],
        "the module holds the root and one sibling, in module order"
    );
    assert_eq!(t.self_func(), SelfFunc::Pinned(3658));
    assert_eq!(t.func_pin(1).expect("callee").0, 3657);
    assert_eq!(
        t.func_pin(1).expect("callee").1,
        "expr::meta::ExprMeta::loose_bvar_range"
    );
    // The sibling's Clean name prefix and its OWN interface — the two facts
    // that would otherwise be hand choices inside the specification.
    assert_eq!(t.body_prefix(1, "ir_hlb"), "ir_lbr");
    assert_eq!(t.body_prefix(0, "ir_hlb"), "ir_hlb");
    let callee = t.body_interface(1).expect("the sibling's interface");
    assert_eq!(callee.functy, 433, "the callee's OWN signature index");
    assert_ne!(
        callee.functy, t.interface.functy,
        "…and it is not the caller's"
    );
    assert!(
        callee.clauses.contains("proof") && !t.interface.clauses.contains("proof"),
        "only the callee carries `#proof: shift_in_range`"
    );
    // Every other committed chain declares ONE body, so nothing they mint moves.
    for (name, table) in [
        ("ir_h2", super::IR_H2_TAGS),
        ("ir_lz", super::IR_LZ_TAGS),
        ("ir_sm", super::IR_SM_TAGS),
    ] {
        let t = tags::parse(table).unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(t.body_canonicals(), vec![0], "{name} declares one body");
    }
}

/// The design's falsifiable prediction, run.
///
/// `docs/CRYSTAL_STATUS.md` records `expr_path_step_clone`'s fixture refresh
/// failing on `emitted enum176` vs registered `IRTy.enum_ 184` — a pure
/// crate-level re-interning artifact. Under first-use normalization that index
/// is local and the whole failure class disappears; here is the proof, over the
/// committed fixture and a copy of it with the enum id moved.
#[test]
fn enum_reinterning_is_absorbed_by_first_use_normalization() {
    let text = include_str!("../../tests/fixtures/expr_path_step_clone.trust-ir.txt");
    let a = core::print(&read_emitted(text).expect("as committed")).expect("print");
    let moved = text.replace("enum.184", "enum.176");
    assert_ne!(moved, text, "the substitution must actually move the id");
    let b = core::print(&read_emitted(&moved).expect("with the enum id moved")).expect("print");
    assert_eq!(
        a, b,
        "the enum re-interning drift class must be absorbed, not erased by table"
    );
    assert!(a.contains("(enum 0)"), "the normalized id is local:\n{a}");
    assert!(
        !a.contains("184") && !a.contains("176"),
        "no crate id survives:\n{a}"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// The function's own index and its callee ids are ONE namespace.
// ────────────────────────────────────────────────────────────────────────────

/// The committed `level_is_zero` table pins the namespace, and `self_func`
/// reads the body's own entry out of it.
#[test]
fn the_lz_tag_table_pins_the_whole_function_namespace() {
    let t = tags::parse(super::IR_LZ_TAGS).expect("the lz tag table must parse");
    assert_eq!(
        t.funcs.len(),
        2,
        "the body itself and its one foreign callee"
    );
    assert_eq!(t.self_func(), SelfFunc::Pinned(3905));
    assert_eq!(
        t.func_pin(0).expect("self").1,
        "level::Level::is_zero",
        "canonical 0 is the body"
    );
    assert_eq!(
        t.func_pin(1).expect("callee").1,
        "<level::LevelArc as std::ops::Deref>::deref"
    );
    assert_eq!(t.func_canonical(3894).expect("invertible"), 1);
    assert!(
        t.func_pin(2).is_err(),
        "an index no row pins must refuse, never default"
    );
}

/// A table with no `funcs` lane reads as `Unpinned`, which is the honest state
/// for a body that calls nothing — and `has_cubical_layer` is one.
#[test]
fn an_empty_funcs_lane_is_unpinned_not_zero() {
    let t = tags::parse(super::IR_H2_TAGS).expect("tag table");
    assert!(t.funcs.is_empty(), "has_cubical_layer calls nothing");
    assert_eq!(
        t.self_func(),
        SelfFunc::Unpinned,
        "an absent own id must not be reported as id 0 — 0 is a real crate id somewhere"
    );
}

/// **The minter refuses to mint a call it cannot account for.**
///
/// Stated so it needs no exception for a body that calls nothing: an empty
/// `funcs` lane is consistent only with a module containing no `call`.
#[test]
fn mint_refuses_a_call_the_tag_table_does_not_pin() {
    let core = core::parse(super::IR_LZ_CORE).expect("the lz core module parses");
    let empty = tags::parse(
        r#"{"body":"t","interface":{"linkage":"external","calling_conv":"rustcc","functy":0,"producer":null,"params":[],"block_params":[],"aligns":[],"clauses":[]},"enums":[{"canonical":0,"crate_id":2,"alias":"t"}],"structs":[],"funcs":[]}"#,
    )
    .expect("a table with no funcs lane");
    let e =
        mint(&core, "ir_lz", &empty).expect_err("a calling body with no funcs lane must refuse");
    assert!(
        format!("{e}").contains("one namespace"),
        "the refusal must name the namespace, not something downstream: {e}"
    );

    // …and a lane that pins the namespace gets past this check. Since the
    // 2026-08-22 pool widening the pinned mint SUCCEEDS outright — the
    // divergence-vs-hand story lives in tests/crystal_a2_mint/lz_wall.rs —
    // and both callees land at their pinned canonical indices.
    let pinned = tags::parse(super::IR_LZ_TAGS).expect("the lz table");
    let minted = mint(&core, "ir_lz", &pinned)
        .expect("the pinned lz body mints under the ir_d0..ir_d63 pool")
        .text();
    assert!(
        minted.contains("IRInst.call ir_d0") && minted.contains("IRInst.call ir_d1"),
        "self at 0 and the deref at 1: {minted}"
    );
}

/// Reader B interns the body's own id into the SAME map as its callees, and
/// nothing else can reach the reserved index.
#[test]
fn reader_b_shares_one_namespace_between_the_body_and_its_callees() {
    const LZ: &str = include_str!("../../tests/fixtures/level_is_zero.trust-ir.txt");
    let t = tags::parse(super::IR_LZ_TAGS).expect("tags");
    let (sx, obs) = super::read_emitted_with_self(LZ, t.self_func()).expect("reader B");
    assert_eq!(
        obs.funcs.get(&super::SELF_FUNC_INDEX),
        Some(&3905),
        "the pinned own id takes the reserved index"
    );
    let text = core::print(&sx).expect("print");
    assert!(
        text.contains("(func 0"),
        "the function's own index is the reserved one"
    );
    assert!(
        text.contains("(call 1 (args 9))") && text.contains("(call 0 (args 12))"),
        "the deref is a FOREIGN callee (1) and the recursive call is the body itself (0):\n{text}"
    );

    let (_, unpinned) = super::read_emitted_with_self(LZ, SelfFunc::Unpinned).expect("B");
    assert!(
        !unpinned.funcs.contains_key(&super::SELF_FUNC_INDEX),
        "unpinned, the reserved index stays EMPTY: a callee interned there is the collision"
    );
}
