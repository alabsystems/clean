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

/// Counts of this intentional fail-closed fragment. Installed-family subset
/// membership and explicit unsupported constructors are checked separately.
#[test]
fn shape_table_covers_the_declared_alphabets() {
    assert_eq!(
        shape::INSTS.len(),
        30,
        "the text-mint fragment has 30 images"
    );
    assert_eq!(
        shape::TYS.len(),
        21,
        "the 18 legacy IRTy constructors plus crystal E5's three fat kinds"
    );
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
    assert_eq!(t.enums[&0], (17, "ir_h2_tmode".to_string()));
    assert_eq!(t.enum_canonical(17).expect("invertible"), 0);
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
        vec!["def ir_h2_tmode : IRTy := IRTy.enum_ 17".to_string()]
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

/// The specimen is DERIVED from the bound, one above it: it was a literal `99`
/// chosen when the pool ended at `ir_d63`, and the 2026-09-16 widening to
/// `ir_d130` (`9e1d4df2d`) made `99` a MEMBER, so this refusal pin stopped
/// refusing without anyone moving it. A literal cannot follow the next
/// widening; `MAX_STRUCTURAL_ATOM + 1` does — which also means this pin
/// follows the constant wherever it goes and says nothing about its VALUE.
/// [`max_structural_atom_is_exactly_the_registered_pool`] pins that.
#[test]
fn mint_refuses_a_numeral_outside_the_atom_pool() {
    let above_pool = mint::MAX_STRUCTURAL_ATOM + 1;
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
                                                    vec![Sx::tag(
                                                        "vals",
                                                        vec![Sx::a(above_pool.to_string())],
                                                    )],
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
    let e = mint(&sx, "ir_x", &tags::Tags::default())
        .expect_err("one above MAX_STRUCTURAL_ATOM is outside the pool");
    assert!(
        matches!(e, super::MintError::Numeral(n) if n == above_pool),
        "expected Numeral({above_pool}), got: {e}"
    );
    assert!(format!("{e}").contains("atom pool"), "unexpected: {e}");
}

/// Crystal E3b: an unwritten aggregate lane (`uninit`, trust-ir `Constant::Uninit`) reads as the
/// core constant `(undef)` -- `IRConst.undef_` -- inside an aggregate, and ONLY there: a whole
/// constant `uninit` has no image, exactly as trust-ir's validator refuses it.
#[test]
fn reader_b_images_an_unwritten_lane_and_only_as_a_lane() {
    let lane = "rustcc fn @x(functy.0) {\nbb0:\n    %1 = const struct.0 { 7, uninit }\n    \
                ret %1\n}\n";
    let text = core::print(&read_emitted(lane).expect("an unwritten lane reads")).expect("print");
    assert!(
        text.contains("(agg (int 7) (undef))"),
        "the lane is `(undef)`:\n{text}"
    );
    let whole = "rustcc fn @x(functy.0) {\nbb0:\n    %1 = const u64 uninit\n    ret %1\n}\n";
    let e = read_emitted(whole).expect_err("a whole `uninit` constant has no image");
    assert!(format!("{e}").contains("uninit"), "unexpected: {e}");
}

/// The pool BOUND against the atoms the specification declares: every
/// `def ir_d<N> : Nat` under `src/` is exactly `ir_d0..=ir_d<MAX_STRUCTURAL_ATOM>`,
/// and `nat` accepts the bound and refuses one above it.
///
/// The two refusal pins derive their specimen from the constant, and the
/// external `crystal_a2_mint_pv`/`_sm` pins forge a literal `131`, so before
/// this a constant moved BELOW the registered pool (a `ir_d130` artifact then
/// refuses to mint) or ABOVE it (a minted `ir_d131` names a constant the spec
/// never declares, found only when registration fails) passed every in-crate
/// pin; only the spec-building pv/sm pins saw the upward move.
#[test]
fn max_structural_atom_is_exactly_the_registered_pool() {
    fn walk(dir: &std::path::Path, out: &mut std::collections::BTreeSet<u128>) {
        for entry in std::fs::read_dir(dir).expect("a source directory") {
            let path = entry.expect("a directory entry").path();
            if path.is_dir() {
                walk(&path, out);
            } else if path.extension().is_some_and(|x| x == "rs") {
                let text = std::fs::read_to_string(&path).expect("a source file");
                for rest in text.split("def ir_d").skip(1) {
                    let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
                    if !digits.is_empty() && rest[digits.len()..].starts_with(" : Nat") {
                        out.insert(digits.parse().expect("a numeral"));
                    }
                }
            }
        }
    }
    let mut declared = std::collections::BTreeSet::new();
    walk(
        &std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src"),
        &mut declared,
    );
    let pool: std::collections::BTreeSet<u128> = (0..=mint::MAX_STRUCTURAL_ATOM).collect();
    assert_eq!(
        declared,
        pool,
        "MAX_STRUCTURAL_ATOM ({}) is not the specification's ir_d atom pool",
        mint::MAX_STRUCTURAL_ATOM
    );
    assert_eq!(
        mint::nat(mint::MAX_STRUCTURAL_ATOM).as_deref(),
        Ok(format!("ir_d{}", mint::MAX_STRUCTURAL_ATOM).as_str())
    );
    assert!(mint::nat(mint::MAX_STRUCTURAL_ATOM + 1).is_err());
}

#[test]
fn reader_b_refuses_an_unknown_instruction() {
    // Actual pinned Rust display spellings for both byte-only atomic types
    // and result-free Release stay outside this text parser's capability.
    for instruction in [
        "%1 = quantum_teleport u8 %0",
        "release %0",
        "%2 = atomicrmw add relaxed u64 ptr %0, %1",
        "%2 = atomicrmw add relaxed usize ptr %0, %1",
    ] {
        let text = format!("rustcc fn @x(functy.0) {{\nbb0:\n    {instruction}\n    ret\n}}\n");
        let error = read_emitted(&text).expect_err("an unsupported printed form must refuse");
        assert!(
            format!("{error}").contains("no Clean image"),
            "unexpected: {error}"
        );
    }
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
    assert_eq!(t.self_func(), SelfFunc::Pinned(1730));
    assert_eq!(t.func_pin(1).expect("callee").0, 1729);
    assert_eq!(
        t.func_pin(1).expect("callee").1,
        "expr::meta::ExprMeta::loose_bvar_range"
    );
    // The sibling's Clean name prefix and its OWN interface — the two facts
    // that would otherwise be hand choices inside the specification.
    assert_eq!(t.body_prefix(1, "ir_hlb"), "ir_lbr");
    assert_eq!(t.body_prefix(0, "ir_hlb"), "ir_hlb");
    let callee = t.body_interface(1).expect("the sibling's interface");
    assert_eq!(callee.functy, 408, "the callee's OWN signature index");
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
    let moved = text.replace("enum.225", "enum.176");
    assert_ne!(moved, text, "the substitution must actually move the id");
    let b = core::print(&read_emitted(&moved).expect("with the enum id moved")).expect("print");
    assert_eq!(
        a, b,
        "the enum re-interning drift class must be absorbed, not erased by table"
    );
    assert!(a.contains("(enum 0)"), "the normalized id is local:\n{a}");
    assert!(
        !a.contains("225") && !a.contains("176"),
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
    assert_eq!(t.self_func(), SelfFunc::Pinned(1961));
    assert_eq!(
        t.func_pin(0).expect("self").1,
        "level::Level::is_zero",
        "canonical 0 is the body"
    );
    assert_eq!(
        t.func_pin(1).expect("callee").1,
        "<level::LevelArc as std::ops::Deref>::deref"
    );
    assert_eq!(t.func_canonical(1947).expect("invertible"), 1);
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
        .expect("the pinned lz body mints under the ir_d0..ir_d130 pool")
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
        Some(&1961),
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

// ────────────────────────────────────────────────────────────────────────────
// The `ir_lzc` table: two bodies, two declarations, one module-table global.
// ────────────────────────────────────────────────────────────────────────────

/// A minimal table head every globals-lane refusal probe below shares — the
/// three required lanes present and empty, so the only thing under test is
/// the `globals` array appended after it.
pub(super) const GLOBALS_PROBE_HEAD: &str = r#"{"body":"t","interface":{"linkage":"external","calling_conv":"rustcc","functy":0,"producer":null,"params":[],"block_params":[],"aligns":[],"clauses":[]},"enums":[],"structs":[],"funcs":[],"globals":"#;

/// The `ir_lzc` tag table pins the whole module: the root and the deref as
/// BODIES, `Option::as_deref` / `Option::expect` as DECLARATIONS in the same
/// function namespace, and the one module-table global by name, resolved type
/// and linkage. Every lane the mint and `project` need is pinned rather than
/// defaulted — and every OTHER committed table, which omits the `globals`
/// lane, parses unchanged with an empty one.
#[test]
fn the_lzc_tag_table_declares_two_bodies_two_declarations_and_one_global() {
    let t = tags::parse(super::IR_LZC_TAGS).expect("the lzc tag table must parse");
    assert_eq!(
        t.body_canonicals(),
        vec![0, 1],
        "the module holds the root and the deref, in module order"
    );
    assert_eq!(t.body_prefix(1, "ir_lzc"), "ir_lad");
    assert_eq!(t.body_prefix(0, "ir_lzc"), "ir_lzc");
    assert_eq!(t.self_func(), SelfFunc::Pinned(1961));
    assert_eq!(
        t.funcs.len(),
        4,
        "self, the deref, and its two callee declarations"
    );
    assert_eq!(t.func_pin(0).expect("self").1, "level::Level::is_zero");
    assert_eq!(
        t.func_pin(1).expect("the deref"),
        &(
            1947,
            "<level::LevelArc as std::ops::Deref>::deref".to_string()
        )
    );
    assert_eq!(
        t.func_pin(2).expect("as_deref declaration").1,
        "std::option::Option::<T>::as_deref"
    );
    assert_eq!(t.func_pin(2).expect("as_deref declaration").0, 4924);
    assert_eq!(
        t.func_pin(3).expect("expect declaration"),
        &(4925, "std::option::Option::<T>::expect".to_string())
    );
    assert_eq!(t.func_canonical(4924).expect("invertible"), 2);
    assert!(
        t.func_pin(4).is_err(),
        "an index no row pins must refuse, never default"
    );
    // The deref's OWN interface: its own signature index, no join, no memory
    // instruction, and no proof clause.
    let deref = t.body_interface(1).expect("the deref's interface");
    assert_eq!(deref.functy, 22, "the deref's OWN signature index");
    assert_ne!(
        deref.functy, t.interface.functy,
        "…and it is not the root's"
    );
    assert_eq!(deref.params.len(), 1, "one receiver");
    assert_eq!(deref.params[0].ty, "ptr");
    assert!(deref.block_params.is_empty() && deref.aligns.is_empty());
    assert!(!deref.clauses.contains("proof"));
    // The root interface is ir_lz's, verbatim.
    let lz = tags::parse(super::IR_LZ_TAGS).expect("the lz table");
    assert_eq!(
        t.interface, lz.interface,
        "the root interface is COPIED from ir_lz"
    );
    assert_eq!(t.enums[&0].0, lz.enums[&0].0, "same crate id for Level…");
    assert_eq!(t.enums[&0].1, "ir_lzc_tlevel", "…under a NEW alias name");
    assert_ne!(
        t.enums[&0].1, lz.enums[&0].1,
        "reusing ir_lz_tlevel would double-register"
    );
    // The global: id and type RESOLVED. The NAME is not the stable half it was
    // once written down as: a promoted global is named `__trust_promoted_<index>`,
    // so the 2026-10-07 rebaseline moved both (4557 -> 1135) together.
    assert_eq!(t.globals.len(), 1);
    let g = t.global_pin(0).expect("the one global");
    assert_eq!(g.crate_id, 1135);
    assert_eq!(g.name, "__trust_promoted_1135");
    assert_eq!(g.ty, "[u8 x 34]");
    assert_eq!(g.linkage, "internal");
    assert_eq!(t.global_canonical(1135).expect("invertible"), 0);
    assert!(
        t.global_pin(1).is_err() && t.global_canonical(4558).is_err(),
        "an unpinned global index or id must refuse, never default"
    );
    // Every existing table omits the lane and parses UNCHANGED, with an empty
    // globals map — which is what keeps their minted scripts byte-identical.
    for (name, table) in [
        ("ir_h2", super::IR_H2_TAGS),
        ("ir_lz", super::IR_LZ_TAGS),
        ("ir_sm", super::IR_SM_TAGS),
        ("ir_hlb", super::IR_HLB_TAGS),
    ] {
        let t = tags::parse(table).unwrap_or_else(|e| panic!("{name}: {e}"));
        assert!(t.globals.is_empty(), "{name} pins no global");
        assert!(
            t.global_pin(0).is_err(),
            "{name}: no lane is not an empty pin"
        );
    }
    // The lane is fail-closed on shape, exactly like `funcs`.
    let row = |canonical: u32, crate_id: u32, name: &str, linkage: &str| {
        format!(
            r#"{{"canonical":{canonical},"crate_id":{crate_id},"name":"{name}","ty":"[u8 x 34]","linkage":"{linkage}"}}"#
        )
    };
    let table = |rows: &[String]| format!("{GLOBALS_PROBE_HEAD}[{}]}}", rows.join(","));
    tags::parse(&table(&[row(0, 4557, "g", "internal")])).expect("a dense, invertible lane parses");
    assert!(
        tags::parse(&table(&[row(1, 4557, "g", "internal")])).is_err(),
        "the globals lane must be DENSE from 0: a hole is a global index no row accounts for"
    );
    assert!(
        tags::parse(&table(&[
            row(0, 7, "a", "internal"),
            row(1, 7, "b", "internal")
        ]))
        .is_err(),
        "two canonical global indices claiming one crate id is not invertible"
    );
    assert!(
        tags::parse(&table(&[
            row(0, 7, "a", "internal"),
            row(0, 8, "b", "internal")
        ]))
        .is_err(),
        "a canonical index listed twice is refused"
    );
    assert!(
        tags::parse(&table(&[
            row(0, 7, "a", "internal"),
            row(1, 8, "a", "internal")
        ]))
        .is_err(),
        "two rows sharing a NAME would make reader B's resolution first-match-wins"
    );
    assert!(
        tags::parse(&table(&[row(0, 7, "a", "static")])).is_err(),
        "a linkage the producer cannot print is a typo, not a pin"
    );
    assert!(
        tags::parse(&format!(
            r#"{GLOBALS_PROBE_HEAD}[{{"canonical":0,"crate_id":7,"name":"a","linkage":"internal"}}]}}"#
        ))
        .is_err(),
        "a row without `ty` pins no type: the `param-type` blind slot one lane over"
    );
    assert!(
        tags::parse(&format!(r#"{GLOBALS_PROBE_HEAD}{{}}}}"#)).is_err(),
        "`globals` must be an array"
    );
}

/// The two DECLARATION rows carry the keys the Phase-B append will join on,
/// spelled exactly as the sidecar manifest's root rows spell them — so that
/// when the sidecar bodies arrive, the join is against a key that was pinned
/// here first and not invented then.
///
/// The keys are DOCUMENTARY today: `tags::parse` ignores them (like
/// `observed_ty`), and this test reads the raw JSON to pin them.
#[test]
fn phase_b_append_keys_match_the_sidecar_manifest_schema() {
    let v: serde_json::Value =
        serde_json::from_str(super::IR_LZC_TAGS).expect("the lzc tag table is JSON");
    let funcs = v["funcs"].as_array().expect("a funcs array");
    assert_eq!(funcs.len(), 4);
    let caller = funcs[1]["name"].as_str().expect("the deref's name");
    assert_eq!(caller, "<level::LevelArc as std::ops::Deref>::deref");
    // Rows 0 and 1 are BODIES of the module: no `defined: false`, no join key.
    for row in &funcs[..2] {
        assert_ne!(
            row.get("defined"),
            Some(&serde_json::Value::Bool(false)),
            "a body row is never marked undefined: {row}"
        );
        assert!(
            row.get("sidecar_join").is_none(),
            "a body row has nothing to join: {row}"
        );
    }
    // Rows 2 and 3 are DECLARATIONS: `defined: false`, a `sidecar_join`
    // whose `caller` is the deref and whose `callee_def_path` is the row's
    // own crate decl path, and the observed functy that — together with the
    // crate id — is what the sidecar body is matched against, because the
    // crate artifact holds more than one `as_deref` declaration (a SECOND at
    // functy.947 on the control dump; three `!trust_bodyless_instance::`
    // spellings of it on the 2026-10-07 rebaseline's dump) and
    // `(caller, callee_def_path)` alone cannot tell them apart.
    for (row, crate_id, functy) in [(&funcs[2], 4924, 986), (&funcs[3], 4925, 955)] {
        let name = row["name"].as_str().expect("name");
        assert_eq!(row["defined"], serde_json::Value::Bool(false), "{name}");
        assert_eq!(row["crate_id"].as_u64(), Some(crate_id), "{name}");
        assert_eq!(row["observed_functy"].as_u64(), Some(functy), "{name}");
        let join = row["sidecar_join"]
            .as_object()
            .unwrap_or_else(|| panic!("{name}: no sidecar_join object"));
        assert_eq!(
            join.len(),
            2,
            "{name}: exactly the manifest's two root-row keys"
        );
        assert_eq!(join["caller"].as_str(), Some(caller), "{name}");
        assert_eq!(join["callee_def_path"].as_str(), Some(name), "{name}");
    }
    // …and the parser sees none of it: the parsed funcs lane is exactly the
    // four (id, name) pairs, documentary keys dropped.
    let t = tags::parse(super::IR_LZC_TAGS).expect("parses");
    let pairs: Vec<(u32, &str)> = t.funcs.values().map(|(id, n)| (*id, n.as_str())).collect();
    assert_eq!(
        pairs,
        vec![
            (1961, "level::Level::is_zero"),
            (1947, caller),
            (4924, "std::option::Option::<T>::as_deref"),
            (4925, "std::option::Option::<T>::expect"),
        ]
    );
}

// ────────────────────────────────────────────────────────────────────────────
// Reader B's `ptr_from_parts` / `fatptr<str>` grammar and the global namespace
// (the `<LevelArc as Deref>::deref` body of the `ir_lzc` chain).
// ────────────────────────────────────────────────────────────────────────────

/// The deref body's shape, verbatim from the control dump but for the ids:
/// a module-table global, its byte length, and the `&str` built from the two.
fn deref_shaped_body(fat_kind: &str) -> String {
    format!(
        "rustcc fn @m::f(functy.0) {{\nbb0(%0: ptr):\n    %1 = global_addr @global.4557\n    \
         %2 = const u64 34\n    %3 = ptr_from_parts fatptr<{fat_kind}> ptr %1, u64 %2\n    ret \
         %3\n}}\n"
    )
}

/// Under a tag-table globals lane, `ptr_from_parts fatptr<str> ptr %d, u64 %m`
/// reads as the specification's `IRInst.ptrfromparts` with `&str` imaged as
/// `(fatptr (uint 8))`, and the `global_addr` resolves through the lane.
#[test]
fn reader_b_reads_ptr_from_parts_over_str() {
    let ns: std::collections::BTreeMap<u32, u32> = [(4557u32, 0u32)].into_iter().collect();
    let (sx, obs) = super::emitted::read_body(
        &deref_shaped_body("str"),
        SelfFunc::Unpinned,
        super::SELF_FUNC_INDEX,
        &std::collections::BTreeMap::new(),
        None,
        &ns,
        (
            &std::collections::BTreeMap::new(),
            &std::collections::BTreeMap::new(),
        ),
    )
    .expect("reader B must read the deref-shaped body under a globals lane");
    let text = core::print(&sx).expect("print");
    assert!(
        text.contains("(ptrfromparts (fatptr (uint 8)) (uint 64) 1 2)"),
        "the core form is `(ptrfromparts <ptr_ty> <metadata_ty> <data> <metadata>)`, reader \
         A's order:\n{text}"
    );
    assert!(
        text.contains("(globaladdr 0)"),
        "the global resolves to its canonical index through the lane:\n{text}"
    );
    assert_eq!(
        obs.globals,
        vec![4557],
        "the raw id this body addressed is reported at its canonical index"
    );

    // An id the lane does not carry interns ABOVE it on first use — and is
    // still reported, so `project` can refuse it against the pins.
    let (sx2, obs2) = super::emitted::read_body(
        &deref_shaped_body("str").replace("@global.4557", "@global.9"),
        SelfFunc::Unpinned,
        super::SELF_FUNC_INDEX,
        &std::collections::BTreeMap::new(),
        None,
        &ns,
        (
            &std::collections::BTreeMap::new(),
            &std::collections::BTreeMap::new(),
        ),
    )
    .expect("an unpinned global interns above the lane");
    assert!(core::print(&sx2).expect("print").contains("(globaladdr 1)"));
    assert_eq!(obs2.globals, vec![9]);

    // `ptr_data` / `ptr_metadata` READ since crystal E5 (decision memo §23), each to the
    // specification's order: `(ptrdata ty p)` and `(ptrmetadata pt mt p)`. Until then they were
    // refused because no chained body printed either; the E5 slices of real m0off bodies do.
    for (inst, image) in [
        ("ptr_data fatptr<str> %3", "(ptrdata (fatptr (uint 8)) 3)"),
        (
            "ptr_metadata fatptr<str> %3 to u64",
            "(ptrmetadata (fatptr (uint 8)) (uint 64) 3)",
        ),
    ] {
        let body = deref_shaped_body("str").replace("ret %3", &format!("%4 = {inst}\n    ret %4"));
        let (sx, _) = super::emitted::read_body(
            &body,
            SelfFunc::Unpinned,
            super::SELF_FUNC_INDEX,
            &std::collections::BTreeMap::new(),
            None,
            &ns,
            (
                &std::collections::BTreeMap::new(),
                &std::collections::BTreeMap::new(),
            ),
        )
        .unwrap_or_else(|e| panic!("{inst} reads since crystal E5: {e}"));
        let printed = core::print(&sx).expect("print");
        assert!(
            printed.contains(image),
            "{inst}: expected `{image}` in\n{printed}"
        );
    }
}

/// `str` and, since crystal E5 (decision memo §23), `container_len`, `container_vtable` and
/// `dyn.N` have images, each its OWN spelling. `slice ty.N` (printed WITH a space, which is why the
/// type token is split at bracket depth and not at the first space) is refused by a message that
/// names the kind, not by a syntax error further along the line.
#[test]
fn reader_b_refuses_fat_pointer_kinds_outside_the_fragment() {
    let ns: std::collections::BTreeMap<u32, u32> = [(4557u32, 0u32)].into_iter().collect();
    let read = |kind: &str| {
        super::emitted::read_body(
            &deref_shaped_body(kind),
            SelfFunc::Unpinned,
            super::SELF_FUNC_INDEX,
            &std::collections::BTreeMap::new(),
            None,
            &ns,
            (
                &std::collections::BTreeMap::new(),
                &std::collections::BTreeMap::new(),
            ),
        )
    };
    let e = read("slice ty.0")
        .map(|_| ())
        .expect_err("a slice fat pointer must refuse");
    let msg = format!("{e}");
    assert!(
        msg.contains("fat pointer kind `slice ty.0`") && msg.contains("REFUSED in both readers"),
        "`fatptr<slice ty.0>`: the refusal must name the kind: {msg}"
    );
    assert!(
        !msg.contains("ptr_from_parts needs"),
        "`fatptr<slice ty.0>`: refused as a syntax error, not as the kind: {msg}"
    );
    for (kind, image) in [
        ("dyn.3", "(fatdyn 3)"),
        ("container_len", "(containerlen)"),
        ("container_vtable", "(containervtable)"),
    ] {
        let (sx, _) = read(kind).unwrap_or_else(|e| panic!("fatptr<{kind}> reads since E5: {e}"));
        let printed = core::print(&sx).expect("print");
        assert!(
            printed.contains(&format!("(ptrfromparts {image} (uint 64) 1 2)")),
            "fatptr<{kind}>: expected {image} in\n{printed}"
        );
    }
    // …and the same arm serves every type position, not only `ptr_from_parts`.
    let e = read_emitted(
        "rustcc fn @x(functy.0) {\nbb0:\n    %1 = undef fatptr<slice ty.3>\n    ret %1\n}\n",
    )
    .expect_err("undef of a slice fat pointer must refuse");
    assert!(
        format!("{e}").contains("fat pointer kind `slice ty.3`"),
        "{e}"
    );
}

/// A BARE read — no tag table, no globals lane — still refuses a
/// `global_addr`: the per-body module prints an empty `(globals)` list, so a
/// canonical index into it would name an entry the module does not declare.
/// The message names the global, the empty list, and where to read instead.
#[test]
fn a_bare_read_still_refuses_a_global_addr() {
    let e = read_emitted(&deref_shaped_body("str"))
        .map(|_| ())
        .expect_err("a bare read must refuse a global_addr");
    let msg = format!("{e}");
    assert!(
        msg.contains("global.4557") && msg.contains("empty"),
        "the refusal names the global and the empty list: {msg}"
    );
    assert!(
        msg.contains("globals lane"),
        "the refusal says where the instruction CAN be read: {msg}"
    );
    // Every bare entry point is bare in the same way.
    let (_, tags) = super::read_emitted_with_self(
        &deref_shaped_body("str").replace("global_addr @global.4557", "const bool true"),
        SelfFunc::Unpinned,
    )
    .expect("the same body without the global reads bare");
    assert!(tags.globals.is_empty(), "a bare read reports no global");
    assert!(
        super::emitted::read_with_pins(&deref_shaped_body("str"), SelfFunc::Unpinned, Some(64))
            .is_err(),
        "read_with_pins is a bare entry point too"
    );
}

#[test]
fn supported_instruction_subset_matches_actual_headers_and_omissions_fail_closed() {
    use super::shape::Arg;
    use clean_kernel::{BinderInfo, Expr, Name};
    crate::test_utils::run_with_stack(|| {
        let mut spec = crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack()
            .expect("actual checked public canonical syntax owner");
        let family = spec
            .env()
            .get_inductive(&Name::from_string("IRInst"))
            .unwrap();
        assert_eq!(family.constructor_names.len(), 33);
        let supported: Vec<_> = shape::INSTS
            .iter()
            .map(|s| Name::from_string(s.clean))
            .collect();
        let omitted: Vec<_> = family
            .constructor_names
            .iter()
            .filter(|name| !supported.contains(name))
            .map(ToString::to_string)
            .collect();
        assert_eq!(
            omitted,
            [
                "IRInst.atomic_fetch_add_relaxed_u64_seq",
                "IRInst.atomic_fetch_add_relaxed_usize_seq",
                "IRInst.release"
            ]
        );
        for shape in shape::INSTS {
            let fields: Vec<Expr> = shape
                .args
                .iter()
                .map(|arg| match arg {
                    Arg::Ty => Expr::const_str("IRTy"),
                    Arg::Val | Arg::Blk | Arg::Nat | Arg::Data => Expr::const_str("Nat"),
                    Arg::Flag => Expr::const_str("Bool"),
                    Arg::Vals(_) => Expr::app(Expr::const_str("IRList"), Expr::const_str("Nat")),
                    Arg::Cases => {
                        Expr::app(Expr::const_str("IRList"), Expr::const_str("IRSwitchCase"))
                    }
                    Arg::Const => Expr::const_str("IRConst"),
                    Arg::OptVal => Expr::app(Expr::const_str("IROption"), Expr::const_str("Nat")),
                    Arg::Op(alpha) => Expr::const_str(match *alpha {
                        "binop" => "IRBinOp",
                        "unop" => "IRUnOp",
                        "overflow" => "IROverflowOp",
                        "icmp" => "IRICmpOp",
                        "fcmp" => "IRFCmpOp",
                        "cast" => "IRCastOp",
                        other => panic!("unknown fixed operator alphabet {other}"),
                    }),
                })
                .collect();
            let expected = fields
                .into_iter()
                .rev()
                .fold(Expr::const_str("IRInst"), |rest, field| {
                    Expr::pi(BinderInfo::Default, field, rest)
                });
            let ctor = spec
                .env()
                .get_constructor(&Name::from_string(shape.clean))
                .unwrap();
            assert_eq!(
                ctor.type_, expected,
                "{}: subset telescope drift",
                shape.clean
            );
        }
        let tags = tags::Tags::default();
        for (suffix, args) in [
            ("atomic_fetch_add_relaxed_u64_seq", "0 1"),
            ("atomic_fetch_add_relaxed_usize_seq", "64 0 1"),
            ("release", "0"),
        ] {
            let core = core::parse(&format!("(module (funcs (func 0 (params) (entry 0) (blocks (block 0 (params) (nodes (node (results) ({suffix} {args}))))))) (globals))")).unwrap();
            let error =
                mint(&core, "unsupported", &tags).expect_err("unsupported mnemonic must not mint");
            assert!(
                format!("{error}").contains("instruction mnemonic"),
                "{error}"
            );
            let name = format!("unsupported_{suffix}");
            spec.add_recursive_def(&format!("def {name} : IRModule := IRModule.mk (@IRList.cons IRFunc (IRFunc.mk 0 (@IRList.nil Nat) 0 (@IRList.cons IRBlock (IRBlock.mk 0 (@IRList.nil Nat) (@IRList.cons IRNode (IRNode.mk (IRInst.{suffix} {args}) (@IRList.nil Nat)) (@IRList.nil IRNode))) (@IRList.nil IRBlock))) (@IRList.nil IRFunc)) (@IRList.nil IRGlobal)"), "Unsupported text-mint data only").unwrap();
            let error = super::decode::decode(spec.env(), &name, &tags)
                .expect_err("unsupported canonical constructor must not decode");
            assert!(
                format!("{error}").contains("declared IRInst constructors"),
                "{error}"
            );
        }
    });
}
