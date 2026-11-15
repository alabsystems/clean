// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `aggregate-id` blind slot: WHICH crate aggregate a body's `enum.N` /
//! `struct.N` denotes, and the constructed pair that measures nobody comparing
//! it.
//!
//! A sibling of [`super`] rather than a section inside it, for the reason
//! `ir_mint::tests_corpus` is a sibling of `ir_mint::tests`: the parent file
//! crossed the repository's 500-line convention long ago and crossed the
//! `files_over_1000` ratchet the moment this witness landed in it. Splitting is
//! the fix the ratchet is asking for; absorbing the row would have been the
//! lane laundering its own debt.

use clean_verify::ir_mint;

/// **The aggregate id a body names is COMPARED, and the pair is refused.**
///
/// This test measured the opposite for one commit, and the record of that is
/// the point. `Reader::intern` hands out canonical aggregate indices by
/// FIRST-SEEN order within one body, from 0, with no reference to the tag
/// table; the `enums`/`structs` lanes carry a `crate_id`; and until
/// 2026-09-10 `project` related the two NOWHERE — `interface.rs` mentioned
/// neither lane. The lane's crate id is what reaches the committed PROOF
/// artifact all the same, because `Tags::alias_defs` writes
/// `def <alias> : IRTy := IRTy.enum_ ir_d<crate_id>`; this tree's
/// `ir_lzc.defs.txt` line 1 is `def ir_lzc_tlevel : IRTy := IRTy.enum_ ir_d2`.
/// So the NUMERAL in the spec came from the lane and the INDEX in the core came
/// from the body, with nothing checking they were about the same type.
///
/// It was harmless on every chain minted before, and harmless BY CONSTRUCTION
/// rather than by luck: each was assembled from ONE artifact, so first-seen
/// order and the lane's order are the same walk. That argument does not survive
/// a module assembled from TWO artifacts with independent type numbering, which
/// is what the Phase-B five-body module is.
///
/// `interface_aggregates::check_aggregates` closes it in four directions. This
/// test drives all four, and its first case is the pair that used to pass.
#[test]
fn the_aggregate_id_a_body_names_is_compared_and_the_pair_is_now_refused() {
    fn table(crate_id: u32) -> ir_mint::Tags {
        ir_mint::tags::parse(&format!(
            r#"{{"body":"m::f","interface":{{"linkage":"external","calling_conv":"rustcc",
            "functy":0,"producer":null,"params":[{{"block":0,"index":0,"ssa":0,"ty":"ptr"}}],
            "block_params":[],"aligns":["load:None"],"clauses":[]}},
            "enums":[{{"canonical":0,"crate_id":{crate_id},"alias":"t_alias"}}],
            "structs":[],"funcs":[],"globals":[]}}"#
        ))
        .expect("the constructed table must parse")
    }
    fn body(agg: &str) -> String {
        format!(
            "rustcc fn @m::f(functy.0) {{\nbb0(%0: ptr):\n    %1 = load {agg}, ptr %0\n    \
             %2 = extractfield u8 %1, 0\n    ret %2\n}}\n"
        )
    }

    // THE PAIR THAT USED TO PASS. One body names the aggregate the lane pins,
    // the other names a DIFFERENT crate type. Before this lane they projected
    // to ONE core module and both minted `IRTy.enum_ ir_d2`.
    ir_mint::project(&body("enum.2"), &table(2)).expect("the pinned id still projects");
    let e = ir_mint::project(&body("enum.7"), &table(2))
        .map(|_| ())
        .expect_err("an id the lane does not pin must now be REFUSED");
    let msg = format!("{e}");
    // The refusal takes the UNPINNED route rather than the disagreement one,
    // and that is the aggregate NAMESPACE at work rather than a weaker check.
    // Pre-seeded with the lane, reader B no longer lands `enum.7` on canonical
    // 0 at all: `enum.2` owns that index whoever names it, so `enum.7` interns
    // ABOVE the lane and is refused for being a type no row pins. The message
    // names the id and lists what IS pinned, which is what makes a genuine
    // re-interning a one-line re-pin.
    assert!(
        msg.contains("enum.7") && msg.contains("`enum.2`"),
        "the refusal must name the id the body printed and the crate id the lane does pin: {msg}"
    );
    assert!(
        msg.contains("alias_defs"),
        "…and it must say why an unpinned index matters — it is the numeral the proof would \
         carry: {msg}"
    );

    // DIRECTION 1, which the namespace leaves reachable: two bodies that each
    // name a DIFFERENT id the lane does not pin both intern above the lane and
    // collide there.
    let t2 = ir_mint::tags::parse(
        r#"{"body":"m::f","interface":{"linkage":"external","calling_conv":"rustcc","functy":0,
        "producer":null,"params":[{"block":0,"index":0,"ssa":0,"ty":"ptr"}],"block_params":[],
        "aligns":["load:None"],"clauses":[]},
        "enums":[{"canonical":0,"crate_id":2,"alias":"t_a"}],
        "structs":[],
        "funcs":[{"canonical":0,"crate_id":100,"name":"m::f"},
                 {"canonical":1,"crate_id":101,"name":"m::g"}],
        "extra_bodies":[{"canonical":1,"prefix":"ir_probe_g","body":"m::g",
          "interface":{"linkage":"external","calling_conv":"rustcc","functy":0,"producer":null,
          "params":[{"block":0,"index":0,"ssa":0,"ty":"ptr"}],"block_params":[],
          "aligns":["load:None"],"clauses":[]}}],
        "globals":[]}"#,
    )
    .expect("the constructed two-body table must parse");
    let fa = "rustcc fn @m::f(functy.0) {\nbb0(%0: ptr):\n    %1 = load enum.7, ptr %0\n    \
              %2 = extractfield u8 %1, 0\n    ret %2\n}\n";
    let gb = "rustcc fn @m::g(functy.0) {\nbb0(%0: ptr):\n    %1 = load enum.9, ptr %0\n    \
              %2 = extractfield u8 %1, 0\n    ret %2\n}\n";
    let e = ir_mint::project(&format!("{fa}{gb}"), &t2)
        .map(|_| ())
        .expect_err("two bodies interning different unpinned ids at one index must be refused");
    let msg = format!("{e}");
    assert!(
        msg.contains("enum.7") || msg.contains("enum.9"),
        "the refusal must name the ids that collided: {msg}"
    );

    // A PIN OVER NOTHING. The lane pins a type no instruction and no parameter
    // reaches. `ir_hlb` is why this direction reads the UNION of the two:
    // its `structs` pin is named only by the root's parameter type, and a
    // first cut that looked at instructions alone refused that committed
    // chain.
    let bare = "rustcc fn @m::f(functy.0) {\nbb0(%0: ptr):\n    %1 = const bool true\n    \
                ret %1\n}\n";
    let t = ir_mint::tags::parse(
        r#"{"body":"m::f","interface":{"linkage":"external","calling_conv":"rustcc","functy":0,
        "producer":null,"params":[{"block":0,"index":0,"ssa":0,"ty":"ptr"}],"block_params":[],
        "aligns":[],"clauses":[]},
        "enums":[{"canonical":0,"crate_id":2,"alias":"t_alias"}],
        "structs":[],"funcs":[],"globals":[]}"#,
    )
    .expect("the constructed table must parse");
    let e = ir_mint::project(bare, &t)
        .map(|_| ())
        .expect_err("a pin nothing reaches must be refused");
    assert!(
        format!("{e}").contains("pin over nothing"),
        "the refusal must name the slot: {e}"
    );

    // …and the SAME pin is accepted when a PARAMETER type reaches it, which is
    // the `ir_hlb` shape reduced to one body.
    let via_param = "rustcc fn @m::f(functy.0) {\nbb0(%0: enum.2):\n    %1 = const bool true\n \
                     \n    ret %1\n}\n";
    let t2 = ir_mint::tags::parse(
        r#"{"body":"m::f","interface":{"linkage":"external","calling_conv":"rustcc","functy":0,
        "producer":null,"params":[{"block":0,"index":0,"ssa":0,"ty":"enum#0"}],"block_params":[],
        "aligns":[],"clauses":[]},
        "enums":[{"canonical":0,"crate_id":2,"alias":"t_alias"}],
        "structs":[],"funcs":[],"globals":[]}"#,
    )
    .expect("the constructed table must parse");
    ir_mint::project(via_param, &t2)
        .expect("a pin reached only by a PARAMETER type is reached, not orphaned");
}

/// **Two bodies naming DIFFERENT aggregates are now one module, and were not
/// before.**
///
/// This is the capability the aggregate NAMESPACE buys, and it is the reason
/// the namespace exists rather than a side effect. `Reader::intern` assigns
/// canonical indices by first-seen order within ONE body, from 0. So before
/// this lane, a module whose body 0 named `enum.2` and whose body 1 named
/// `enum.5` had BOTH of them claiming canonical 0 — one `(enum 0)` meaning two
/// crate types — and no table could express it. Every committed multi-body
/// chain dodged that by accident: `ir_hlb`'s two bodies name the SAME
/// `struct.29`, and `ir_lzc`'s deref names no aggregate at all.
///
/// The Phase-B five-body module cannot dodge it. Its crate body names
/// `enum.2` (`level::Level`) and its sidecar bodies name `enum.0` and `enum.1`
/// (two `Option` instantiations), so three distinct types would have claimed
/// canonical 0.
///
/// `project` now hands each body the chain's `enums`/`structs` lanes as a
/// namespace — the `funcs` and `globals` pattern one lane over — so an id the
/// lane pins resolves to ITS canonical index whichever body names it, and an
/// id the lane does not pin interns above the lane and is then refused by
/// `check_aggregates` for being unpinned.
#[test]
fn two_bodies_naming_different_aggregates_are_one_module() {
    let t = ir_mint::tags::parse(
        r#"{"body":"m::f","interface":{"linkage":"external","calling_conv":"rustcc","functy":0,
        "producer":null,"params":[{"block":0,"index":0,"ssa":0,"ty":"ptr"}],"block_params":[],
        "aligns":["load:None"],"clauses":[]},
        "enums":[{"canonical":0,"crate_id":2,"alias":"t_a"},
                 {"canonical":1,"crate_id":5,"alias":"t_b"}],
        "structs":[],
        "funcs":[{"canonical":0,"crate_id":100,"name":"m::f"},
                 {"canonical":1,"crate_id":101,"name":"m::g"}],
        "extra_bodies":[{"canonical":1,"prefix":"ir_probe_g","body":"m::g",
          "interface":{"linkage":"external","calling_conv":"rustcc","functy":0,"producer":null,
          "params":[{"block":0,"index":0,"ssa":0,"ty":"ptr"}],"block_params":[],
          "aligns":["load:None"],"clauses":[]}}],
        "globals":[]}"#,
    )
    .expect("the constructed two-body table must parse");
    let f = "rustcc fn @m::f(functy.0) {\nbb0(%0: ptr):\n    %1 = load enum.2, ptr %0\n    \
             %2 = extractfield u8 %1, 0\n    ret %2\n}\n";
    let g = "rustcc fn @m::g(functy.0) {\nbb0(%0: ptr):\n    %1 = load enum.5, ptr %0\n    \
             %2 = extractfield u8 %1, 0\n    ret %2\n}\n";

    let p = ir_mint::project(&format!("{f}{g}"), &t)
        .expect("two bodies naming different aggregates must be ONE module");
    let canonical = ir_mint::print(&p.core).expect("print");
    assert!(
        canonical.contains("(enum 0)") && canonical.contains("(enum 1)"),
        "each body's aggregate resolves to ITS OWN canonical index, not both to 0:\n{canonical}"
    );
    assert_eq!(p.interfaces.len(), 2, "one interface per body");

    // …and the namespace does not weaken the refusal it was added beside: a
    // body naming an id NEITHER row pins still interns above the lane and is
    // still refused.
    let alien = g.replace("enum.5", "enum.77");
    let e = ir_mint::project(&format!("{f}{alien}"), &t)
        .map(|_| ())
        .expect_err("an id no row pins must still be refused");
    assert!(
        format!("{e}").contains("enum.77"),
        "the refusal must name the id: {e}"
    );
}
