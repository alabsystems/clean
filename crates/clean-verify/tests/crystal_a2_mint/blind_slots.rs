// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **M9 — the blind-slot list: every erasure named in ONE place, and anchored
//! so it cannot rot.**
//!
//! `data/crystal_mint_blind_slots.json` is the complete list of fields the
//! emitted artifact carries that the committed core module does not. Every row
//! is a pair of artifacts this gate cannot tell apart.
//!
//! That list is not a confession, it is a claim boundary — Clean's `IRModule`
//! genuinely does not encode most of what trust-ir prints. The reason it has to
//! be WRITTEN is the 2026-08-20 callee-namespace collision: that was an erasure
//! nobody had written down, in a slot two writers each assumed the other owned,
//! and it survived every check the gate had. A finite set on one page is what
//! stops the next one being found by counterexample.
//!
//! **2026-08-20: eight of the eleven rows stopped being erasures**, four in the
//! second pass and four in the third, and the list itself grew by two rows that
//! were found while hunting for a counterexample. The anchoring
//! below is what forced this file to be rewritten rather than left to rot —
//! closing `param-type`, `function-name`, `global-index` and `spans-and-tags`
//! broke the four anchors that claimed them, and the lane went red until the
//! rows were restated. Every witness in this file has been INVERTED with the
//! closure: a test that asserted "these two bodies are one core module" now
//! asserts "the gate REFUSES the second", and the assertion it used to make is
//! kept beside it, stated at the strength it still holds. That pairing is the
//! acceptance test for the closure and the honest boundary of it in one place:
//! the core module still cannot separate the pair, and the gate no longer
//! accepts it.
//!
//! Two mechanisms keep the file honest, and neither is a promise:
//!
//! * **Anchoring.** Every row names source sites with VERBATIM text. Removing
//!   an erasure breaks the row that claims it, so the file must be updated
//!   rather than quietly outlived.
//! * **Constructed witnesses.** The rows that can be demonstrated are: two
//!   emitted bodies that differ ONLY in the named slot are built here. For a
//!   row still marked `erased` the pair is asserted to project to ONE core
//!   module; for a row marked `compared` or `refused` the pair is asserted to
//!   be REJECTED by `ir_mint::project`, the gate's acceptance predicate. A row
//!   with a `witness` names the test below that does it.
//!
//! What this lane does NOT do, stated so it is not read in: it cannot prove the
//! list is COMPLETE. Nothing here enumerates the fields of `trust_ir::Inst` and
//! diffs them against the fragment. Completeness rests on the shape table being
//! total-or-refusing — an unrecognised construct is a hard error in both
//! readers, so a field can only be erased by a line someone wrote to erase it,
//! and those lines are what the anchors point at.

use std::path::PathBuf;

use clean_verify::ir_mint::{self, InterfaceError, SelfFunc, Tags};

use super::canon;

const BLIND_SLOTS: &str = include_str!("../../../../data/crystal_mint_blind_slots.json");

fn repo_root() -> PathBuf {
    // crates/clean-verify -> the workspace root.
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("the workspace root must resolve")
}

fn slots() -> Vec<serde_json::Value> {
    let v: serde_json::Value =
        serde_json::from_str(BLIND_SLOTS).expect("the blind-slot list must be valid JSON");
    v["slots"]
        .as_array()
        .expect("`slots` must be an array")
        .clone()
}

// ────────────────────────────────────────────────────────────────────────────
// The list is well formed, and every claim in it points at live source.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m9_every_blind_slot_is_anchored_in_live_source() {
    let root = repo_root();
    let rows = slots();
    assert!(
        rows.len() >= 9,
        "the list shrank to {} rows. A slot is removed from this file only when the erasure is \
         CLOSED — and closing one changes the core form, so the core digests move with it.",
        rows.len()
    );

    let mut anchors_checked = 0usize;
    for row in &rows {
        let id = row["id"].as_str().expect("every row has an `id`");
        for key in [
            "kind",
            "slot",
            "artifact_carries",
            "core_carries",
            "consequence",
            "read_by",
        ] {
            let s = row[key].as_str().unwrap_or_default();
            assert!(
                !s.trim().is_empty(),
                "row `{id}` has no `{key}`; a slot with no stated consequence is a note, not a \
                 claim boundary"
            );
        }
        assert!(
            matches!(
                row["kind"].as_str(),
                Some("erased" | "unwitnessed" | "compared" | "refused")
            ),
            "row `{id}`: `kind` must be one of erased / unwitnessed / compared / refused, found \
             {:?}",
            row["kind"]
        );
        // A row that stays an ERASURE owes a justification that is not a
        // comment: the standard is `ir_ty_is_agg_enum_any`, a kernel-checked
        // theorem that the semantics cannot consult the field, or a measured
        // fact. `compared` and `refused` rows owe a lane instead, and
        // `read_by` already carries it.
        if row["kind"] == "erased" {
            let j = row["justification"].as_str().unwrap_or_default();
            assert!(
                !j.trim().is_empty(),
                "row `{id}` is still an ERASURE and carries no `justification`. An erasure \
                 justified by prose is the failure mode this whole file exists to stop; the \
                 standard is a kernel-checked theorem or a measured fact."
            );
        }

        let anchors = row["anchors"].as_array().expect("every row has `anchors`");
        assert!(!anchors.is_empty(), "row `{id}` has no anchor");
        for a in anchors {
            let file = a["file"].as_str().expect("anchor `file`");
            let text = a["text"].as_str().expect("anchor `text`");
            let path = root.join(file);
            let src = std::fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("row `{id}`: anchor file {file} is unreadable: {e}"));
            assert!(
                src.contains(text),
                "row `{id}`: the anchor\n    {text}\nis no longer in {file}. Either the erasure \
                 moved — re-anchor the row — or it was CLOSED, in which case delete the row and \
                 the core digests it stood behind have moved too."
            );
            anchors_checked += 1;
        }
    }
    assert!(
        anchors_checked >= 14,
        "only {anchors_checked} anchors checked; the list is thinner than it reads"
    );

    let mut ids: Vec<&str> = rows.iter().filter_map(|r| r["id"].as_str()).collect();
    ids.sort_unstable();
    let n = ids.len();
    ids.dedup();
    assert_eq!(ids.len(), n, "duplicate slot id in the blind-slot list");
}

/// Every row that claims a constructed witness must name a test that exists in
/// this module. A `witness` pointing at nothing is the same failure mode as a
/// `cost_is_uniform` that is only ever printed.
#[test]
fn m9_every_claimed_witness_names_a_test_in_this_file() {
    let root = repo_root().join("crates/clean-verify/tests/crystal_a2_mint");
    let this = ["blind_slots.rs", "blind_slots_annotations.rs"]
        .map(|file| {
            std::fs::read_to_string(root.join(file)).expect("witness source must be readable")
        })
        .join("\n");
    let mut found = 0usize;
    for row in slots() {
        let Some(w) = row["witness"].as_str() else {
            continue;
        };
        assert!(
            this.contains(&format!("fn {w}(")),
            "row `{}` claims the witness `{w}`, which is not a test in the blind_slots module",
            row["id"]
        );
        found += 1;
    }
    assert!(
        found >= 5,
        "only {found} rows carry a constructed witness. A row that CAN be demonstrated and is not \
         is the weaker half of this file: prose about an erasure nobody built the pair for."
    );
}

// ────────────────────────────────────────────────────────────────────────────
// The constructed witnesses.
//
// Each one is a PAIR of emitted bodies that denote different programs. Before
// 2026-08-20 every test here asserted the pair was one core module. Four of
// them now assert the pair is REFUSED, and keep the old assertion beside the
// new one at the strength it still holds — because "the module cannot separate
// them" and "the gate accepts both" stopped being the same sentence, and the
// difference is the whole content of this change.
// ────────────────────────────────────────────────────────────────────────────

/// The tag table a constructed witness is read under.
///
/// Written out rather than generated so the pin a witness is refused against is
/// visible in the test that uses it.
fn witness_tags(body: &str, params: &str, aligns: &str, clauses: &str) -> Tags {
    let json = format!(
        r#"{{"body":"{body}",
            "interface":{{"linkage":"external","calling_conv":"rustcc","functy":0,
                          "producer":null,"params":[{params}],"block_params":[],
                          "aligns":[{aligns}],"clauses":[{clauses}]}},
            "enums":[{{"canonical":0,"crate_id":13,"alias":"t"}}],
            "structs":[],"funcs":[]}}"#
    );
    ir_mint::tags::parse(&json).expect("the witness tag table must parse")
}

/// The pin the `param-type` and `function-name` witnesses are read under:
/// `m::f`, one `ptr` receiver, one unaligned load, no annotations.
fn mf_tags() -> Tags {
    witness_tags(
        "m::f",
        r#"{"block":0,"index":0,"ssa":0,"ty":"ptr"}"#,
        r#""load:None""#,
        "",
    )
}

/// Minimal well-formed emitted bodies differing only in the parameter TYPE.
const PARAM_PTR: &str = r"rustcc fn @m::f(functy.0) {
bb0(%0: ptr):
    %1 = load enum.13, ptr %0
    ret %1
}
";
const PARAM_RC: &str = r"rustcc fn @m::f(functy.0) {
bb0(%0: enum.175):
    %1 = load enum.13, ptr %0
    ret %1
}
";
/// The sharpest form of the pair, and the one the row is written about: the
/// SAME aggregate, reached through a different indirection. `&CleanMode` and
/// `Rc<CleanMode>` — where the entry `load` reads the discriminant in one and
/// the refcount header in the other.
const PARAM_RC_SAME_ENUM: &str = r"rustcc fn @m::f(functy.0) {
bb0(%0: Rc<enum.13>):
    %1 = load enum.13, ptr %0
    ret %1
}
";

/// **`param-type`, CLOSED as a comparison.** `&CleanMode` and `Rc<CleanMode>`
/// are still one core module — and are no longer one accepted artifact.
///
/// The two halves are asserted together on purpose. The first is the boundary
/// (the fragment gained nothing, no digest moved); the second is the closure
/// (the gate's acceptance predicate is no longer the module alone).
#[test]
fn param_types_are_compared_and_the_pair_is_now_refused() {
    let t = mf_tags();
    assert_ne!(PARAM_PTR, PARAM_RC, "the two texts must actually differ");

    // (1) THE BOUNDARY, unchanged. This is the exact assertion this test made
    // before 2026-08-20, kept because it is still true and is the reason the
    // closure had to happen in the tag table rather than in the module.
    let a = ir_mint::read_emitted(PARAM_PTR).expect("a reads");
    let b = ir_mint::read_emitted(PARAM_RC).expect("b reads");
    let c = ir_mint::read_emitted(PARAM_RC_SAME_ENUM).expect("c reads");
    assert_eq!(
        canon(&a),
        canon(&b),
        "the CORE MODULE still cannot separate the pair, and cannot until Clean's `IRFunc` \
         carries a type. If these now differ, every committed core digest moved with it."
    );
    assert_eq!(
        canon(&a),
        canon(&c),
        "…and neither can it separate `Rc<enum.13>`"
    );

    // (2) THE CLOSURE. The pair is no longer ACCEPTED.
    ir_mint::project(PARAM_PTR, &t).expect("the pinned body must still be accepted");
    for (label, body, expect) in [
        ("an enum receiver", PARAM_RC, "enum#?"),
        ("an Rc receiver", PARAM_RC_SAME_ENUM, "Rc<enum#0>"),
    ] {
        let e = ir_mint::project(body, &t).map(|_| ()).expect_err(&format!(
            "the gate ACCEPTED {label}: the pair is still indistinguishable and this row is not \
             closed"
        ));
        let msg = format!("{e}");
        assert!(
            msg.contains(expect) && msg.contains("ptr"),
            "the refusal must print BOTH the pinned type and the one the artifact carries \
             ({expect}): {msg}"
        );
    }

    // The 2026-08-19 `load_tys` correction, still standing: the LOAD's type is
    // carried by the core form itself.
    let d = ir_mint::read_emitted(&PARAM_PTR.replace("load enum.13", "load u32")).expect("d reads");
    assert_ne!(
        canon(&a),
        canon(&d),
        "the load type is carried by the core form and must discriminate; if it does not, the \
         2026-08-19 `load_tys` correction has been undone"
    );

    // And the M7 split, still standing on the other side: an aggregate's CRATE
    // id is not in the module's identity, it is pinned by the tag table.
    let e =
        ir_mint::read_emitted(&PARAM_PTR.replace("load enum.13", "load enum.99")).expect("e reads");
    assert_eq!(
        canon(&a),
        canon(&e),
        "an aggregate's crate id must NOT be in the module's identity; it is pinned by the tag \
         table (M7) precisely so a re-interning is a re-pin and not a different program"
    );
}

/// **`function-name`, CLOSED as a comparison.** Two different shipped functions
/// with the same body are still one core module, and are no longer one accepted
/// artifact.
#[test]
fn the_function_name_is_compared_and_the_pair_is_now_refused() {
    let other = PARAM_PTR.replace("@m::f(", "@completely::different::g(");
    assert_ne!(other, PARAM_PTR);

    // (1) THE BOUNDARY, unchanged: the module carries no name, which is what
    // keeps the digest producer-invariant across a rename.
    let a = ir_mint::read_emitted(PARAM_PTR).expect("a");
    let b = ir_mint::read_emitted(&other).expect("b");
    assert_eq!(
        canon(&a),
        canon(&b),
        "the core module must not carry the name"
    );
    assert!(
        !canon(&a).contains("m::f"),
        "no name may leak into the printed core module:\n{}",
        canon(&a)
    );

    // (2) THE CLOSURE.
    let t = mf_tags();
    ir_mint::project(PARAM_PTR, &t).expect("the pinned body must still be accepted");
    let e = ir_mint::project(&other, &t)
        .map(|_| ())
        .expect_err("a body whose header names a DIFFERENT function must be refused");
    assert!(
        matches!(e, InterfaceError::FunctionName { .. }),
        "the refusal must be the name one: {e}"
    );
    assert!(
        format!("{e}").contains("completely::different::g"),
        "…and must print the name the artifact carries: {e}"
    );
}

/// **`callee-name`, CLOSED at the acceptance.** Two different FOREIGN callees
/// are still one core module; a body calling a callee the table does not pin,
/// or pins as a different crate id, is refused.
///
/// The self-call half — the one that was BROKEN until 2026-08-20 — is covered
/// by `callee_identity::the_swap_counterexample_is_closed` and is asserted
/// again here so both halves are readable in one place.
#[test]
fn foreign_callee_identity_is_now_pinned_and_a_swap_is_refused() {
    let body = |callee: &str| {
        format!(
            "rustcc fn @m::f(functy.0) {{\nbb0(%0: ptr):\n    \
             %1 = call @func.{callee}(%0)\n    ret %1\n}}\n"
        )
    };
    let pin = SelfFunc::Pinned(7);

    // (1) THE BOUNDARY, unchanged: the MODULE numbers callees by first use, so
    // two different foreign callees project identically.
    let a = ir_mint::read_emitted_with_self(&body("100"), pin)
        .expect("a")
        .0;
    let b = ir_mint::read_emitted_with_self(&body("200"), pin)
        .expect("b")
        .0;
    assert_eq!(
        canon(&a),
        canon(&b),
        "two DIFFERENT foreign callees project identically — that is the `callee-name` row. It is \
         invisible to the semantics only because a one-function module refuses every foreign \
         callee alike; widening the module makes this a defect."
    );
    let me = ir_mint::read_emitted_with_self(&body("7"), pin)
        .expect("self")
        .0;
    assert_ne!(
        canon(&a),
        canon(&me),
        "a call to the body ITSELF must not project like a call to a stranger"
    );
    assert!(
        canon(&me).contains("(call 0 (args 0))"),
        "the self-call resolves to the function's own index:\n{}",
        canon(&me)
    );

    // (2) THE CLOSURE: the table pins WHICH crate id each canonical index is,
    // and a body naming a different one is refused rather than renumbered.
    let json = r#"{"body":"m::f",
        "interface":{"linkage":"external","calling_conv":"rustcc","functy":0,"producer":null,
                     "params":[{"block":0,"index":0,"ssa":0,"ty":"ptr"}],
                     "block_params":[],"aligns":[],"clauses":[]},
        "enums":[],"structs":[],
        "funcs":[{"canonical":0,"crate_id":7,"name":"m::f"},
                 {"canonical":1,"crate_id":100,"name":"m::callee"}]}"#;
    let t = ir_mint::tags::parse(json).expect("the witness table must parse");
    ir_mint::project(&body("100"), &t).expect("the pinned callee must be accepted");
    let e = ir_mint::project(&body("200"), &t)
        .map(|_| ())
        .expect_err("a call to a DIFFERENT foreign function must be refused");
    assert!(
        format!("{e}").contains("@func.200") && format!("{e}").contains("m::callee"),
        "the refusal must name the pinned callee and the one the artifact reached: {e}"
    );
}

/// **`global-index`, CLOSED by refusal.** The row claimed the slot was latent
/// on all eleven chained bodies. It still is — measured, not believed — and a
/// body that does address a global is now refused instead of read into a module
/// whose global list is empty.
#[test]
fn the_global_slot_is_now_a_refusal_on_every_chained_fixture() {
    let root = repo_root().join("crates/clean-verify/tests/fixtures");
    let mut checked = 0usize;
    for chain in [
        "has_cubical_layer",
        "expr_path_step_clone",
        "level_is_zero",
        "from_source_system",
        "level_kind_ord",
        "bvar_in_range",
        "flat_flags_contains",
        "float_div",
        "get_char_val_trunc",
        "is_valid_char",
        "meta_tag_shl",
    ] {
        let text = std::fs::read_to_string(root.join(format!("{chain}.trust-ir.txt")))
            .unwrap_or_else(|e| panic!("{chain}: {e}"));
        let (_, observed) =
            ir_mint::read_emitted_with_self(&text, SelfFunc::Unpinned).expect("reader B");
        assert!(
            observed.globals.is_empty(),
            "{chain} names {} global(s)",
            observed.globals.len()
        );
        checked += 1;
    }
    assert_eq!(checked, 11, "all eleven chained bodies");

    // NON-VACUITY, and the closure in one step: the reader really does reach a
    // `global_addr` — and now REFUSES it, instead of interning it into a module
    // whose `(globals)` list is hard-coded empty. Before 2026-08-20 this read
    // cleanly and produced `(globaladdr 0)` inside `(globals)`, a canonical
    // index denoting an entry the module does not declare.
    //
    // Constructed rather than taken from `level_is_zero_deref_callee`, which
    // does address a global but is refused as a whole for a DIFFERENT reason
    // (it uses `ptr_from_parts`, outside the fragment) — and a refusal for the
    // wrong reason is not a measurement.
    const WITH_GLOBAL: &str = r"rustcc fn @m::f(functy.0) {
bb0(%0: ptr):
    %1 = global_addr @global.4527
    ret %1
}
";
    let e = ir_mint::read_emitted_with_self(WITH_GLOBAL, SelfFunc::Unpinned)
        .map(|_| ())
        .expect_err("a body addressing a global must now be REFUSED");
    let msg = format!("{e}");
    assert!(
        msg.contains("global.4527") && msg.contains("empty"),
        "the refusal must name the global and the empty list that makes it incoherent: {msg}"
    );

    // …and the refusal is about the GLOBAL, not about the body: the same body
    // without it reads.
    ir_mint::read_emitted_with_self(
        &WITH_GLOBAL.replace("global_addr @global.4527", "const bool true"),
        SelfFunc::Unpinned,
    )
    .expect("the same body without the global must still read");
}

// ────────────────────────────────────────────────────────────────────────────
// The counterexamples the 2026-08-20 close was ANSWERING.
//
// Each of these is a pair of emitted bodies that denote different programs and
// that `ir_mint::project` ACCEPTED AS ONE before this lane. They are kept as
// tests, not as prose, because a witness is the only thing that turns "we
// should compare this" into a runnable acceptance test — and because a witness
// that stops being constructible is how a closure quietly rots.
// ────────────────────────────────────────────────────────────────────────────

/// The header of a one-block body, with the three header slots parameterised.
fn header_body(prefix: &str, functy: u32) -> String {
    format!("{prefix}fn @m::f(functy.{functy}) {{\nbb0(%0: ptr):\n    unreachable\n}}\n")
}

fn header_tags(functy: u32, linkage: &str, conv: &str) -> Tags {
    ir_mint::tags::parse(&format!(
        r#"{{"body":"m::f","interface":{{"linkage":"{linkage}","calling_conv":"{conv}",
            "functy":{functy},"producer":null,
            "params":[{{"block":0,"index":0,"ssa":0,"ty":"ptr"}}],
            "block_params":[],"aligns":[],"clauses":[]}},
            "enums":[],"structs":[],"funcs":[]}}"#
    ))
    .expect("the witness tag table must parse")
}

/// **The `functy` witness: a variadic function and a non-variadic one.**
///
/// `trust_ir::FuncTy` is `{ params, returns, is_vararg }` (`trust-ir/src/ty.rs`).
/// A printed body shows its parameter types in the entry block header — which
/// this lane already pins — and shows its return types only through a `ret` an
/// execution can reach. It shows `is_vararg` NOWHERE, at all, ever.
///
/// So these two texts, byte-identical but for one numeral, are a `fn(ptr, ...)`
/// and a `fn(ptr)`. On AArch64 Apple and on x86-64 SysV those are different
/// ABIs, and calling one through the other's signature is undefined. Both
/// projected to the same core module AND the same interface until the header's
/// signature index was pinned.
#[test]
fn functy_is_compared_and_the_vararg_pair_is_now_refused() {
    let non_variadic = header_body("rustcc ", 7);
    let variadic = header_body("rustcc ", 8);
    assert_ne!(non_variadic, variadic, "the pair must differ in the text");

    // THE COUNTEREXAMPLE, still true and now measured: the CORE MODULE cannot
    // separate them, and never will — `IRFunc` has no type field.
    assert_eq!(
        ir_mint::print(&ir_mint::read_emitted(&non_variadic).expect("read")).expect("print"),
        ir_mint::print(&ir_mint::read_emitted(&variadic).expect("read")).expect("print"),
        "if these ever differ, the fragment gained a signature slot and every core digest moved"
    );

    // THE CLOSURE: the gate no longer accepts both.
    let t = header_tags(7, "external", "rustcc");
    ir_mint::project(&non_variadic, &t).expect("the pinned signature must be accepted");
    let e = ir_mint::project(&variadic, &t)
        .map(|_| ())
        .expect_err("a body whose header names a DIFFERENT signature must be refused");
    assert!(
        format!("{e}").contains("functy.8"),
        "the refusal must name the signature it found: {e}"
    );
}

/// **The calling-convention and linkage witness — and the false premise it
/// corrects.**
///
/// `data/crystal_mint_blind_slots.json` carried this row for months as
/// `unwitnessed`, on the stated ground that *"the producer prints neither, so
/// no text reader CAN witness them"*. That was not true.
/// `trust_ir::display::Display for Function` prints both, suppressing each only
/// when it holds its default — the `rustcc` at the head of every committed
/// fixture IS the calling convention — and `trust_ir::parser` reads both back.
///
/// The old reader did refuse `ccc fn @m::f`, but by matching the literal prefix
/// `"rustcc fn @"`, so it could not say WHAT it had refused, and a chain on an
/// `internal`-linkage body would have been unblocked by widening the prefix.
#[test]
fn the_calling_convention_and_linkage_are_read_from_the_header_not_assumed() {
    let t = header_tags(7, "external", "rustcc");
    let p = ir_mint::project(&header_body("rustcc ", 7), &t).expect("the control must be accepted");
    assert_eq!(p.interface.calling_conv, "rustcc");
    assert_eq!(
        p.interface.linkage, "external",
        "an ABSENT linkage keyword is `external`, which is a VALUE and not an unknown: the \
         producer suppresses the default and its parser restores it"
    );

    // A different ABI, same body. Refused, and refused BY NAME.
    for (prefix, expect) in [
        ("ccc ", "calling convention"),
        ("fastcc ", "fastcc"),
        ("internal rustcc ", "linkage"),
        ("private rustcc ", "private"),
    ] {
        let e = ir_mint::project(&header_body(prefix, 7), &t)
            .map(|_| ())
            .expect_err(&format!("`{prefix}` must be refused"));
        assert!(
            format!("{e}").contains(expect),
            "`{prefix}` was refused for the wrong reason — expected `{expect}`: {e}"
        );
    }

    // …and the default-shaped header, which prints NEITHER keyword, is read as
    // `external`/`ccc` rather than as the pin. This is the row that would go
    // silently wrong if absence were modelled as "unknown".
    let plain = header_tags(7, "external", "ccc");
    let p = ir_mint::project(&header_body("", 7), &plain)
        .expect("a header with no keyword at all must read as the two suppressed defaults");
    assert_eq!(
        (
            p.interface.linkage.as_str(),
            p.interface.calling_conv.as_str()
        ),
        ("external", "ccc")
    );
    ir_mint::project(&header_body("", 7), &t)
        .map(|_| ())
        .expect_err("…and must NOT satisfy a pin that says `rustcc`");
}

/// **The one annotation-clause kind whose CONTENT is compared, and the
/// measurement that says why the other four are not.**
#[test]
fn the_producer_clause_content_is_compared_and_the_other_four_are_measured_inert() {
    let t = super::tags();
    // (1) `#producer` names WHICH COMPILER emitted this body — the fact link 2a
    //     exists to establish. Claiming a `trust` lineage for an `llvm` body is
    //     now a refusal.
    for bad in ["llvm", "clang", "Other(\"anything\")"] {
        let mutated = super::FIXTURE.replace("; #producer: trust", &format!("; #producer: {bad}"));
        assert_ne!(mutated, super::FIXTURE, "the substitution must bite");
        let e = ir_mint::project(&mutated, &t)
            .map(|_| ())
            .expect_err("a body claimed for a different producer must be refused");
        assert!(format!("{e}").contains("producer"), "wrong refusal: {e}");
    }
    // …including DELETING the clause, which is the silent-default direction.
    let stripped: String = super::FIXTURE
        .lines()
        .filter(|l| !l.contains("#producer"))
        .map(|l| format!("{l}\n"))
        .collect();
    assert_ne!(stripped, super::FIXTURE, "the deletion must bite");
    ir_mint::project(&stripped, &t)
        .map(|_| ())
        .expect_err("a body that names NO producer must not satisfy a pin that names one");

    // (2) The other four kinds keep their content erased, and this is the
    //     measurement that justifies it rather than a comment: a `#loc` moved
    //     to a different file, line and column is the SAME PROGRAM, so a gate
    //     that refused it would be refusing a pair it has no business
    //     refusing. `#loc` content is a lineage fact and it has a lane —
    //     `scripts/crystal_fixture_freshness.py`'s AMBER `loc-file-index`.
    let relocated = super::FIXTURE
        .replace("; #loc: 399 312 8", "; #loc: 12 1000 3")
        .replace("; #loc: 399 313 5", "; #loc: 12 1001 7")
        .replace("%0=\"self\"", "%0=\"receiver\"");
    assert_ne!(relocated, super::FIXTURE, "the substitution must bite");
    let moved = ir_mint::project(&relocated, &t)
        .expect("debug-info content is erased, deliberately, and must not be refused");
    assert_eq!(
        ir_mint::print(&moved.core).expect("print"),
        ir_mint::print(&ir_mint::project(super::FIXTURE, &t).expect("base").core).expect("print"),
        "…and it must not move the core module either"
    );
}

/// **The second counterexample of the third pass, and the sharper of the two:
/// the reader was not TOTAL over its own input.**
///
/// `Reader::run` used to `break` on the first line equal to `}` and ignore
/// everything after it. That is an erasure nobody had written down — the exact
/// shape this file exists to stop — and it is worse than a missing field,
/// because the completeness argument the whole ledger rests on is that both
/// readers are *total-or-refusing*: a field can only be erased by a line
/// somebody wrote to erase it, and the anchors point at those lines. A reader
/// that stops early and drops the remainder erases things nobody enumerated.
///
/// Measured before the fix, all four accepted and all four producing the
/// IDENTICAL core module to the one-function body: a text carrying `m::f`
/// followed by a whole second function `m::g`; the same text followed by a
/// `global` declaration; followed by a `file` table; followed by arbitrary
/// prose. And the sharp one — a `}` appearing MID-BODY truncated the function
/// and dropped every instruction after it in silence.
#[test]
fn content_after_the_closing_brace_is_now_refused_rather_than_dropped_unread() {
    const ONE: &str = "rustcc fn @m::f(functy.7) {\nbb0(%0: ptr):\n    unreachable\n}\n";
    const TRUNCATED: &str =
        "rustcc fn @m::f(functy.7) {\nbb0(%0: ptr):\n    unreachable\n}\n    ret\n";
    let t = header_tags(7, "external", "rustcc");
    let base = ir_mint::project(ONE, &t).expect("the one-function control must be accepted");
    let base = ir_mint::print(&base.core).expect("print");

    for (what, text) in [
        (
            "a second function",
            format!("{ONE}rustcc fn @m::g(functy.9) {{\nbb0(%0: ptr):\n    ret\n}}\n"),
        ),
        ("a module global", format!("{ONE}\nglobal @g i64 = 7\n")),
        ("a file table", format!("{ONE}\nfile 0 \"src/lib.rs\"\n")),
        (
            "arbitrary prose",
            format!("{ONE}THIS IS NOT TRUST-IR AT ALL\n"),
        ),
        // The sharp one: before the fix this read as a body whose only
        // instruction is `unreachable`, with the `ret` dropped in silence.
        ("a MID-BODY close that truncates it", TRUNCATED.to_string()),
    ] {
        let e = ir_mint::project(&text, &t)
            .map(|_| ())
            .unwrap_err_or_else(what);
        assert!(
            format!("{e}").contains("closing brace"),
            "`{what}` was refused for the wrong reason: {e}"
        );
    }

    // NON-VACUITY in the other direction: trailing BLANK lines are still fine,
    // so this refuses content and not whitespace.
    let padded = ir_mint::project(&format!("{ONE}\n\n   \n"), &t)
        .expect("trailing blank lines must still be accepted");
    assert_eq!(
        ir_mint::print(&padded.core).expect("print"),
        base,
        "…and must project to the same core module"
    );

    // The mirror at the other end: a body that never closes is a TRUNCATED
    // artifact, and reading it as a complete one is the same erasure inverted.
    let e = ir_mint::project(
        "rustcc fn @m::f(functy.7) {\nbb0(%0: ptr):\n    unreachable\n",
        &t,
    )
    .map(|_| ())
    .expect_err("a body with no closing brace must be refused");
    assert!(
        format!("{e}").contains("no closing brace"),
        "unexpected refusal for an unterminated body: {e}"
    );
}

/// `Result::expect_err` with the case name in the message, so a row that is
/// wrongly ACCEPTED names itself rather than printing `called unwrap on an Ok`.
trait UnwrapErrOr {
    fn unwrap_err_or_else(self, what: &str) -> InterfaceError;
}

impl UnwrapErrOr for Result<(), InterfaceError> {
    fn unwrap_err_or_else(self, what: &str) -> InterfaceError {
        match self {
            Ok(()) => panic!(
                "ACCEPTED a body with {what} after its close. Everything past `}}` would be \
                 dropped unread, which is the one erasure no anchor in this file could ever \
                 point at."
            ),
            Err(e) => e,
        }
    }
}

#[path = "blind_slots_annotations.rs"]
mod annotations;
