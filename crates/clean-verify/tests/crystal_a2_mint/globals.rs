// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The GLOBALS lane of `project`: the module-table preamble, the tag table's
//! `globals` pins and every body's `global_addr` must account for one another,
//! and then the global list is spliced into the core module.**
//!
//! Until 2026-09-09 reader B refused a `global_addr` outright and `project`
//! spliced a hard-coded empty `(globals)` list. `ir_lzc` projects a body that
//! addresses one — the `expect` message the producer promoted to
//! `@__trust_promoted_4557` — so the refusal is lifted on exactly one path:
//! under a tag table with a `globals` lane, through `project`, which reads the
//! `type ty.N = …` / `global …` preamble (`src/ir_mint/emitted_globals.rs`)
//! and runs `check_globals` (`src/ir_mint/interface_globals.rs`).
//!
//! Every test here is CONSTRUCTED, on purpose: the committed `ir_lzc` fixture
//! pair is the subject of its own gate file, and a lane whose only witness is
//! the one artifact it was written for has not been shown to discriminate.
//! Each refusal below asserts the SLOT the refusal names, never merely that
//! something was refused.

use clean_verify::ir_mint::{self, InterfaceError};

/// A one-body table whose `globals` lane pins exactly one global.
pub(super) fn table(pin_ty: &str, pin_linkage: &str) -> ir_mint::Tags {
    ir_mint::tags::parse(&format!(
        r#"{{"body":"m::f","interface":{{"linkage":"external","calling_conv":"rustcc","functy":0,
        "producer":null,"params":[{{"block":0,"index":0,"ssa":0,"ty":"ptr"}}],"block_params":[],
        "aligns":[],"clauses":[]}},"enums":[],"structs":[],"funcs":[],
        "globals":[{{"canonical":0,"crate_id":7,"name":"g","ty":"{pin_ty}","linkage":"{pin_linkage}"}}]}}"#
    ))
    .expect("the constructed table must parse")
}

pub(super) const PREAMBLE: &str = "type ty.0 = u8\nglobal internal @g [ty.0 x 2] = array[ 1, 2 ]\n";

pub(super) const BODY: &str =
    "rustcc fn @m::f(functy.0) {\nbb0(%0: ptr):\n    %1 = global_addr @global.7\n    ret %1\n}\n";

pub(super) fn text(preamble: &str, body: &str) -> String {
    format!("{preamble}\n{body}")
}

fn refused(preamble: &str, body: &str, t: &ir_mint::Tags) -> InterfaceError {
    ir_mint::project(&text(preamble, body), t)
        .map(|_| ())
        .expect_err("this projection must be refused")
}

/// The slot a `Mismatch` names, or the whole message of any other refusal.
pub(super) fn slot(e: &InterfaceError) -> String {
    match e {
        InterfaceError::Mismatch { slot, .. } => slot.clone(),
        other => format!("{other}"),
    }
}

// ────────────────────────────────────────────────────────────────────────────
// The positive projection.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn a_preamble_and_a_body_project_to_a_module_with_its_global_list() {
    let p = ir_mint::project(&text(PREAMBLE, BODY), &table("[u8 x 2]", "internal"))
        .expect("the constructed preamble + body must project under the constructed table");
    let canonical = ir_mint::print(&p.core).expect("print");
    assert!(
        canonical.contains("(globals (global 0 (agg (int 1) (int 2))))"),
        "the global list is spliced in canonical order as `(global k <agg>)`:\n{canonical}"
    );
    assert!(
        canonical.contains("(globaladdr 0)"),
        "the body's `global_addr` resolved to the pinned canonical index:\n{canonical}"
    );
    assert_eq!(
        p.tags.globals,
        vec![7],
        "the root body reports the raw id it addressed"
    );
    // The preamble is tolerant of blank lines and of a leading blank line —
    // whitespace is not content — but of nothing else.
    ir_mint::project(
        &format!("\n\ntype ty.0 = u8\n\nglobal internal @g [ty.0 x 2] = array[ 1, 2 ]\n\n\n{BODY}"),
        &table("[u8 x 2]", "internal"),
    )
    .expect("blank lines around the preamble rows are not content");
}

/// A fixture with NO preamble projects exactly as it did before this lane:
/// `split_preamble` hands the whole text to `split_bodies`, and the spliced
/// list is the literal empty `(globals)`.
#[test]
fn a_fixture_without_a_preamble_projects_unchanged() {
    let p = ir_mint::project(super::FIXTURE, &super::tags()).expect("the committed fixture");
    assert_eq!(
        ir_mint::print(&p.core).expect("print"),
        ir_mint::print(&super::core_b()).expect("print"),
        "no preamble, no globals lane: the same core module reader B always produced"
    );
    assert!(ir_mint::print(&p.core)
        .expect("print")
        .contains("  (globals)\n"));
}

// ────────────────────────────────────────────────────────────────────────────
// Refusals — each naming its slot.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn an_unpinned_global_is_refused_by_its_crate_id() {
    let e = refused(
        PREAMBLE,
        &BODY.replace("@global.7", "@global.8"),
        &table("[u8 x 2]", "internal"),
    );
    let m = format!("{e}");
    assert!(
        matches!(e, InterfaceError::Unpinned(_)) && m.contains("@global.8"),
        "an id no row pins is refused as UNPINNED, naming the id: {m}"
    );
}

#[test]
fn a_pinned_global_the_preamble_does_not_declare_is_refused() {
    let e = refused("type ty.0 = u8\n", BODY, &table("[u8 x 2]", "internal"));
    assert_eq!(slot(&e), "global declaration", "{e}");
    assert!(format!("{e}").contains("`@g`"), "{e}");
}

#[test]
fn a_pinned_global_no_body_addresses_is_refused() {
    let e = refused(
        PREAMBLE,
        &BODY.replace("global_addr @global.7", "const bool true"),
        &table("[u8 x 2]", "internal"),
    );
    let m = format!("{e}");
    assert!(
        matches!(e, InterfaceError::Unpinned(_)) && m.contains("a pinned global no body addresses"),
        "{m}"
    );
}

#[test]
fn a_declaration_no_row_pins_is_refused_by_name() {
    let e = refused(
        &format!("{PREAMBLE}global internal @h [ty.0 x 1] = array[ 9 ]\n"),
        BODY,
        &table("[u8 x 2]", "internal"),
    );
    let m = format!("{e}");
    assert!(
        matches!(e, InterfaceError::Unpinned(_)) && m.contains("`@h`"),
        "the surplus declaration is refused BY NAME, never dropped: {m}"
    );
}

#[test]
fn a_resolved_array_type_that_disagrees_with_the_pin_is_refused() {
    // The preamble says three bytes; the pin says two. `[ty.0 x 3]` resolves
    // to `[u8 x 3]` through the type table, and it is the RESOLVED form that
    // is compared — the pin never sees `ty.0`.
    let e = refused(
        "type ty.0 = u8\nglobal internal @g [ty.0 x 3] = array[ 1, 2, 3 ]\n",
        BODY,
        &table("[u8 x 2]", "internal"),
    );
    assert!(slot(&e).starts_with("global type"), "{e}");
    let m = format!("{e}");
    assert!(m.contains("[u8 x 3]") && m.contains("[u8 x 2]"), "{m}");
    // …and a resolved ELEMENT that disagrees, same slot: `[u16 x 2]` vs `[u8 x 2]`.
    let e = refused(
        "type ty.0 = u16\nglobal internal @g [ty.0 x 2] = array[ 1, 2 ]\n",
        BODY,
        &table("[u8 x 2]", "internal"),
    );
    assert!(slot(&e).starts_with("global type"), "{e}");
}

#[test]
fn a_linkage_that_disagrees_with_the_pin_is_refused() {
    // No keyword IS `external` — absence is a value — and the pin says
    // `internal`.
    let e = refused(
        "type ty.0 = u8\nglobal @g [ty.0 x 2] = array[ 1, 2 ]\n",
        BODY,
        &table("[u8 x 2]", "internal"),
    );
    assert!(slot(&e).starts_with("global linkage"), "{e}");
    let m = format!("{e}");
    assert!(m.contains("external") && m.contains("internal"), "{m}");
    // The other direction: the row says `internal`, the pin `external`.
    let e = refused(PREAMBLE, BODY, &table("[u8 x 2]", "external"));
    assert!(slot(&e).starts_with("global linkage"), "{e}");
}

/// The three fields `IRGlobal.mk` has no slot for, refused BY NAME: a `mut`, a
/// `tls(…)` and an `align(…)` global each carry something the module cannot,
/// and reading one as the plain global it is not would be an erasure. (Reader
/// A refuses the same three in `scripts/crystal_a2_project/src/main.rs`.)
#[test]
fn mut_tls_and_align_globals_are_refused_by_name() {
    for (row, name) in [
        ("global internal mut @g [ty.0 x 2] = array[ 1, 2 ]", "mut"),
        (
            "global internal tls(local_exec) @g [ty.0 x 2] = array[ 1, 2 ]",
            "tls(",
        ),
        (
            "global internal align(4) @g [ty.0 x 2] = array[ 1, 2 ]",
            "align(",
        ),
        // The printer's full order: linkage, tls, mut, align.
        (
            "global internal tls(general_dynamic) mut align(16) @g [ty.0 x 2] = array[ 1, 2 ]",
            "tls(",
        ),
    ] {
        let e = refused(
            &format!("type ty.0 = u8\n{row}\n"),
            BODY,
            &table("[u8 x 2]", "internal"),
        );
        let m = format!("{e}");
        assert!(
            matches!(e, InterfaceError::Read(_)) && m.contains(&format!("`{name}")),
            "`{row}`: the refusal must name `{name}`: {m}"
        );
        assert!(m.contains("no slot"), "{m}");
    }
}

/// The Aggregate/Array rule is a POSITION rule: `{…}` reads only as an
/// instruction constant and `array[…]` only as a global initializer.
#[test]
fn the_aggregate_and_array_spellings_are_each_accepted_in_one_position_only() {
    let e = refused(
        "type ty.0 = u8\nglobal internal @g [ty.0 x 2] = { 1, 2 }\n",
        BODY,
        &table("[u8 x 2]", "internal"),
    );
    let m = format!("{e}");
    assert!(
        matches!(e, InterfaceError::Read(_)) && m.contains("position rule"),
        "a `{{…}}` global initializer is refused, naming the rule: {m}"
    );
    // …and `array[` in an INSTRUCTION constant stays refused in `cst()`.
    let e = refused(
        PREAMBLE,
        &BODY.replace("ret %1", "%2 = const u8 array[ 1 ]\n    ret %1"),
        &table("[u8 x 2]", "internal"),
    );
    assert!(
        format!("{e}").contains("no Clean image"),
        "`array[` as an instruction constant has no image: {e}"
    );
}

#[test]
fn an_element_above_the_element_width_is_refused() {
    let e = refused(
        "type ty.0 = u8\nglobal internal @g [ty.0 x 2] = array[ 256, 2 ]\n",
        BODY,
        &table("[u8 x 2]", "internal"),
    );
    let m = format!("{e}");
    assert!(
        matches!(e, InterfaceError::Read(_)) && m.contains("256") && m.contains("8-bit"),
        "{m}"
    );
    // 255 fits.
    ir_mint::project(
        &text(
            "type ty.0 = u8\nglobal internal @g [ty.0 x 2] = array[ 255, 0 ]\n",
            BODY,
        ),
        &table("[u8 x 2]", "internal"),
    )
    .expect("255 is a byte");
}

#[test]
fn a_length_that_disagrees_with_the_element_count_is_refused() {
    for init in ["array[ 1 ]", "array[ 1, 2, 3 ]", "array[ ]"] {
        let e = refused(
            &format!("type ty.0 = u8\nglobal internal @g [ty.0 x 2] = {init}\n"),
            BODY,
            &table("[u8 x 2]", "internal"),
        );
        let m = format!("{e}");
        assert!(
            matches!(e, InterfaceError::Read(_)) && m.contains("declares 2 element"),
            "`{init}`: {m}"
        );
    }
}

#[test]
fn a_non_scalar_type_alias_is_refused() {
    for tok in ["struct.3", "enum.2", "usize", "[u8 x 4]", "fatptr<str>"] {
        let e = refused(
            &format!("type ty.0 = {tok}\nglobal internal @g [ty.0 x 2] = array[ 1, 2 ]\n"),
            BODY,
            &table("[u8 x 2]", "internal"),
        );
        let m = format!("{e}");
        assert!(
            matches!(e, InterfaceError::Read(_)) && m.contains("SCALAR") && m.contains(tok),
            "`type ty.0 = {tok}`: {m}"
        );
    }
    // …and an element index with no `type` row at all.
    let e = refused(
        "global internal @g [ty.0 x 2] = array[ 1, 2 ]\n",
        BODY,
        &table("[u8 x 2]", "internal"),
    );
    assert!(format!("{e}").contains("no `type ty.0 = …` row"), "{e}");
}

/// The initializer list is read as the printer writes it: an empty element —
/// a doubled comma, a trailing comma — is refused, never skipped, so
/// `array[ 1,, 2 ]` is not two elements and `array[ 1, 2, ]` is not either.
#[test]
fn an_empty_array_element_is_refused_as_not_the_printers_output() {
    for init in ["array[ 1,, 2 ]", "array[ 1, 2, ]", "array[ , 1, 2 ]"] {
        let e = refused(
            &format!("type ty.0 = u8\nglobal internal @g [ty.0 x 2] = {init}\n"),
            BODY,
            &table("[u8 x 2]", "internal"),
        );
        let m = format!("{e}");
        assert!(
            matches!(e, InterfaceError::Read(_))
                && m.contains("EMPTY element")
                && m.contains("not the printer's output"),
            "`{init}`: {m}"
        );
    }
    // A length-0 array is the ONE element-less spelling, and it still reads.
    let t = ir_mint::tags::parse(
        r#"{"body":"m::f","interface":{"linkage":"external","calling_conv":"rustcc","functy":0,
        "producer":null,"params":[{"block":0,"index":0,"ssa":0,"ty":"ptr"}],"block_params":[],
        "aligns":[],"clauses":[]},"enums":[],"structs":[],"funcs":[],
        "globals":[{"canonical":0,"crate_id":7,"name":"g","ty":"[u8 x 0]","linkage":"internal"}]}"#,
    )
    .expect("the constructed table must parse");
    let p = ir_mint::project(
        &text(
            "type ty.0 = u8\nglobal internal @g [ty.0 x 0] = array[ ]\n",
            BODY,
        ),
        &t,
    )
    .expect("`array[ ]` over `[ty.0 x 0]` is the printer's empty list");
    assert!(
        ir_mint::print(&p.core)
            .expect("print")
            .contains("(globals (global 0 (agg)))"),
        "{}",
        ir_mint::print(&p.core).expect("print")
    );
}

/// A numeral that is not the canonical decimal of its value (`007`) is
/// refused: it is not what `{}` of a `u8` prints, and accepting it would give
/// one byte two atoms (`(int 007)` beside `(int 7)`).
#[test]
fn a_non_canonical_numeral_is_refused() {
    for init in ["array[ 007, 2 ]", "array[ 1, 00 ]"] {
        let e = refused(
            &format!("type ty.0 = u8\nglobal internal @g [ty.0 x 2] = {init}\n"),
            BODY,
            &table("[u8 x 2]", "internal"),
        );
        let m = format!("{e}");
        assert!(
            matches!(e, InterfaceError::Read(_)) && m.contains("canonical decimal"),
            "`{init}`: {m}"
        );
    }
    // `0` IS canonical.
    ir_mint::project(
        &text(
            "type ty.0 = u8\nglobal internal @g [ty.0 x 2] = array[ 0, 0 ]\n",
            BODY,
        ),
        &table("[u8 x 2]", "internal"),
    )
    .expect("`0` is the canonical decimal of zero");
}

/// On a preamble-bearing fixture, a refusal `split_bodies` raises names the
/// FILE line: the preamble's line count is threaded in as a base, so the
/// trailing-content refusal below points at line 9 of the text — two preamble
/// rows, one blank line, a five-line body — and not at body-relative line 6.
#[test]
fn a_split_refusal_names_the_file_line_past_the_preamble() {
    let e = ir_mint::project(
        &text(PREAMBLE, &format!("{BODY}type ty.0 = u8\n")),
        &table("[u8 x 2]", "internal"),
    )
    .map(|_| ())
    .expect_err("module-table rows after the body are trailing content");
    let m = format!("{e}");
    assert!(
        m.contains("at line 9:") && m.contains("follows the closing brace"),
        "the line named must be the FILE line (9), not the body-relative one (6): {m}"
    );
}

/// A `type`/`global` row AFTER the body is not a preamble: `split_preamble`
/// takes only the LEADING run, and `split_bodies` refuses the rest as trailing
/// content exactly as it did before this lane.
#[test]
fn a_preamble_placed_after_the_body_is_refused_as_trailing_content() {
    let e = ir_mint::project(&format!("{BODY}{PREAMBLE}"), &table("[u8 x 2]", "internal"))
        .map(|_| ())
        .expect_err("module-table rows after the body are trailing content");
    let m = format!("{e}");
    assert!(
        matches!(e, InterfaceError::Read(_)) && m.contains("follows the closing brace"),
        "{m}"
    );
}
