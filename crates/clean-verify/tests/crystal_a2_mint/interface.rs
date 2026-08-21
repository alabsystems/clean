// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **M10 — the INTERFACE lane: the blind slots that stopped being blind.**
//!
//! `data/crystal_mint_blind_slots.json` listed nine erasures, five of them with
//! a CONSTRUCTED WITNESS — a pair of emitted bodies denoting different programs
//! that the gate accepted as one. Four of those five closed here on 2026-08-20,
//! and one (`global-index`) closed by refusal in the reader. The third pass the
//! same day closed four more — the calling convention, the linkage, the
//! signature index and the `#producer` token — so the ledger now runs to eleven
//! rows with none marked `erased`. This lane is the check; `blind_slots.rs`
//! carries the witnesses that used to pass and now fail.
//!
//! ## What is compared, and why it is compared HERE and not in the module
//!
//! Clean's `IRFunc` carries an id, parameter SSA ids, an entry block and blocks
//! — and no type (`eval_ir_syntax.rs`). A parameter type therefore cannot go
//! into the core module without changing the specification's own inductive,
//! which would move every registered term and every core digest. So the
//! interface follows the **M7 split** exactly: the fact the module cannot
//! express is pinned in the chain's reviewed tag table, and
//! [`ir_mint::project`] — the gate's one acceptance predicate — refuses a body
//! whose interface is not the pinned one.
//!
//! That is a real strengthening and a bounded one, and the boundary is worth
//! stating twice: **the core module's digest did not move.** What moved is that
//! the core module no longer stands alone. `ir_h2_module` is accepted as the
//! projection of `has_cubical_layer` only together with the table that says its
//! receiver is a `ptr`, its join binds a `bool`, its load specifies no
//! alignment, and its annotations are `#loc`/`#names`/`#producer`.
//!
//! ## Producer invariance, which is the half that decides whether it survives
//!
//! A pinned interface that fired on renumbering would be switched off within a
//! week, exactly like a pinned `enum.N`. `Tags::canon_ty` resolves every
//! `<kind>.<digits>` inside a printed type through the chain's own tag lanes,
//! so the pinned form moves under the same re-pin M7 already owns and under
//! nothing else. `renumbering_does_not_fire_the_interface_lane` measures that.

use clean_verify::ir_mint::{self, InterfaceError};

use super::{tags, FIXTURE};

const LZ_FIXTURE: &str = include_str!("../fixtures/level_is_zero.trust-ir.txt");

fn lz_tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_LZ_TAGS).expect("the committed lz tag table must parse")
}

// ────────────────────────────────────────────────────────────────────────────
// The pin describes the artifact.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m10_the_committed_fixture_projects_under_its_pinned_interface() {
    let t = tags();
    let p = ir_mint::project(FIXTURE, &t).expect("the committed fixture must project");

    // The core module is UNCHANGED by this lane. Said as an assertion because
    // it is the claim boundary: no digest moved, nothing was re-minted.
    assert_eq!(
        ir_mint::print(&p.core).expect("print"),
        ir_mint::print(&super::core_b()).expect("print"),
        "projecting under the interface pin must produce the same core module reader B always \
         produced; if it does not, this lane changed the proved module rather than checking it"
    );

    // COVERAGE DENOMINATOR — a pin over nothing accepts everything.
    assert_eq!(p.interface.params.len(), 1, "one receiver");
    assert_eq!(p.interface.block_params.len(), 1, "one join parameter");
    assert_eq!(p.interface.aligns.len(), 1, "one memory instruction");
    assert_eq!(p.interface.clauses.len(), 3, "#loc, #names, #producer");
    assert_eq!(p.interface.params[0].ty, "ptr");
    assert_eq!(p.interface.block_params[0].ty, "bool");
    assert_eq!(p.interface.aligns[0], "load:None");
    assert_eq!(
        p.interface.function_name,
        "mode::CleanMode::has_cubical_layer"
    );
    assert_eq!(
        p.tags.functy, 0,
        "the header's signature-table index is READ"
    );
}

#[test]
fn m10_the_designated_target_projects_under_its_pinned_interface() {
    let p = ir_mint::project(LZ_FIXTURE, &lz_tags()).expect("level_is_zero must project");
    assert_eq!(p.interface.params.len(), 1);
    assert_eq!(p.interface.params[0].ty, "ptr");
    assert_eq!(
        p.interface
            .block_params
            .iter()
            .map(|b| (b.block, b.ssa, b.ty.clone()))
            .collect::<Vec<_>>(),
        vec![(6, 1, "bool".to_string()), (9, 2, "bool".to_string())],
        "the outer join and the short-circuit join, in order"
    );
    // …and every callee index is a function the table NAMES, which is the
    // fail-closed half of the `callee-name` row.
    assert_eq!(p.tags.funcs.len(), 2, "the body itself and its one callee");
}

// ────────────────────────────────────────────────────────────────────────────
// It discriminates — in both directions, one row per slot.
// ────────────────────────────────────────────────────────────────────────────

/// One perturbation of an interface slot, and the refusal it must produce.
struct Row {
    slot: &'static str,
    from: &'static str,
    to: &'static str,
    /// A fragment the refusal must contain, so a row cannot be satisfied by the
    /// WRONG refusal — the failure mode that makes a mutation battery green
    /// while checking nothing.
    expect: &'static str,
}

const ROWS: &[Row] = &[
    Row {
        slot: "param-type: &CleanMode becomes Rc<CleanMode>",
        from: "bb0(%0: ptr):",
        to: "bb0(%0: Rc<enum.13>):",
        expect: "Rc<enum#0>",
    },
    Row {
        slot: "param-type: the receiver becomes an enum the body never names",
        from: "bb0(%0: ptr):",
        to: "bb0(%0: enum.175):",
        expect: "enum#?",
    },
    Row {
        slot: "param-type: a second receiver appears",
        from: "bb0(%0: ptr):",
        to: "bb0(%0: ptr, %7: u64):",
        expect: "%7: u64",
    },
    Row {
        slot: "block param-type: the join binds a u8 instead of a bool",
        from: "bb4(%1: bool):",
        to: "bb4(%1: u8):",
        expect: "block parameter",
    },
    Row {
        slot: "function-name: a DIFFERENT shipped function with this body",
        from: "@mode::CleanMode::has_cubical_layer(",
        to: "@mode::CleanMode::has_simplicial_layer(",
        expect: "has_simplicial_layer",
    },
    Row {
        slot: "align: the load starts specifying one",
        from: "load enum.13, ptr %0  ; #loc",
        to: "load enum.13, ptr %0, align 8  ; #loc",
        expect: "load:Some(8)",
    },
    Row {
        slot: "annotation kind: an undeclared trailing clause",
        from: "  ; #loc: 401 338 5",
        to: "  ; #trustme: 1",
        expect: "trustme",
    },
    // ── the three slots closed on 2026-08-20, all three in the ONE header line
    Row {
        slot: "calling convention: the Rust ABI becomes the C ABI",
        from: "rustcc fn @",
        to: "ccc fn @",
        expect: "calling convention",
    },
    Row {
        slot: "calling convention: the Rust ABI becomes Swift's",
        from: "rustcc fn @",
        to: "swiftcc fn @",
        expect: "swiftcc",
    },
    Row {
        slot: "linkage: an externally visible symbol becomes module-private",
        from: "rustcc fn @",
        to: "internal rustcc fn @",
        expect: "internal",
    },
    Row {
        slot: "signature index: a different entry of the function-type table",
        from: "(functy.0)",
        to: "(functy.4242)",
        expect: "functy.4242",
    },
    Row {
        slot: "producer: the body is claimed for a different compiler",
        from: "; #producer: trust",
        to: "; #producer: llvm",
        expect: "llvm",
    },
];

#[test]
fn m10_every_interface_slot_discriminates() {
    let t = tags();
    // NON-VACUITY, first: the unmutated fixture is ACCEPTED. A lane that
    // refuses everything is not a lane.
    ir_mint::project(FIXTURE, &t).expect("the control must be accepted");

    let mut report = String::from("\nA2 INTERFACE LANE — one row per closed blind slot\n");
    for r in ROWS {
        assert!(
            FIXTURE.contains(r.from),
            "mutation anchor `{}` is not in the fixture, so the row would be vacuous",
            r.from
        );
        let mutated = FIXTURE.replacen(r.from, r.to, 1);
        assert_ne!(mutated, FIXTURE, "the substitution must bite: {}", r.slot);
        let e = ir_mint::project(&mutated, &t)
            .map(|_| ())
            .expect_err(&format!(
            "ACCEPTED a body that differs in `{}`. That slot is not in the core module, so it is \
             refused here or nowhere.",
            r.slot
        ));
        let msg = format!("{e}");
        assert!(
            msg.contains(r.expect),
            "row `{}` was refused for the WRONG reason — expected the message to name `{}`:\n  {msg}",
            r.slot,
            r.expect
        );
        report.push_str(&format!("  REFUSED  {:<62} {msg}\n", r.slot));
    }
    println!("{report}");

    // The other half, so this lane is not read as stronger than it is: for the
    // type and name rows the CORE MODULE still cannot tell the pair apart. The
    // pair is rejected by the GATE, not by the module —
    // `the_core_module_alone_still_cannot_separate_the_type_rows` measures it.
}

/// The four rows whose pair the CORE MODULE still cannot separate, measured
/// rather than asserted.
///
/// This is the honest boundary of the close: `bb0(%0: ptr)` and
/// `bb0(%0: Rc<enum.13>)` still produce the identical core module, and they
/// always will until Clean's `IRFunc` carries a type. What changed is that the
/// pair is no longer ACCEPTED — the module alone is no longer the acceptance
/// predicate.
#[test]
fn the_core_module_alone_still_cannot_separate_the_type_rows() {
    let mut same = 0usize;
    for r in ROWS {
        // The two rows that are not type/name rows change the instruction
        // stream or refuse at the read, so they are not part of this claim.
        if r.slot.starts_with("align") || r.slot.starts_with("annotation") {
            continue;
        }
        let mutated = FIXTURE.replacen(r.from, r.to, 1);
        let (Ok(a), Ok(b)) = (
            ir_mint::read_emitted(FIXTURE),
            ir_mint::read_emitted(&mutated),
        ) else {
            continue;
        };
        if ir_mint::print(&a).ok() == ir_mint::print(&b).ok() {
            same += 1;
        }
    }
    assert!(
        same >= 3,
        "at least the three whole-parameter/name rows must still project to ONE core module; if \
         they no longer do, the fragment gained a type slot and every committed core digest moved \
         with it — which is a much larger change than this lane"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// …and it does NOT fire on the thing that moves.
// ────────────────────────────────────────────────────────────────────────────

/// **The negative control that decides whether this lane survives contact.**
///
/// Crate-level renumbering moves `enum.N`, `struct.N`, `@func.N`, `functy.N`
/// and `#loc` indices with not one instruction changed — measured over three
/// producer dumps. A gate that alarms on all of that gets switched off. The
/// interface pin is stated in `Tags::canon_ty`'s canonical form precisely so it
/// is invariant under the re-pin M7 already owns.
///
/// The line this lane draws, since 2026-08-20, is between an index that can be
/// CANONICALISED and one that can only be RE-PINNED:
///
/// * `enum.N` inside a printed type is resolved through the chain's own lanes
///   to a first-use index, so a re-interning does not reach the pin at all.
/// * `#loc`'s file index is erased outright, along with the rest of the clause
///   content, and is not pinned anywhere.
/// * `functy.N` can be neither. A body has exactly one header signature, so
///   first-use interning would map every body to `functy#0` and pin nothing,
///   and the emitted text carries no signature table to resolve the index
///   through. It is therefore pinned VERBATIM and a re-interning is a reviewed
///   re-pin — the same bargain the `funcs` lane already makes for a callee's
///   `@func.N`.
#[test]
fn renumbering_does_not_fire_the_interface_lane() {
    let t = tags();
    let renumbered = FIXTURE.replace("#loc: 401", "#loc: 12");
    assert_ne!(renumbered, FIXTURE, "the substitution must bite");
    let p = ir_mint::project(&renumbered, &t)
        .expect("pure debug-info renumbering must NOT be refused by the interface lane");
    assert_eq!(
        p.interface.params[0].ty, "ptr",
        "the pinned form does not carry a whole-crate index"
    );

    // And the other half of the same line, stated as an assertion so the COST
    // of the `functy` closure is measured and not merely mentioned: a producer
    // that re-interns the signature table now DOES fire this lane, and the fix
    // is a reviewed one-line re-pin, not a loosened gate.
    let resigned = FIXTURE.replace("functy.0", "functy.4242");
    assert_ne!(resigned, FIXTURE, "the substitution must bite");
    let e = ir_mint::project(&resigned, &t)
        .map(|_| ())
        .expect_err("a moved signature index must be refused, not read and dropped");
    assert!(
        format!("{e}").contains("functy.4242") && format!("{e}").contains("functy.0"),
        "the refusal must PRINT both the artifact's index and the pin, so the re-pin is a \
         one-line edit rather than an investigation: {e}"
    );
}

/// A re-interning of the enum the body LOADS also leaves the interface alone
/// here — the receiver is a `ptr`, so no canonicalization is even reached —
/// and M7 remains the lane that attributes it.
#[test]
fn an_enum_reinterning_is_attributed_to_the_tag_lane_not_to_this_one() {
    let t = tags();
    let reinterned = FIXTURE.replace("enum.13", "enum.176");
    assert_ne!(reinterned, FIXTURE, "the substitution must bite");
    ir_mint::project(&reinterned, &t)
        .expect("the interface lane must stay silent on a re-interning; M7 is the lane that fires");
}

// ────────────────────────────────────────────────────────────────────────────
// The pin itself is fail-closed.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn a_tag_table_without_an_interface_is_refused() {
    let ids_only = r#"{"enums":[],"structs":[],"funcs":[],"body":"m::f"}"#;
    let e = ir_mint::tags::parse(ids_only).expect_err("a table with no interface must refuse");
    assert!(
        format!("{e}").contains("interface"),
        "unexpected refusal: {e}"
    );
    let no_body = r#"{"enums":[],"structs":[],"funcs":[],"interface":{"linkage":"external","calling_conv":"rustcc","functy":0,"producer":null,"params":[],"block_params":[],"aligns":[],"clauses":[]}}"#;
    let e = ir_mint::tags::parse(no_body).expect_err("a table with no body must refuse");
    assert!(format!("{e}").contains("body"), "unexpected refusal: {e}");
}

/// A callee index the table does not account for is refused, which is the
/// `callee-name` row's fail-closed half.
#[test]
fn a_callee_the_table_does_not_pin_is_refused() {
    let t = tags();
    assert!(t.funcs.is_empty(), "has_cubical_layer calls nothing");
    let with_call = FIXTURE.replace("    ret %1", "    %9 = call @func.4914(%1)\n    ret %1");
    assert_ne!(with_call, FIXTURE, "the substitution must bite");
    let e = ir_mint::project(&with_call, &t).map(|_| ()).expect_err(
        "a body that calls something under a table with an EMPTY funcs lane must refuse: the \
         canonical index would be a numeral standing for nothing",
    );
    assert!(
        matches!(e, InterfaceError::Unpinned(_)),
        "the refusal must be the unpinned-callee one: {e}"
    );
}
