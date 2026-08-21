// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Falsification for the A2 mint gate.**
//!
//! A gate that cannot be made to fail is not a gate. Every row below perturbs
//! the artifact one of the readers reads — an operand, a field index, a
//! constant, a branch target, a switch label, a switch default, a load type, a
//! volatile flag, the exhaustive-enum flag, a block parameter, and four
//! perturbations of the emitted TEXT — and the matrix prints which checks
//! rejected it. A row no check rejects fails this test.
//!
//! The last row is the one that decides whether the gate is usable: **pure
//! crate-level renumbering must NOT fire.** `func.N` / `enum.N` / `#loc`
//! indices are measured to move under a producer change with zero instructions
//! changed; a gate that alarms on that gets switched off within a week.

use clean_verify::ir_mint;

use super::emitted_cfg::{assert_lanes, parse_clean, parse_emitted};
use super::{canon, core_b, FIXTURE, PREFIX};

/// One perturbation, applied to the artifact one of the readers reads.
struct Mutation {
    kind: &'static str,
    target: &'static str,
    from: &'static str,
    to: &'static str,
}

const MUTATIONS: &[Mutation] = &[
    Mutation {
        kind: "operand — read a different local",
        target: "core",
        from: "(extractfield (uint 8) 2 0)",
        to: "(extractfield (uint 8) 3 0)",
    },
    Mutation {
        kind: "field index — read a different field",
        target: "core",
        from: "(extractfield (uint 8) 2 0)",
        to: "(extractfield (uint 8) 2 1)",
    },
    Mutation {
        kind: "constant value — one arm answers the other way",
        target: "core",
        from: "(node (results 6) (const (bool) (bool false)))",
        to: "(node (results 6) (const (bool) (bool true)))",
    },
    Mutation {
        kind: "branch target — an arm joins the wrong block",
        target: "core",
        from: "(br 4 (args 5))",
        to: "(br 3 (args 5))",
    },
    Mutation {
        kind: "switch label — a tag dispatches elsewhere",
        target: "core",
        from: "(case 3 2 (args))",
        to: "(case 5 2 (args))",
    },
    Mutation {
        kind: "switch default — the fallthrough arm moves",
        target: "core",
        from: "(switch 3 3 (args)",
        to: "(switch 3 1 (args)",
    },
    Mutation {
        kind: "load type — the wrong aggregate is read",
        target: "core",
        from: "(load (enum 0) 0 false)",
        to: "(load (uint 8) 0 false)",
    },
    Mutation {
        kind: "volatile flag — a printed but semantically live flag",
        target: "core",
        from: "(load (enum 0) 0 false)",
        to: "(load (enum 0) 0 true)",
    },
    Mutation {
        kind: "exhaustive flag — THE SLOT NO TEXT-ANCHORED GATE CAN SEE",
        target: "core",
        from: "(case 3 2 (args))) false)",
        to: "(case 3 2 (args))) true)",
    },
    Mutation {
        kind: "block parameter — the join binds a different id",
        target: "core",
        from: "(block 4\n          (params 1)",
        to: "(block 4\n          (params 2)",
    },
    Mutation {
        kind: "emitted text: operand",
        target: "fixture",
        from: "%3 = extractfield u8 %2, 0",
        to: "%3 = extractfield u8 %0, 0",
    },
    Mutation {
        kind: "emitted text: constant value",
        target: "fixture",
        from: "%6 = const bool false",
        to: "%6 = const bool true",
    },
    Mutation {
        kind: "emitted text: switch arm target",
        target: "fixture",
        from: "switch %3 [ 2: bb1 3: bb2 default: bb3 ]",
        to: "switch %3 [ 2: bb2 3: bb1 default: bb3 ]",
    },
    Mutation {
        kind: "emitted text: block argument",
        target: "fixture",
        from: "br bb4(%5)",
        to: "br bb4(%4)",
    },
    // The interface rows: EIGHT slots the CORE MODULE cannot hold, so M1/M2/M3
    // are structurally silent on them and M10 is the only check that can fire.
    // That asymmetry is the point of the lane, and the matrix prints it.
    Mutation {
        kind: "emitted text: PARAMETER TYPE — &CleanMode becomes Rc<CleanMode>",
        target: "fixture",
        from: "bb0(%0: ptr):",
        to: "bb0(%0: Rc<enum.13>):",
    },
    Mutation {
        kind: "emitted text: FUNCTION NAME — a different shipped function",
        target: "fixture",
        from: "@mode::CleanMode::has_cubical_layer(",
        to: "@mode::CleanMode::has_simplicial_layer(",
    },
    Mutation {
        kind: "emitted text: ALIGN — the load starts specifying one",
        target: "fixture",
        from: "load enum.13, ptr %0  ; #loc",
        to: "load enum.13, ptr %0, align 8  ; #loc",
    },
    Mutation {
        kind: "emitted text: ANNOTATION KIND — an undeclared trailing clause",
        target: "fixture",
        from: "  ; #loc: 399 313 5",
        to: "  ; #trustme: 1",
    },
    // The four slots the third pass closed, all four in the ONE header line
    // plus the one annotation whose CONTENT is read. Same asymmetry: none of
    // them is in the core module, so M10 is the only check that can fire.
    Mutation {
        kind: "emitted text: CALLING CONVENTION — the Rust ABI becomes the C ABI",
        target: "fixture",
        from: "rustcc fn @",
        to: "ccc fn @",
    },
    Mutation {
        kind: "emitted text: LINKAGE — an exported symbol becomes module-private",
        target: "fixture",
        from: "rustcc fn @",
        to: "internal rustcc fn @",
    },
    Mutation {
        kind: "emitted text: SIGNATURE INDEX — a different function-type entry",
        target: "fixture",
        from: "(functy.0)",
        to: "(functy.4242)",
    },
    Mutation {
        kind: "emitted text: PRODUCER — the body is claimed for a different compiler",
        target: "fixture",
        from: "; #producer: trust",
        to: "; #producer: llvm",
    },
];

/// Which checks reject a mutated artifact. `None` for a check the mutation is
/// structurally invisible to — recorded, never rounded up to a pass.
#[derive(Debug, PartialEq, Eq)]
struct Verdicts {
    m1: bool,
    m2: bool,
    m3: bool,
    m5: bool,
    /// The TAG lane. Separate on purpose: a crate-level re-interning must land
    /// here and NOT in the module-identity checks.
    m7: bool,
    /// The INTERFACE lane. Separate for the same reason one step out: the
    /// function's name, its parameter TYPES, its `align` operands and its
    /// annotation kinds are not in the core module at all, so a change in one
    /// of them must land here and nowhere else — and a renumbering must not
    /// land here.
    m10: bool,
}

fn verdicts(core_text: &str, fixture_text: &str) -> Verdicts {
    verdicts_with(core_text, fixture_text, ir_mint::IR_H2_TAGS)
}

fn verdicts_with(core_text: &str, fixture_text: &str, tags_text: &str) -> Verdicts {
    let t = match ir_mint::tags::parse(tags_text) {
        Ok(t) => t,
        Err(_) => {
            return Verdicts {
                m1: true,
                m2: true,
                m3: true,
                m5: true,
                m7: true,
                m10: true,
            };
        }
    };
    let a = ir_mint::parse(core_text);
    let m1 = match &a {
        Ok(sx) => ir_mint::print(sx).map(|t| t != core_text).unwrap_or(true),
        Err(_) => true,
    };
    let m2 = match (&a, ir_mint::read_emitted(fixture_text)) {
        (Ok(sx), Ok(b)) => match ir_mint::mask_text_unwitnessed(sx) {
            Ok((masked, _)) => ir_mint::print(&masked).ok() != ir_mint::print(&b).ok(),
            Err(_) => true,
        },
        _ => true,
    };
    let m3 = match &a {
        Ok(sx) => ir_mint::mint(sx, PREFIX, &t)
            .map(|s| s.text() != ir_mint::IR_H2_DEFS)
            .unwrap_or(true),
        Err(_) => true,
    };
    let m7 = match ir_mint::read_emitted_with_tags(fixture_text) {
        Ok((_, observed)) => {
            observed.enums.len() != t.enums.len()
                || observed.enums.iter().enumerate().any(|(c, id)| {
                    u32::try_from(c)
                        .map_or(true, |c| t.enum_alias(c).map_or(true, |(rec, _)| rec != id))
                })
        }
        Err(_) => true,
    };
    let m5 = std::panic::catch_unwind(|| {
        let emitted = parse_emitted(fixture_text);
        let clean = parse_clean(ir_mint::IR_H2_DEFS, "def ir_h2_b");
        assert_lanes(&emitted, &clean, "mutation");
    })
    .is_err();
    let m10 = ir_mint::project(fixture_text, &t).is_err();
    Verdicts {
        m1,
        m2,
        m3,
        m5,
        m7,
        m10,
    }
}

#[test]
fn mutation_matrix() {
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    let base = verdicts(ir_mint::IR_H2_CORE, FIXTURE);
    let mut report = String::from(
        "\nA2 MUTATION MATRIX — R = rejected, . = did not fire\n\
         kind                                                        M1 M2 M3 M5 M7 M10\n",
    );
    let mark = |b: bool| if b { "R " } else { ". " };
    let row = |label: &str, v: &Verdicts, note: &str| {
        format!(
            "{label:<58} {}{}{}{}{}{}{note}\n",
            mark(v.m1),
            mark(v.m2),
            mark(v.m3),
            mark(v.m5),
            mark(v.m7),
            mark(v.m10)
        )
    };
    report.push_str(&row("(none)", &base, "  <- unmutated control"));

    let mut rows = Vec::new();
    for m in MUTATIONS {
        let (core_text, fixture_text) = match m.target {
            "core" => (
                mutate(ir_mint::IR_H2_CORE, m.from, m.to),
                FIXTURE.to_string(),
            ),
            _ => (
                ir_mint::IR_H2_CORE.to_string(),
                mutate(FIXTURE, m.from, m.to),
            ),
        };
        let v = verdicts(&core_text, &fixture_text);
        report.push_str(&row(&format!("[{}] {}", m.target, m.kind), &v, ""));
        rows.push((m, v));
    }

    // The TAG lane, both directions.
    //
    // (a) The artifact re-interns the enum: the module is the same program and
    //     the tag table is stale. M1..M5 must stay silent; M7 must fire.
    let reinterned = FIXTURE.replace("enum.13", "enum.176");
    assert_ne!(reinterned, FIXTURE, "the substitution must bite");
    let reint = verdicts(ir_mint::IR_H2_CORE, &reinterned);
    report.push_str(&row(
        "[fixture] enum RE-INTERNING 13 -> 176",
        &reint,
        "  <- M7 ONLY",
    ));

    // (b) The tag table itself is edited: the REGISTERED term would name a
    //     different crate id, which is a real change to the proved module.
    let bad_tags = ir_mint::IR_H2_TAGS.replace("\"crate_id\": 13", "\"crate_id\": 176");
    assert_ne!(bad_tags, ir_mint::IR_H2_TAGS, "the substitution must bite");
    let tagmut = verdicts_with(ir_mint::IR_H2_CORE, FIXTURE, &bad_tags);
    report.push_str(&row("[tags] crate id 13 -> 176", &tagmut, ""));

    // The negative control: renumbering that carries NO recorded fact must not
    // fire anything at all. `#loc`'s file index was measured to move under a
    // producer change with no instruction changed, and it is in neither the
    // core form nor the tag table.
    //
    // `functy.N` USED TO BE IN THIS CONTROL and was taken out of it on
    // 2026-08-20, which is a real narrowing and is recorded as one. It moves
    // for the same reason `#loc` does — but unlike `#loc` it names something
    // the body cannot otherwise show (`FuncTy` is `{ params, returns,
    // is_vararg }`, and neither `is_vararg` nor an unreached `returns` appears
    // in a printed body), so it is now pinned in the tag table and a producer
    // re-interning must be RE-PINNED under review, exactly as an `enum.N` or a
    // callee `@func.N` re-interning already is. The price of that is paid here,
    // in this control, deliberately.
    let renumbered = FIXTURE.replace("#loc: 399", "#loc: 12");
    assert_ne!(renumbered, FIXTURE, "the substitution must bite");
    let v = verdicts(ir_mint::IR_H2_CORE, &renumbered);
    report.push_str(&row(
        "[fixture] pure renumbering (#loc file index)",
        &v,
        "  <- MUST NOT FIRE",
    ));

    std::panic::set_hook(hook);
    println!("{report}");

    assert_eq!(
        base,
        Verdicts {
            m1: false,
            m2: false,
            m3: false,
            m5: false,
            m7: false,
            m10: false
        },
        "the unmutated control must not fire any check:{report}"
    );
    for (m, v) in &rows {
        assert!(
            v.m1 || v.m2 || v.m3 || v.m5 || v.m7 || v.m10,
            "NO CHECK REJECTED the `{}` mutation on the {}. A gate that cannot be made to fail is \
             not a gate.{report}",
            m.kind,
            m.target
        );
    }
    assert!(
        !(v.m1 || v.m2 || v.m3 || v.m5 || v.m7 || v.m10),
        "pure renumbering that carries no recorded fact fired a check. A gate that alarms on \
         re-interning gets switched off within a week; the core form exists to absorb it.{report}"
    );

    // THE SPLIT, asserted rather than left to the eye — and stated at the
    // strength it actually holds.
    //
    // M1/M2/M3 are the MODULE-identity checks: they read the core form, which
    // carries the canonical first-use index and not the crate table entry. A
    // re-interning must not move them, and does not. That is the property this
    // design adds.
    //
    // M5 is the A1 lane comparator, and it DOES fire — deliberately. The
    // 2026-08-19 `load_tys` lane pins the crate id on purpose, because a model
    // that cannot tell `enum.13` from `enum.0` cannot see a wrong load. So the
    // gate as a whole still stops on a re-interning; what changed is that the
    // stop is now ATTRIBUTED. M7 says "the tag table is stale, re-pin it",
    // where before the only available reading was "the proved module and the
    // artifact disagree".
    assert!(
        !(reint.m1 || reint.m2 || reint.m3),
        "a crate-level re-interning moved the MODULE-identity checks. The body is the same \
         program; that is the false alarm the core form exists to absorb.{report}"
    );
    assert!(
        reint.m7,
        "…and it must be ATTRIBUTED, as a stale tag table needing a reviewed re-pin.{report}"
    );
    assert!(
        reint.m5,
        "the A1 load-type lane pins the crate id on purpose (2026-08-19); if it stopped firing, \
         that pin was lost.{report}"
    );
    assert!(
        tagmut.m3,
        "editing the tag table changes the REGISTERED term (`IRTy.enum_ ir_d176`), so the mint \
         check must reject it.{report}"
    );

    // The other discriminating cell: the flag no text-anchored lane can see.
    let exh = rows
        .iter()
        .find(|(m, _)| m.kind.starts_with("exhaustive flag"))
        .expect("the exhaustive-flag row");
    assert!(
        !exh.1.m2 && !exh.1.m5,
        "M2/M5 read the emitted TEXT, which never prints this flag; if they fired, this test's \
         claim about where the blindness lies is wrong.{report}"
    );
    assert!(
        exh.1.m3,
        "the mint check must reject a changed exhaustive flag — it is the only in-repo check that \
         can.{report}"
    );
}

fn mutate(text: &str, from: &str, to: &str) -> String {
    assert!(
        text.contains(from),
        "mutation anchor not found, so the mutation would be vacuous: {from:?}"
    );
    text.replacen(from, to, 1)
}

#[test]
fn negative_control_a_different_body_is_rejected() {
    // The gate must not pass just because *some* core module is present.
    let other = include_str!("../../src/spec/core_spec/generated/ir_ko.core.txt");
    let sx = ir_mint::parse(other).expect("parse");
    let ko_tags = ir_mint::tags::parse(
        r#"{"body":"t","interface":{"linkage":"external","calling_conv":"rustcc","functy":0,"producer":null,"params":[],"block_params":[],"aligns":[],"clauses":[]},"enums":[{"canonical":0,"crate_id":2,"alias":"ir_h2_tmode"}],"structs":[],"funcs":[]}"#,
    )
    .expect("a one-row table");
    let minted = ir_mint::mint(&sx, PREFIX, &ko_tags).expect("mint").text();
    assert_ne!(
        minted,
        ir_mint::IR_H2_DEFS,
        "minting a DIFFERENT body's core module under the h2 prefix produced the h2 script"
    );
    let (masked, _) = ir_mint::mask_text_unwitnessed(&sx).expect("mask");
    assert_ne!(
        canon(&masked),
        canon(&core_b()),
        "a different body's core module compared equal to the h2 emitted text"
    );
}

/// **The `level_is_zero` wall, stated mechanically instead of asserted.**
///
/// `crystal_a1_lineage/level_is_zero.rs` asserts the emitted `is_zero` CFG and
/// the registered `ir_lz_*` module DIFFER, and fails if they ever agree. This
/// change does **not** make them agree: `ir_lz_module` is untouched, still hand
/// authored, and that gate is left exactly as it was — no silent inversion.
///
/// What this change does add is the measurement behind the wall. Reader A
/// projected the shipped `is_zero` body out of the same artifact binary and it
/// is a complete, faithful core module (`generated/ir_lz.core.txt`: ten blocks,
/// two `gep`s, four calls to two callees, a short-circuit through a second join
/// block). So the blocker for link 2a on the designated target was never that
/// the body could not be read. Minting it refuses for one nameable reason, and
/// this test pins that reason so it cannot quietly become a different one.
#[test]
fn level_is_zero_mints_only_up_to_a_named_refusal() {
    let core = include_str!("../../src/spec/core_spec/generated/ir_lz.core.txt");
    let sx = ir_mint::parse(core).expect("the emitted is_zero body parses as a core module");
    // Non-vacuity: this really is the branching, calling body.
    //
    // `(call 1 …)` and not `(call 0 …)`: since 2026-08-20 the function's own
    // index and its callee indices are ONE namespace with the body at 0, so the
    // FOREIGN deref callee sits at 1 and the recursive self-call sits at 0. The
    // old form had the deref at 0 — colliding with the body's own id — and
    // `crystal_a2_mint::callee_identity` carries the counterexample that closed
    // it.
    assert!(
        core.contains("(call 1 (args 9))") && core.contains("(call 0 (args 12))"),
        "is_zero calls its deref callee (foreign, index 1) and then itself (index 0):\n{core}"
    );
    assert!(
        core.contains("(gep (int 8) 0 (idx 8) true)"),
        "and geps into the payload"
    );
    let lz_tags = ir_mint::tags::parse(
        r#"{"body":"t","interface":{"linkage":"external","calling_conv":"rustcc","functy":0,"producer":null,"params":[],"block_params":[],"aligns":[],"clauses":[]},"enums":[{"canonical":0,"crate_id":2,"alias":"ir_lz_tlevel"}],"structs":[],"funcs":[{"canonical":0,"crate_id":4925,"name":"level::Level::is_zero"},{"canonical":1,"crate_id":4914,"name":"<level::LevelArc as std::ops::Deref>::deref"}]}"#,
    )
    .expect("a one-row table");
    let e = ir_mint::mint(&sx, "ir_lz", &lz_tags).expect_err("mint must refuse this body today");
    let msg = format!("{e}");
    assert!(
        msg.contains("atom pool"),
        "the refusal must be the ir_d0..ir_d16 numeral pool, not something else: {msg}"
    );
    println!("\nlevel_is_zero mint refusal: {msg}\n");
}

#[path = "mutation_cfg.rs"]
mod cfg_lane;
