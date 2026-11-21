// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The NDJSON front door's fidelity to Lean's verdict where Clean's own
//! representation differs from Lean's: the 2026-10-22 re-review's findings
//! N1-N10 (decisions R118, R124, R125 and R128 in `docs/DECISIONS.md`).
//!
//! - Name-keyed folds (N1, R128): Lean's kernel folds `Nat.add` and the other
//!   `reduce_nat` heads on literals BY NAME, and expands string literals
//!   through `String.ofList`/`Char.ofNat` and types literals as `Nat`; Clean
//!   folds only a definition its native-fold authority admits by content and
//!   δ-unfolds any other. An export that declares such a name Clean does not
//!   admit is never accepted.
//! - Levels (N2, N5, N7, N8, N9, R125): the reader builds levels with the
//!   kernel's constructors, as the `.olean` loader does. A record they build
//!   as `zero`, or rewrite through an `imax`, is declined; a rewritten level
//!   in an inductive block is declined on every path; the reader's level cost
//!   is bounded.
//! - Nested reflexive blocks (N3, N6, N10, R124): Lean computes `isReflexive`
//!   over a nested block's auxiliary types; an honest export of one is
//!   accepted and a forged flag refused, through a dependent container too
//!   (R124's open item, closed by R139). The `Nat.pow` exponent cap (R140)
//!   and Lean's level equivalence (R125's open item; R150) are judged as Lean
//!   judges them.
//! - Names (N4, R118): a name with a `.` inside a component (fourteen
//!   ordinary `Init` notation definitions) is judged under its own name.
//!
//! Every arm runs the whole front door on an export and asserts the exit
//! AND the rule or declaration that decided it. The honest exports are minted
//! from the pinned v4.30.0-rc2 toolchain's own declarations
//! (`tests/fixtures/lean/v4.30.0-rc2/ndjson_minted/MintExports.lean`); the
//! forgeries are the review's repros (`tests/fixtures/ndjson_fidelity/`) or
//! perturbations of archived arena tests, and each states what pinned Lean
//! does with it.

#[path = "support/kernel_arena.rs"]
mod kernel_arena;

#[path = "support/ndjson_fidelity.rs"]
mod fidelity;

use std::time::{Duration, Instant};

use clean_olean::ndjson::{
    check_export_reader, DeclarationVerdict, ExitClass, ExportCheckOptions, ExportReport,
};
use fidelity::{
    archived, axiom_named, debug_scaled, escaped_name_collision, forged, forged_fold_head,
    forged_reduce_nat, imax_succ_def, inserted_before, level_drop_rounds, level_spine,
    level_succ_groups, minted, replaced_once, verdict_of, within, META_429,
};

fn check(text: &str) -> ExportReport {
    check_export_reader(text.as_bytes(), ExportCheckOptions::default())
}

fn rule(report: &ExportReport) -> &str {
    report.reader_error.as_ref().map_or("<none>", |e| e.rule)
}

fn decline_reason(report: &ExportReport) -> &str {
    report.decline_reason.as_deref().unwrap_or_default()
}

/// Whether the decision declined the export by level rule `rule` (R125): the
/// reader read it, the replay refused nothing, and the reason names the rule.
fn declined_by(report: &ExportReport, rule: &str) -> bool {
    report.exit == ExitClass::Decline
        && report.reader_error.is_none()
        && report.refused == 0
        && decline_reason(report).contains(&format!("[{rule}]"))
}

/// The round table's expected outcome of an archived test.
fn round_outcome(path: &str) -> String {
    let table = kernel_arena::table();
    table["tests"]
        .as_array()
        .and_then(|rows| rows.iter().find(|r| r["path"] == path))
        .and_then(|r| r["outcome"].as_str())
        .unwrap_or_else(|| panic!("{path}: no row in the round table"))
        .to_owned()
}

// -- N1: name-keyed folds -------------------------------------------------------

/// `Nat.add := fun a _ => a` and `forgedAdd : Nat.add 2 3 = 2`: Lean folds
/// `Nat.add 2 3` to `5` by name and refuses the theorem; Clean δ-unfolds the
/// forged definition to `2`. The export is declined, never accepted. Under
/// any other name Lean unfolds it too, and the export is accepted.
#[test]
fn test_fidelity_forged_fold_head_is_declined_never_accepted() {
    let forged = check(&forged_fold_head("add"));
    assert_eq!(forged.exit, ExitClass::Decline, "{forged:?}");
    let reason = forged.decline_reason.as_deref().unwrap_or_default();
    assert!(
        reason.contains("`Nat.add`") && reason.contains("R128"),
        "declined for the fold head: {reason}"
    );
    // Clean's replay admits it (the forged body computes `2`): only the
    // fold-head rule stands between it and exit 0.
    assert_eq!(
        verdict_of(&forged, "forgedAdd"),
        Some(DeclarationVerdict::Admitted),
        "{forged:?}"
    );
    let control = check(&forged_fold_head("addForged"));
    assert_eq!(control.exit, ExitClass::Accept, "{control:?}");
}

/// Every name Lean's kernel keys a literal rule on: the fourteen binary
/// `reduce_nat` heads (`type_checker.cpp`), the string-literal expansion's
/// `String.ofList` and `Char.ofNat` (`inductive.cpp`), and `Nat`, which types
/// every literal; and the two Lean evaluates with compiled code
/// (`reduce_native`), `Lean.reduceBool` and `Lean.reduceNat`. Declared as an
/// axiom, none is a definition Clean's native-fold authority admits, so each
/// export is declined.
#[test]
fn test_fidelity_every_name_keyed_fold_head_is_declined_unless_authorized() {
    let heads = [
        "Nat.add",
        "Nat.sub",
        "Nat.mul",
        "Nat.div",
        "Nat.mod",
        "Nat.gcd",
        "Nat.beq",
        "Nat.ble",
        "Nat.land",
        "Nat.lor",
        "Nat.xor",
        "Nat.shiftLeft",
        "Nat.shiftRight",
        "Nat.pow",
        "String.ofList",
        "Char.ofNat",
        "Nat",
        "Lean.reduceBool",
        "Lean.reduceNat",
    ];
    let mut failures = Vec::new();
    for head in heads {
        let report = check(&axiom_named(head));
        let reason = report.decline_reason.as_deref().unwrap_or_default();
        if report.exit != ExitClass::Decline || !reason.contains(&format!("`{head}`")) {
            failures.push(format!(
                "{head}: exit {:?} reader {:?} decline {reason:?}",
                report.exit, report.reader_error
            ));
        }
    }
    for free in ["Nat.addX", "Nat.add.x", "Nats"] {
        let report = check(&axiom_named(free));
        if report.exit != ExitClass::Accept {
            failures.push(format!("{free} (no fold keys on it): {report:?}"));
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// Pinned Lean evaluates `Lean.reduceNat c` by name with compiled code, which
/// an export lacks. A transparent identity lets Clean replay the theorem by
/// unfolding, and R128 then declines the named head. F1 excludes native
/// evaluation of an opaque identity in the export loader's Lean theory, so
/// the theorem over either opaque spelling is refused during replay.
#[test]
fn test_fidelity_native_evaluation_heads_are_declined() {
    let transparent = check(&forged_reduce_nat("reduceNat", false));
    assert_eq!(transparent.exit, ExitClass::Decline, "{transparent:?}");
    assert_eq!(transparent.refused, 0, "{transparent:?}");
    assert_eq!(
        verdict_of(&transparent, "forgedReduceNat"),
        Some(DeclarationVerdict::Admitted),
        "{transparent:?}"
    );

    let renamed = check(&forged_reduce_nat("reduceNatForged", false));
    assert_eq!(renamed.exit, ExitClass::Accept, "{renamed:?}");
    assert_eq!(
        verdict_of(&renamed, "forgedReduceNat"),
        Some(DeclarationVerdict::Admitted),
        "{renamed:?}"
    );

    let named_opaque = forged_reduce_nat("reduceNat", true);
    let renamed_opaque = forged_reduce_nat("reduceNatForged", true);
    for export in [&named_opaque, &renamed_opaque] {
        let report = check(export);
        assert_eq!(report.exit, ExitClass::Reject, "{report:?}");
        assert_eq!(report.refused, 1, "{report:?}");
        assert_eq!(
            report.first_refusal.as_ref().map(|r| r.name.as_str()),
            Some("forgedReduceNat"),
            "{report:?}"
        );
        assert_eq!(
            verdict_of(&report, "forgedReduceNat"),
            Some(DeclarationVerdict::Refused),
            "{report:?}"
        );
    }

    // Without the final theorem, no replay refusal masks the R128 decision
    // for the opaque head itself.
    let (prefix, theorem) = named_opaque
        .trim_end()
        .rsplit_once('\n')
        .expect("fixture rows");
    assert!(theorem.starts_with(r#"{"thm":"#), "{theorem}");
    let opaque_prefix = check(prefix);
    assert_eq!(opaque_prefix.exit, ExitClass::Decline, "{opaque_prefix:?}");
    assert_eq!(opaque_prefix.refused, 0, "{opaque_prefix:?}");
    for report in [&transparent, &opaque_prefix] {
        assert_eq!(
            verdict_of(report, "Lean.reduceNat"),
            Some(DeclarationVerdict::Admitted),
            "{report:?}"
        );
        let reason = decline_reason(report);
        assert!(
            reason.contains("`Lean.reduceNat`") && reason.contains("R128"),
            "{report:?}"
        );
    }
}

/// An honest v4.30.0-rc2 export of `2 + 3 = 5 := rfl`: its `Nat.add` is the
/// pinned world's, so the fold is authorized and the export is accepted.
#[test]
fn test_fidelity_an_authorized_fold_head_is_accepted() {
    let report = check(&minted("nat_add_literal.ndjson"));
    assert_eq!(report.exit, ExitClass::Accept, "{report:?}");
    for name in ["Nat.add", "natAddLit"] {
        assert_eq!(
            verdict_of(&report, name),
            Some(DeclarationVerdict::Admitted),
            "{name}: {report:?}"
        );
    }
}

// -- N2, N9: a level built as zero ------------------------------------------------

/// `axiom P : Sort (max 0 0)`, then `axiom p : P` and `thm t : P := p`.
fn theorem_over_max00(level_record: &str, sort: u64) -> String {
    [
        META_429,
        r#"{"in":1,"str":{"pre":0,"str":"P"}}"#,
        r#"{"in":2,"str":{"pre":0,"str":"p"}}"#,
        r#"{"in":3,"str":{"pre":0,"str":"t"}}"#,
        level_record,
        &format!(r#"{{"ie":0,"sort":{sort}}}"#),
        r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":1,"type":0}}"#,
        r#"{"ie":1,"const":{"name":1,"us":[]}}"#,
        r#"{"axiom":{"isUnsafe":false,"levelParams":[],"name":2,"type":1}}"#,
        r#"{"ie":2,"const":{"name":2,"us":[]}}"#,
        r#"{"thm":{"all":[3],"levelParams":[],"name":3,"type":1,"value":2}}"#,
    ]
    .join("\n")
}

/// A `max`/`imax` record the kernel's constructors build as `zero` changes
/// Prop-ness wherever Lean reads the level as written (`is_prop`, the
/// recursor's elimination level) and hides any parameter it names from the
/// undeclared-parameter check. Pinned Lean refuses each export below (review
/// N2: "Invalid recursor S.rec", "declaration type mismatch", "type of
/// theorem 't' is not a proposition"; N9: "invalid reference to undefined
/// universe level parameter 'u'"); Clean declines each.
#[test]
fn test_fidelity_level_built_as_zero_is_declined() {
    let cases = [
        (
            "large elimination over a `Sort (max 0 0)` field",
            forged("large_elim_over_max00_field.ndjson"),
        ),
        (
            "proof irrelevance at a `Sort (max 0 0)` type",
            forged("sort_max00_proof_irrel.ndjson"),
        ),
        (
            "a theorem whose type lives in `Sort (max 0 0)`",
            theorem_over_max00(r#"{"il":1,"max":[0,0]}"#, 1),
        ),
        (
            "an undeclared `u` inside `imax u 0`",
            forged("undef_imax.ndjson"),
        ),
    ];
    let mut failures = Vec::new();
    for (what, text) in &cases {
        let report = check(text);
        if !declined_by(&report, "level-rewritten-to-zero") {
            failures.push(format!(
                "{what}: exit {:?} reader {:?} first refusal {:?} decline {:?}",
                report.exit, report.reader_error, report.first_refusal, report.decline_reason
            ));
        }
    }
    // Controls: written as `Prop`, the same declarations are accepted (Lean
    // accepts them too); an undeclared parameter with no rewrite is refused
    // by the structural tier, as Lean refuses it.
    let prop = check(&theorem_over_max00(r#"{"il":1,"succ":0}"#, 0));
    if prop.exit != ExitClass::Accept {
        failures.push(format!("the theorem over Prop: {prop:?}"));
    }
    let large = replaced_once(
        &forged("large_elim_over_max00_field.ndjson"),
        r#"{"il":1,"max":[0,0]}"#,
        r#"{"il":1,"succ":0}"#,
    );
    let large_prop = check(&replaced_once(
        &large,
        r#"{"ie":0,"sort":1}"#,
        r#"{"ie":0,"sort":0}"#,
    ));
    if large_prop.exit != ExitClass::Accept {
        failures.push(format!(
            "large elimination over a Prop field: {large_prop:?}"
        ));
    }
    let undeclared = check(&replaced_once(
        &replaced_once(
            &forged("undef_imax.ndjson"),
            r#"{"il":2,"imax":[1,0]}"#,
            r#"{"il":2,"succ":1}"#,
        ),
        r#"{"ie":0,"sort":2}"#,
        r#"{"ie":0,"sort":1}"#,
    ));
    if undeclared.exit != ExitClass::Reject
        || verdict_of(&undeclared, "X") != Some(DeclarationVerdict::Refused)
    {
        failures.push(format!("`Sort u` with `u` undeclared: {undeclared:?}"));
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

// -- R125: a rewrite Lean's normalization does not make ----------------------------

/// `imax v (w+1)` is built as `max v (w+1)`. Lean's `normalize` turns
/// `succ (succ (imax v (w+1)))` into `succ (succ (max v (w+1)))` and stops,
/// so it does not find `max (v+2) (w+3)` equivalent and refuses the
/// definition (pinned v4.30.0-rc2, measured); over the rewritten level Clean
/// would accept it. A rewrite through an `imax` is declined. Rewrites of
/// `imax`-free levels are not (`max u u`, `max u (max u v)`: Lean's
/// normalization identifies them, in every context it compares them in).
#[test]
fn test_fidelity_level_rewrite_through_imax_is_declined() {
    let mut failures = Vec::new();
    let forged_def = check(&imax_succ_def(true));
    if !declined_by(&forged_def, "level-rewrite-lean-visible") {
        failures.push(format!(
            "`imax v (w+1)` under `succ`: exit {:?} reader {:?} first refusal {:?} decline {:?}",
            forged_def.exit,
            forged_def.reader_error,
            forged_def.first_refusal,
            forged_def.decline_reason
        ));
    }
    let control = check(&imax_succ_def(false));
    if control.exit != ExitClass::Accept {
        failures.push(format!("`max v (w+1)` under `succ`: {control:?}"));
    }
    // The archive: `imax 0 1` (016) is declined though Lean accepts the test;
    // `max u u` (026) and `max u (max u v)` (027) are rewritten and accepted.
    for (path, declined) in [
        (
            "good/tutorial/016_levelComp2.ndjson",
            Some("level-rewrite-lean-visible"),
        ),
        ("good/tutorial/026_levelMaxIdem.ndjson", None),
        ("good/tutorial/027_levelMaxAbsorb.ndjson", None),
    ] {
        assert_eq!(round_outcome(path), "accept", "{path}");
        let report = check(&archived(path));
        let as_expected = match declined {
            Some(by) => declined_by(&report, by),
            None => report.exit == ExitClass::Accept,
        };
        if !as_expected {
            failures.push(format!(
                "{path}: exit {:?} reader {:?} decline {:?} (expected {declined:?})",
                report.exit, report.reader_error, report.decline_reason
            ));
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

// -- N7, N8: a rewritten level anywhere in an inductive block ------------------------

/// `good/tutorial/037_boolType` with `il 3 = max u u`, `ie 22 = Sort (max u
/// u)` and `ie 23 = Bool → Sort (max u u)` (the motive's type), plus `extra`.
fn bool_with_max_uu_motive(extra: &[&str]) -> String {
    let honest = archived("good/tutorial/037_boolType.ndjson");
    let mut text = replaced_once(
        &honest,
        r#"{"il":2,"param":5}"#,
        "{\"il\":2,\"param\":5}\n{\"il\":3,\"max\":[2,2]}",
    );
    let mut lines = vec![
        r#"{"ie":22,"sort":3}"#,
        r#"{"forallE":{"binderInfo":"default","body":22,"name":7,"type":1},"ie":23}"#,
    ];
    lines.extend_from_slice(extra);
    for line in lines {
        text = inserted_before(&text, r#"{"inductive":"#, line);
    }
    text
}

/// Lean compares a block's stored constructors and recursors with the ones it
/// generates from the block as written, structurally; Clean generates them
/// over the rewritten level. A rewritten level on ANY path of the block (an
/// inductive type's type, a constructor's type, a recursor's type, any rule's
/// right-hand side) declines the export. Each forgery below puts it on one
/// path only; pinned Lean refuses each of the recursor and constructor ones
/// ("Invalid recursor"; review N7, N8).
#[test]
fn test_fidelity_block_rewritten_level_declines_on_every_path() {
    let lam_over = |body: u64| {
        format!(r#"{{"ie":24,"lam":{{"binderInfo":"default","body":{body},"name":6,"type":23}}}}"#)
    };
    let rec_type = replaced_once(
        &bool_with_max_uu_motive(&[
            r#"{"forallE":{"binderInfo":"implicit","body":14,"name":6,"type":23},"ie":24}"#,
        ]),
        r#""rules":[{"ctor":2,"nfields":0,"rhs":18},{"ctor":3,"nfields":0,"rhs":21}],"type":15}"#,
        r#""rules":[{"ctor":2,"nfields":0,"rhs":18},{"ctor":3,"nfields":0,"rhs":21}],"type":24}"#,
    );
    let rhs0 = replaced_once(
        &bool_with_max_uu_motive(&[&lam_over(17)]),
        r#""rhs":18"#,
        r#""rhs":24"#,
    );
    let rhs1 = replaced_once(
        &bool_with_max_uu_motive(&[&lam_over(20)]),
        r#""rhs":21"#,
        r#""rhs":24"#,
    );
    let both = replaced_once(
        &replaced_once(
            &archived("good/tutorial/037_boolType.ndjson"),
            r#"{"il":2,"param":5}"#,
            "{\"il\":2,\"param\":5}\n{\"il\":3,\"max\":[2,2]}",
        ),
        r#"{"ie":2,"sort":2}"#,
        r#"{"ie":2,"sort":3}"#,
    );
    let poly = archived("good/tutorial/060_typeWithTypeFieldPoly.ndjson");
    let poly_with = |lines: &[&str]| {
        let mut text = poly.clone();
        for line in lines {
            text = inserted_before(&text, r#"{"inductive":"#, line);
        }
        text
    };
    // Review N8's repro: the constructor's `α : Sort (max (u+1) (u+1))`.
    let ctor = replaced_once(
        &poly_with(&[
            r#"{"il":5,"max":[2,2]}"#,
            r#"{"ie":21,"sort":5}"#,
            r#"{"forallE":{"binderInfo":"default","body":2,"name":4,"type":21},"ie":22}"#,
        ]),
        r#""numFields":1,"numParams":0,"type":3}"#,
        r#""numFields":1,"numParams":0,"type":22}"#,
    );
    // The inductive type's own `Sort (max (u+2) (u+2))`.
    let type_ = replaced_once(
        &poly_with(&[r#"{"il":5,"max":[3,3]}"#, r#"{"ie":21,"sort":5}"#]),
        r#""numParams":0,"type":0}]}}"#,
        r#""numParams":0,"type":21}]}}"#,
    );
    let cases = [
        (
            "the recursor's type alone",
            rec_type,
            "Bool.rec",
            "recursor type",
        ),
        (
            "rule 0's right-hand side alone",
            rhs0,
            "Bool.rec",
            "right-hand side",
        ),
        (
            "rule 1's right-hand side alone",
            rhs1,
            "Bool.rec",
            "right-hand side",
        ),
        (
            "the recursor's type and both rules",
            both,
            "Bool.rec",
            "recursor type",
        ),
        (
            "a constructor's type alone",
            ctor,
            "TypeWithTypeFieldPoly.mk",
            "constructor type",
        ),
        (
            "an inductive type's type alone",
            type_,
            "TypeWithTypeFieldPoly",
            "inductive type's type",
        ),
    ];
    let mut failures = Vec::new();
    for (what, text, member, path) in &cases {
        let report = check(text);
        let reason = decline_reason(&report);
        if !declined_by(&report, "level-rewritten-in-block")
            || !reason.contains(&format!("of `{member}`"))
            || !reason.contains(path)
        {
            failures.push(format!(
                "{what}: exit {:?} reader {:?} first refusal {:?} decline {reason:?}",
                report.exit, report.reader_error, report.first_refusal
            ));
        }
    }
    for path in [
        "good/tutorial/037_boolType.ndjson",
        "good/tutorial/060_typeWithTypeFieldPoly.ndjson",
    ] {
        let control = check(&archived(path));
        if control.exit != ExitClass::Accept {
            failures.push(format!("{path} as archived: {control:?}"));
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

// -- N5: the reader's level cost --------------------------------------------------

/// A 225 KB spine of 1023 `imax` arguments plus 1000 `max` lines (review N5:
/// hours in the reader) declines at once; so does a spine under the tree
/// budget with 63 such arguments and 20,000 `max` lines (each line a fresh
/// normalization, cubic in the arguments). At the bound -- 8 arguments --
/// 10,000 lines (250 KB) are read in seconds.
#[test]
fn test_fidelity_level_cost_is_bounded() {
    let bomb = level_spine(1023, 1000);
    assert!(bomb.len() < 256 << 10, "{} bytes", bomb.len());
    let report = within(debug_scaled(Duration::from_secs(10)), move || check(&bomb));
    assert_eq!(report.exit, ExitClass::Decline, "{report:?}");
    assert_eq!(rule(&report), "level-max-args-budget", "{report:?}");

    let wide = level_spine(63, 20_000);
    let report = within(debug_scaled(Duration::from_secs(10)), move || check(&wide));
    assert_eq!(report.exit, ExitClass::Decline, "{report:?}");
    assert_eq!(rule(&report), "level-max-args-budget", "{report:?}");

    let bound = debug_scaled(Duration::from_secs(10));
    let at_bound = level_spine(8, 10_000);
    let start = Instant::now();
    let report = within(bound, move || check(&at_bound));
    assert_eq!(report.exit, ExitClass::Accept, "{report:?}");
    eprintln!("8 arguments, 10,000 lines: {:?}", start.elapsed());
}

/// Review round 3's variants of N5: within the 256-node and 8-argument caps,
/// eight `succ`-wrapped spines (61 composite arguments once normalization
/// distributes the `succ`) or 50 composites under one counted argument with
/// seven subsumed one per round make every `max` record cost millions of
/// steps, hours for a 290 KB export in a debug build. The export's total
/// level work is bounded, and both decline within seconds.
#[test]
fn test_fidelity_level_work_is_bounded_per_export() {
    for (what, text) in [
        ("succ-wrapped groups", level_succ_groups(10_000)),
        ("subsume drop rounds", level_drop_rounds(10_000)),
    ] {
        assert!(text.len() < 300 << 10, "{what}: {} bytes", text.len());
        let report = within(debug_scaled(Duration::from_secs(10)), move || check(&text));
        assert_eq!(report.exit, ExitClass::Decline, "{what}: {report:?}");
        assert_eq!(rule(&report), "level-work-budget", "{what}: {report:?}");
    }
}

// -- N3, N6, N10: nested reflexive blocks ---------------------------------------------

/// An honest v4.30.0-rc2 export of `NRT | mk : List (Nat → NRT) → NRT`,
/// `HNR | mk : HBox HNR → HNR` (`HBox α` has a field `Nat → α`) and `NW | mk
/// : List NW → NW`: Lean stores `isReflexive := true` for the first two
/// (computed over the auxiliary block) though no constructor domain is a
/// function type, and `false` for `NW`. It is accepted. A forged flag in
/// either direction is refused by the replay, which regenerates the block
/// with its auxiliary types and compares the flags.
#[test]
fn test_fidelity_nested_reflexive_blocks_are_judged_as_lean_judges_them() {
    let honest = minted("nested_reflexive.ndjson");
    let report = check(&honest);
    assert_eq!(report.exit, ExitClass::Accept, "{report:?}");
    for name in ["NRT", "HNR", "NW", "NRT.rec_1", "HNR.rec_1"] {
        assert_eq!(
            verdict_of(&report, name),
            Some(DeclarationVerdict::Admitted),
            "{name}: {report:?}"
        );
    }
    let mut failures = Vec::new();
    for (what, from, to, name) in [
        (
            "NRT stored non-reflexive",
            r#"{"all":[23],"ctors":[24],"isRec":true,"isReflexive":true"#,
            r#"{"all":[23],"ctors":[24],"isRec":true,"isReflexive":false"#,
            "NRT",
        ),
        (
            "HNR stored non-reflexive",
            r#"{"all":[45],"ctors":[46],"isRec":true,"isReflexive":true"#,
            r#"{"all":[45],"ctors":[46],"isRec":true,"isReflexive":false"#,
            "HNR",
        ),
        (
            "NW stored reflexive",
            r#"{"all":[50],"ctors":[51],"isRec":true,"isReflexive":false"#,
            r#"{"all":[50],"ctors":[51],"isRec":true,"isReflexive":true"#,
            "NW",
        ),
    ] {
        let report = check(&replaced_once(&honest, from, to));
        let refused = report
            .records
            .iter()
            .find(|r| r.name == name)
            .filter(|r| r.verdict == DeclarationVerdict::Refused)
            .and_then(|r| r.reason.clone())
            .unwrap_or_default();
        if report.exit != ExitClass::Reject
            || report.reader_error.is_some()
            || !refused.contains("isReflexive")
        {
            failures.push(format!(
                "{what}: exit {:?} reader {:?} {name}: {refused:?}",
                report.exit, report.reader_error
            ));
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// R124's open item, closed by R139: an honest v4.30.0-rc2 export of `SGS |
/// mk : (Σ _ : Nat, Nat → SGS) → SGS`. Lean builds the auxiliary `Sigma.mk`
/// field without beta reduction, as the redex `(fun _ => Nat → SGS) fst`, so
/// it stores `isReflexive := false` and the redex in `SGS.rec`/`SGS.rec_1`,
/// and accepts the block. The shared replay regenerated the auxiliary types
/// beta-normalized, computed `true` and refused it (this test pinned that
/// refusal until R139); it now keeps the redex, as Lean does, and the export
/// is accepted. The stored flag forged to `true` is still refused.
#[test]
fn test_fidelity_dependent_container_nested_block_is_judged_as_lean_judges_it() {
    let honest = minted("sigma_const_nested.ndjson");
    let report = check(&honest);
    assert_eq!(report.exit, ExitClass::Accept, "{report:?}");
    for name in ["SGS", "SGS.mk", "SGS.rec", "SGS.rec_1"] {
        assert_eq!(
            verdict_of(&report, name),
            Some(DeclarationVerdict::Admitted),
            "{name}: {report:?}"
        );
    }
    let forged_true = check(&replaced_once(
        &honest,
        r#"{"all":[27],"ctors":[28],"isRec":true,"isReflexive":false"#,
        r#"{"all":[27],"ctors":[28],"isRec":true,"isReflexive":true"#,
    ));
    assert_eq!(forged_true.exit, ExitClass::Reject, "{forged_true:?}");
    let refused = forged_true
        .records
        .iter()
        .find(|r| r.name == "SGS")
        .filter(|r| r.verdict == DeclarationVerdict::Refused)
        .and_then(|r| r.reason.clone())
        .unwrap_or_default();
    assert!(refused.contains("isReflexive"), "SGS: {refused:?}");
}

/// The round-3 review's other two kernel items, on their repros under
/// `tests/fixtures/ndjson_fidelity/open/` (named there by the R124-R128
/// record). Pinned Lean refuses `powLimit : Nat.pow 1 16777217 = 1 := rfl` and
/// `Nat.pow 0 16777217 = 0` (deep recursion past `reduce_pow`'s `2^24` cap),
/// and `B : Sort (max (u+1) (v+1)) := A` with `A : Sort (max (u+1) (max (v+1)
/// (imax (v+1) u)))` (`declaration type mismatch`: the levels are equal at
/// every assignment but not `is_equivalent`); it accepts the control `B : Sort
/// <A's level> := A`. So does the front door: the pow repros since R140, the
/// level repro since R150 (each was admitted, exit 0, before).
#[test]
fn test_fidelity_pow_cap_and_level_equivalence_follow_lean() {
    let open = |name: &str| {
        let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/ndjson_fidelity/open")
            .join(name);
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
    };
    for (file, name) in [
        ("pow_1_over_cap.ndjson", "powLimit"),
        ("pow_0_over_cap.ndjson", "powLimit"),
        ("join_subsumed_imax.ndjson", "B"),
    ] {
        let report = check(&open(file));
        assert!(report.reader_error.is_none(), "{file}: {report:?}");
        assert_eq!(report.exit, ExitClass::Reject, "{file}: {report:?}");
        assert_eq!(
            verdict_of(&report, name),
            Some(DeclarationVerdict::Refused),
            "{file}: {report:?}"
        );
    }
    let control = check(&open("join_control_same_level.ndjson"));
    assert_eq!(control.exit, ExitClass::Accept, "{control:?}");
}

// -- N4: names with a `.` inside a component ---------------------------------------------

/// The index the export binds to the name `pre.component` (`pre` an index).
fn name_index(text: &str, pre: u64, component: &str) -> u64 {
    let needle = format!(r#","str":{{"pre":{pre},"str":"{component}"}}}}"#);
    let line = text
        .lines()
        .find(|l| l.starts_with(r#"{"in":"#) && l.ends_with(&needle))
        .unwrap_or_else(|| panic!("no name record for {pre}.{component:?}"));
    line[6..line.len() - needle.len()]
        .parse()
        .expect("a name index")
}

/// An honest v4.30.0-rc2 export of the fourteen non-internal `Init`
/// constants whose names have a `.` inside a component (twelve
/// `Std.«term_..._»`-style notations, `Rat.«term_/._»`,
/// `Lean.«termMacro.trace[_]_»`) and of `Std.«a.b» := 1` beside `Std.a.b :=
/// 2`: every declaration is judged under its own name, and the export is
/// accepted. A theorem pointed at the other name is refused; two names the
/// reader would store alike are declined.
#[test]
fn test_fidelity_names_with_dotted_components_are_judged_by_exact_name() {
    let honest = minted("init_dotted_names.ndjson.gz");
    let report = check(&honest);
    assert_eq!(report.exit, ExitClass::Accept, "{report:?}");
    let init_names = [
        "Std.«term_<...<_»",
        "Std.«term_...*»",
        "Std.«term_...<_»",
        "Lean.«termMacro.trace[_]_»",
        "Std.«term_<...=_»",
        "Std.«term_...=_»",
        "Std.«term*...=_»",
        "Std.«term_<..._»",
        "Std.«term*...*»",
        "Std.«term_<...*»",
        "Std.«term*...<_»",
        "Std.«term_..._»",
        "Std.«term*..._»",
        "Rat.«term_/._»",
    ];
    for name in init_names
        .iter()
        .chain(&["Std.«a.b»", "Std.a.b", "Std.ab_one", "Std.ab_two"])
    {
        assert_eq!(
            verdict_of(&report, name),
            Some(DeclarationVerdict::Admitted),
            "{name}: {:?}",
            report.reader_error
        );
    }
    // `Std.ab_two : Std.a.b = 2 := rfl`, pointed at `Std.«a.b»` (which is 1):
    // Lean refuses it, and so must Clean, under that name, while `Std.ab_one`
    // stands. (The pointed-at name is bound before the theorem.)
    let std = name_index(&honest, 0, "Std");
    let dotted = name_index(&honest, std, "a.b");
    let plain = name_index(&honest, name_index(&honest, std, "a"), "b");
    let pointed = check(&replaced_once(
        &honest,
        &format!(r#""const":{{"name":{plain},"us":[]}}"#),
        &format!(r#""const":{{"name":{dotted},"us":[]}}"#),
    ));
    assert_eq!(pointed.exit, ExitClass::Reject, "{pointed:?}");
    assert!(pointed.reader_error.is_none(), "{pointed:?}");
    assert_eq!(
        verdict_of(&pointed, "Std.ab_two"),
        Some(DeclarationVerdict::Refused),
        "{:?}",
        pointed.first_refusal
    );
    assert_eq!(
        verdict_of(&pointed, "Std.ab_one"),
        Some(DeclarationVerdict::Admitted)
    );
    let collision = check(&escaped_name_collision());
    assert_eq!(rule(&collision), "name-collision", "{collision:?}");
    assert_eq!(collision.exit, ExitClass::Decline, "{collision:?}");
}
