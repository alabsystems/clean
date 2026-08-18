// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A1 — pin the proved module to the EMITTED artifact.**
//!
//! `ir_h2_correct` (`eval_ir_mode.rs`) proves that the EvalIR machine running
//! `ir_h2_module` returns `clean_mode_has_cubical m` for every `CleanMode`. That
//! is a theorem about a module in Clean's spec. The crystal needs it to be a
//! theorem about the module the COMPILER EMITS for
//! `CleanMode::has_cubical_layer`, and those are different objects until
//! something checks them against each other.
//!
//! Before this gate the only thing connecting them was that I read the emitted
//! IR and wrote the spec module to match — my eyesight, at one moment, with no
//! guard against either side moving. That is exactly how the FIRST version went
//! wrong: it was hand-authored from `mode.rs` instead of from emitted output,
//! and it disagreed with the shipped body in four structural ways (six switch
//! cases instead of two-plus-default, one shared true block instead of two,
//! direct returns instead of a join block taking a block parameter, and an
//! `unreachable` default instead of a default edge carrying `false`). Every one
//! of those is invisible to the axiom ratchet and to the vacuity firewall,
//! because none of them is about axioms or about emptiness.
//!
//! ## What this gate checks
//!
//! The fixture is the trust-ir `trustc` actually emitted, recorded verbatim,
//! together with L1's per-body lineage digest and the differential verdict:
//!
//! ```text
//! derived_mir.verdict       agreed
//! derived_mir.markers_exact true
//! lineage                   sha256:b06ffd67…
//! ```
//!
//! The test parses the emitted function's control-flow graph out of that text
//! and asserts the registered spec sources encode the SAME graph: same block
//! count, same switch cases and default, same per-block constants, same
//! branch targets, and a join block that takes a parameter. A drift on either
//! side fails here rather than silently making `ir_h2_correct` a theorem about
//! something that is no longer shipped.
//!
//! ## What it does NOT establish — read before quoting it
//!
//! * It is a STRUCTURAL correspondence, not a semantic proof that Clean's
//!   `IRInst` encoding of `switch`/`br` means what trust-ir's does. The two
//!   agree by construction of `eval_ir_syntax`, which this does not re-derive.
//! * The lineage digest is RECORDED here, not recomputed from the artifact by
//!   this test. It pins WHICH emitted body the theorem is about; verifying it
//!   at flip time is A6's job, in trust.
//! * `ir_h2_module` remains hand-transcribed. This gate makes an incorrect
//!   transcription FAIL rather than making a correct one automatic.
//!
//! So this is the link that was missing, at the strength it can honestly be
//! claimed: the proved module and the emitted module are checked equal on every
//! run, and the emitted one is named by digest.
//!
//! ## Two bodies, and only one of them has this link
//!
//! `has_cubical_layer` is **not** the body the execution plan designates. The
//! designated target is `level::Level::is_zero`, and for it link 2a is OPEN. The
//! `level_is_zero` module keeps that measured instead of asserted: the emitted
//! `is_zero` body is recorded verbatim
//! (`fixtures/level_is_zero.trust-ir.txt`), the callee that blocks transcription
//! is recorded with it (`…_deref_callee.trust-ir.txt`), the A0 verdicts are
//! pinned (`level_is_zero.a0.json` — 4 PASS, 2 FAIL), and the divergence between
//! the registered `ir_lz_*` module and the emitted CFG is checked. Those tests
//! FAIL when the wall moves, which is how the transcription work gets triggered
//! rather than forgotten.

// The CFG parser both sides of this gate are read with, and the lane
// comparator that reads it. Split out on 2026-08-14: with the sixth and
// seventh chains this file reached 945 lines against a 500-line convention,
// and the parser is the half that is shared rather than the half that is about
// any one body.
#[path = "crystal_a1_lineage/emitted_cfg.rs"]
mod emitted_cfg;

use std::collections::{BTreeMap, BTreeSet};

pub(crate) use emitted_cfg::{
    assert_entry_params, assert_lanes, clean_block_sources, fixture, parse_clean, parse_emitted,
    Cfg,
};

/// A0 and A6, asserted for a chain in one place: every criterion of the
/// candidate filter, the flip event, and **the flip-event lineage == the
/// coverage-row lineage** — the gate that says the artifact the differential
/// inspected is the artifact codegen compiled.
///
/// Factored out when the sixth and seventh chains landed. The first five each
/// carry their own copy, which had already drifted: two of them check
/// `deferred_to_seam`, one checks the negative control, and one checks neither.
/// A helper cannot retroactively fix those, but it stops the drift growing.
fn assert_a0_a6(evidence: &serde_json::Value, def_path: &str) {
    assert_a0_a6_on_seam(evidence, def_path, "codegen", 0);
}

/// The same, for a chain whose flip fired on a seam other than codegen or whose
/// body carries asserts.
///
/// **Added 2026-08-16 by the TENTH chain**, which is the first over a CTFE flip
/// and the first over a panic arm. Both facts were HARD-CODED here before —
/// `seam == "codegen"` and `asserts == 0` — and both are still pinned, per
/// chain, rather than relaxed: a codegen chain that started reporting `ctfe`,
/// or a zero-assert body that grew one, still fails. The count is the number of
/// asserts `verify_assert_parity` VERIFIED (count + kind class + polarity, in
/// canonical DFS preorder, against the built sibling), so on the CTFE chain it
/// is evidence rather than metadata: on all 178 codegen flips that check is
/// vacuous at zero.
fn assert_a0_a6_on_seam(evidence: &serde_json::Value, def_path: &str, seam: &str, asserts: u64) {
    assert_eq!(
        evidence["crate"].as_str(),
        Some("clean-kernel (THE SHIPPED KERNEL, not a probe)")
    );
    assert_eq!(evidence["def_path"].as_str(), Some(def_path));

    // A0, criterion by criterion.
    assert_eq!(evidence["lowered"].as_bool(), Some(true));
    assert_eq!(evidence["spliced"].as_bool(), Some(true));
    assert_eq!(
        evidence["unsupported"].as_array().map(Vec::is_empty),
        Some(true)
    );
    assert_eq!(evidence["derived_mir"]["verdict"].as_str(), Some("agreed"));
    assert_eq!(
        evidence["derived_mir"]["markers_exact"].as_bool(),
        Some(true),
        "markers_exact is the -O gate Level::is_zero fails; it must be TRUE here"
    );
    for k in ["resolved", "extern_decls", "unresolved"] {
        assert_eq!(
            evidence["calls"][k].as_u64(),
            Some(0),
            "a non-zero {k} call count would reopen the closure question"
        );
    }
    assert_eq!(evidence["deferred_to_seam"].as_bool(), Some(false));
    assert_eq!(evidence["flip_event"]["fired"].as_bool(), Some(true));
    assert_eq!(
        evidence["flip_event"]["seam"].as_str(),
        Some(seam),
        "the seam is part of what link 2b MEANS: a codegen flip binds the instruction stream \
         codegen consumes, a CTFE flip binds the VALUE the const-eval interpreter produced. They \
         are not interchangeable and neither is a default."
    );
    assert_eq!(
        evidence["flip_event"]["asserts"].as_u64(),
        Some(asserts),
        "the number of asserts `verify_assert_parity` verified against the built sibling"
    );

    // A6: the artifact inspected must be the artifact compiled.
    let artifact_lineage = evidence["lineage"]
        .as_str()
        .expect("artifact lineage must be a string");
    let flip_lineage = evidence["flip_event"]["lineage"]
        .as_str()
        .expect("flip-event lineage must be a string");
    assert!(
        artifact_lineage.starts_with("sha256:") && artifact_lineage.len() > "sha256:".len(),
        "artifact lineage must be a non-empty sha256 identifier"
    );
    assert_eq!(
        artifact_lineage, flip_lineage,
        "the artifact inspected by the differential gate must be the artifact compiled by A6"
    );
    assert_eq!(
        evidence["flip_event"]["matches_artifact_lineage"].as_bool(),
        Some(true)
    );
    assert!(
        evidence["flip_event"]["raw"]
            .as_str()
            .is_some_and(|raw| raw.contains(artifact_lineage)),
        "the raw flip event must carry the same lineage"
    );
    assert!(
        evidence["flip_event"]["raw"]
            .as_str()
            .is_some_and(|raw| raw.contains("clean_kernel[")),
        "attribution: THIS chain's flip event must name clean_kernel, whatever the aggregates say"
    );
    assert_eq!(
        evidence["lineage_domain"].as_str(),
        Some("trust_thir_lower.body_lineage.v2"),
        "a digest and its domain travel together or neither means anything"
    );

    // The negative control and the reproduction are part of the evidence.
    assert_eq!(
        evidence["negative_control"]["flip_events_crate_wide"].as_u64(),
        Some(0)
    );
    assert_eq!(
        evidence["negative_control"]["event_for_this_body_present"].as_bool(),
        Some(false)
    );
    assert_eq!(
        evidence["reproduction"]["coverage_json_byte_identical_across_all_three"].as_bool(),
        Some(true),
        "three clean builds must reproduce the digest, or `lineage` is not a measurement"
    );
}

// The FIRST complete chain — `mode::CleanMode::has_cubical_layer`. Its two
// gates lived in THIS file until 2026-08-16, when the ninth chain took it past
// the 500-line convention; they moved unchanged, into the per-chain file every
// other chain already had.
#[path = "crystal_a1_lineage/has_cubical_layer.rs"]
mod has_cubical_layer;

// The designated `Level::is_zero` target has a separate measured-open lane.
#[path = "crystal_a1_lineage/level_is_zero.rs"]
mod level_is_zero;

// The SECOND complete chain — `Level::kind_ord` — has the same two gates, over
// a structurally different body: seven blocks, a four-case switch with a
// reachable default, five distinct integer answers, a `u8` join parameter.
#[path = "crystal_a1_lineage/level_kind_ord.rs"]
mod level_kind_ord;

// The THIRD complete chain — `CleanMode::from_source_system` — fourteen blocks,
// eleven explicit switch cases on a NON-CONTIGUOUS list, a by-value argument
// with no load at all, and AGGREGATE constants as its answers. It was measured
// as unchainable until `IRConst` gained an aggregate form.
#[path = "crystal_a1_lineage/from_source_system.rs"]
mod from_source_system;

// The FOURTH complete chain — `flat::types::FlatFlags::contains` — and the
// first over a body that COMPUTES: a width-8 bitwise AND and a width-8
// equality, two parameters, three field reads one of which is a duplicate, and
// no constant anywhere. `markers_exact` here is NON-vacuous (8 marker lines).
#[path = "crystal_a1_lineage/flat_flags_contains.rs"]
mod flat_flags_contains;

// The FIFTH complete chain — `expr::bvar_in_range` — and the first over a body
// that BRANCHES: two condbrs, four icmps, seven blocks, two chained join
// blocks, three parameters, and a short circuit expressed as control flow.
// 21 non-vacuous marker lines, and the only chained body the producer's own
// interpreter differential exercised (agreed on 125 sampled inputs).
#[path = "crystal_a1_lineage/bvar_in_range.rs"]
mod bvar_in_range;

// Every chain above records `markers_exact: true` while comparing ZERO marker lines — the
// flag is vacuous on them. This module keeps that from being a free pass: it pins a
// two-sided witness (markers that exist and agree on a flipping body; markers that exist and
// DIFFER on a body the -O gate consequently refuses) so the channel is shown to discriminate
// rather than to report `true` about everything.
#[path = "crystal_a1_lineage/markers_channel.rs"]
mod markers_channel;

// The SIXTH complete chain — `env::native_reducers_char::is_valid_char` — the
// second and last condbr-carrying body in the crate, at width 64, with a
// materialised constant in an `icmp`'s LEFT operand and an entry `condbr` whose
// polarity is the opposite of the fifth chain's. 12 non-vacuous marker lines,
// and the only branching body with an affordable concrete `ir_eval` witness.
#[path = "crystal_a1_lineage/is_valid_char.rs"]
mod is_valid_char;

// The SEVENTH complete chain — `<tc::ExprPathStep as Clone>::clone` — thirteen
// blocks, ten explicit cases plus a reachable default over eleven variants,
// eleven aggregate constants, and a `load` prologue: the first chained body
// combining the first chain's shape with the third chain's. Written by
// `#[derive(Clone)]`, not by hand. Its `markers_exact` is VACUOUS and the gate
// asserts that rather than omitting it.
#[path = "crystal_a1_lineage/expr_path_step_clone.rs"]
mod expr_path_step_clone;

// The EIGHTH chain, 2026-08-15 —
// `env::native_reducers_float::reduce_float_div::{closure#0}`, the first over
// FLOAT ARITHMETIC and the ground the 2026-08-15 lane-8 census recorded as
// covered by no chain. It is one block and two instructions — not the smallest
// chainable body (106 of the 177 are ONE instruction, every one a bare `ret`),
// but one of only four in the whole chainable set that does float arithmetic.
// Being two instructions is why it forced two new lanes into
// `emitted_cfg.rs`: the binop's TYPE (`fdiv f32` vs `fdiv f64` are different
// operations and differed in no lane) and the RETURNED value id (`ret %1`
// instead of `ret %3` returns an argument instead of the answer, and agreed
// with every lane this file had, on every chain).
#[path = "crystal_a1_lineage/float_div.rs"]
mod float_div;

// The NINTH chain, 2026-08-16 —
// `env::native_reducers_beq_shortcircuit::get_char_val::{closure#0}`, the first
// over a CAST and the other half of the ground the 2026-08-15 lane-8 census
// recorded as covered by no chain. One block, two instructions — and until this
// module it parsed to an ENTIRELY EMPTY `Cfg` on both sides, because a cast was
// in no lane at all. It adds two: `casts` (op, result, operand — `zext` and
// `trunc` are the same shape and opposite operations) and `cast_tys` (op,
// result, SOURCE, DESTINATION — a cast has TWO types and both are semantic
// input, one more than `binop_tys` has to carry).
#[path = "crystal_a1_lineage/get_char_val_trunc.rs"]
mod get_char_val_trunc;

// The TENTH complete chain —
// `tc::local_context::LocalContext::push_low_local::META_TAG`, the first over a
// PANIC ARM and the first over a CTFE FLIP. Nine nodes in one block, and three
// of them were invisible before it: the `assert` (in no lane at all — it binds
// no result, carries no type and has no target, so DELETING it changed nothing
// the gate read), the three constants in ONE block (the value lanes were keyed
// by block and kept one of each kind, and `assert_lanes` carried a ratchet that
// refused such a body and named this repair), and a multi-result node's ids (the
// program-order lane's result slot was a single `u32` read with
// `unwrap_or(u32::MAX)`).
#[path = "crystal_a1_lineage/meta_tag_shl.rs"]
mod meta_tag_shl;

// THE COVERAGE DENOMINATOR FOR THE WHOLE FILE — ten chains against every lane,
// pinned cell by cell, plus parser totality over the emitted instruction set.
// Added 2026-08-16 by the lane-completeness audit, which found four constructs
// present in the bodies that no lane read and one lane a chain never compared.
#[path = "crystal_a1_lineage/lane_matrix.rs"]
mod lane_matrix;

/// **The numeral convention the type lane resolves through, PROVED from the
/// registered sources rather than assumed.**
///
/// `norm_clean_ty` reads `ir_d64` as 64 — the name carries the value. That is a
/// convention, and a convention a gate relies on silently is a hole: if
/// `ir_d32` were ever registered as anything but 32, every width comparison in
/// the type lanes would compare two wrong numbers and agree. So the numeral
/// chain is re-derived here from the `def ir_dK` declarations themselves.
#[test]
fn numeral_names_carry_their_values() {
    let dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/spec/core_spec");
    let mut seen: BTreeMap<u32, String> = BTreeMap::new();
    for entry in std::fs::read_dir(&dir)
        .expect("core_spec must be readable")
        .flatten()
    {
        let p = entry.path();
        if p.extension().and_then(|e| e.to_str()) != Some("rs") {
            continue;
        }
        let Ok(src) = std::fs::read_to_string(&p) else {
            continue;
        };
        for line in src.lines() {
            let Some((_, rest)) = line.split_once("def ir_d") else {
                continue;
            };
            let Some((num, body)) = rest.split_once(" : Nat := ") else {
                continue;
            };
            let Ok(k) = num.parse::<u32>() else { continue };
            let body = body.split('"').next().unwrap_or(body).trim().to_string();
            if let Some(prev) = seen.insert(k, body.clone()) {
                assert_eq!(
                    prev, body,
                    "ir_d{k} is declared twice with different bodies"
                );
            }
        }
    }
    assert!(
        seen.len() >= 18,
        "the numeral chain must have been found: {seen:?}"
    );
    assert_eq!(seen.get(&0).map(String::as_str), Some("Nat.zero"));
    for (k, body) in &seen {
        if *k == 0 {
            continue;
        }
        if let Some(pred) = body.strip_prefix("Nat.succ ir_d") {
            let pred: u32 = pred.parse().unwrap_or_else(|_| panic!("ir_d{k} := {body}"));
            assert_eq!(pred + 1, *k, "ir_d{k} is Nat.succ ir_d{pred}");
        } else if let Some(sum) = body.strip_prefix("Nat.add ir_d") {
            let (a, b) = sum
                .split_once(" ir_d")
                .unwrap_or_else(|| panic!("ir_d{k} := {body}"));
            let a: u32 = a.parse().unwrap_or_else(|_| panic!("ir_d{k} := {body}"));
            let b: u32 = b.parse().unwrap_or_else(|_| panic!("ir_d{k} := {body}"));
            assert_eq!(a + b, *k, "ir_d{k} is Nat.add ir_d{a} ir_d{b}");
        } else {
            panic!(
                "ir_d{k} := {body} — an unrecognised numeral form. The type lanes read `ir_dK` as \
                 K; a numeral defined some other way would silently make every width comparison \
                 compare the wrong numbers."
            );
        }
    }
    // The three widths the type lanes actually resolve today.
    for w in [8u32, 32, 64] {
        assert!(seen.contains_key(&w), "ir_d{w} must be registered");
    }
}
