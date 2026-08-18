// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Measured-open A1 lineage for the designated `Level::is_zero` target.
//!
//! Link 2a (proved module = emitted module) is still open here. These tests pin
//! both the emitted body and the exact closure wall. When the wall moves they
//! deliberately fail, requiring a real transcription and equality gate.

use std::path::PathBuf;

use super::*;

/// Record the emitted body verbatim so it cannot silently rot.
#[test]
fn emitted_body_is_recorded_verbatim() {
    let text = fixture("level_is_zero.trust-ir.txt");
    assert!(
        text.starts_with("rustcc fn @level::Level::is_zero("),
        "the fixture must be the is_zero body itself"
    );
    let emitted = parse_emitted(&text);

    assert_eq!(
        emitted.blocks,
        (0..10).collect::<Vec<u32>>(),
        "10 blocks, bb0..bb9"
    );
    assert_eq!(
        emitted.cases,
        BTreeMap::from([(0, 1), (1, 2), (2, 4), (4, 3)]),
        "four EXPLICIT switch cases: Zero->bb1, Succ->bb2, Max->bb4, Param->bb3"
    );
    assert_eq!(
        emitted.default, 5,
        "the default edge carries the reachable IMax arm"
    );
    assert_eq!(
        emitted.param_blocks,
        BTreeSet::from([6, 9]),
        "two join blocks take bool block parameters"
    );
    assert!(
        text.contains("gep inbounds i8, ptr %0, %8")
            && text.contains("gep inbounds i8, ptr %0, %10"),
        "payload reads are geps at byte offsets 8 and 16"
    );
    assert!(!text.contains("unreachable"));
}

/// Pin the exact reason link 2a remains open and the live CFG divergence.
#[test]
fn is_not_transcribed_and_the_wall_stands() {
    let evidence: serde_json::Value = serde_json::from_str(&fixture("level_is_zero.a0.json"))
        .expect("the A0 evidence must be valid JSON");
    assert_eq!(evidence["def_path"].as_str(), Some("level::Level::is_zero"));
    assert_eq!(evidence["lowered"].as_bool(), Some(true));
    assert_eq!(evidence["spliced"].as_bool(), Some(true));
    assert_eq!(
        evidence["unsupported"].as_array().map(Vec::is_empty),
        Some(true)
    );
    assert_eq!(evidence["derived_mir"]["verdict"].as_str(), Some("agreed"));
    assert_eq!(
        evidence["a0_criteria"]["bodyful_reachable_closure"].as_str(),
        Some("FAIL")
    );
    assert_eq!(
        evidence["a0_criteria"]["flip_event_observed"].as_str(),
        Some("FAIL")
    );
    assert_eq!(evidence["flip_event"]["fired"].as_bool(), Some(false));

    let body = fixture("level_is_zero.trust-ir.txt");
    let callee = fixture("level_is_zero_deref_callee.trust-ir.txt");
    assert!(body.contains("call @func.4914"));
    assert!(
        callee.starts_with("rustcc fn @<level::LevelArc as std::ops::Deref>::deref("),
        "func 4914 is that deref"
    );
    assert!(
        callee.contains("call @func.8369") && callee.contains("call @func.7675"),
        "the deref's declaration-only callees keep the reachable closure non-bodyful"
    );

    let clean = parse_clean(
        &std::fs::read_to_string(
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/spec/core_spec/eval_ir_crystal.rs"),
        )
        .expect("eval_ir_crystal.rs must be readable"),
        "def ir_lz_b",
    );
    assert_eq!(clean.blocks, (0..7).collect::<Vec<u32>>());
    assert_eq!(
        clean.cases,
        BTreeMap::from([(0, 1), (1, 2), (2, 3), (3, 5), (4, 2)])
    );
    assert_eq!(clean.default, 6);
    assert!(clean.param_blocks.is_empty());

    let emitted = parse_emitted(&body);
    assert_ne!(
        emitted, clean,
        "the wall moved: transcribe the body and replace this with equality"
    );
    assert_ne!(
        emitted.default, clean.default,
        "emitted default bb{} is reachable IMax; Clean default bb{} is a trap",
        emitted.default, clean.default
    );
}
