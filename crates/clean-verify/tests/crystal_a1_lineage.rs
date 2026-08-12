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

use std::collections::BTreeMap;
use std::path::PathBuf;

fn fixture(name: &str) -> String {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(name);
    std::fs::read_to_string(&p).unwrap_or_else(|e| {
        panic!(
            "crystal A1: fixture {} is missing or unreadable ({e}). It is the EMITTED trust-ir \
             this gate exists to check against; without it the gate would pass vacuously, so it \
             fails closed instead.",
            p.display()
        )
    })
}

/// The emitted function's CFG, reduced to the facts a theorem about it depends on.
#[derive(Debug, PartialEq, Eq)]
struct Cfg {
    /// block id -> the constant it materializes, if any
    consts: BTreeMap<u32, bool>,
    /// switch case value -> target block
    cases: BTreeMap<u32, u32>,
    /// the switch's default target
    default: u32,
    /// block id -> branch target
    branches: BTreeMap<u32, u32>,
    /// the block that takes a parameter, if any
    join_with_param: Option<u32>,
    blocks: Vec<u32>,
}

fn parse_emitted(text: &str) -> Cfg {
    let (mut consts, mut cases, mut branches) = (BTreeMap::new(), BTreeMap::new(), BTreeMap::new());
    let (mut default, mut join_with_param, mut blocks, mut cur) = (u32::MAX, None, vec![], None);
    for raw in text.lines() {
        let line = raw.split("; #").next().unwrap_or(raw).trim();
        if let Some(rest) = line.strip_prefix("bb") {
            if let Some((num, tail)) = rest.split_once([':', '(']) {
                if let Ok(id) = num.parse::<u32>() {
                    blocks.push(id);
                    cur = Some(id);
                    // A parameter list is `bbN(%k: ty):`; the entry block's `(%0: ptr)`
                    // is the FUNCTION parameter, so only non-entry blocks count.
                    if (raw.contains("(%") || tail.starts_with('%')) && id != 0 {
                        join_with_param = Some(id);
                    }
                }
            }
        } else if line.contains("switch") {
            if let Some(inner) = line.split_once('[').and_then(|(_, r)| r.split_once(']')) {
                for tok in inner.0.split_whitespace().collect::<Vec<_>>().chunks(2) {
                    if let [k, v] = tok {
                        let tgt = v
                            .trim_start_matches("bb")
                            .parse::<u32>()
                            .unwrap_or(u32::MAX);
                        if k.starts_with("default") {
                            default = tgt;
                        } else if let Ok(val) = k.trim_end_matches(':').parse::<u32>() {
                            cases.insert(val, tgt);
                        }
                    }
                }
            }
        } else if line.contains("const bool") {
            if let Some(b) = cur {
                consts.insert(b, line.contains("true"));
            }
        } else if let Some(t) = line.strip_prefix("br bb") {
            if let (Some(b), Ok(tgt)) = (cur, t.split('(').next().unwrap_or("").parse::<u32>()) {
                branches.insert(b, tgt);
            }
        }
    }
    Cfg {
        consts,
        cases,
        default,
        branches,
        join_with_param,
        blocks,
    }
}

/// The same facts, read off the registered Clean spec sources.
fn parse_clean(src: &str) -> Cfg {
    // `ir_dN` numerals; blocks are `IRBlock.mk ir_dID params ...`.
    let n = |s: &str| s.trim().trim_start_matches("ir_d").parse::<u32>().ok();
    let (mut consts, mut cases, mut branches) = (BTreeMap::new(), BTreeMap::new(), BTreeMap::new());
    let (mut default, mut join_with_param, mut blocks) = (u32::MAX, None, vec![]);
    for decl in src.split("def ir_h2_b").skip(1) {
        let body = decl.split_once(":=").map(|(_, b)| b).unwrap_or(decl);
        let after = body.split_once("IRBlock.mk").map(|(_, r)| r).unwrap_or("");
        let mut it = after.split_whitespace();
        let id = it.next().and_then(n).unwrap_or(u32::MAX);
        blocks.push(id);
        if !after
            .split_whitespace()
            .nth(1)
            .is_some_and(|p| p == "ir_nl0")
            && id != 0
        {
            join_with_param = Some(id);
        }
        if body.contains("IRConst.bool_ Bool.true") {
            consts.insert(id, true);
        } else if body.contains("IRConst.bool_ Bool.false") {
            consts.insert(id, false);
        }
        if let Some(sw) = body.split_once("IRInst.switch").map(|(_, r)| r) {
            let toks: Vec<&str> = sw.split_whitespace().collect();
            // `switch <scrut> <dflt> <dargs> (ir_sc <v> <tgt> (ir_sc …))`
            if let Some(d) = toks.get(1).and_then(|t| n(t)) {
                default = d;
            }
            let mut rest = sw;
            while let Some((_, r)) = rest.split_once("ir_sc ") {
                let mut t = r.split_whitespace();
                if let (Some(v), Some(g)) = (t.next().and_then(n), t.next().and_then(n)) {
                    cases.insert(v, g);
                }
                rest = r;
            }
        }
        if let Some(br) = body.split_once("IRInst.br").map(|(_, r)| r) {
            if let Some(t) = br.split_whitespace().next().and_then(n) {
                branches.insert(id, t);
            }
        }
    }
    blocks.sort_unstable();
    Cfg {
        consts,
        cases,
        default,
        branches,
        join_with_param,
        blocks,
    }
}

/// The registered spec sources for the five blocks, in one string.
fn clean_block_sources() -> String {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/spec/core_spec/eval_ir_mode.rs");
    let src = std::fs::read_to_string(&p).expect("eval_ir_mode.rs must be readable");
    // Each block is `const SRC_IR_H2_BN: &str = "def ir_h2_bN ...";`
    src.lines()
        .filter(|l| l.starts_with("const SRC_IR_H2_B"))
        .map(|l| l.to_string())
        .collect::<Vec<_>>()
        .join("\n")
}

/// THE GATE: the module Clean proves about must be the module trustc emits.
#[test]
fn proved_module_matches_the_emitted_artifact() {
    let emitted = parse_emitted(&fixture("has_cubical_layer.trust-ir.txt"));
    let clean = parse_clean(&clean_block_sources());

    // COVERAGE DENOMINATOR. Two empty CFGs compare equal, so a parser that
    // silently extracted nothing would make every assertion below pass while
    // checking nothing. Pin what the emitted body actually contains first.
    assert_eq!(emitted.blocks.len(), 5, "parser found {:?}", emitted.blocks);
    assert_eq!(
        emitted.cases.len(),
        2,
        "two switch cases: {:?}",
        emitted.cases
    );
    assert_eq!(
        emitted.consts.len(),
        3,
        "three constant-producing arms: {:?}",
        emitted.consts
    );
    assert_eq!(
        emitted.branches.len(),
        3,
        "three br edges: {:?}",
        emitted.branches
    );
    assert!(
        emitted.join_with_param.is_some(),
        "a join block taking a parameter"
    );
    assert_ne!(emitted.default, u32::MAX, "a switch default");

    assert_eq!(
        emitted.blocks, clean.blocks,
        "block set differs: emitted {:?} vs Clean {:?}",
        emitted.blocks, clean.blocks
    );
    assert_eq!(
        emitted.cases, clean.cases,
        "SWITCH CASES differ: emitted {:?} vs Clean {:?}. The first version of this module \
         enumerated all six tags; the compiler emits only the true ones and routes the rest \
         through the default.",
        emitted.cases, clean.cases
    );
    assert_eq!(
        emitted.default, clean.default,
        "switch DEFAULT differs: emitted bb{} vs Clean bb{}",
        emitted.default, clean.default
    );
    assert_eq!(
        emitted.consts, clean.consts,
        "per-block CONSTANTS differ: emitted {:?} vs Clean {:?}. Two distinct true blocks are \
         emitted; collapsing them into one is a different CFG.",
        emitted.consts, clean.consts
    );
    assert_eq!(
        emitted.branches, clean.branches,
        "BRANCH targets differ: emitted {:?} vs Clean {:?}",
        emitted.branches, clean.branches
    );
    assert_eq!(
        emitted.join_with_param, clean.join_with_param,
        "the JOIN block differs: emitted {:?} vs Clean {:?}. The emitted body funnels every arm \
         into a block taking a bool parameter and returns it; returning directly from each arm \
         is a different body.",
        emitted.join_with_param, clean.join_with_param
    );
    assert!(
        !fixture("has_cubical_layer.trust-ir.txt").contains("unreachable"),
        "the emitted body has no trap block; a Clean module with one is not this body"
    );
}

/// The measurement the whole chain rests on, pinned so it cannot quietly rot.
///
/// Taken on **clean-kernel itself**, not on a probe crate: the differential
/// verdict, the flip event, and the equality of the two lineage digests.
#[test]
fn a0_a6_evidence_is_pinned_on_the_shipped_kernel() {
    let j = fixture("has_cubical_layer.lineage.json");
    let evidence: serde_json::Value =
        serde_json::from_str(&j).expect("crystal A0/A6 evidence must be valid JSON");
    assert_eq!(
        evidence["crate"].as_str(),
        Some("clean-kernel (THE SHIPPED KERNEL, not a probe)")
    );
    assert_eq!(
        evidence["def_path"].as_str(),
        Some("mode::CleanMode::has_cubical_layer")
    );
    assert_eq!(evidence["derived_mir"]["verdict"].as_str(), Some("agreed"));
    assert_eq!(
        evidence["derived_mir"]["markers_exact"].as_bool(),
        Some(true)
    );
    assert_eq!(
        evidence["unsupported"].as_array().map(Vec::is_empty),
        Some(true)
    );
    assert_eq!(evidence["flip_event"]["fired"].as_bool(), Some(true));
    assert_eq!(
        evidence["flip_event"]["matches_artifact_lineage"].as_bool(),
        Some(true)
    );

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
    assert!(
        evidence["flip_event"]["raw"]
            .as_str()
            .is_some_and(|raw| raw.contains(artifact_lineage)),
        "the raw flip event must carry the same lineage"
    );
    assert!(
        !j.contains("hclprobe") && !j.contains("hclflip"),
        "the evidence must come from clean-kernel, not from a probe crate"
    );
}
