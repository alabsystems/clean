// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Source-level assertions for the CALL chain
//! (`super`, `eval_ir_has_loose_bvars.rs`): that the registered module is the
//! MINTED script and not a transcription, that the call targets the callee's
//! own id out of one namespace, that the composition really is split at the
//! call boundary, and that every source this stage registers is balanced ASCII.
//!
//! Split out of the stage file for the 500-line rule.

use super::*;

/// The MINTED `def` line for one name, from the committed script.
fn minted_line(name: &str) -> &'static str {
    let prefix = format!("def {name} ");
    ir_hlb_module_defs()
        .iter()
        .find(|l| l.starts_with(&prefix))
        .unwrap_or_else(|| panic!("the minted script must define {name}"))
}

/// The caller's one call names the callee's OWN id, from one namespace —
/// the level_is_zero minter collision, now refused BY CONSTRUCTION: reader
/// A interns the caller's own id first and the callee's second, so both
/// numerals come out of one counter and no hand can disagree with itself.
#[test]
fn test_the_call_targets_the_callee_by_its_registered_id() {
    assert!(minted_line("ir_hlb_b0").contains("IRInst.call ir_d1 (ir_nl1 ir_d0)"));
    assert!(
        minted_line("ir_lbr_func").contains("IRFunc.mk ir_d1 "),
        "the callee's own id is the call's target"
    );
    assert!(
        minted_line("ir_hlb_func").contains("IRFunc.mk ir_d0 "),
        "the caller's id is distinct from the callee's"
    );
    assert!(
        minted_line("ir_hlb_module").contains("ir_hlb_func (IRList.cons IRFunc ir_lbr_func"),
        "one module, two functions, caller first"
    );
    assert!(
        !SRC_IR_HLB_HEADLESS.contains("ir_lbr_func"),
        "the headless counterfactual must NOT contain the callee"
    );
}

/// Every line the specification registers for this module comes from the
/// MINTED script — there is no hand transcription left to drift.
#[test]
fn test_the_module_is_minted_and_not_transcribed() {
    let names: Vec<&str> = ir_hlb_module_defs()
        .iter()
        .filter_map(|l| l.strip_prefix("def ").and_then(|r| r.split(' ').next()))
        .collect();
    assert_eq!(
        names,
        [
            "ir_hlb_tself",
            "ir_hlb_b0",
            "ir_hlb_func",
            "ir_lbr_b0",
            "ir_lbr_func",
            "ir_hlb_module"
        ],
        "the minted script's six definitions, in module order"
    );
    let src = include_str!("eval_ir_has_loose_bvars.rs");
    for gone in [
        "SRC_IR_HLB_B0",
        "SRC_IR_LBR_B0",
        "SRC_IR_HLB_FUNC",
        "SRC_IR_LBR_FUNC",
        "SRC_IR_HLB_MODULE",
        "SRC_IR_HLB_TSELF",
    ] {
        assert!(
            !src.contains(&format!("const {gone}")),
            "{gone} is a hand transcription of a minted line and must not exist"
        );
    }
}

/// The composed proof goes through the boundary: split, callee lemma at
/// the caller's frame, resume — and not one flat reflexivity.
#[test]
fn test_the_composition_is_split_at_the_call_boundary() {
    let proof = SRC_IR_HLB_EXACT.split(":=").nth(1).unwrap_or("");
    assert!(proof.contains("ir_run_steps_split ir_hlb_module ir_d12 ir_d1"));
    assert!(proof.contains("ir_run_steps_split ir_hlb_module ir_d3 ir_d9"));
    assert!(proof.contains("ir_hlb_call_step"));
    assert!(proof.contains("ir_lbr_activation e px (ir_nl1 ir_d1)"));
    assert!(proof.contains("ir_hlb_resume (expr_meta_loose_bvar_range e)"));
    assert!(
        !proof.trim_start().starts_with("Eq.refl"),
        "the composed theorem must not be one flat Eq.refl"
    );
    // The callee lemma is frame-generic and is used BOTH ways.
    let act = SRC_IR_LBR_ACTIVATION.split(":=").next().unwrap_or("");
    assert!(act.contains("(ds : IRList Nat)") && act.contains("(rest : IRList IRFrame)"));
    assert!(SRC_IR_LBR_EXACT.contains("ir_lbr_activation e px (IRList.nil Nat)"));
    // The seam lemma abstracts the callee's answer.
    let resume = SRC_IR_HLB_RESUME.split(":=").next().unwrap_or("");
    assert!(resume.contains("(k : Nat)") && resume.contains("(IRScalar.int_ k)"));
}

/// A4 quantifies over everything but the module; the fuel bounds are 9
/// and 13; and both A4s run the SAME two-function module.
#[test]
fn test_a4_shapes_and_the_shared_module() {
    for (src, fuel, fid) in [
        (SRC_IR_LBR_CORRECT, "ir_d9", "ir_d1"),
        (SRC_IR_HLB_CORRECT, "ir_d13", "ir_d0"),
    ] {
        let statement = src.split(":=").next().unwrap_or("");
        assert!(statement.contains("(m : ExprMetaR)"));
        assert!(statement.contains("(mem : IRList IRMemSlot)"));
        assert!(statement.contains(&format!("Le {fuel} fuel ->")));
        assert!(statement.contains(&format!("ir_eval fuel ir_hlb_module {fid}")));
        assert!(
            !statement.contains("ir_mem0"),
            "a concrete heap would make A4 a witness"
        );
    }
    assert!(SRC_IR_HLB_AGREES.contains("(mem2 : IRList IRMemSlot)"));
}

/// Witness points and the seam-honesty facts, as data.
#[test]
fn test_witness_points_and_seam_honesty() {
    assert!(SRC_W_HLB_BOUNDARY.contains("17592186044416"));
    assert!(SRC_W_HLB_BELOW.contains("17592186044415"));
    assert!(SRC_W_LBR_HIGH.contains("72057594037927935"));
    assert!(SRC_W_LBR_HIGH.contains("(IRScalar.int_ 4095)"));
    assert!(
        SRC_W_LBR_MAX_BY_A4.contains("18446744073709551615")
            && SRC_W_LBR_MAX_BY_A4.contains("ir_lbr_correct ir_mem0"),
        "the callee MAX row is an A4 instance -- the decided form was measured and refused"
    );
    assert!(
        SRC_W_HLB_MAX_BY_COMPOSITION.contains("ir_hlb_correct ir_mem0"),
        "the caller MAX row is an A4 instance, not a decided Bool -- stated, not hidden"
    );
    assert!(SRC_W_TOP_FITS.contains("1048575 4294967296"));
    assert!(SRC_W_TRUNC_DROPS.contains("4294967296) 0"));
    assert!(SRC_W_SEAM_TRUNCATED.contains("(IRScalar.int_ 4294967296)"));
    assert!(SRC_W_MISSING_CALLEE.contains("IROutcome.stuck IRFault.no_func"));
    assert!(SRC_W_NOT_AGG.contains("IRFault.not_agg"));
    assert!(SRC_W_BAD_FIELD.contains("IRFault.bad_field"));
}

#[test]
fn test_sources_balanced_ascii() {
    for src in [
        SRC_EXPRMETAR,
        SRC_EXPR_META_BITS,
        SRC_IR_LBR_SHIFT,
        SRC_EXPR_META_LOOSE_BVAR_RANGE,
        SRC_IR_HLB_GT,
        SRC_EXPR_META_HAS_LOOSE_BVARS,
        SRC_ENCODESEXPRMETA,
        SRC_ENCODES_EXPR_META_INHABITED,
        SRC_IR_HLB_VAL,
        SRC_IR_HLB_MACH0,
        SRC_IR_HLB_FRAME1,
        SRC_IR_LBR_FRAME,
        SRC_IR_LBR_MACH0,
        SRC_IR_HLB_PUSHED,
        SRC_IR_HLB_INIT,
        SRC_IR_LBR_INIT,
        SRC_IR_LBR_GUARD,
        SRC_IR_LBR_GUARD_HOLDS,
        SRC_IR_HLB_CALL_STEP,
        SRC_IR_LBR_ACTIVATION,
        SRC_IR_HLB_RESUME,
        SRC_IR_LBR_EXACT,
        SRC_IR_HLB_EXACT,
        SRC_IR_LBR_CORRECT,
        SRC_IR_HLB_CORRECT,
        SRC_IR_LBR_MACHINE_SOUND,
        SRC_IR_HLB_MACHINE_SOUND,
        SRC_IR_LBR_NEVER_FAULTS,
        SRC_IR_HLB_NEVER_FAULTS,
        SRC_IR_HLB_RETURNS_IFF,
        SRC_IR_HLB_AGREES,
        SRC_W_HLB_ZERO,
        SRC_W_LBR_ZERO,
        SRC_W_HLB_BOUNDARY,
        SRC_W_LBR_BOUNDARY,
        SRC_W_HLB_BELOW,
        SRC_W_LBR_BELOW,
        SRC_W_HLB_MID,
        SRC_W_LBR_MID,
        SRC_W_LBR_HIGH,
        SRC_W_HLB_HIGH,
        SRC_W_LBR_MAX_BY_A4,
        SRC_W_HLB_MAX_BY_COMPOSITION,
        SRC_W_TOP_FITS,
        SRC_W_TRUNC_LOSSLESS,
        SRC_W_TRUNC_DROPS,
        SRC_W_SEAM_TRUNCATED,
        SRC_W_NOT_AGG,
        SRC_W_BAD_FIELD,
        SRC_IR_HLB_HEADLESS,
        SRC_W_MISSING_CALLEE,
        SRC_W_HLB_CORRECT,
        SRC_W_LBR_CORRECT,
        SRC_W_HLB_SOUND,
        SRC_W_LBR_SOUND,
        SRC_W_AGREES,
    ]
    .into_iter()
    // The module's six definitions are MINTED, not written here, and they
    // are checked by the same rule rather than exempted from it.
    .chain(ir_hlb_module_defs().iter().copied())
    {
        let mut d: i64 = 0;
        for ch in src.chars() {
            match ch {
                '(' => d += 1,
                ')' => d -= 1,
                _ => {}
            }
            assert!(d >= 0, "unbalanced parens in {src}");
        }
        assert_eq!(d, 0, "unbalanced parens in {src}");
        assert!(src.is_ascii(), "spec sources must be ASCII");
    }
}
