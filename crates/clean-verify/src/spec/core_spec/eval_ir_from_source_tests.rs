// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Acceptance tests for the THIRD chain's registered `ir_fs_*` sources — the
//! eleven-case non-contiguous switch, the twelve aggregate-constant arms, the
//! by-value argument, the aggregate join, A4/A5 and their executed witnesses.
//!
//! Moved out of `eval_ir_from_source.rs` on 2026-08-21 (the
//! `eval_ir_float_div_tests.rs` precedent) as part of the A2 MINT migration.
//! The only assertions that changed with the move are the ones that read the
//! now-minted module lines: they read `MINTED_IR_FS` through [`minted_line`]
//! where they read `SRC_IR_FS_B0` / `_B12` / the `BLOCKS` array before, and
//! the inlined `(IRConst.aggv (IRConst.vcons (IRConst.int_ ir_dN)
//! IRConst.vnil))` spine where the hand blocks named `ir_cvar ir_dN`.

use super::*;
use crate::test_utils::parse_check;

/// The minted `def` line for one name, from the committed script.
fn minted_line(name: &str) -> &'static str {
    let prefix = format!("def {name} ");
    ir_fs_module_defs()
        .iter()
        .find(|l| l.starts_with(&prefix))
        .unwrap_or_else(|| panic!("the minted script must define {name}"))
}

/// The minted arm blocks b1..b12, in block order.
fn minted_arms() -> Vec<&'static str> {
    (1..=12)
        .map(|i| minted_line(&format!("ir_fs_b{i}")))
        .collect()
}

/// The minted block lines b0..b13, in block order.
fn blocks() -> Vec<&'static str> {
    (0..=13)
        .map(|i| minted_line(&format!("ir_fs_b{i}")))
        .collect()
}

const ALL: &[&str] = &[
    SRC_SOURCESYSTEMR,
    SRC_SOURCE_SYSTEM_TAG,
    SRC_CLEAN_MODE_FROM_SOURCE,
    SRC_CLEAN_MODE_OF_TAG,
    SRC_CLEAN_MODE_OF_TAG_TAG,
    SRC_ENCODESSOURCESYSTEMVAL,
    SRC_IR_FS_MACH0,
    SRC_IR_FS_EXACT,
    SRC_IR_FS_CORRECT,
    SRC_IR_SPINE_HEAD_NAT,
    SRC_IR_AGG_DISC,
    SRC_IR_VALS_HEAD_DISC,
    SRC_IR_OUTCOME_DISC,
    SRC_IR_FS_MACHINE_SOUND,
    SRC_IR_FS_MACHINE_SOUND_MODE,
    SRC_IR_FS_MACHINE_SOUND_CUBICAL,
    SRC_IR_FS_NEVER_FAULTS,
    SRC_IR_FS_CORRECT_WITNESS,
    SRC_IR_FS_MACHINE_SOUND_WITNESS,
    SRC_IR_FS_MACHINE_SOUND_MODE_WITNESS,
    SRC_IR_FS_MACHINE_SOUND_CUBICAL_WITNESS,
    SRC_IR_FS_MACHINE_SOUND_JUNK_WITNESS,
];

#[test]
fn test_every_source_parses() {
    for src in ALL
        .iter()
        .copied()
        .chain(ir_fs_module_defs().iter().copied())
    {
        parse_check(src).unwrap_or_else(|e| panic!("parse error in `{src}`:\n  {e}"));
    }
}

#[test]
fn test_sources_are_ascii_and_balanced() {
    for src in ALL
        .iter()
        .copied()
        .chain(ir_fs_module_defs().iter().copied())
    {
        assert!(src.is_ascii(), "non-ascii in `{src}`");
        let open = src.chars().filter(|c| *c == '(').count();
        let close = src.chars().filter(|c| *c == ')').count();
        assert_eq!(open, close, "unbalanced parens in `{src}`");
    }
}

/// The switch is ELEVEN explicit cases on a NON-CONTIGUOUS list, plus a
/// default that carries the twelfth answer. A contiguous 0..10 table would
/// still answer Classical for ACL2 by accident, so this is checked on the
/// case list itself and not only on the answers.
#[test]
fn test_switch_is_eleven_cases_with_a_hole_at_ten() {
    let b0 = minted_line("ir_fs_b0");
    assert!(b0.contains("(ir_sc ir_d9 ir_d10 (ir_sc ir_d11 ir_d11 ir_sc0))"));
    assert!(
        !b0.contains("ir_sc ir_d10 "),
        "tag 10 (PVS) has NO explicit case; it is the value the default edge carries"
    );
    assert!(b0.contains("IRInst.switch ir_d2 ir_d12 ir_nl0"));
    assert!(
        minted_line("ir_fs_b12").contains("(IRConst.int_ ir_d4)"),
        "the default block is a real answer, not a trap"
    );
    for s in blocks() {
        assert!(!s.contains("unreachable"), "the emitted body has no trap");
    }
}

/// Every arm materializes an AGGREGATE constant. If any arm were a scalar
/// constant the chain would be about a body the compiler does not emit —
/// and it would silently stop exercising the construct this whole stage
/// exists to model.
#[test]
fn test_every_arm_is_an_aggregate_constant() {
    for s in minted_arms() {
        assert!(
            s.contains("IRInst.const_ ir_fs_tmode (IRConst.aggv (IRConst.vcons (IRConst.int_ "),
            "every arm must be `const enum.17 {{ k }}`, i.e. IRConst.aggv: {s}"
        );
        // The scalar the aggregate WRAPS is fine (that is the tag inside
        // the spine, which the hand `ir_cvar` alias used to hide); a BARE
        // scalar constant at the enum type is the drift this pins against.
        assert!(
            !s.contains("IRInst.const_ ir_fs_tmode (IRConst.int_") && !s.contains("IRConst.bool_"),
            "no arm materializes a bare scalar constant: {s}"
        );
    }
}

/// The body takes its argument BY VALUE, so nothing in this chain may load.
#[test]
fn test_no_block_performs_a_load() {
    for s in blocks() {
        assert!(
            !s.contains("IRInst.load"),
            "the emitted body performs no load; a module with one is a different body: {s}"
        );
    }
}

/// A5's fuel bound must match the minted module's cost: 2 nodes in the
/// entry block, 2 in an arm, 1 in the join.
#[test]
fn test_fuel_bound_matches_the_minted_module() {
    for src in [
        SRC_IR_FS_CORRECT,
        SRC_IR_FS_MACHINE_SOUND,
        SRC_IR_FS_MACHINE_SOUND_MODE,
        SRC_IR_FS_MACHINE_SOUND_CUBICAL,
        SRC_IR_FS_NEVER_FAULTS,
    ] {
        assert!(src.contains("Le ir_d5 fuel"), "fuel bound drifted: {src}");
    }
    assert!(SRC_IR_FS_EXACT.contains("ir_run ir_d5 ir_fs_module"));
}

/// A5 must go THROUGH A4 rather than restate it, must be hypothesised on a
/// machine observation, and must reach a conclusion about the reflected
/// function — including, at the end of the composition, the FIRST chain's
/// reflected predicate.
#[test]
fn test_a5_is_present_and_composes() {
    assert!(SRC_IR_FS_MACHINE_SOUND.contains("ir_eval fuel ir_fs_module"));
    assert!(
        SRC_IR_FS_MACHINE_SOUND.contains(": @Eq Nat (clean_mode_tag (clean_mode_from_source s)) t")
    );
    assert!(SRC_IR_FS_MACHINE_SOUND.contains("ir_fs_correct mem fuel na r s henc hle"));
    assert!(SRC_IR_FS_MACHINE_SOUND.contains("ir_outcome_disc"));
    assert!(SRC_IR_FS_MACHINE_SOUND_MODE.contains("clean_mode_of_tag_tag"));
    assert!(SRC_IR_FS_MACHINE_SOUND_MODE
        .contains(": @Eq CleanModeR (clean_mode_of_tag t) (clean_mode_from_source s)"));
    assert!(
        SRC_IR_FS_MACHINE_SOUND_CUBICAL.contains("clean_mode_has_cubical"),
        "the cross-chain composition must reach the FIRST chain's reflected predicate"
    );
    assert!(SRC_IR_FS_NEVER_FAULTS.contains("ir_outcome_is_ret"));
}

/// Every premise of every witness is discharged concretely: no witness may
/// be a restatement with a free hypothesis.
#[test]
fn test_witnesses_discharge_their_premises() {
    for src in [
        SRC_IR_FS_CORRECT_WITNESS,
        SRC_IR_FS_MACHINE_SOUND_WITNESS,
        SRC_IR_FS_MACHINE_SOUND_MODE_WITNESS,
        SRC_IR_FS_MACHINE_SOUND_CUBICAL_WITNESS,
        SRC_IR_FS_MACHINE_SOUND_JUNK_WITNESS,
    ] {
        assert!(src.contains("EncodesSourceSystemVal.mk"), "no A2: {src}");
        assert!(src.contains("Le.refl ir_d5"), "no fuel bound: {src}");
    }
    assert!(
        SRC_IR_FS_MACHINE_SOUND_JUNK_WITNESS.contains("IRScalar.undef_"),
        "the junk witness must actually carry a junk payload"
    );
}

// The uniqueness lane keeps its original home; the path moved with the
// 2026-08-21 tests split (inner `#[path]`s resolve against THIS file's
// directory now, not against `eval_ir_from_source/tests/`).
#[path = "eval_ir_from_source/tests/eval_ir_from_source_uniqueness_tests.rs"]
mod uniqueness;

/// The reflected map is the one `mode.rs:184-196` writes: twelve systems
/// onto five modes.
#[test]
fn test_reflected_map_is_the_source_function() {
    let arms: Vec<&str> = SRC_CLEAN_MODE_FROM_SOURCE
        .split("CleanModeR.")
        .skip(1) // the text before the first `CleanModeR.` constructor
        .map(|s| s.split(|c: char| !c.is_alphanumeric()).next().unwrap_or(""))
        .collect();
    assert_eq!(
        arms,
        vec![
            "constructive",
            "impredicative",
            "constructive",
            "cubical",
            "classical",
            "classical",
            "classical",
            "settheoretic",
            "settheoretic",
            "classical",
            "classical",
            "classical",
        ],
        "the reflected map must match mode.rs's twelve arms exactly"
    );
}
