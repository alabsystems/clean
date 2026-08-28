// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Acceptance tests for the SECOND chain's registered `ir_ko_*` sources —
//! the four-case-plus-reachable-default switch, the five distinct constant
//! arms, the integer join, payload-agnosticism, A4's shape, A5 and its
//! executed witnesses.
//!
//! Moved out of `eval_ir_kind_ord.rs` on 2026-08-21 (the
//! `eval_ir_float_div_tests.rs` precedent: the file stood at the 500-line
//! convention that `data/paragon_ratchet.json`'s `files_over_500` enforces
//! shrink-only) as part of the A2 MINT migration. The only assertions that
//! changed with the move are the ones that read the now-minted module lines:
//! they read `MINTED_IR_KO` through [`minted_line`] where they read
//! `SRC_IR_KO_B0` / `_B6` / `_MODULE` before, and the inlined
//! `(IRTy.uint_ ir_d8)` where the hand blocks named the `ir_tU8` alias.

use super::*;

/// The minted `def` line for one name, from the committed script.
fn minted_line(name: &str) -> &'static str {
    let prefix = format!("def {name} ");
    ir_ko_module_defs()
        .iter()
        .find(|l| l.starts_with(&prefix))
        .unwrap_or_else(|| panic!("the minted script must define {name}"))
}

/// The switch must be FOUR explicit cases plus a default that carries the
/// fifth answer — the emitted shape. A five-case table, or a default
/// routed to a trap, is a different body.
#[test]
fn test_switch_matches_emitted_four_cases_plus_reachable_default() {
    let b0 = minted_line("ir_ko_b0");
    assert!(b0.contains(
        "(ir_sc ir_d0 ir_d1 (ir_sc ir_d1 ir_d2 (ir_sc ir_d2 ir_d3 (ir_sc ir_d3 ir_d4 ir_sc0))))"
    ));
    assert!(
        !b0.contains("ir_sc ir_d4"),
        "the emitted switch lists no tag-4 case; Param goes through the default"
    );
    // the default target is b5, and b5 is a real answer, not a trap
    assert!(b0.contains("IRInst.switch ir_d3 ir_d5 ir_nl0"));
    assert!(minted_line("ir_ko_b5").contains("IRConst.int_ ir_d4"));
    for s in ir_ko_module_defs() {
        assert!(
            !s.contains("unreachable"),
            "the emitted body has no trap block"
        );
    }
}

/// Five SEPARATE constant blocks with five DISTINCT answers. This is what
/// makes the chain more than a predicate: collapsing any two is a
/// different CFG and a different theorem.
#[test]
fn test_five_distinct_constant_arms() {
    let arms = [
        (minted_line("ir_ko_b1"), "ir_d0"),
        (minted_line("ir_ko_b2"), "ir_d1"),
        (minted_line("ir_ko_b3"), "ir_d2"),
        (minted_line("ir_ko_b4"), "ir_d3"),
        (minted_line("ir_ko_b5"), "ir_d4"),
    ];
    for (src, val) in arms {
        assert!(
            src.contains(&format!("IRConst.int_ {val}")),
            "arm must materialize {val}"
        );
        assert!(
            src.contains("IRInst.br ir_d6"),
            "every arm branches to the join"
        );
        assert!(
            !src.contains("IRConst.bool_"),
            "this body's answers are integers, not Bools"
        );
    }
    let mut seen: Vec<&str> = arms.iter().map(|(s, _)| *s).collect();
    seen.sort_unstable();
    seen.dedup();
    assert_eq!(seen.len(), 5, "five distinct arm blocks, as emitted");
}

/// The join block takes a `u8` parameter, not a `bool`. That is the
/// difference that routes the answer through `ir_const_int_eval`.
#[test]
fn test_join_block_takes_an_integer_parameter() {
    let b6 = minted_line("ir_ko_b6");
    assert!(b6.contains("IRBlock.mk ir_d6 (ir_nl1 ir_d1)"));
    assert!(b6.contains("IRInst.ret (ir_nl1 ir_d1)"));
    for name in ["ir_ko_b1", "ir_ko_b2", "ir_ko_b3", "ir_ko_b4", "ir_ko_b5"] {
        // the minted script inlines the type the hand blocks aliased as
        // `ir_tU8`; the two are definitionally equal
        assert!(minted_line(name).contains("IRInst.const_ (IRTy.uint_ ir_d8)"));
    }
}

/// The representation premise must stay PAYLOAD-AGNOSTIC. Pinning the
/// spine would smuggle in facts the emitted body never observes, and would
/// make this chain a re-run of the fieldless-enum one.
#[test]
fn test_representation_is_payload_agnostic() {
    assert!(SRC_ENCODESLEVELKINDCELL.contains("(fs : IRScalar)"));
    assert!(SRC_ENCODESLEVELKINDCELL.contains("(ir_var (level_kind_tag l) fs)"));
    for pinned in ["ir_sp0)", "ir_sp1", "ir_sp2"] {
        assert!(
            !SRC_ENCODESLEVELKINDCELL.contains(pinned),
            "the payload spine must not be pinned to {pinned}"
        );
    }
    // exactly one lookup EQUATION; membership would be satisfiable by a
    // shadowed duplicate while the machine reads a different cell
    assert_eq!(
        SRC_ENCODESLEVELKINDCELL
            .matches("ir_mem_lookup mem")
            .count(),
        1
    );
    assert!(SRC_ENCODESLEVELKINDCELL.contains("(IRScalar.ptr_ a)"));
    assert!(SRC_ENCODESLEVELKINDCELL.contains("Bool.true"));
    for bad in ["Exists", "Sigma"] {
        assert!(!SRC_ENCODESLEVELKINDCELL.contains(bad));
    }
}

/// The bridge makes the weakening CHECKED: every heap the recursive `Level`
/// relation accepts is accepted here, one arm per constructor.
#[test]
fn test_bridge_covers_every_level_constructor() {
    for ctor in [
        "Level.zero",
        "Level.succ",
        "Level.max",
        "Level.imax",
        "Level.param",
    ] {
        assert!(
            SRC_ENCODES_LEVEL_KIND_OF_ARC.contains(ctor),
            "no bridge arm for {ctor}"
        );
    }
    assert!(SRC_ENCODES_LEVEL_KIND_OF_ARC.contains("EncodesLevelArc.rec mem"));
    assert!(SRC_ENCODES_LEVEL_KIND_OF_ARC
        .contains("(_arc1 : EncodesLevelArc mem (IRScalar.ptr_ b1) l1)"));
}

/// A4 stays universally quantified over `Level`, over the heap, and over
/// the fuel. Naming a constructor in the statement would make it a sample.
#[test]
fn test_a4_shape() {
    let statement = SRC_IR_KO_CORRECT.split(":=").next().unwrap_or("");
    assert!(statement.contains("(l : Level)"));
    assert!(statement.contains("(mem : IRList IRMemSlot)"));
    assert!(SRC_IR_KO_CORRECT.contains("Le ir_d6 fuel ->"));
    assert!(SRC_IR_KO_CORRECT.contains("ir_run_le_ret"));
    for c in ["Level.zero", "Level.succ", "Level.max", "Level.imax"] {
        assert!(
            !statement.contains(c),
            "A4's STATEMENT must not mention {c}"
        );
    }
    assert!(
        !statement.contains("ir_cell"),
        "a concrete heap would make this a witness, not a theorem"
    );
}

/// A5 exists, composes with A4 through `ir_outcome_nat`, and reaches a
/// denotational conclusion rather than stopping at the reflected function.
/// The `has_cubical_layer` chain lost its A5 once, silently, to a
/// re-authoring; nothing noticed for two days. This is what notices.
#[test]
fn test_a5_is_present_and_reaches_level_eval() {
    assert!(SRC_IR_KO_MACHINE_SOUND.contains("ir_eval fuel ir_ko_module"));
    assert!(SRC_IR_KO_MACHINE_SOUND.contains(": Eq Nat (level_kind_ord l) n"));
    assert!(SRC_IR_KO_MACHINE_SOUND.contains("ir_ko_correct mem fuel na r l henc hle"));
    assert!(SRC_IR_KO_MACHINE_SOUND.contains("ir_outcome_nat"));
    // …and the denotational step, which ir_h2_machine_sound has no
    // analogue of because there is no CleanMode semantics to compose with.
    assert!(SRC_IR_KO_MACHINE_SOUND_DENOT.contains("level_is_zero_sound"));
    assert!(SRC_IR_KO_MACHINE_SOUND_DENOT.contains("level_kind_zero_is_zero"));
    assert!(SRC_IR_KO_MACHINE_SOUND_DENOT
        .contains("forall (rho : Name -> Nat), Eq Nat (level_eval rho l) Nat.zero"));
    assert!(SRC_IR_KO_NEVER_FAULTS.contains("ir_outcome_is_ret"));
}

/// Every premise of A5 is discharged concretely, and the payload-bearing
/// witness runs on `undef_` payloads over ARBITRARY sub-levels — the
/// executable form of payload-agnosticism.
#[test]
fn test_a5_witnesses_are_concrete_and_run_the_machine() {
    assert!(SRC_IR_KO_MACHINE_SOUND_DENOT_WITNESS.contains("EncodesLevelKindCell.mk"));
    assert!(SRC_IR_KO_MACHINE_SOUND_DENOT_WITNESS.contains("Le.refl ir_d6"));
    assert!(SRC_IR_KO_MACHINE_SOUND_DENOT_WITNESS.contains("Eq.refl IROutcome"));
    assert!(SRC_IR_KO_MACHINE_SOUND_WITNESS.contains("(l1 : Level) (l2 : Level)"));
    assert!(SRC_IR_KO_MACHINE_SOUND_WITNESS.contains("(ir_sp2 IRScalar.undef_ IRScalar.undef_)"));
}

/// All FIVE emitted arms are executed, including the default edge, and the
/// default-edge witness carries an unreadable payload.
#[test]
fn test_every_emitted_arm_has_an_executed_witness() {
    let witnesses = [
        (SRC_IR_KO_ON_ZERO, "ir_var ir_d0", "ir_d0"),
        (SRC_IR_KO_ON_SUCC, "ir_var ir_d1", "ir_d1"),
        (SRC_IR_KO_ON_MAX, "ir_var ir_d2", "ir_d2"),
        (SRC_IR_KO_ON_IMAX, "ir_var ir_d3", "ir_d3"),
        (SRC_IR_KO_ON_PARAM, "ir_var ir_d4", "ir_d4"),
    ];
    for (src, cell, ans) in witnesses {
        assert!(src.contains(cell), "witness must encode {cell}");
        assert!(src.contains(&format!("IRScalar.int_ {ans}")));
        assert!(src.contains("Eq.refl IROutcome"), "discharged by execution");
    }
    assert!(
        SRC_IR_KO_ON_PARAM.contains("IRScalar.undef_"),
        "the default-edge witness must carry an unreadable payload"
    );
}

/// The fuel bound must match the minted module's cost: 3 steps in the
/// entry block, 2 in an arm, 1 in the join.
#[test]
fn test_fuel_bound_matches_the_minted_module() {
    for src in [
        SRC_IR_KO_CORRECT,
        SRC_IR_KO_MACHINE_SOUND,
        SRC_IR_KO_MACHINE_SOUND_DENOT,
        SRC_IR_KO_NEVER_FAULTS,
    ] {
        assert!(src.contains("Le ir_d6 fuel"));
    }
    assert!(SRC_IR_KO_EXACT.contains("ir_run ir_d6 ir_ko_module"));
}

/// `level_kind_tag` (a LAYOUT claim) and `level_kind_ord` (the reflected
/// SOURCE function) coincide for `Level` and must stay separately stated,
/// so a layout change can move one without silently moving the other.
#[test]
fn test_tag_and_ord_are_separate_declarations() {
    assert!(SRC_LEVEL_KIND_TAG.starts_with("def level_kind_tag"));
    assert!(SRC_LEVEL_KIND_ORD.starts_with("def level_kind_ord"));
    assert_eq!(
        SRC_LEVEL_KIND_TAG.replace("level_kind_tag", "X"),
        SRC_LEVEL_KIND_ORD.replace("level_kind_ord", "X"),
        "they coincide today; that is a measured fact about Level, and it is \
             exactly why the two must remain distinguishable"
    );
    // the relation is stated with the LAYOUT function…
    assert!(SRC_ENCODESLEVELKINDCELL.contains("level_kind_tag"));
    // …and the theorem's conclusion with the SOURCE one
    assert!(SRC_IR_KO_CORRECT.contains("IRScalar.int_ (level_kind_ord l)"));
}

#[test]
fn test_sources_balanced_ascii() {
    let hand = [
        SRC_LEVEL_KIND_TAG,
        SRC_LEVEL_KIND_ORD,
        SRC_ENCODESLEVELKINDCELL,
        SRC_ENCODES_LEVEL_KIND_OF_ARC,
        SRC_IR_KO_EXACT,
        SRC_IR_KO_CORRECT,
        SRC_IR_KO_MACHINE_SOUND,
        SRC_LEVEL_KIND_ZERO_IS_ZERO,
        SRC_IR_KO_MACHINE_SOUND_DENOT,
        SRC_IR_KO_NEVER_FAULTS,
        SRC_IR_KO_KIND_BOUND,
    ];
    for src in hand
        .iter()
        .copied()
        .chain(ir_ko_module_defs().iter().copied())
    {
        assert!(src.is_ascii(), "spec sources stay ASCII");
        assert_eq!(src.matches('(').count(), src.matches(')').count());
    }
}
