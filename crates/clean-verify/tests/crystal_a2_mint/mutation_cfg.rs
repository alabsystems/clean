// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// **How coarse is CFG equality? Constructed, and re-measured.**
///
/// The A1 lane set has been extended seven times to close exactly this kind of
/// hole. As of the 2026-08-19 operand audit it reads operands, field indices,
/// block arguments, block parameters, instruction order, the load TYPE and the
/// load's VOLATILE flag — so the counterexample this test was originally
/// written around (a `volatile load` that no lane could see) is CLOSED, and
/// this test now pins it closed rather than pinning the hole open.
///
/// ONE field of the emitted instruction still has no lane and structurally
/// cannot get one: `Switch.exhaustive_enum_unreachable`. trust-ir's `Display`
/// matches `Inst::Switch { .., .. }` and never prints it, so it cannot even be
/// perturbed in the text. Its only in-repo witness is the artifact binary,
/// which is why reader B writes `?` there, the gate names the slot, and the
/// mutation matrix shows M3 catching a change to it while M2 and M5 cannot.
#[test]
fn cfg_lanes_pin_the_one_unprinted_core_field() {
    let base = parse_emitted(FIXTURE);
    assert_eq!(
        base.loads,
        std::collections::BTreeMap::from([(0u32, vec![(2u32, 0u32)])]),
        "the unmutated body loads through its receiver into %2"
    );

    // (1) `volatile` — CLOSED. Both readers see it, and they see the same thing.
    let volatile = FIXTURE.replace(
        "%2 = load enum.13, ptr %0",
        "%2 = volatile load enum.13, ptr %0",
    );
    assert_ne!(volatile, FIXTURE, "the substitution must bite");
    let v = parse_emitted(&volatile);
    assert_ne!(
        v.load_tys, base.load_tys,
        "the load-type lane carries the volatile flag and must see the change"
    );
    let a = canon(&core_b());
    let b = canon(&ir_mint::read_emitted(&volatile).expect("reader B"));
    assert_ne!(a, b, "and so must the core form");
    assert!(
        b.contains("(load ir_h2_tmode_canonical 0 true)") || b.contains(" 0 true)"),
        "…as the FLAG it is, not as a lost instruction:\n{b}"
    );

    // (2) `exhaustive_enum_unreachable` — still invisible, and the only one.
    assert!(
        !FIXTURE.contains("exhaustive"),
        "trust-ir's Display never prints this field; if it starts to, reader B should read it \
         and the unwitnessed ledger should shrink"
    );
    let (_, ledger) =
        ir_mint::mask_text_unwitnessed(&ir_mint::parse(ir_mint::IR_H2_CORE).expect("parse"))
            .expect("mask");
    assert_eq!(ledger.len(), 1, "exactly one unwitnessed slot: {ledger:?}");
}
