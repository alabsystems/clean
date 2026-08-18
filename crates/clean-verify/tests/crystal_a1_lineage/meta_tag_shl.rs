// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Links 2a and 2c for the TENTH complete chain — the first over a PANIC ARM
//! and the first over a CTFE flip:
//! `tc::local_context::LocalContext::push_low_local::META_TAG`.**
//!
//! ```text
//! bb0:
//!     %0 = const u64 1
//!     %1 = const i32 63
//!     %2 = bitcast i32 %1 to u32
//!     %3 = const u32 64
//!     %4 = icmp ult u32 %2, %3
//!     assert %4                      ; #proof: shift_in_range
//!     %5 = sext i32 %1 to u64
//!     %6 = shl u64 %0, %5
//!     ret %6
//! ```
//!
//! Nine nodes — the longest block any chain has transcribed — and three of them
//! were invisible to this gate before this lane:
//!
//! * **The `assert`.** It binds no result, carries no type and has no branch
//!   target, so it was in no lane at all. A transcription that DELETED it, or
//!   that asserted a different SSA id, agreed with the artifact on every lane
//!   the gate had. The `asserts` lane carries its scrutinee.
//! * **The three constants in ONE block.** The value lanes were one-per-BLOCK,
//!   and `assert_lanes` carried a ratchet that refused a body materializing two
//!   — naming the repair in its own message. They are per-instruction now, with
//!   the bound result id, and the ratchet is replaced by a check that no
//!   constant is left unread by all three.
//! * **The program-order lane's result slot**, which was one `u32` read with
//!   `unwrap_or(u32::MAX)`. A node binding two ids scored `MAX` on both sides
//!   whatever it bound — the shape of nine of the crate's twenty-one
//!   assert-carrying CTFE flips.
//!
//! Measured on `clean-kernel` itself at this HEAD, with the sealed lane-1
//! frontier stage1 trustc (`seal_driver.sh verify` OK and `guard` PASS before
//! the run), reproducing the frontier lane's three dump digests byte for byte:
//!
//! ```text
//! derived_mir.verdict        agreed  ("4 canonical line(s) identical")
//! derived_mir.markers_exact  true
//! interpreter differential   agreed  on 1 sampled input
//! unsupported                []
//! calls                      0 resolved / 0 extern / 0 unresolved
//! lineage                    sha256:501b50e5…
//! flip event                 FIRED, CTFE seam, same lineage, asserts=1, flipped_so_far=18
//! ```
//!
//! ## What these gates do NOT establish
//!
//! Structural correspondence, not a semantic proof that Clean's `IRInst.assert`
//! means what trust-ir's does. The lineage digest is RECORDED, not recomputed.
//! `ir_mt_module` is hand-transcribed: this makes an incorrect transcription
//! FAIL, it does not make a correct one automatic. And **link 2b is a CTFE flip,
//! which binds the constant's VALUE rather than an instruction sequence the
//! artifact executes** — see the module doc of `spec/core_spec/eval_ir_meta_tag.rs`
//! §"What LINK 2b means here", which states plainly where that is weaker than
//! the codegen form and the one axis on which it is stronger.

use super::*;

/// THE GATE: the module Clean proves about must be the module trustc emits.
#[test]
fn meta_tag_shl_proved_module_matches_the_emitted_artifact() {
    let text = fixture("meta_tag_shl.trust-ir.txt");
    assert!(
        text.starts_with(
            "rustcc fn @tc::local_context::LocalContext::push_low_local::META_TAG::{const-init}("
        ),
        "the fixture must be the META_TAG const-initializer itself"
    );
    let emitted = parse_emitted(&text);
    let clean = parse_clean(
        &clean_block_sources("eval_ir_meta_tag.rs", "const SRC_IR_MT_B0"),
        "def ir_mt_b0",
    );

    // COVERAGE DENOMINATOR — one block, nine nodes, and every one of them in a
    // lane. `order` is the only lane that sees all nine, and it is asserted in
    // full so a node dropped by any other lane is still counted here.
    assert_eq!(emitted.blocks, vec![0u32], "ONE block, bb0");
    assert_eq!(
        emitted.order,
        BTreeMap::from([(
            0,
            vec![
                ("const".to_string(), vec![0u32]),
                ("const".to_string(), vec![1]),
                ("cast".to_string(), vec![2]),
                ("const".to_string(), vec![3]),
                ("icmp".to_string(), vec![4]),
                ("assert".to_string(), vec![]),
                ("cast".to_string(), vec![5]),
                ("binop".to_string(), vec![6]),
                ("ret".to_string(), vec![]),
            ]
        )]),
        "NINE nodes in this order. The assert is the SIXTH and binds NOTHING; the two casts are \
         separated by the assert and read the same operand; and the shl comes AFTER the check, \
         which is the whole point of the body: {:?}",
        emitted.order
    );

    // THE PANIC ARM.
    assert_eq!(
        emitted.asserts,
        BTreeMap::from([(0, vec![4u32])]),
        "exactly one assert, on %4 — the result of the icmp, not on %0, %2 or %3: {:?}",
        emitted.asserts
    );
    assert!(
        text.contains("assert %4  ; #proof: shift_in_range"),
        "the emitted assert carries the producer's own proof obligation name, and it is the \
         SHIFT-RANGE one: the panic Rust would raise is `attempt to shift left with overflow`"
    );

    // The three constants, in one block, each with the SSA id it binds. Before
    // this lane the value lanes were keyed by block and kept ONE of these.
    assert_eq!(
        emitted.int_consts,
        BTreeMap::from([(0, vec![(0u32, 1u32), (1, 63), (3, 64)])]),
        "THREE integer constants in bb0: the shifted value 1 -> %0, the shift amount 63 -> %1, \
         and the width bound 64 -> %3. Each is a different number bound to a different id, and \
         the pre-2026-08-16 block-keyed lane compared exactly one of them: {:?}",
        emitted.int_consts
    );
    assert_eq!(
        emitted.const_tys,
        BTreeMap::from([(
            0,
            vec![
                (0u32, "uint64".to_string()),
                (1, "int32".to_string()),
                (3, "uint32".to_string()),
            ]
        )]),
        "THREE DIFFERENT TYPES, and every one is semantic: u64 is the shift's width, i32 is \
         SIGNED (which is why the body needs both a bitcast and a sext of the same constant), \
         and u32 is the comparison's width: {:?}",
        emitted.const_tys
    );
    assert!(
        emitted.consts.is_empty() && emitted.agg_consts.is_empty(),
        "no Bool and no aggregate constants: {:?} / {:?}",
        emitted.consts,
        emitted.agg_consts
    );

    // The two casts of ONE operand, and their four widths.
    assert_eq!(
        emitted.casts,
        BTreeMap::from([(
            0,
            vec![
                ("bitcast".to_string(), 2u32, 1u32),
                ("sext".to_string(), 5, 1),
            ]
        )]),
        "TWO casts, both reading %1 — the same constant — and binding different ids: {:?}",
        emitted.casts
    );
    assert_eq!(
        emitted.cast_tys,
        BTreeMap::from([(
            0,
            vec![
                (
                    "bitcast".to_string(),
                    2u32,
                    "int32".to_string(),
                    "uint32".to_string()
                ),
                (
                    "sext".to_string(),
                    5,
                    "int32".to_string(),
                    "uint64".to_string()
                ),
            ]
        )]),
        "the bitcast is i32 -> u32 (SAME width, a reinterpretation) and the sext is i32 -> u64 \
         (a WIDENING). Swapping them is a different program: at the i32 sign bit the bitcast \
         answers 2^31 and the sext answers 2^64 - 2^31, which is the executed pair \
         `ir_mt_bitcast_zero_extends_the_sign_bit` / `ir_mt_sext_sign_extends_the_same_pattern`: \
         {:?}",
        emitted.cast_tys
    );

    assert_eq!(
        emitted.icmps,
        BTreeMap::from([(0, vec![("ult".to_string(), 4u32, 2u32, 3u32)])]),
        "one comparison: %2 (the bitcast) ULT %3 (the bound). Operand order is the predicate — \
         `64 < amount` is the negation of what this body checks: {:?}",
        emitted.icmps
    );
    assert_eq!(
        emitted.icmp_tys,
        BTreeMap::from([(0, vec![("ult".to_string(), 4u32, "uint32".to_string())])]),
        "at width 32 — `ir_int_cmp` canonicalizes BOTH operands at it, and \
         `ir_mt_icmp_width_is_semantic` executes the same two operands at width 8 to the \
         OPPOSITE answer: {:?}",
        emitted.icmp_tys
    );
    assert_eq!(
        emitted.binops,
        BTreeMap::from([(0, vec![("shl".to_string(), 6u32, 0u32, 5u32)])]),
        "one arithmetic instruction: shl of %0 by %5. `shl %5, %0` is a different number: {:?}",
        emitted.binops
    );
    assert_eq!(
        emitted.binop_tys,
        BTreeMap::from([(0, vec![("shl".to_string(), 6u32, "uint64".to_string())])]),
        "at width 64 — the width is BOTH the modulus and the shl's own range bound, so at width \
         32 this body's shift of 63 would be `ub shift_oob` instead of a value: {:?}",
        emitted.binop_tys
    );
    assert_eq!(
        emitted.rets,
        BTreeMap::from([(0, vec![6u32])]),
        "the body returns %6 — the SHIFTED value, not %0 the constant 1 and not %5 the amount: \
         {:?}",
        emitted.rets
    );

    assert!(
        emitted.condbrs.is_empty()
            && emitted.cases.is_empty()
            && emitted.branches.is_empty()
            && emitted.loads.is_empty()
            && emitted.extracts.is_empty()
            && emitted.param_blocks.is_empty()
            && emitted.edge_args.is_empty()
            && emitted.block_params.is_empty(),
        "one block: this body branches nowhere, reads no field, loads nothing and joins nothing"
    );
    assert_eq!(emitted.default, u32::MAX, "no switch");
    assert_eq!(emitted.switch_on, u32::MAX, "…and therefore no scrutinee");

    // ZERO parameters — the first chain whose subject takes none. The entry
    // header is bare `bb0:`, and the registered IRFunc must bind `ir_nl0`.
    assert!(
        text.contains("\nbb0:\n"),
        "the entry block takes NO parameters: a const initializer has none, which is what makes \
         A4 quantify over nothing but the heap and the fuel"
    );
    let func = clean_block_sources("eval_ir_meta_tag.rs", "const SRC_IR_MT_FUNC");
    assert!(
        func.contains("IRFunc.mk ir_d0 ir_nl0 ir_d0"),
        "the registered IRFunc must bind NO parameters: {func}"
    );

    assert_eq!(
        emitted.blocks, clean.blocks,
        "block set differs: emitted {:?} vs Clean {:?}",
        emitted.blocks, clean.blocks
    );
    assert_eq!(
        emitted.int_consts, clean.int_consts,
        "per-instruction INTEGER constants differ: emitted {:?} vs Clean {:?}. Three constants \
         in one block; the block-keyed lane this replaced compared one of them.",
        emitted.int_consts, clean.int_consts
    );
    assert_eq!(
        emitted.consts, clean.consts,
        "per-instruction BOOL constants differ: emitted {:?} vs Clean {:?}. BOTH must be empty.",
        emitted.consts, clean.consts
    );
    assert_eq!(
        emitted.agg_consts, clean.agg_consts,
        "per-instruction AGGREGATE constants differ: emitted {:?} vs Clean {:?}. BOTH empty.",
        emitted.agg_consts, clean.agg_consts
    );
    assert_eq!(
        emitted.asserts, clean.asserts,
        "ASSERT lane differs: emitted {:?} vs Clean {:?}",
        emitted.asserts, clean.asserts
    );
    assert_entry_params(
        &text,
        &clean_block_sources("eval_ir_meta_tag.rs", "const SRC_IR_MT_FUNC"),
        "meta_tag_shl",
    );
    assert_lanes(&emitted, &clean, "meta_tag_shl");
    assert!(
        !text.contains("unreachable"),
        "the emitted body has no trap block; a Clean module with one is not this body"
    );
    assert!(
        !text.contains("call @func."),
        "the body must make no calls — that is what makes its reachable closure bodyful"
    );
}

/// **WHERE THE ASSERT GOES WHEN IT FAILS — read off the registered spec source,
/// because trust-ir has no target operand for it to be read off the artifact.**
///
/// Every other lane compares two sides. The failing edge has only one: the
/// instruction carries a scrutinee and nothing else, and where control goes on
/// `false` is fixed by the SEMANTICS. So the gate reads the registered
/// declarations and requires the outcome to be the panic — and requires the
/// two-sidedness to be structural (`Bool.rec` over both minors) rather than a
/// statement about the arm this body happens to take.
///
/// This is the lane's honest form, and it is what makes the perturbation
/// "redirect the assert's failure target" a REAL case: change
/// `IROutcome.ub IRFault.assert_failed` in the registered theorem and this goes
/// red, naming it.
#[test]
fn meta_tag_shl_the_failing_arm_is_pinned_to_the_panic_outcome() {
    let dichotomy = clean_block_sources("eval_ir_meta_tag.rs", "const SRC_IR_MT_DICHOTOMY");
    // COUNTED, not `contains`. The theorem names each arm THREE times — in the
    // statement, in the proof's motive and in its minor — so a `contains` test
    // passes while one of the three has been redirected. The perturbation
    // battery found exactly that: P8 and P9 mutated the statement's arm and the
    // gate stayed green off the surviving copies.
    assert_eq!(
        dichotomy
            .matches("(IRConfig.halted (IROutcome.ub IRFault.assert_failed))")
            .count(),
        3,
        "the FALSE arm of the assert must be `ub assert_failed` — a Rust panic, and at CTFE a \
         hard error that means there is no artifact — in the statement, the motive AND the \
         minor. Got: {dichotomy}"
    );
    assert_eq!(
        dichotomy.matches("(ir_advance s)").count(),
        3,
        "…and the TRUE arm must ADVANCE, not bind a result, in all three places: {dichotomy}"
    );
    assert!(
        !dichotomy.contains("IRFault.unreachable") && !dichotomy.contains("IRFault.not_bool"),
        "…and the failing arm must be the ASSERT's fault tag, not another one: {dichotomy}"
    );
    assert!(
        dichotomy.contains("(b : Bool)") && dichotomy.contains("(s : IRMachine)"),
        "…for BOTH truth values and EVERY machine state, or it is a statement about this body's \
         own arm rather than about the instruction: {dichotomy}"
    );
    assert_eq!(
        dichotomy.matches("Bool.rec").count(),
        3,
        "the two-sidedness must be structural — a `Bool.rec` in the statement's image, one as \
         the proof's recursor and one as its motive: {dichotomy}"
    );
    // …and the failing arm must be reachable on this body's own shape, not
    // only in the abstract. The OOB counterfactual is that, and it must differ
    // from the shipped module in exactly the shift amount.
    let oob = clean_block_sources("eval_ir_meta_tag.rs", "const SRC_IR_MT_OOB_TRAPS");
    assert!(
        oob.contains("(IROutcome.ub IRFault.assert_failed)"),
        "the executed counterfactual must reach the panic: {oob}"
    );
    assert_eq!(
        oob.matches("ir_mt_oob_module").count(),
        1,
        "…and it must RUN THE COUNTERFACTUAL. Pointing it at `ir_mt_module` would make the \
         recorded panic a claim about the body that returns a value — the battery's P10, which \
         was green until this assertion existed: {oob}"
    );
    assert!(
        !oob.contains("ir_run ir_d9 ir_mt_module"),
        "…explicitly: not the shipped module: {oob}"
    );
    let mine = clean_block_sources("eval_ir_meta_tag.rs", "const SRC_IR_MT_B0");
    let counterfactual = clean_block_sources("eval_ir_meta_tag.rs", "const SRC_IR_MT_OOB_B0");
    assert!(
        mine.contains("IRConst.int_ 63") && counterfactual.contains("IRConst.int_ 64"),
        "the counterfactual changes the SHIFT AMOUNT and nothing else"
    );
    assert!(
        !counterfactual.contains("IRConst.int_ 63"),
        "…and it must not still carry 63, or it is the shipped body under another name"
    );
    // The any-fuel statement: nothing after the assert runs.
    let any_fuel = clean_block_sources("eval_ir_meta_tag.rs", "const SRC_IR_MT_OOB_ANY_FUEL");
    assert!(
        any_fuel.contains("(g : Nat)") && any_fuel.contains("Nat.add g ir_d6"),
        "the terminality of the failing arm must hold at EVERY fuel, not at one: {any_fuel}"
    );
}

// The LANE-DRIFT proofs — four drifted transcriptions per lane, and the
// multi-result and `?usize` cases. Split out at the commit that creates it, so
// this lane's `files_over_500` delta is ZERO.
#[path = "meta_tag_shl_drift.rs"]
mod drift;

// The A0/A6 EVIDENCE gates — the measured row, the CTFE-seam census, the
// twenty-one candidates, and what link 2b does and does not bind.
#[path = "meta_tag_shl_evidence.rs"]
mod evidence;
