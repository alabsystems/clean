// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The TENTH chain's LANE-DRIFT proofs** — the negative half of the gate.
//!
//! Every assertion here constructs a DRIFTED transcription and checks that the
//! pre-existing lanes still compare equal on it, so the lanes this chain added
//! are load-bearing by measurement rather than by argument. Split out of
//! `meta_tag_shl.rs` at the commit that creates it, following the ninth chain:
//! that file is the gate proper, this one is the proof that the gate can see.

use super::super::*;

/// **The assert lane is not decoration: without it the perturbations are
/// invisible.** The negative half — four drifted transcriptions, each of which
/// every PRE-EXISTING lane compares equal on.
#[test]
fn meta_tag_shl_the_assert_lane_catches_what_every_old_lane_misses() {
    let emitted = parse_emitted(&fixture("meta_tag_shl.trust-ir.txt"));
    let head = "rustcc fn @x(functy.130) {\nbb0:\n";
    let tail = "    %5 = sext i32 %1 to u64\n    %6 = shl u64 %0, %5\n    ret %6\n}\n";
    let prefix = "    %0 = const u64 1\n    %1 = const i32 63\n    \
                  %2 = bitcast i32 %1 to u32\n    %3 = const u32 64\n    \
                  %4 = icmp ult u32 %2, %3\n";

    // Drift 0: the assert DELETED. This is the body an unchecked shift would
    // emit, and before the assert lane it was indistinguishable from the
    // checked one on every lane except `order`.
    let no_assert = parse_emitted(&format!("{head}{prefix}{tail}"));
    assert_eq!(emitted.blocks, no_assert.blocks);
    assert_eq!(emitted.int_consts, no_assert.int_consts);
    assert_eq!(emitted.const_tys, no_assert.const_tys);
    assert_eq!(emitted.casts, no_assert.casts);
    assert_eq!(emitted.cast_tys, no_assert.cast_tys);
    assert_eq!(emitted.icmps, no_assert.icmps);
    assert_eq!(emitted.icmp_tys, no_assert.icmp_tys);
    assert_eq!(emitted.binops, no_assert.binops);
    assert_eq!(emitted.rets, no_assert.rets);
    assert_ne!(
        emitted.asserts, no_assert.asserts,
        "…and the ASSERT lane must: an unchecked shift is a different program"
    );

    // Drift 1: the assert on a DIFFERENT SSA id. %0 is the constant 1, which is
    // not even a Bool — `ir_assert_exec` would fault `type_error not_bool`.
    let wrong_scrutinee = parse_emitted(&format!("{head}{prefix}    assert %0\n{tail}"));
    assert_eq!(
        emitted.order, wrong_scrutinee.order,
        "the PROGRAM ORDER lane cannot see it — same nine classes, same nine result lists"
    );
    assert_eq!(emitted.icmps, wrong_scrutinee.icmps);
    assert_eq!(emitted.int_consts, wrong_scrutinee.int_consts);
    assert_ne!(
        emitted.asserts, wrong_scrutinee.asserts,
        "…and the ASSERT lane must"
    );

    // Drift 2: the assert MOVED after the shift — the check that happens too
    // late. Only the order lane can see this, and only the assert lane makes
    // the order lane's `assert` entry mean anything.
    let late = parse_emitted(&format!(
        "{head}{prefix}    %5 = sext i32 %1 to u64\n    %6 = shl u64 %0, %5\n    assert %4\n    \
         ret %6\n}}\n"
    ));
    assert_eq!(
        emitted.asserts, late.asserts,
        "the ASSERT lane cannot see a MOVE — it records what is asserted, not where"
    );
    assert_eq!(emitted.binops, late.binops);
    assert_ne!(
        emitted.order, late.order,
        "…and the PROGRAM ORDER lane must: a range check after the shift is not a range check"
    );

    // Drift 3: a THIRD constant dropped. The pre-2026-08-16 value lanes were
    // keyed by block, so bb0's three integer constants collapsed to one entry
    // and two of the three were never compared at all.
    let one_const = parse_emitted(&format!(
        "{head}    %0 = const u64 1\n    %1 = const i32 63\n    %2 = bitcast i32 %1 to u32\n    \
         %3 = const u32 99\n    %4 = icmp ult u32 %2, %3\n    assert %4\n{tail}"
    ));
    assert_eq!(emitted.order, one_const.order, "same classes, same results");
    assert_eq!(emitted.asserts, one_const.asserts);
    assert_eq!(emitted.casts, one_const.casts);
    assert_ne!(
        emitted.int_consts, one_const.int_consts,
        "…and the per-INSTRUCTION integer lane must: the width bound moved from 64 to 99, which \
         a block-keyed lane holding only the FIRST constant would not have seen"
    );

    // Drift 4: the two casts SWAPPED. Same operand, same result ids, same
    // count — only the opcode and the destination width move.
    let swapped = parse_emitted(&format!(
        "{head}    %0 = const u64 1\n    %1 = const i32 63\n    %2 = sext i32 %1 to u32\n    \
         %3 = const u32 64\n    %4 = icmp ult u32 %2, %3\n    assert %4\n    \
         %5 = bitcast i32 %1 to u64\n    %6 = shl u64 %0, %5\n    ret %6\n}}\n"
    ));
    assert_eq!(
        emitted.order, swapped.order,
        "both are `cast`, in both places"
    );
    assert_eq!(emitted.asserts, swapped.asserts);
    assert_eq!(emitted.int_consts, swapped.int_consts);
    assert_ne!(emitted.casts, swapped.casts, "…and the CAST lane must");
}

/// **A multi-result node is READ, and it was not before 2026-08-16.**
///
/// This body has none — but nine of the twenty-one assert-carrying CTFE flips
/// are `%2, %3 = mul.overflow usize %0, %1`, and until the program-order lane's
/// result slot became a list, `id_of("%2, %3")` returned `None`, the instruction
/// fell out of EVERY lane, and both sides recorded `u32::MAX`. This pins the
/// repair on the shape that needed it, so a future overflow chain inherits a
/// parser that reads it rather than one that drops it.
#[test]
fn meta_tag_shl_a_two_result_node_binds_two_ids_in_the_order_lane() {
    let two = parse_emitted(
        "rustcc fn @x(functy.29) {\nbb0:\n    %0 = const usize 16\n    %1 = const usize 1024\n    \
         %2, %3 = mul.overflow usize %0, %1\n    %6 = select bool %3, %4, %5\n    assert %6\n    \
         ret %2\n}\n",
    );
    let seq = two.order.get(&0).expect("bb0 must be in the order lane");
    assert_eq!(
        seq[2],
        ("mul.overflow".to_string(), vec![2u32, 3u32]),
        "BOTH results, in order: {seq:?}"
    );
    assert_eq!(
        seq[3],
        ("select".to_string(), vec![6u32]),
        "and a single-result node is a one-element list: {seq:?}"
    );
    assert_eq!(seq[4], ("assert".to_string(), vec![]), "{seq:?}");
    // The drift that used to be invisible: the two results EXCHANGED. The
    // wrapped product and the overflow flag are different values, and swapping
    // them makes the assert read the product and the return read the flag.
    let exchanged = parse_emitted(
        "rustcc fn @x(functy.29) {\nbb0:\n    %0 = const usize 16\n    %1 = const usize 1024\n    \
         %3, %2 = mul.overflow usize %0, %1\n    %6 = select bool %3, %4, %5\n    assert %6\n    \
         ret %2\n}\n",
    );
    assert_ne!(
        two.order, exchanged.order,
        "the exchanged results must be visible; before the slot was a list both read u32::MAX"
    );
}

/// **`usize` is why the OTHER nine assert-carrying CTFE flips are not chained,
/// and the gate refuses them rather than guessing.**
///
/// The `no_overflow` shape is every bit as available as this one — same seam,
/// same `markers_exact: true`, same `asserts=1`. Its operands are `usize`, and
/// resolving that to a width is a target assumption the ninth chain declined to
/// make. This test pins the refusal so the reason survives as a mechanism.
#[test]
fn meta_tag_shl_the_usize_shape_is_refused_rather_than_guessed() {
    let usize_body = parse_emitted(
        "rustcc fn @x(functy.29) {\nbb0:\n    %0 = const usize 16\n    %1 = const usize 1024\n    \
         ret %0\n}\n",
    );
    let tys = usize_body
        .const_tys
        .get(&0)
        .expect("the constants must be in the type lane");
    assert_eq!(tys[0].1, "?usize", "the loud token, not a guessed 64");
    assert_eq!(tys[1].1, "?usize");
    // …and this chain's own constants all resolve, which is why it is the one
    // that could be chained.
    let mine = parse_emitted(&fixture("meta_tag_shl.trust-ir.txt"));
    for tys in mine.const_tys.values() {
        for (r, ty) in tys {
            assert!(
                !ty.starts_with('?'),
                "this chain's const -> %{r} must RESOLVE, and it is why this body and not the \
                 `no_overflow` shape: {ty}"
            );
        }
    }
}
