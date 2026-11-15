// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Checked freshness and allocation rules for the actual byte-memory profile.
//!
//! Strict high-water evidence refers to every real allocation record, including
//! retired records. It is stronger than the existing world-owner check, and is
//! not inferred from that check. Freshness must survive provider/import effects
//! separately. These laws do not assert native allocator fidelity.

use crate::spec::{SpecError, Specification};

const HIGH_WATER: &str = r"def ir_byte_high_water_v1
  (allocs : IRList IRByteAllocationV1) (cursor : Nat) : Prop :=
@IRList.rec IRByteAllocationV1 (fun (_ : IRList IRByteAllocationV1) => Prop)
  True
  (fun (a : IRByteAllocationV1) (_ : IRList IRByteAllocationV1) (ih : Prop) =>
    And (Nat.lt (Nat.add (ir_byte_alloc_base_v1 a) (ir_byte_alloc_size_v1 a)) cursor) ih) allocs";

const FRESH_MEMORY: &str = r"def ir_byte_fresh_memory_v1
  (allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat)
  (base size owner : Nat) : IRByteMemoryV1 :=
IRByteMemoryV1.mk
  (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk base size owner Bool.true) allocs)
  (ir_byte_clear_v1 bytes base size) (Nat.succ (Nat.add base size))";

const POSITIVE: &str = r"def ir_byte_allocation_pos_v1 (n : Nat) (positive : Nat.lt 0 n) :
@Eq Bool (ir_nat_pos n) Bool.true :=
@Nat.rec (fun (x : Nat) => Nat.lt 0 x -> @Eq Bool (ir_nat_pos x) Bool.true)
  (fun (bad : Nat.lt 0 0) => @False.elim (@Eq Bool Bool.false Bool.true)
    (Nat.not_succ_le_zero 0 bad))
  (fun (x : Nat) (_ : Nat.lt 0 x -> @Eq Bool (ir_nat_pos x) Bool.true) =>
    fun (_ : Nat.lt 0 (Nat.succ x)) => @Eq.refl Bool Bool.true) n positive";

const LT_FALSE: &str = r"def ir_byte_allocation_ltb_false_v1
  (a b : Nat) (ge : Nat.le b a) : @Eq Bool (ir_nat_ltb a b) Bool.false :=
@Eq.trans Bool (ir_nat_ltb a b) (ir_nat_ltb_walk a b) Bool.false
  (ir_nat_ltb_walk_eq a b)
  (@Nat.rec
    (fun (x : Nat) => forall (y : Nat), Nat.le y x -> @Eq Bool (ir_nat_ltb_walk x y) Bool.false)
    (fun (y : Nat) => @Nat.rec
      (fun (z : Nat) => Nat.le z 0 -> @Eq Bool (ir_nat_ltb_walk 0 z) Bool.false)
      (fun (_ : Nat.le 0 0) => @Eq.refl Bool Bool.false)
      (fun (z : Nat) (_ : Nat.le z 0 -> @Eq Bool (ir_nat_ltb_walk 0 z) Bool.false) =>
        fun (bad : Nat.le (Nat.succ z) 0) => @False.elim (@Eq Bool Bool.true Bool.false)
          (Nat.not_succ_le_zero z bad)) y)
    (fun (x : Nat)
      (ih : forall (y : Nat), Nat.le y x -> @Eq Bool (ir_nat_ltb_walk x y) Bool.false) =>
      fun (y : Nat) => @Nat.rec
        (fun (z : Nat) => Nat.le z (Nat.succ x) -> @Eq Bool (ir_nat_ltb_walk (Nat.succ x) z) Bool.false)
        (fun (_ : Nat.le 0 (Nat.succ x)) => @Eq.refl Bool Bool.false)
        (fun (z : Nat) (_ : Nat.le z (Nat.succ x) -> @Eq Bool (ir_nat_ltb_walk (Nat.succ x) z) Bool.false) =>
          fun (h : Nat.le (Nat.succ z) (Nat.succ x)) => ih z (Nat.le_of_succ_le_succ z x h)) y)
    a b ge)";

const LE_FALSE: &str = r"def ir_byte_allocation_leb_false_v1
  (a b : Nat) (gt : Nat.lt b a) : @Eq Bool (ir_nat_leb a b) Bool.false :=
@Eq.trans Bool (ir_nat_leb a b) (ir_nat_leb_walk a b) Bool.false
  (ir_nat_leb_walk_eq a b)
  (@Nat.rec
    (fun (x : Nat) => forall (y : Nat), Nat.lt y x -> @Eq Bool (ir_nat_leb_walk x y) Bool.false)
    (fun (y : Nat) (bad : Nat.lt y 0) => @False.elim (@Eq Bool (ir_nat_leb_walk 0 y) Bool.false)
      (Nat.not_succ_le_zero y bad))
    (fun (x : Nat)
      (ih : forall (y : Nat), Nat.lt y x -> @Eq Bool (ir_nat_leb_walk x y) Bool.false) =>
      fun (y : Nat) => @Nat.rec
        (fun (z : Nat) => Nat.lt z (Nat.succ x) -> @Eq Bool (ir_nat_leb_walk (Nat.succ x) z) Bool.false)
        (fun (_ : Nat.lt 0 (Nat.succ x)) => @Eq.refl Bool Bool.false)
        (fun (z : Nat) (_ : Nat.lt z (Nat.succ x) -> @Eq Bool (ir_nat_leb_walk (Nat.succ x) z) Bool.false) =>
          fun (h : Nat.lt (Nat.succ z) (Nat.succ x)) => ih z (Nat.le_of_succ_le_succ (Nat.succ z) x h)) y)
    a b gt)";

const AND_FALSE: &str = r"def ir_byte_allocation_and_false_v1 (a b : Bool)
  (h : @Eq Bool b Bool.false) : @Eq Bool (Bool.and a b) Bool.false :=
@Bool.rec (fun (x : Bool) => @Eq Bool (Bool.and x b) Bool.false)
  (@Eq.refl Bool Bool.false) h a";

const POINTER_VALUE: &str = r"def ir_byte_allocation_pointer_value_v1
  (address : Nat) (positive : Nat.lt 0 address) :
@Eq IRScalar (ir_byte_pointer_value_v1 address) (IRScalar.ptr_ address) :=
@Nat.rec (fun (n : Nat) => Nat.lt 0 n -> @Eq IRScalar (ir_byte_pointer_value_v1 n) (IRScalar.ptr_ n))
  (fun (bad : Nat.lt 0 0) => @False.elim (@Eq IRScalar IRScalar.nullptr_ (IRScalar.ptr_ 0))
    (Nat.not_succ_le_zero 0 bad))
  (fun (n : Nat) (_ : Nat.lt 0 n -> @Eq IRScalar (ir_byte_pointer_value_v1 n) (IRScalar.ptr_ n)) =>
    fun (_ : Nat.lt 0 (Nat.succ n)) => @Eq.refl IRScalar (IRScalar.ptr_ (Nat.succ n))) address positive";

const HIGH_WATER_RAISE: &str = r"def ir_byte_high_water_raise_v1
  (allocs : IRList IRByteAllocationV1) (cursor bound : Nat)
  (above : Nat.le cursor bound) (before : ir_byte_high_water_v1 allocs cursor) :
ir_byte_high_water_v1 allocs bound :=
@IRList.rec IRByteAllocationV1
  (fun (xs : IRList IRByteAllocationV1) => ir_byte_high_water_v1 xs cursor -> ir_byte_high_water_v1 xs bound)
  (fun (_ : True) => True.intro)
  (fun (a : IRByteAllocationV1) (tail : IRList IRByteAllocationV1)
    (ih : ir_byte_high_water_v1 tail cursor -> ir_byte_high_water_v1 tail bound) =>
    fun (h : And (Nat.lt (Nat.add (ir_byte_alloc_base_v1 a) (ir_byte_alloc_size_v1 a)) cursor)
      (ir_byte_high_water_v1 tail cursor)) =>
    @And.intro (Nat.lt (Nat.add (ir_byte_alloc_base_v1 a) (ir_byte_alloc_size_v1 a)) bound)
      (ir_byte_high_water_v1 tail bound)
      (@Nat.le_trans (Nat.succ (Nat.add (ir_byte_alloc_base_v1 a) (ir_byte_alloc_size_v1 a))) cursor bound
        (@And.left (Nat.lt (Nat.add (ir_byte_alloc_base_v1 a) (ir_byte_alloc_size_v1 a)) cursor)
          (ir_byte_high_water_v1 tail cursor) h) above)
      (ih (@And.right (Nat.lt (Nat.add (ir_byte_alloc_base_v1 a) (ir_byte_alloc_size_v1 a)) cursor)
        (ir_byte_high_water_v1 tail cursor) h))) allocs before";

const HIGH_WATER_RETIRE: &str = r"def ir_byte_high_water_retire_v1
  (owner : Nat) (allocs : IRList IRByteAllocationV1) (cursor : Nat)
  (before : ir_byte_high_water_v1 allocs cursor) :
ir_byte_high_water_v1 (ir_byte_retire_allocs_v1 owner allocs) cursor :=
@IRList.rec IRByteAllocationV1
  (fun (xs : IRList IRByteAllocationV1) => ir_byte_high_water_v1 xs cursor ->
    ir_byte_high_water_v1 (ir_byte_retire_allocs_v1 owner xs) cursor)
  (fun (_ : True) => True.intro)
  (fun (a : IRByteAllocationV1) (tail : IRList IRByteAllocationV1)
    (ih : ir_byte_high_water_v1 tail cursor -> ir_byte_high_water_v1 (ir_byte_retire_allocs_v1 owner tail) cursor) =>
    fun (h : And (Nat.lt (Nat.add (ir_byte_alloc_base_v1 a) (ir_byte_alloc_size_v1 a)) cursor)
      (ir_byte_high_water_v1 tail cursor)) =>
    @And.intro (Nat.lt (Nat.add (ir_byte_alloc_base_v1 a) (ir_byte_alloc_size_v1 a)) cursor)
      (ir_byte_high_water_v1 (ir_byte_retire_allocs_v1 owner tail) cursor)
      (@And.left (Nat.lt (Nat.add (ir_byte_alloc_base_v1 a) (ir_byte_alloc_size_v1 a)) cursor)
        (ir_byte_high_water_v1 tail cursor) h)
      (ih (@And.right (Nat.lt (Nat.add (ir_byte_alloc_base_v1 a) (ir_byte_alloc_size_v1 a)) cursor)
        (ir_byte_high_water_v1 tail cursor) h))) allocs before";

const HIGH_WATER_FRESH: &str = r"def ir_byte_high_water_fresh_v1
  (allocs : IRList IRByteAllocationV1) (cursor base size owner : Nat)
  (above : Nat.le cursor base) (before : ir_byte_high_water_v1 allocs cursor) :
ir_byte_high_water_v1
  (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk base size owner Bool.true) allocs)
  (Nat.succ (Nat.add base size)) :=
@And.intro (Nat.lt (Nat.add base size) (Nat.succ (Nat.add base size)))
  (ir_byte_high_water_v1 allocs (Nat.succ (Nat.add base size)))
  (Nat.le_refl (Nat.succ (Nat.add base size)))
  (ir_byte_high_water_raise_v1 allocs cursor (Nat.succ (Nat.add base size))
    (@Nat.le_trans cursor (Nat.add base size) (Nat.succ (Nat.add base size))
      (@Nat.le_trans cursor base (Nat.add base size) above (Nat.le_add_right base size))
      (Nat.le_add_right (Nat.add base size) 1)) before)";

fn and(a: &str, b: &str) -> String {
    format!("(Bool.and {a} {b})")
}

fn join(a: &str, b: &str, pa: &str, pb: &str) -> String {
    format!("(ir_byte_world_and_intro_v1 {a} {b} {pa} {pb})")
}

fn conjunction(parts: &[(String, String)]) -> (String, String) {
    let Some((last, prefix)) = parts.split_last() else {
        return (
            "Bool.true".to_owned(),
            "(@Eq.refl Bool Bool.true)".to_owned(),
        );
    };
    prefix.iter().rev().fold(
        (last.0.to_owned(), last.1.clone()),
        |(tail, proof), (head, head_proof)| {
            (and(head, &tail), join(head, &tail, head_proof, &proof))
        },
    )
}

fn fresh_row() -> &'static str {
    "(IRByteAllocationV1.mk base size owner Bool.true)"
}

fn fresh_allocs() -> String {
    format!("(@IRList.cons IRByteAllocationV1 {} allocs)", fresh_row())
}

fn cover_source() -> (&'static str, String) {
    let (valid, valid_proof) = conjunction(&[
        (
            "(ir_nat_pos base)".into(),
            "(ir_byte_allocation_pos_v1 base basePositive)".into(),
        ),
        (
            "(ir_nat_pos size)".into(),
            "(ir_byte_allocation_pos_v1 size sizePositive)".into(),
        ),
        (
            "(ir_nat_leb (Nat.add base size) ir_byte_limit_v1)".into(),
            "(ir_byte_leb_of_le_v1 (Nat.add base size) ir_byte_limit_v1 bounded)".into(),
        ),
    ]);
    let (_, proof) = conjunction(&[
        (valid, valid_proof),
        ("Bool.true".into(), "(@Eq.refl Bool Bool.true)".into()),
        (
            "(ir_nat_leb base address)".into(),
            "(ir_byte_leb_of_le_v1 base address lower)".into(),
        ),
        (
            "(ir_nat_leb (Nat.add address width) (Nat.add base size))".into(),
            "(ir_byte_leb_of_le_v1 (Nat.add address width) (Nat.add base size) upper)".into(),
        ),
    ]);
    (
        "ir_byte_fresh_cover_v1",
        format!(
            "def ir_byte_fresh_cover_v1 (base size owner address width : Nat)\n\
      (basePositive : Nat.lt 0 base) (sizePositive : Nat.lt 0 size)\n\
      (bounded : Nat.le (Nat.add base size) ir_byte_limit_v1)\n\
      (lower : Nat.le base address) (upper : Nat.le (Nat.add address width) (Nat.add base size)) :\n\
      @Eq Bool (ir_byte_cover_v1 {} address width) Bool.true := {proof}",
            fresh_row()
        ),
    )
}

fn overlap_source() -> (&'static str, String) {
    let inside = "(@Nat.add_lt_add_left 0 width widthPositive address)";
    let start_lt_end = format!(
        "(@Nat.le_trans (Nat.succ base) (Nat.succ address) (Nat.add address width)\n\
      (@Nat.succ_le_succ base address lower) {inside})"
    );
    let before_end = format!(
        "(@Nat.le_trans (Nat.succ address) (Nat.add address width) (Nat.add base size) {inside} upper)"
    );
    let (_, proof) = conjunction(&[
        (
            "(ir_nat_pos size)".into(),
            "(ir_byte_allocation_pos_v1 size sizePositive)".into(),
        ),
        (
            "(ir_nat_pos width)".into(),
            "(ir_byte_allocation_pos_v1 width widthPositive)".into(),
        ),
        (
            "(ir_nat_ltb base (Nat.add address width))".into(),
            format!("(ir_byte_ltb_of_lt_v1 base (Nat.add address width) {start_lt_end})"),
        ),
        (
            "(ir_nat_ltb address (Nat.add base size))".into(),
            format!("(ir_byte_ltb_of_lt_v1 address (Nat.add base size) {before_end})"),
        ),
    ]);
    (
        "ir_byte_fresh_overlap_v1",
        format!(
            "def ir_byte_fresh_overlap_v1 (base size owner address width : Nat)\n\
      (sizePositive : Nat.lt 0 size) (widthPositive : Nat.lt 0 width)\n\
      (lower : Nat.le base address) (upper : Nat.le (Nat.add address width) (Nat.add base size)) :\n\
      @Eq Bool (ir_byte_overlaps_v1 {} address width) Bool.true := {proof}",
            fresh_row()
        ),
    )
}

fn point_source() -> (&'static str, String) {
    let (guard, row_proof) = conjunction(&[
        (
            "(ir_nat_leb base address)".into(),
            "(ir_byte_leb_of_le_v1 base address lower)".into(),
        ),
        (
            "(ir_nat_leb address (Nat.add base size))".into(),
            "(ir_byte_leb_of_le_v1 address (Nat.add base size) upper)".into(),
        ),
    ]);
    let count = "(ir_byte_point_count_v1 allocs address)";
    let zero = "(ir_byte_high_water_point_count_v1 allocs cursor address (@Nat.le_trans cursor base address above lower) before)";
    (
        "ir_byte_fresh_point_count_v1",
        format!(
            "def ir_byte_fresh_point_count_v1\n\
      (allocs : IRList IRByteAllocationV1) (cursor base size owner address : Nat)\n\
      (above : Nat.le cursor base) (before : ir_byte_high_water_v1 allocs cursor)\n\
      (lower : Nat.le base address) (upper : Nat.le address (Nat.add base size)) :\n\
      @Eq Nat (ir_byte_point_count_v1 {} address) 1 :=\n\
      @Eq.trans Nat (ir_byte_point_count_v1 {} address) (Nat.succ {count}) 1\n\
        (ir_eq_cong Bool Nat (fun (inside : Bool) => @Bool.rec (fun (_ : Bool) => Nat) {count} (Nat.succ {count}) inside)\n\
          {guard} Bool.true {row_proof})\n\
        (ir_eq_cong Nat Nat Nat.succ {count} 0 {zero})",
            fresh_allocs(),
            fresh_allocs()
        ),
    )
}

fn accessible_source() -> (&'static str, String) {
    let row = fresh_row();
    let allocs = fresh_allocs();
    let count = "(ir_byte_overlap_count_v1 allocs address width)";
    let total = format!("(ir_byte_overlap_count_v1 {allocs} address width)");
    let count_one = format!(
        "(@Eq.trans Nat {total} (Nat.succ {count}) 1\n\
      (ir_eq_cong Bool Nat (fun (overlap : Bool) => @Bool.rec (fun (_ : Bool) => Nat) {count} (Nat.succ {count}) overlap)\n\
        (ir_byte_overlaps_v1 {row} address width) Bool.true\n\
        (ir_byte_fresh_overlap_v1 base size owner address width sizePositive widthPositive lower upper))\n\
      (ir_eq_cong Nat Nat Nat.succ {count} 0\n\
        (ir_byte_high_water_overlap_count_v1 allocs cursor address width (@Nat.le_trans cursor base address above lower) before)))"
    );
    let (_, proof) = conjunction(&[
        ("(ir_nat_pos address)".into(),
         "(ir_byte_allocation_pos_v1 address (@Nat.le_trans 1 base address basePositive lower))".into()),
        ("(ir_nat_pos width)".into(), "(ir_byte_allocation_pos_v1 width widthPositive)".into()),
        ("(ir_nat_leb (Nat.add address width) ir_byte_limit_v1)".into(),
         "(ir_byte_leb_of_le_v1 (Nat.add address width) ir_byte_limit_v1 (@Nat.le_trans (Nat.add address width) (Nat.add base size) ir_byte_limit_v1 upper bounded))".into()),
        ("(ir_byte_alignment_v1 align)".into(), "alignment".into()),
        ("(ir_nat_eqb (Nat.mod address align) 0)".into(),
         "(ir_eq_cong Nat Bool (fun (r : Nat) => ir_nat_eqb r 0) (Nat.mod address align) 0 divisible)".into()),
        (format!("(ir_nat_eqb {total} 1)"),
         format!("(ir_eq_cong Nat Bool (fun (n : Nat) => ir_nat_eqb n 1) {total} 1 {count_one})")),
        (format!("(ir_byte_any_cover_v1 {allocs} address width)"),
         format!("(ir_byte_lifetime_or_head_v1 (ir_byte_cover_v1 {row} address width) (ir_byte_any_cover_v1 allocs address width)\n\
           (ir_byte_fresh_cover_v1 base size owner address width basePositive sizePositive bounded lower upper))")),
    ]);
    (
        "ir_byte_fresh_accessible_v1",
        format!(
            "def ir_byte_fresh_accessible_v1\n\
      (allocs : IRList IRByteAllocationV1) (cursor base size owner address width align : Nat)\n\
      (above : Nat.le cursor base) (before : ir_byte_high_water_v1 allocs cursor)\n\
      (basePositive : Nat.lt 0 base) (sizePositive : Nat.lt 0 size) (widthPositive : Nat.lt 0 width)\n\
      (bounded : Nat.le (Nat.add base size) ir_byte_limit_v1)\n\
      (lower : Nat.le base address) (upper : Nat.le (Nat.add address width) (Nat.add base size))\n\
      (alignment : @Eq Bool (ir_byte_alignment_v1 align) Bool.true)\n\
      (divisible : @Eq Nat (Nat.mod address align) 0) :\n\
      @Eq Bool (ir_byte_accessible_v1 {allocs} address width align) Bool.true := {proof}"
        ),
    )
}

fn same_allocation_source() -> (&'static str, String) {
    let row = fresh_row();
    let allocs = fresh_allocs();
    let point = |address: &str, lower: &str, upper: &str| {
        let count = format!("(ir_byte_point_count_v1 {allocs} {address})");
        (
            format!("(ir_nat_eqb {count} 1)"),
            format!(
                "(ir_eq_cong Nat Bool (fun (n : Nat) => ir_nat_eqb n 1) {count} 1\n\
          (ir_byte_fresh_point_count_v1 allocs cursor base size owner {address} above before {lower} {upper}))"
            ),
        )
    };
    let (cover_pair, cover_proof) = conjunction(&[
        (format!("(ir_byte_cover_v1 {row} base 0)"),
         "(ir_byte_fresh_cover_v1 base size owner base 0 basePositive sizePositive bounded (Nat.le_refl base) (Nat.le_add_right base size))".into()),
        (format!("(ir_byte_cover_v1 {row} address 0)"),
         "(ir_byte_fresh_cover_v1 base size owner address 0 basePositive sizePositive bounded lower upper)".into()),
    ]);
    let tail =
        "(@IRList.rec IRByteAllocationV1 (fun (_ : IRList IRByteAllocationV1) => Bool) Bool.false\n\
      (fun (a : IRByteAllocationV1) (_ : IRList IRByteAllocationV1) (ih : Bool) =>\n\
        Bool.or (Bool.and (ir_byte_cover_v1 a base 0) (ir_byte_cover_v1 a address 0)) ih) allocs)";
    let (_, proof) = conjunction(&[
        point("base", "(Nat.le_refl base)", "(Nat.le_add_right base size)"),
        point("address", "lower", "upper"),
        (
            format!("(Bool.or {cover_pair} {tail})"),
            format!("(ir_byte_lifetime_or_head_v1 {cover_pair} {tail} {cover_proof})"),
        ),
    ]);
    (
        "ir_byte_fresh_same_allocation_v1",
        format!(
            "def ir_byte_fresh_same_allocation_v1\n\
      (allocs : IRList IRByteAllocationV1) (cursor base size owner address : Nat)\n\
      (above : Nat.le cursor base) (before : ir_byte_high_water_v1 allocs cursor)\n\
      (basePositive : Nat.lt 0 base) (sizePositive : Nat.lt 0 size)\n\
      (bounded : Nat.le (Nat.add base size) ir_byte_limit_v1)\n\
      (lower : Nat.le base address) (upper : Nat.le address (Nat.add base size)) :\n\
      @Eq Bool (ir_byte_same_allocation_v1 {allocs} base address) Bool.true := {proof}"
        ),
    )
}

fn allocate_source() -> (&'static str, String) {
    let base = "(ir_byte_aligned_base_v1 cursor align)";
    let end = format!("(Nat.add {base} size)");
    let cursor_le_end =
        format!("(@Nat.le_trans cursor {base} {end} above (Nat.le_add_right {base} size))");
    let cursor_lt_limit = format!(
        "(@Nat.le_trans (Nat.succ cursor) (Nat.succ {end}) ir_byte_limit_v1\n\
      (@Nat.succ_le_succ cursor {end} {cursor_le_end}) room)"
    );
    let count = format!("(ir_byte_overlap_count_v1 allocs {base} size)");
    let (guard, proof) = conjunction(&[
        (
            "(ir_nat_pos cursor)".into(),
            "(ir_byte_allocation_pos_v1 cursor cursorPositive)".into(),
        ),
        (
            "(ir_nat_ltb cursor ir_byte_limit_v1)".into(),
            format!("(ir_byte_ltb_of_lt_v1 cursor ir_byte_limit_v1 {cursor_lt_limit})"),
        ),
        (
            "(ir_nat_pos size)".into(),
            "(ir_byte_allocation_pos_v1 size sizePositive)".into(),
        ),
        ("(ir_byte_alignment_v1 align)".into(), "alignment".into()),
        (
            format!("(ir_nat_pos {base})"),
            format!(
                "(ir_byte_allocation_pos_v1 {base} (@Nat.le_trans 1 cursor {base} cursorPositive above))"
            ),
        ),
        (
            format!("(ir_nat_ltb {end} ir_byte_limit_v1)"),
            format!("(ir_byte_ltb_of_lt_v1 {end} ir_byte_limit_v1 room)"),
        ),
        (
            format!("(ir_nat_eqb {count} 0)"),
            format!(
                "(ir_eq_cong Nat Bool (fun (n : Nat) => ir_nat_eqb n 0) {count} 0\n\
          (ir_byte_high_water_overlap_count_v1 allocs cursor {base} size above before))"
            ),
        ),
    ]);
    let mem = "(IRByteMemoryV1.mk allocs bytes cursor)";
    let expected = format!(
        "(IRByteMemoryResultV1.value (IRScalar.ptr_ {base}) (ir_byte_fresh_memory_v1 allocs bytes {base} size owner))"
    );
    (
        "ir_byte_fresh_allocate_range_v1",
        format!(
            "def ir_byte_fresh_allocate_range_v1\n\
      (allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat) (cursor align size owner : Nat)\n\
      (cursorPositive : Nat.lt 0 cursor) (sizePositive : Nat.lt 0 size)\n\
      (above : Nat.le cursor {base}) (alignment : @Eq Bool (ir_byte_alignment_v1 align) Bool.true)\n\
      (room : Nat.lt {end} ir_byte_limit_v1) (before : ir_byte_high_water_v1 allocs cursor) :\n\
      @Eq IRByteMemoryResultV1 (ir_byte_allocate_range_v1 size align owner {mem}) {expected} :=\n\
      ir_byte_case_true_v1 IRByteMemoryResultV1 {guard}\n\
        (IRByteMemoryResultV1.fault (IROutcome.ub IRFault.bad_addr) {mem}) {expected} {expected}\n\
        {proof} (@Eq.refl IRByteMemoryResultV1 {expected})"
        ),
    )
}

fn gep_source() -> (&'static str, String) {
    let delta = "(Nat.mul stride index)";
    let result = format!("(Nat.add base {delta})");
    let end = "(Nat.add base size)";
    let within = format!("(@Nat.add_le_add_left {delta} size within base)");
    let result_bound = format!(
        "(@Nat.le_trans (Nat.succ {result}) (Nat.succ {end}) ir_byte_limit_v1\n\
      (@Nat.succ_le_succ {result} {end} {within}) room)"
    );
    let delta_lower = format!(
        "(@Eq.subst Nat (fun (upper : Nat) => Nat.le {delta} upper)\n\
      (Nat.add {delta} base) {result} (@Nat.add_comm {delta} base) (Nat.le_add_right {delta} base))"
    );
    let delta_bound = format!(
        "(@Nat.le_trans (Nat.succ {delta}) (Nat.succ {result}) ir_byte_limit_v1\n\
      (@Nat.succ_le_succ {delta} {result} {delta_lower}) {result_bound})"
    );
    let same = format!(
        "(ir_byte_same_allocation_v1 {} base {result})",
        fresh_allocs()
    );
    let (guard, proof) = conjunction(&[
        (
            "(ir_nat_pos base)".into(),
            "(ir_byte_allocation_pos_v1 base basePositive)".into(),
        ),
        (
            format!("(ir_nat_ltb {delta} ir_byte_limit_v1)"),
            format!("(ir_byte_ltb_of_lt_v1 {delta} ir_byte_limit_v1 {delta_bound})"),
        ),
        (
            format!("(ir_nat_ltb {result} ir_byte_limit_v1)"),
            format!("(ir_byte_ltb_of_lt_v1 {result} ir_byte_limit_v1 {result_bound})"),
        ),
        (
            same,
            format!(
                "(ir_byte_fresh_same_allocation_v1 allocs cursor base size owner {result}\n\
          above before basePositive sizePositive (@Nat.le_of_lt {end} ir_byte_limit_v1 room)\n\
          (Nat.le_add_right base {delta}) {within})"
            ),
        ),
    ]);
    let mem = "(ir_byte_fresh_memory_v1 allocs bytes base size owner)";
    let expected =
        format!("(IRByteMemoryResultV1.value (ir_byte_pointer_value_v1 {result}) {mem})");
    (
        "ir_byte_fresh_inbounds_gep_at_v1",
        format!(
            "def ir_byte_fresh_inbounds_gep_at_v1\n\
      (allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat)\n\
      (cursor base size owner stride index : Nat)\n\
      (above : Nat.le cursor base) (before : ir_byte_high_water_v1 allocs cursor)\n\
      (basePositive : Nat.lt 0 base) (sizePositive : Nat.lt 0 size)\n\
      (room : Nat.lt {end} ir_byte_limit_v1) (within : Nat.le {delta} size) :\n\
      @Eq IRByteMemoryResultV1 (ir_byte_gep_at_v1 base stride index Bool.true {mem}) {expected} :=\n\
      ir_byte_case_true_v1 IRByteMemoryResultV1 {guard}\n\
        (IRByteMemoryResultV1.fault (IROutcome.ub IRFault.bad_addr) {mem}) {expected} {expected}\n\
        {proof} (@Eq.refl IRByteMemoryResultV1 {expected})"
        ),
    )
}

fn frame16_sources() -> Vec<(&'static str, String)> {
    let base = "(ir_byte_aligned_base_v1 cursor 8)";
    let end = format!("(Nat.add {base} 16)");
    let mem = format!("(ir_byte_fresh_memory_v1 allocs bytes {base} 16 owner)");
    let allocs = format!(
        "(@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk {base} 16 owner Bool.true) allocs)"
    );
    let above = "(ir_byte_align_eight_above_v1 cursor)";
    let positive = "(ir_byte_align_eight_positive_v1 cursor cursorPositive)";
    let bounded = format!("(@Nat.le_of_lt {end} ir_byte_limit_v1 room)");
    let common = format!(
        "(allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat) (cursor owner : Nat)\n\
      (cursorPositive : Nat.lt 0 cursor) (room : Nat.lt {end} ir_byte_limit_v1)\n\
      (before : ir_byte_high_water_v1 allocs cursor)"
    );
    let mut out = vec![(
        "ir_byte_frame16_allocate_range_v1",
        format!(
            "def ir_byte_frame16_allocate_range_v1 {common} :\n\
      @Eq IRByteMemoryResultV1 (ir_byte_allocate_range_v1 16 8 owner (IRByteMemoryV1.mk allocs bytes cursor))\n\
        (IRByteMemoryResultV1.value (IRScalar.ptr_ {base}) {mem}) :=\n\
      ir_byte_fresh_allocate_range_v1 allocs bytes cursor 8 16 owner cursorPositive (Nat.zero_lt_succ 15)\n\
        {above} (@Eq.refl Bool Bool.true) room before"
        ),
    )];
    out.push((
        "ir_byte_frame16_high_water_v1",
        format!(
            "def ir_byte_frame16_high_water_v1 {common} :\n\
      ir_byte_high_water_v1 (ir_byte_mem_allocs_v1 {mem}) (ir_byte_mem_next_v1 {mem}) :=\n\
      ir_byte_high_water_fresh_v1 allocs cursor {base} 16 owner {above} before"
        ),
    ));
    for (offset, access_name, gep_name) in [
        (
            0,
            "ir_byte_frame16_first_accessible_v1",
            "ir_byte_frame16_first_gep_v1",
        ),
        (
            8,
            "ir_byte_frame16_second_accessible_v1",
            "ir_byte_frame16_second_gep_v1",
        ),
    ] {
        let address = if offset == 0 {
            base.to_owned()
        } else {
            format!("(Nat.add {base} 8)")
        };
        let lower = if offset == 0 {
            format!("(Nat.le_refl {base})")
        } else {
            format!("(Nat.le_add_right {base} 8)")
        };
        let upper = if offset == 0 {
            format!("(@Nat.add_le_add_left 8 16 (Nat.le_add_right 8 8) {base})")
        } else {
            format!(
                "(@Eq.subst Nat (fun (edge : Nat) => Nat.le edge {end})\n\
              {end} (Nat.add (Nat.add {base} 8) 8)\n\
              (@Eq.symm Nat (Nat.add (Nat.add {base} 8) 8) {end} (@Nat.add_assoc {base} 8 8))\n\
              (Nat.le_refl {end}))"
            )
        };
        let modulo = if offset == 0 {
            "ir_byte_align_eight_mod_v1"
        } else {
            "ir_byte_align_eight_offset_eight_mod_v1"
        };
        out.push((
            access_name,
            format!(
                "def {access_name} {common} :\n\
          @Eq Bool (ir_byte_accessible_v1 {allocs} {address} 8 8) Bool.true :=\n\
          ir_byte_fresh_accessible_v1 allocs cursor {base} 16 owner {address} 8 8 {above} before\n\
            {positive} (Nat.zero_lt_succ 15) (Nat.zero_lt_succ 7) {bounded} {lower} {upper}\n\
            (@Eq.refl Bool Bool.true) ({modulo} cursor)"
            ),
        ));
        let within = if offset == 0 {
            "(Nat.zero_le 16)"
        } else {
            "(Nat.le_add_right 8 8)"
        };
        let actual = format!("(ir_byte_gep_at_v1 {base} 1 {offset} Bool.true {mem})");
        let middle =
            format!("(IRByteMemoryResultV1.value (ir_byte_pointer_value_v1 {address}) {mem})");
        let expected = format!("(IRByteMemoryResultV1.value (IRScalar.ptr_ {address}) {mem})");
        out.push((gep_name, format!("def {gep_name} {common} : @Eq IRByteMemoryResultV1 {actual} {expected} :=\n\
          @Eq.trans IRByteMemoryResultV1 {actual} {middle} {expected}\n\
            (ir_byte_fresh_inbounds_gep_at_v1 allocs bytes cursor {base} 16 owner 1 {offset}\n\
              {above} before {positive} (Nat.zero_lt_succ 15) room {within})\n\
            (ir_eq_cong IRScalar IRByteMemoryResultV1 (fun (ptr : IRScalar) => IRByteMemoryResultV1.value ptr {mem})\n\
              (ir_byte_pointer_value_v1 {address}) (IRScalar.ptr_ {address})\n\
              (ir_byte_allocation_pointer_value_v1 {address}\n\
                (@Nat.le_trans 1 {base} {address} {positive} {lower})))")));
    }
    let ty = "(IRTy.array_ (IRTy.uint_ 8) 16)";
    let layout = format!("(IRByteLayoutV1.mk {ty} 16 1 (@IRList.nil IRTy) (@IRList.nil Nat))");
    let old = "(IRByteMemoryV1.mk allocs bytes cursor)";
    let failure =
        format!("(IRByteMemoryResultV1.fault (IROutcome.unmodelled IRFault.width_bounded) {old})");
    let expected = format!("(IRByteMemoryResultV1.value (IRScalar.ptr_ {base}) {mem})");
    let body = format!(
        "(@Bool.rec (fun (_ : Bool) => IRByteMemoryResultV1) {failure}\n\
      (ir_byte_allocate_range_v1 (Nat.mul (ir_byte_layout_size_v1 layout) 1)\n\
        (ir_byte_effective_align_v1 8 (ir_byte_layout_align_v1 layout)) owner {old})\n\
      (Bool.and (ir_nat_pos 1) (Bool.and (ir_nat_pos (ir_byte_layout_size_v1 layout))\n\
        (Bool.and (ir_nat_ltb 1 ir_byte_limit_v1)\n\
          (Bool.and (ir_nat_ltb (ir_byte_layout_size_v1 layout) ir_byte_limit_v1)\n\
            (ir_byte_alignment_v1 (ir_byte_layout_align_v1 layout)))))))"
    );
    out.push(("ir_byte_frame16_typed_allocate_v1", format!("def ir_byte_frame16_typed_allocate_v1 (ctx : IRByteContextV1) {common}\n\
      (layoutFound : @Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 ctx {ty}) (@IROption.some IRByteLayoutV1 {layout})) :\n\
      @Eq IRByteMemoryResultV1 (ir_byte_alloc_v1 ctx {ty} 1 8 owner {old}) {expected} :=\n\
      ir_byte_case_some_v1 IRByteLayoutV1 IRByteMemoryResultV1 (ir_byte_layout_v1 ctx {ty}) {layout}\n\
        {failure} (fun (layout : IRByteLayoutV1) => {body}) {expected} layoutFound\n\
        (ir_byte_frame16_allocate_range_v1 allocs bytes cursor owner cursorPositive room before)")));
    out
}

fn zero_count_source(point: bool) -> (&'static str, String) {
    let name = if point {
        "ir_byte_high_water_point_count_v1"
    } else {
        "ir_byte_high_water_overlap_count_v1"
    };
    let extra = if point { "" } else { " (size : Nat)" };
    let counter = |xs: &str| {
        if point {
            format!("(ir_byte_point_count_v1 {xs} address)")
        } else {
            format!("(ir_byte_overlap_count_v1 {xs} address size)")
        }
    };
    let end = "(Nat.add (ir_byte_alloc_base_v1 a) (ir_byte_alloc_size_v1 a))";
    let ht = "(ir_byte_high_water_v1 tail cursor)".to_string();
    let he = format!("(Nat.lt {end} cursor)");
    let last = if point {
        format!("(ir_nat_leb address {end})")
    } else {
        format!("(ir_nat_ltb address {end})")
    };
    let less =
        format!("(@Nat.le_trans (Nat.succ {end}) cursor address (@And.left {he} {ht} h) above)");
    let mut predicate = last.clone();
    let mut proof = if point {
        format!("(ir_byte_allocation_leb_false_v1 address {end} {less})")
    } else {
        format!(
            "(ir_byte_allocation_ltb_false_v1 address {end} (@Nat.le_of_lt {end} address {less}))"
        )
    };
    let prefix = if point {
        vec!["(ir_nat_leb (ir_byte_alloc_base_v1 a) address)".to_owned()]
    } else {
        vec![
            "(ir_nat_pos (ir_byte_alloc_size_v1 a))".to_owned(),
            "(ir_nat_pos size)".to_owned(),
            "(ir_nat_ltb (ir_byte_alloc_base_v1 a) (Nat.add address size))".to_owned(),
        ]
    };
    for head in prefix.iter().rev() {
        proof = format!("(ir_byte_allocation_and_false_v1 {head} {predicate} {proof})");
        predicate = and(head, &predicate);
    }
    let old = counter("tail");
    let tail_proof = format!("(ih (@And.right {he} {ht} h))");
    (
        name,
        format!(
            "def {name} (allocs : IRList IRByteAllocationV1) (cursor address : Nat){extra}\n\
      (above : Nat.le cursor address) (before : ir_byte_high_water_v1 allocs cursor) :\n\
      @Eq Nat {} 0 :=\n\
      @IRList.rec IRByteAllocationV1\n\
        (fun (xs : IRList IRByteAllocationV1) => ir_byte_high_water_v1 xs cursor -> @Eq Nat {} 0)\n\
        (fun (_ : True) => @Eq.refl Nat 0)\n\
        (fun (a : IRByteAllocationV1) (tail : IRList IRByteAllocationV1)\n\
          (ih : ir_byte_high_water_v1 tail cursor -> @Eq Nat {old} 0) =>\n\
          fun (h : And {he} {ht}) =>\n\
          @Eq.trans Nat (@Bool.rec (fun (_ : Bool) => Nat) {old} (Nat.succ {old}) {predicate}) {old} 0\n\
            (ir_eq_cong Bool Nat (fun (overlap : Bool) => @Bool.rec (fun (_ : Bool) => Nat) {old} (Nat.succ {old}) overlap)\n\
              {predicate} Bool.false {proof}) {tail_proof}) allocs before",
            counter("allocs"),
            counter("xs")
        ),
    )
}

fn laws() -> Vec<(&'static str, String)> {
    let mut laws = [
        ("ir_byte_high_water_v1", HIGH_WATER),
        ("ir_byte_fresh_memory_v1", FRESH_MEMORY),
        ("ir_byte_allocation_pos_v1", POSITIVE),
        ("ir_byte_allocation_ltb_false_v1", LT_FALSE),
        ("ir_byte_allocation_leb_false_v1", LE_FALSE),
        ("ir_byte_allocation_and_false_v1", AND_FALSE),
        ("ir_byte_allocation_pointer_value_v1", POINTER_VALUE),
        ("ir_byte_high_water_raise_v1", HIGH_WATER_RAISE),
        ("ir_byte_high_water_retire_v1", HIGH_WATER_RETIRE),
        ("ir_byte_high_water_fresh_v1", HIGH_WATER_FRESH),
    ]
    .into_iter()
    .map(|(name, source)| (name, source.to_owned()))
    .collect::<Vec<_>>();
    laws.push(zero_count_source(false));
    laws.push(zero_count_source(true));
    laws.push(cover_source());
    laws.push(overlap_source());
    laws.push(point_source());
    laws.push(accessible_source());
    laws.push(same_allocation_source());
    laws.push(allocate_source());
    laws.push(gep_source());
    laws.extend(frame16_sources());
    laws
}

impl Specification {
    pub(super) fn add_eval_ir_byte_allocation_laws_v1(&mut self) -> Result<(), SpecError> {
        for (name, source) in laws() {
            self.add_recursive_def(&source, "Checked actual allocation/high-water law; no assumed post-access or native refinement.")
                .map_err(|error| match error {
                    SpecError::ElabError(detail) => SpecError::ElabError(format!("{name}: {detail}")),
                    SpecError::TypeError(detail) => SpecError::TypeError(format!("{name}: {detail}")),
                    SpecError::ParseError(detail) => SpecError::ParseError(format!("{name}: {detail}")),
                    other => other,
                })?;
            self.verify_definition(name)?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "eval_ir_byte_allocation_tests.rs"]
mod tests;
