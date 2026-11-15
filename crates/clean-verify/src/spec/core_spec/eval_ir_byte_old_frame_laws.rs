// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Framing old initialized slots across the actual fresh allocator.
//!
//! High-water evidence concerns the actual allocation history, including dead
//! records. It is not inferred from world validity or native pointer order.
//! Loads return the new memory, not the old memory-bearing load result.

use crate::spec::{SpecError, Specification};

const LE_OF_LEB: &str = r"def ir_byte_old_frame_le_of_leb_v1 (a b : Nat)
  (h : @Eq Bool (ir_nat_leb a b) Bool.true) : Nat.le a b :=
@Nat.rec
  (fun (x : Nat) => forall (y : Nat), @Eq Bool (ir_nat_leb_walk x y) Bool.true -> Nat.le x y)
  (fun (y : Nat) (_ : @Eq Bool (ir_nat_leb_walk 0 y) Bool.true) => Nat.zero_le y)
  (fun (x : Nat)
    (ih : forall (y : Nat), @Eq Bool (ir_nat_leb_walk x y) Bool.true -> Nat.le x y) =>
    fun (y : Nat) => @Nat.rec
      (fun (z : Nat) => @Eq Bool (ir_nat_leb_walk (Nat.succ x) z) Bool.true -> Nat.le (Nat.succ x) z)
      (fun (bad : @Eq Bool Bool.false Bool.true) => @False.elim (Nat.le (Nat.succ x) 0)
        (ir_byte_world_false_true_v1 bad))
      (fun (z : Nat) (_ : @Eq Bool (ir_nat_leb_walk (Nat.succ x) z) Bool.true -> Nat.le (Nat.succ x) z) =>
        fun (below : @Eq Bool (ir_nat_leb_walk x z) Bool.true) =>
        @Nat.succ_le_succ x z (ih z below)) y)
  a b (@Eq.trans Bool (ir_nat_leb_walk a b) (ir_nat_leb a b) Bool.true
    (@Eq.symm Bool (ir_nat_leb a b) (ir_nat_leb_walk a b) (ir_nat_leb_walk_eq a b)) h)";

const OR_ELIM: &str = r"def ir_byte_old_frame_or_elim_v1 (a b : Bool) (P : Prop)
  (left : @Eq Bool a Bool.true -> P) (right : @Eq Bool b Bool.true -> P)
  (h : @Eq Bool (Bool.or a b) Bool.true) : P :=
@Bool.rec
  (fun (x : Bool) => (@Eq Bool x Bool.true -> P) -> @Eq Bool (Bool.or x b) Bool.true -> P)
  (fun (_ : @Eq Bool Bool.false Bool.true -> P) (hb : @Eq Bool b Bool.true) => right hb)
  (fun (yes : @Eq Bool Bool.true Bool.true -> P) (_ : @Eq Bool Bool.true Bool.true) =>
    yes (@Eq.refl Bool Bool.true)) a left h";

pub(super) fn and(parts: &[String]) -> String {
    let Some((last, prefix)) = parts.split_last() else {
        return "Bool.true".into();
    };
    prefix.iter().rev().fold(last.clone(), |tail, head| {
        format!("(Bool.and {head} {tail})")
    })
}

pub(super) fn extract(parts: &[String], index: usize, premise: &str) -> String {
    let mut proof = premise.to_owned();
    for (i, head) in parts.iter().enumerate().take(index) {
        proof = format!(
            "(ir_byte_world_and_right_v1 {head} {} {proof})",
            and(&parts[i + 1..])
        );
    }
    if index + 1 < parts.len() {
        proof = format!(
            "(ir_byte_world_and_left_v1 {} {} {proof})",
            parts[index],
            and(&parts[index + 1..])
        );
    }
    proof
}

pub(super) fn access_parts(allocs: &str, address: &str, width: &str, align: &str) -> Vec<String> {
    vec![
        format!("(ir_nat_pos {address})"),
        format!("(ir_nat_pos {width})"),
        format!("(ir_nat_leb (Nat.add {address} {width}) ir_byte_limit_v1)"),
        format!("(ir_byte_alignment_v1 {align})"),
        format!("(ir_nat_eqb (Nat.mod {address} {align}) 0)"),
        format!("(ir_nat_eqb (ir_byte_overlap_count_v1 {allocs} {address} {width}) 1)"),
        format!("(ir_byte_any_cover_v1 {allocs} {address} {width})"),
    ]
}

pub(super) fn cover_parts(row: &str, address: &str, width: &str) -> Vec<String> {
    vec![
        format!("(ir_byte_alloc_valid_v1 {row})"),
        format!("(ir_byte_alloc_live_v1 {row})"),
        format!("(ir_nat_leb (ir_byte_alloc_base_v1 {row}) {address})"),
        format!(
            "(ir_nat_leb (Nat.add {address} {width}) (Nat.add (ir_byte_alloc_base_v1 {row}) (ir_byte_alloc_size_v1 {row})))"
        ),
    ]
}

fn cover_end_source() -> (&'static str, String) {
    let upper = extract(&cover_parts("row", "address", "width"), 3, "covers");
    (
        "ir_byte_old_frame_cover_end_v1",
        format!(
            "def ir_byte_old_frame_cover_end_v1 (row : IRByteAllocationV1) (address width : Nat)
  (covers : @Eq Bool (ir_byte_cover_v1 row address width) Bool.true) :
Nat.le (Nat.add address width) (Nat.add (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row)) :=
ir_byte_old_frame_le_of_leb_v1 (Nat.add address width)
  (Nat.add (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row)) {upper}"
        ),
    )
}

const COVERED_END: &str = r"def ir_byte_high_water_covered_end_v1
  (allocs : IRList IRByteAllocationV1) (cursor address width : Nat)
  (highWater : ir_byte_high_water_v1 allocs cursor)
  (covered : @Eq Bool (ir_byte_any_cover_v1 allocs address width) Bool.true) :
Nat.lt (Nat.add address width) cursor :=
@IRList.rec IRByteAllocationV1
  (fun (xs : IRList IRByteAllocationV1) => ir_byte_high_water_v1 xs cursor ->
    @Eq Bool (ir_byte_any_cover_v1 xs address width) Bool.true -> Nat.lt (Nat.add address width) cursor)
  (fun (_ : True) (bad : @Eq Bool Bool.false Bool.true) =>
    @False.elim (Nat.lt (Nat.add address width) cursor) (ir_byte_world_false_true_v1 bad))
  (fun (row : IRByteAllocationV1) (tail : IRList IRByteAllocationV1)
    (ih : ir_byte_high_water_v1 tail cursor ->
      @Eq Bool (ir_byte_any_cover_v1 tail address width) Bool.true -> Nat.lt (Nat.add address width) cursor) =>
    fun (high : And (Nat.lt (Nat.add (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row)) cursor)
      (ir_byte_high_water_v1 tail cursor))
      (found : @Eq Bool (Bool.or (ir_byte_cover_v1 row address width)
        (ir_byte_any_cover_v1 tail address width)) Bool.true) =>
    ir_byte_old_frame_or_elim_v1 (ir_byte_cover_v1 row address width)
      (ir_byte_any_cover_v1 tail address width) (Nat.lt (Nat.add address width) cursor)
      (fun (head : @Eq Bool (ir_byte_cover_v1 row address width) Bool.true) =>
        @Nat.le_trans (Nat.succ (Nat.add address width))
          (Nat.succ (Nat.add (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row))) cursor
          (@Nat.succ_le_succ (Nat.add address width)
            (Nat.add (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row))
            (ir_byte_old_frame_cover_end_v1 row address width head))
          (@And.left (Nat.lt (Nat.add (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row)) cursor)
            (ir_byte_high_water_v1 tail cursor) high))
      (fun (rest : @Eq Bool (ir_byte_any_cover_v1 tail address width) Bool.true) =>
        ih (@And.right (Nat.lt (Nat.add (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row)) cursor)
          (ir_byte_high_water_v1 tail cursor) high) rest) found)
  allocs highWater covered";

fn accessible_prepend_source() -> (&'static str, String) {
    let old_parts = access_parts("allocs", "address", "width", "align");
    let covered = extract(&old_parts, 6, "before");
    let old_count = "(ir_byte_overlap_count_v1 allocs address width)";
    let added = "(@IRList.cons IRByteAllocationV1 row allocs)";
    let new_count = format!("(ir_byte_overlap_count_v1 {added} address width)");
    let old_cover = "(ir_byte_any_cover_v1 allocs address width)";
    let new_cover = format!("(ir_byte_any_cover_v1 {added} address width)");
    let mut intermediate = old_parts.clone();
    intermediate[6] = new_cover.clone();
    let mut count_body = intermediate.clone();
    count_body[5] = "(ir_nat_eqb count 1)".into();
    let mut cover_body = old_parts;
    cover_body[6] = "covered".into();
    (
        "ir_byte_accessible_prepend_nonoverlap_v1",
        format!(
            "def ir_byte_accessible_prepend_nonoverlap_v1
  (allocs : IRList IRByteAllocationV1) (row : IRByteAllocationV1) (address width align : Nat)
  (nonoverlap : @Eq Bool (ir_byte_overlaps_v1 row address width) Bool.false)
  (before : @Eq Bool (ir_byte_accessible_v1 allocs address width align) Bool.true) :
@Eq Bool (ir_byte_accessible_v1 {added} address width align) Bool.true :=
@Eq.trans Bool (ir_byte_accessible_v1 {added} address width align) {} Bool.true
  (ir_eq_cong Nat Bool (fun (count : Nat) => {}) {new_count} {old_count}
    (ir_eq_cong Bool Nat
      (fun (hit : Bool) => @Bool.rec (fun (_ : Bool) => Nat) {old_count} (Nat.succ {old_count}) hit)
      (ir_byte_overlaps_v1 row address width) Bool.false nonoverlap))
  (@Eq.trans Bool {} (ir_byte_accessible_v1 allocs address width align) Bool.true
    (ir_eq_cong Bool Bool (fun (covered : Bool) => {}) {new_cover} {old_cover}
      (@Eq.trans Bool {new_cover} Bool.true {old_cover}
        (ir_byte_lifetime_or_tail_v1 (ir_byte_cover_v1 row address width) {old_cover} {covered})
        (@Eq.symm Bool {old_cover} Bool.true {covered}))) before)",
            and(&intermediate),
            and(&count_body),
            and(&intermediate),
            and(&cover_body)
        ),
    )
}

const OVERLAP_BEFORE: &str = r"def ir_byte_old_frame_overlap_before_v1
  (row : IRByteAllocationV1) (address width : Nat)
  (before : Nat.le (Nat.add address width) (ir_byte_alloc_base_v1 row)) :
@Eq Bool (ir_byte_overlaps_v1 row address width) Bool.false :=
ir_byte_allocation_and_false_v1 (ir_nat_pos (ir_byte_alloc_size_v1 row))
  (Bool.and (ir_nat_pos width)
    (Bool.and (ir_nat_ltb (ir_byte_alloc_base_v1 row) (Nat.add address width))
      (ir_nat_ltb address (Nat.add (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row)))))
  (ir_byte_allocation_and_false_v1 (ir_nat_pos width)
    (Bool.and (ir_nat_ltb (ir_byte_alloc_base_v1 row) (Nat.add address width))
      (ir_nat_ltb address (Nat.add (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row))))
    (ir_eq_cong Bool Bool
      (fun (lower : Bool) => Bool.and lower
        (ir_nat_ltb address (Nat.add (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row))))
      (ir_nat_ltb (ir_byte_alloc_base_v1 row) (Nat.add address width)) Bool.false
      (ir_byte_allocation_ltb_false_v1 (ir_byte_alloc_base_v1 row) (Nat.add address width) before)))";

fn accessible_fresh_source() -> (&'static str, String) {
    let cover = extract(
        &access_parts("allocs", "address", "width", "align"),
        6,
        "before",
    );
    ("ir_byte_old_frame_accessible_fresh_v1", format!(
        "def ir_byte_old_frame_accessible_fresh_v1
  (allocs : IRList IRByteAllocationV1) (cursor newBase newSize owner address width align : Nat)
  (above : Nat.le cursor newBase) (highWater : ir_byte_high_water_v1 allocs cursor)
  (before : @Eq Bool (ir_byte_accessible_v1 allocs address width align) Bool.true) :
@Eq Bool (ir_byte_accessible_v1
  (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk newBase newSize owner Bool.true) allocs)
  address width align) Bool.true :=
ir_byte_accessible_prepend_nonoverlap_v1 allocs (IRByteAllocationV1.mk newBase newSize owner Bool.true)
  address width align
  (ir_byte_old_frame_overlap_before_v1 (IRByteAllocationV1.mk newBase newSize owner Bool.true) address width
    (@Nat.le_of_lt (Nat.add address width) newBase
      (@Nat.le_trans (Nat.succ (Nat.add address width)) cursor newBase
        (ir_byte_high_water_covered_end_v1 allocs cursor address width highWater {cover}) above))) before"))
}

const READ_FRESH: &str = r"def ir_byte_old_frame_read_fresh_v1
  (allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat)
  (cursor newBase newSize owner address width : Nat)
  (above : Nat.le cursor newBase) (highWater : ir_byte_high_water_v1 allocs cursor)
  (covered : @Eq Bool (ir_byte_any_cover_v1 allocs address width) Bool.true) :
@Eq (IROption Nat)
  (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 (ir_byte_fresh_memory_v1 allocs bytes newBase newSize owner)) width address)
  (ir_byte_read_word_v1 bytes width address) :=
ir_byte_read_clear_disjoint_v1 bytes address width newBase newSize
  (@Or.inl (Nat.le (Nat.add address width) newBase) (Nat.le (Nat.add newBase newSize) address)
    (@Nat.le_of_lt (Nat.add address width) newBase
      (@Nat.le_trans (Nat.succ (Nat.add address width)) cursor newBase
        (ir_byte_high_water_covered_end_v1 allocs cursor address width highWater covered) above)))";

fn load_fresh_source() -> (&'static str, String) {
    let mem = "(ir_byte_fresh_memory_v1 allocs bytes newBase newSize owner)";
    let align = "(ir_byte_effective_align_v1 requested (ir_byte_layout_align_v1 layout))";
    let old_cover = extract(
        &access_parts("allocs", "address", "8", align),
        6,
        "accessible",
    );
    ("ir_byte_old_frame_load_eight_v1", format!(
        "def ir_byte_old_frame_load_eight_v1
  (ctx : IRByteContextV1) (ty : IRTy) (ptr : IRScalar) (requested : Nat)
  (allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat)
  (cursor newBase newSize owner : Nat) (layout : IRByteLayoutV1) (address word : Nat) (value : IRScalar)
  (above : Nat.le cursor newBase) (highWater : ir_byte_high_water_v1 allocs cursor)
  (lane : @Eq (IROption Nat) (ir_byte_lane_size_v1 ty) (@IROption.some Nat 8))
  (layoutFound : @Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 ctx ty) (@IROption.some IRByteLayoutV1 layout))
  (layoutValid : @Eq Bool (Bool.and (ir_nat_eqb 8 (ir_byte_layout_size_v1 layout)) (ir_byte_alignment_v1 (ir_byte_layout_align_v1 layout))) Bool.true)
  (pointer : @Eq (IROption Nat) (ir_byte_pointer_address_v1 ptr) (@IROption.some Nat address))
  (accessible : @Eq Bool (ir_byte_accessible_v1 allocs address 8 {align}) Bool.true)
  (readBefore : @Eq (IROption Nat) (ir_byte_read_word_v1 bytes 8 address) (@IROption.some Nat word))
  (decoded : @Eq (IROption IRScalar) (ir_byte_decode_word_v1 ctx ty word) (@IROption.some IRScalar value))
  (fits : @Eq Bool (ir_byte_value_matches_v1 ctx ty value) Bool.true) :
@Eq IRByteMemoryResultV1 (ir_byte_load_v1 ctx ty ptr requested Bool.false {mem})
  (IRByteMemoryResultV1.value value {mem}) :=
@Eq.trans IRByteMemoryResultV1 (ir_byte_load_v1 ctx ty ptr requested Bool.false {mem})
  (ir_byte_load_at_v1 ctx ty address 8 {align} {mem}) (IRByteMemoryResultV1.value value {mem})
  (ir_byte_load_dispatch_eight_v1 ctx ty ptr requested {mem} layout address lane layoutFound layoutValid pointer)
  (ir_byte_load_at_rule_v1 ctx ty address 8 {align} {mem} word value
    (ir_byte_old_frame_accessible_fresh_v1 allocs cursor newBase newSize owner address 8 {align} above highWater accessible)
    (@Eq.trans (IROption Nat) (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 {mem}) 8 address)
      (ir_byte_read_word_v1 bytes 8 address) (@IROption.some Nat word)
      (ir_byte_old_frame_read_fresh_v1 allocs bytes cursor newBase newSize owner address 8 above highWater {old_cover}) readBefore)
    decoded fits)"))
}

const COVER_BEFORE: &str = r"def ir_byte_old_frame_cover_before_v1
  (row : IRByteAllocationV1) (address width : Nat)
  (before : Nat.lt address (ir_byte_alloc_base_v1 row)) :
@Eq Bool (ir_byte_cover_v1 row address width) Bool.false :=
ir_byte_allocation_and_false_v1 (ir_byte_alloc_valid_v1 row)
  (Bool.and (ir_byte_alloc_live_v1 row)
    (Bool.and (ir_nat_leb (ir_byte_alloc_base_v1 row) address)
      (ir_nat_leb (Nat.add address width) (Nat.add (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row)))))
  (ir_byte_allocation_and_false_v1 (ir_byte_alloc_live_v1 row)
    (Bool.and (ir_nat_leb (ir_byte_alloc_base_v1 row) address)
      (ir_nat_leb (Nat.add address width) (Nat.add (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row))))
    (ir_eq_cong Bool Bool
      (fun (lower : Bool) => Bool.and lower
        (ir_nat_leb (Nat.add address width) (Nat.add (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row))))
      (ir_nat_leb (ir_byte_alloc_base_v1 row) address) Bool.false
      (ir_byte_allocation_leb_false_v1 (ir_byte_alloc_base_v1 row) address before)))";

const POINT_BEFORE: &str = r"def ir_byte_point_count_prepend_before_v1
  (allocs : IRList IRByteAllocationV1) (row : IRByteAllocationV1) (address : Nat)
  (before : Nat.lt address (ir_byte_alloc_base_v1 row)) :
@Eq Nat (ir_byte_point_count_v1 (@IRList.cons IRByteAllocationV1 row allocs) address)
  (ir_byte_point_count_v1 allocs address) :=
ir_eq_cong Bool Nat
  (fun (lower : Bool) => @Bool.rec (fun (_ : Bool) => Nat)
    (ir_byte_point_count_v1 allocs address) (Nat.succ (ir_byte_point_count_v1 allocs address))
    (Bool.and lower (ir_nat_leb address (Nat.add (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row)))))
  (ir_nat_leb (ir_byte_alloc_base_v1 row) address) Bool.false
  (ir_byte_allocation_leb_false_v1 (ir_byte_alloc_base_v1 row) address before)";

fn same_allocation_source() -> (&'static str, String) {
    let added = "(@IRList.cons IRByteAllocationV1 row allocs)";
    let old_a = "(ir_byte_point_count_v1 allocs address)";
    let old_r = "(ir_byte_point_count_v1 allocs result)";
    let new_a = format!("(ir_byte_point_count_v1 {added} address)");
    let new_r = format!("(ir_byte_point_count_v1 {added} result)");
    let old_any = "(@IRList.rec IRByteAllocationV1 (fun (_ : IRList IRByteAllocationV1) => Bool)
      Bool.false (fun (a : IRByteAllocationV1) (_ : IRList IRByteAllocationV1) (ih : Bool) =>
        Bool.or (Bool.and (ir_byte_cover_v1 a address 0) (ir_byte_cover_v1 a result 0)) ih) allocs)";
    let new_any = |cover: &str| {
        format!("(Bool.or (Bool.and {cover} (ir_byte_cover_v1 row result 0)) {old_any})")
    };
    let expr = |a: &str, r: &str, cover: &str| {
        format!(
            "(Bool.and (ir_nat_eqb {a} 1) (Bool.and (ir_nat_eqb {r} 1) {}))",
            new_any(cover)
        )
    };
    let cover = "(ir_byte_cover_v1 row address 0)";
    let first = expr(old_a, &new_r, cover);
    let second = expr(old_a, old_r, cover);
    ("ir_byte_same_allocation_prepend_before_v1", format!(
        "def ir_byte_same_allocation_prepend_before_v1
  (allocs : IRList IRByteAllocationV1) (row : IRByteAllocationV1) (address result : Nat)
  (addressBefore : Nat.lt address (ir_byte_alloc_base_v1 row))
  (resultBefore : Nat.lt result (ir_byte_alloc_base_v1 row)) :
@Eq Bool (ir_byte_same_allocation_v1 {added} address result) (ir_byte_same_allocation_v1 allocs address result) :=
@Eq.trans Bool (ir_byte_same_allocation_v1 {added} address result) {first}
  (ir_byte_same_allocation_v1 allocs address result)
  (ir_eq_cong Nat Bool (fun (count : Nat) => {}) {new_a} {old_a}
    (ir_byte_point_count_prepend_before_v1 allocs row address addressBefore))
  (@Eq.trans Bool {first} {second} (ir_byte_same_allocation_v1 allocs address result)
    (ir_eq_cong Nat Bool (fun (count : Nat) => {}) {new_r} {old_r}
      (ir_byte_point_count_prepend_before_v1 allocs row result resultBefore))
    (ir_eq_cong Bool Bool (fun (covered : Bool) => {}) {cover} Bool.false
      (ir_byte_old_frame_cover_before_v1 row address 0 addressBefore)))",
        expr("count", &new_r, cover), expr(old_a, "count", cover), expr(old_a, old_r, "covered")))
}

fn eq(ty: &str, lhs: &str, rhs: &str) -> String {
    format!("(@Eq {ty} ({lhs}) ({rhs}))")
}

fn conjunction(parts: &[(String, String)]) -> (String, String) {
    let Some((last, prefix)) = parts.split_last() else {
        return ("True".into(), "True.intro".into());
    };
    prefix
        .iter()
        .rev()
        .fold(last.clone(), |(tail, proof), (head, head_proof)| {
            (
                format!("(And {head} {tail})"),
                format!("(@And.intro {head} {tail} ({head_proof}) ({proof}))"),
            )
        })
}

/// Five actual public operation equations. The old pair is produced by two
/// stores, the next memory by typed allocation, and both old loads name that
/// same final memory. No successful post-read is supplied as a premise.
fn pair_fresh_sources() -> Vec<(&'static str, String)> {
    let old = "(IRByteMemoryV1.mk allocs bytes cursor)";
    // Keep the already-known constructor fields explicit. Repeated projections
    // through nested memory constructors otherwise make elaboration normalize
    // whole effect guards before noticing that their inputs are identical.
    let first_bytes = "(ir_byte_write_word_v1 bytes address1 8 word1)";
    let first = format!("(IRByteMemoryV1.mk allocs {first_bytes} cursor)");
    let initialized_bytes = format!("(ir_byte_write_word_v1 {first_bytes} address2 8 word2)");
    let initialized = format!("(IRByteMemoryV1.mk allocs {initialized_bytes} cursor)");
    let base = "(ir_byte_aligned_base_v1 cursor 8)";
    let fresh = format!("(ir_byte_fresh_memory_v1 allocs {initialized_bytes} {base} 16 owner)");
    let frame_ty = "(IRTy.array_ (IRTy.uint_ 8) 16)";
    let frame_layout =
        format!("(IRByteLayoutV1.mk {frame_ty} 16 1 (@IRList.nil IRTy) (@IRList.nil Nat))");
    let mut header = format!("def ir_byte_store_pair_fresh_frame16_v1
  (ctx : IRByteContextV1) (ty1 ty2 : IRTy) (ptr1 ptr2 value1 value2 : IRScalar)
  (align1 align2 : Nat) (allocs : IRList IRByteAllocationV1) (bytes : Nat -> IROption Nat)
  (cursor owner : Nat) (layout1 layout2 : IRByteLayoutV1) (address1 address2 word1 word2 : Nat)
  (cursorPositive : Nat.lt 0 cursor) (room : Nat.lt (Nat.add {base} 16) ir_byte_limit_v1)
  (highWater : ir_byte_high_water_v1 allocs cursor)
  (frameLayout : @Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 ctx {frame_ty}) (@IROption.some IRByteLayoutV1 {frame_layout}))");
    for i in [1, 2] {
        header.push_str(&format!("
  (lane{i} : @Eq (IROption Nat) (ir_byte_lane_size_v1 ty{i}) (@IROption.some Nat 8))
  (layoutFound{i} : @Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 ctx ty{i}) (@IROption.some IRByteLayoutV1 layout{i}))
  (layoutValid{i} : @Eq Bool (Bool.and (ir_nat_eqb 8 (ir_byte_layout_size_v1 layout{i})) (ir_byte_alignment_v1 (ir_byte_layout_align_v1 layout{i}))) Bool.true)
  (pointer{i} : @Eq (IROption Nat) (ir_byte_pointer_address_v1 ptr{i}) (@IROption.some Nat address{i}))
  (access{i} : @Eq Bool (ir_byte_accessible_v1 allocs address{i} 8
    (ir_byte_effective_align_v1 align{i} (ir_byte_layout_align_v1 layout{i}))) Bool.true)
  (fits{i} : @Eq Bool (ir_byte_value_matches_v1 ctx ty{i} value{i}) Bool.true)
  (encoded{i} : @Eq (IROption Nat) (ir_byte_scalar_word_v1 ctx value{i}) (@IROption.some Nat word{i}))
  (decoded{i} : @Eq (IROption IRScalar) (ir_byte_decode_word_v1 ctx ty{i} word{i}) (@IROption.some IRScalar value{i}))
  (bounded{i} : Nat.lt word{i} ir_byte_limit_v1)"));
    }
    header.push_str("\n  (apart : Or (Nat.le (Nat.add address1 8) address2) (Nat.le (Nat.add address2 8) address1))");
    let mut parts = Vec::new();
    for (i, before, after) in [
        (1, old.to_owned(), first.clone()),
        (2, first.clone(), initialized.clone()),
    ] {
        let alignment =
            format!("(ir_byte_effective_align_v1 align{i} (ir_byte_layout_align_v1 layout{i}))");
        let actual =
            format!("ir_byte_store_v1 ctx ty{i} ptr{i} value{i} align{i} Bool.false {before}");
        let inner =
            format!("ir_byte_store_at_v1 ctx ty{i} address{i} value{i} 8 {alignment} {before}");
        let expected = format!("IRByteMemoryResultV1.value IRScalar.unit_ {after}");
        parts.push((
            eq("IRByteMemoryResultV1", &actual, &expected),
            format!(
                "@Eq.trans IRByteMemoryResultV1 ({actual}) ({inner}) ({expected})
  (ir_byte_store_dispatch_eight_v1 ctx ty{i} ptr{i} value{i} align{i} {before} layout{i} address{i}
    lane{i} layoutFound{i} layoutValid{i} pointer{i})
  (ir_byte_store_at_eight_rule_v1 ctx ty{i} address{i} value{i} {alignment} {before} word{i}
    access{i} fits{i} encoded{i} bounded{i})"
            ),
        ));
    }
    let allocated = format!("IRByteMemoryResultV1.value (IRScalar.ptr_ {base}) {fresh}");
    parts.push((eq("IRByteMemoryResultV1", &format!("ir_byte_alloc_v1 ctx {frame_ty} 1 8 owner {initialized}"), &allocated),
        format!("ir_byte_frame16_typed_allocate_v1 ctx allocs {initialized_bytes} cursor owner cursorPositive room highWater frameLayout")));
    for i in [1, 2] {
        let read = if i == 1 {
            format!(
                "@Eq.trans (IROption Nat)
  (ir_byte_read_word_v1 {initialized_bytes} 8 address1)
  (ir_byte_read_word_v1 {first_bytes} 8 address1) (@IROption.some Nat word1)
  (ir_byte_read_write_disjoint_v1 {first_bytes} address1 8 address2 8 word2 apart)
  (ir_byte_read_write_eight_v1 bytes address1 word1 bounded1)"
            )
        } else {
            format!("ir_byte_read_write_eight_v1 {first_bytes} address2 word2 bounded2")
        };
        let actual = format!("ir_byte_load_v1 ctx ty{i} ptr{i} align{i} Bool.false {fresh}");
        let expected = format!("IRByteMemoryResultV1.value value{i} {fresh}");
        parts.push((
            eq("IRByteMemoryResultV1", &actual, &expected),
            format!(
            "ir_byte_old_frame_load_eight_v1 ctx ty{i} ptr{i} align{i} allocs {initialized_bytes}
  cursor {base} 16 owner layout{i} address{i} word{i} value{i}
  (ir_byte_align_eight_above_v1 cursor) highWater lane{i} layoutFound{i} layoutValid{i} pointer{i}
  access{i} ({read}) decoded{i} fits{i}"),
        ));
    }
    // Check each effect equation once, then compose applications of those
    // checked declarations. Inlining every derivation into nested And.intro
    // repeats large expected types during elaboration; sharing declarations
    // also gives downstream consumers independent operation projections.
    let arguments = "ctx ty1 ty2 ptr1 ptr2 value1 value2 align1 align2 allocs bytes cursor owner
      layout1 layout2 address1 address2 word1 word2 cursorPositive room highWater frameLayout
      lane1 layoutFound1 layoutValid1 pointer1 access1 fits1 encoded1 decoded1 bounded1
      lane2 layoutFound2 layoutValid2 pointer2 access2 fits2 encoded2 decoded2 bounded2 apart";
    let mut out = Vec::new();
    let mut composed = Vec::new();
    for (name, (claim, proof)) in [
        "ir_byte_old_frame_pair_store_first_v1",
        "ir_byte_old_frame_pair_store_second_v1",
        "ir_byte_old_frame_pair_allocate_v1",
        "ir_byte_old_frame_pair_load_first_v1",
        "ir_byte_old_frame_pair_load_second_v1",
    ]
    .into_iter()
    .zip(&parts)
    {
        out.push((
            name,
            format!(
                "{} : {claim} :=\n{proof}",
                header.replacen("ir_byte_store_pair_fresh_frame16_v1", name, 1)
            ),
        ));
        composed.push((claim.clone(), format!("{name} {arguments}")));
    }
    let (claim, proof) = conjunction(&composed);
    out.push((
        "ir_byte_store_pair_fresh_frame16_v1",
        format!("{header} : {claim} :=\n{proof}"),
    ));
    out
}

fn laws() -> Vec<(&'static str, String)> {
    let mut out = vec![
        ("ir_byte_old_frame_le_of_leb_v1", LE_OF_LEB.into()),
        ("ir_byte_old_frame_or_elim_v1", OR_ELIM.into()),
        cover_end_source(),
        ("ir_byte_high_water_covered_end_v1", COVERED_END.into()),
        accessible_prepend_source(),
        ("ir_byte_old_frame_overlap_before_v1", OVERLAP_BEFORE.into()),
        accessible_fresh_source(),
        ("ir_byte_old_frame_read_fresh_v1", READ_FRESH.into()),
        load_fresh_source(),
        ("ir_byte_old_frame_cover_before_v1", COVER_BEFORE.into()),
        ("ir_byte_point_count_prepend_before_v1", POINT_BEFORE.into()),
        same_allocation_source(),
    ];
    out.extend(pair_fresh_sources());
    out
}

impl Specification {
    pub(super) fn add_eval_ir_byte_old_frame_laws_v1(&mut self) -> Result<(), SpecError> {
        for (name, source) in laws() {
            self.add_recursive_def(&source, "Checked old-slot framing across actual fresh allocation; explicit historical freshness and representation premises")
                .map_err(|error| SpecError::TypeError(format!("{name}: {error}")))?;
            self.verify_definition(name)?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "eval_ir_byte_old_frame_tests.rs"]
mod tests;
