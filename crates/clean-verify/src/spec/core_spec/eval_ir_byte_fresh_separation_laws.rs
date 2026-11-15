// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Preserve caller access across a fresh range at any address.
//!
//! Derive separation from the actual overlap count and live allocation lookup.
//! No high-water ordering, assumed post-access, or pointer-type hint is used.
//! Native stack placement and source-to-target memory relations remain separate.

use super::eval_ir_byte_old_frame_laws::{access_parts, cover_parts, extract};
use crate::spec::{SpecError, Specification};

const LT_OF_LTB: &str = r"def ir_byte_separation_lt_of_ltb_v1 (a b : Nat)
  (h : @Eq Bool (ir_nat_ltb a b) Bool.true) : Nat.lt a b :=
@Nat.rec
  (fun (x : Nat) => forall (y : Nat), @Eq Bool (ir_nat_ltb_walk x y) Bool.true -> Nat.lt x y)
  (fun (y : Nat) => @Nat.rec
    (fun (z : Nat) => @Eq Bool (ir_nat_ltb_walk 0 z) Bool.true -> Nat.lt 0 z)
    (fun (bad : @Eq Bool Bool.false Bool.true) => @False.elim (Nat.lt 0 0)
      (ir_byte_world_false_true_v1 bad))
    (fun (z : Nat) (_ : @Eq Bool (ir_nat_ltb_walk 0 z) Bool.true -> Nat.lt 0 z) =>
      fun (_ : @Eq Bool Bool.true Bool.true) => Nat.zero_lt_succ z) y)
  (fun (x : Nat)
    (ih : forall (y : Nat), @Eq Bool (ir_nat_ltb_walk x y) Bool.true -> Nat.lt x y) =>
    fun (y : Nat) => @Nat.rec
      (fun (z : Nat) => @Eq Bool (ir_nat_ltb_walk (Nat.succ x) z) Bool.true -> Nat.lt (Nat.succ x) z)
      (fun (bad : @Eq Bool Bool.false Bool.true) => @False.elim (Nat.lt (Nat.succ x) 0)
        (ir_byte_world_false_true_v1 bad))
      (fun (z : Nat) (_ : @Eq Bool (ir_nat_ltb_walk (Nat.succ x) z) Bool.true -> Nat.lt (Nat.succ x) z) =>
        fun (below : @Eq Bool (ir_nat_ltb_walk x z) Bool.true) =>
        @Nat.succ_le_succ (Nat.succ x) z (ih z below)) y)
  a b (@Eq.trans Bool (ir_nat_ltb_walk a b) (ir_nat_ltb a b) Bool.true
    (@Eq.symm Bool (ir_nat_ltb a b) (ir_nat_ltb_walk a b) (ir_nat_ltb_walk_eq a b)) h)";

const POS_OF_TRUE: &str = r"def ir_byte_separation_pos_of_true_v1 (n : Nat)
  (h : @Eq Bool (ir_nat_pos n) Bool.true) : Nat.lt 0 n :=
@Nat.rec (fun (x : Nat) => @Eq Bool (ir_nat_pos x) Bool.true -> Nat.lt 0 x)
  (fun (bad : @Eq Bool Bool.false Bool.true) => @False.elim (Nat.lt 0 0)
    (ir_byte_world_false_true_v1 bad))
  (fun (x : Nat) (_ : @Eq Bool (ir_nat_pos x) Bool.true -> Nat.lt 0 x) =>
    fun (_ : @Eq Bool Bool.true Bool.true) => Nat.zero_lt_succ x) n h";

const SUCC_ZERO: &str = r"def ir_byte_separation_succ_zero_v1 (n : Nat)
  (bad : @Eq Nat (Nat.succ n) 0) : False :=
Nat.not_succ_le_zero n
  (@Eq.subst Nat (fun (bound : Nat) => Nat.le (Nat.succ n) bound)
    (Nat.succ n) 0 bad (Nat.le_refl (Nat.succ n)))";

const COUNT_HEAD: &str = r"def ir_byte_separation_count_head_v1 (hit : Bool) (n : Nat)
  (zero : @Eq Nat (@Bool.rec (fun (_ : Bool) => Nat) n (Nat.succ n) hit) 0) :
@Eq Bool hit Bool.false :=
@Bool.rec
  (fun (b : Bool) => @Eq Nat (@Bool.rec (fun (_ : Bool) => Nat) n (Nat.succ n) b) 0 -> @Eq Bool b Bool.false)
  (fun (_ : @Eq Nat n 0) => @Eq.refl Bool Bool.false)
  (fun (bad : @Eq Nat (Nat.succ n) 0) => @False.elim (@Eq Bool Bool.true Bool.false)
    (ir_byte_separation_succ_zero_v1 n bad)) hit zero";

const COUNT_TAIL: &str = r"def ir_byte_separation_count_tail_v1 (hit : Bool) (n : Nat)
  (zero : @Eq Nat (@Bool.rec (fun (_ : Bool) => Nat) n (Nat.succ n) hit) 0) : @Eq Nat n 0 :=
@Bool.rec
  (fun (b : Bool) => @Eq Nat (@Bool.rec (fun (_ : Bool) => Nat) n (Nat.succ n) b) 0 -> @Eq Nat n 0)
  (fun (h : @Eq Nat n 0) => h)
  (fun (bad : @Eq Nat (Nat.succ n) 0) => @False.elim (@Eq Nat n 0)
    (ir_byte_separation_succ_zero_v1 n bad)) hit zero";

const FALSE_OF_NOT_TRUE: &str = r"def ir_byte_separation_false_of_not_true_v1 (b : Bool)
  (no : @Eq Bool b Bool.true -> False) : @Eq Bool b Bool.false :=
@Bool.rec (fun (x : Bool) => (@Eq Bool x Bool.true -> False) -> @Eq Bool x Bool.false)
  (fun (_ : @Eq Bool Bool.false Bool.true -> False) => @Eq.refl Bool Bool.false)
  (fun (bad : @Eq Bool Bool.true Bool.true -> False) => @False.elim (@Eq Bool Bool.true Bool.false)
    (bad (@Eq.refl Bool Bool.true))) b no";

fn conjunction(parts: &[(String, String)]) -> String {
    let Some((last, prefix)) = parts.split_last() else {
        return "(@Eq.refl Bool Bool.true)".into();
    };
    prefix
        .iter()
        .rev()
        .fold(
            (last.0.clone(), last.1.clone()),
            |(tail, proof), (head, head_proof)| {
                (
                    format!("(Bool.and {head} {tail})"),
                    format!("(ir_byte_world_and_intro_v1 {head} {tail} {head_proof} {proof})"),
                )
            },
        )
        .1
}

fn cover_overlap_source() -> (&'static str, String) {
    let cover = cover_parts("row", "address", "width");
    let valid = extract(&cover, 0, "covers");
    let valid_parts: Vec<String> = vec![
        "(ir_nat_pos (ir_byte_alloc_base_v1 row))".into(),
        "(ir_nat_pos (ir_byte_alloc_size_v1 row))".into(),
        "(ir_nat_leb (Nat.add (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row)) ir_byte_limit_v1)".into(),
    ];
    let hit: Vec<String> = vec![
        "(ir_nat_pos size)".into(),
        "(ir_nat_pos width)".into(),
        "(ir_nat_ltb base (Nat.add address width))".into(),
        "(ir_nat_ltb address (Nat.add base size))".into(),
    ];
    let lower = format!(
        "(ir_byte_old_frame_le_of_leb_v1 (ir_byte_alloc_base_v1 row) address {})",
        extract(&cover, 2, "covers")
    );
    let upper = "(ir_byte_old_frame_cover_end_v1 row address width covers)";
    let left = format!(
        "(ir_byte_ltb_of_lt_v1 (ir_byte_alloc_base_v1 row) (Nat.add base size)
      (@Nat.le_trans (Nat.succ (ir_byte_alloc_base_v1 row)) (Nat.succ address) (Nat.add base size)
        (@Nat.succ_le_succ (ir_byte_alloc_base_v1 row) address {lower})
        (ir_byte_separation_lt_of_ltb_v1 address (Nat.add base size) {})))",
        extract(&hit, 3, "hit")
    );
    let right = format!("(ir_byte_ltb_of_lt_v1 base (Nat.add (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row))
      (@Nat.le_trans (Nat.succ base) (Nat.add address width)
        (Nat.add (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row))
        (ir_byte_separation_lt_of_ltb_v1 base (Nat.add address width) {}) {upper}))", extract(&hit, 2, "hit"));
    let proof = conjunction(&[
        (valid_parts[1].clone(), extract(&valid_parts, 1, &valid)),
        (hit[0].clone(), extract(&hit, 0, "hit")),
        (
            "(ir_nat_ltb (ir_byte_alloc_base_v1 row) (Nat.add base size))".into(),
            left,
        ),
        (
            "(ir_nat_ltb base (Nat.add (ir_byte_alloc_base_v1 row) (ir_byte_alloc_size_v1 row)))"
                .into(),
            right,
        ),
    ]);
    ("ir_byte_separation_cover_overlap_v1", format!("def ir_byte_separation_cover_overlap_v1
  (row : IRByteAllocationV1) (base size owner address width : Nat)
  (covers : @Eq Bool (ir_byte_cover_v1 row address width) Bool.true)
  (hit : @Eq Bool (ir_byte_overlaps_v1 (IRByteAllocationV1.mk base size owner Bool.true) address width) Bool.true) :
@Eq Bool (ir_byte_overlaps_v1 row base size) Bool.true := {proof}"))
}

const COVER_NONOVERLAP: &str = r"def ir_byte_separation_cover_nonoverlap_v1
  (row : IRByteAllocationV1) (base size owner address width : Nat)
  (apart : @Eq Bool (ir_byte_overlaps_v1 row base size) Bool.false)
  (covers : @Eq Bool (ir_byte_cover_v1 row address width) Bool.true) :
@Eq Bool (ir_byte_overlaps_v1 (IRByteAllocationV1.mk base size owner Bool.true) address width) Bool.false :=
ir_byte_separation_false_of_not_true_v1
  (ir_byte_overlaps_v1 (IRByteAllocationV1.mk base size owner Bool.true) address width)
  (fun (hit : @Eq Bool (ir_byte_overlaps_v1 (IRByteAllocationV1.mk base size owner Bool.true) address width) Bool.true) =>
    ir_byte_world_false_true_v1
      (@Eq.trans Bool Bool.false (ir_byte_overlaps_v1 row base size) Bool.true
        (@Eq.symm Bool (ir_byte_overlaps_v1 row base size) Bool.false apart)
        (ir_byte_separation_cover_overlap_v1 row base size owner address width covers hit)))";

const FRESH_NONOVERLAP: &str = r"def ir_byte_fresh_range_nonoverlap_v1
  (allocs : IRList IRByteAllocationV1) (base size owner address width : Nat)
  (fresh : @Eq Nat (ir_byte_overlap_count_v1 allocs base size) 0)
  (covered : @Eq Bool (ir_byte_any_cover_v1 allocs address width) Bool.true) :
@Eq Bool (ir_byte_overlaps_v1 (IRByteAllocationV1.mk base size owner Bool.true) address width) Bool.false :=
@IRList.rec IRByteAllocationV1
  (fun (xs : IRList IRByteAllocationV1) => @Eq Nat (ir_byte_overlap_count_v1 xs base size) 0 ->
    @Eq Bool (ir_byte_any_cover_v1 xs address width) Bool.true ->
    @Eq Bool (ir_byte_overlaps_v1 (IRByteAllocationV1.mk base size owner Bool.true) address width) Bool.false)
  (fun (_ : @Eq Nat 0 0) (bad : @Eq Bool Bool.false Bool.true) =>
    @False.elim (@Eq Bool (ir_byte_overlaps_v1 (IRByteAllocationV1.mk base size owner Bool.true) address width) Bool.false)
      (ir_byte_world_false_true_v1 bad))
  (fun (row : IRByteAllocationV1) (tail : IRList IRByteAllocationV1)
    (ih : @Eq Nat (ir_byte_overlap_count_v1 tail base size) 0 ->
      @Eq Bool (ir_byte_any_cover_v1 tail address width) Bool.true ->
      @Eq Bool (ir_byte_overlaps_v1 (IRByteAllocationV1.mk base size owner Bool.true) address width) Bool.false) =>
    fun (zero : @Eq Nat (ir_byte_overlap_count_v1 (@IRList.cons IRByteAllocationV1 row tail) base size) 0)
      (cover : @Eq Bool (ir_byte_any_cover_v1 (@IRList.cons IRByteAllocationV1 row tail) address width) Bool.true) =>
    ir_byte_old_frame_or_elim_v1 (ir_byte_cover_v1 row address width)
      (ir_byte_any_cover_v1 tail address width)
      (@Eq Bool (ir_byte_overlaps_v1 (IRByteAllocationV1.mk base size owner Bool.true) address width) Bool.false)
      (fun (head : @Eq Bool (ir_byte_cover_v1 row address width) Bool.true) =>
        ir_byte_separation_cover_nonoverlap_v1 row base size owner address width
          (ir_byte_separation_count_head_v1 (ir_byte_overlaps_v1 row base size)
            (ir_byte_overlap_count_v1 tail base size) zero) head)
      (fun (rest : @Eq Bool (ir_byte_any_cover_v1 tail address width) Bool.true) =>
        ih (ir_byte_separation_count_tail_v1 (ir_byte_overlaps_v1 row base size)
          (ir_byte_overlap_count_v1 tail base size) zero) rest) cover)
  allocs fresh covered";

fn accessible_source() -> (&'static str, String) {
    let covered = extract(
        &access_parts("allocs", "address", "width", "align"),
        6,
        "before",
    );
    ("ir_byte_accessible_fresh_range_v1", format!("def ir_byte_accessible_fresh_range_v1
  (allocs : IRList IRByteAllocationV1) (base size owner address width align : Nat)
  (fresh : @Eq Nat (ir_byte_overlap_count_v1 allocs base size) 0)
  (before : @Eq Bool (ir_byte_accessible_v1 allocs address width align) Bool.true) :
@Eq Bool (ir_byte_accessible_v1
  (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk base size owner Bool.true) allocs)
  address width align) Bool.true :=
ir_byte_accessible_prepend_nonoverlap_v1 allocs (IRByteAllocationV1.mk base size owner Bool.true)
  address width align (ir_byte_fresh_range_nonoverlap_v1 allocs base size owner address width fresh {covered}) before"))
}

fn disjoint_source() -> (&'static str, String) {
    let hit = conjunction(&[
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
            "(ir_byte_ltb_of_lt_v1 base (Nat.add address width) right)".into(),
        ),
        (
            "(ir_nat_ltb address (Nat.add base size))".into(),
            "(ir_byte_ltb_of_lt_v1 address (Nat.add base size) left)".into(),
        ),
    ]);
    let left = "(Nat.le (Nat.add base size) address)";
    let right = "(Nat.le (Nat.add address width) base)";
    let claim = format!("(Or {left} {right})");
    ("ir_byte_separation_disjoint_v1", format!("def ir_byte_separation_disjoint_v1
  (base size owner address width : Nat)
  (sizePositive : Nat.lt 0 size) (widthPositive : Nat.lt 0 width)
  (apart : @Eq Bool (ir_byte_overlaps_v1 (IRByteAllocationV1.mk base size owner Bool.true) address width) Bool.false) :
{claim} :=
Or.rec (fun (before : {left}) => @Or.inl {left} {right} before)
  (fun (left : Nat.lt address (Nat.add base size)) =>
    Or.rec (fun (after : {right}) => @Or.inr {left} {right} after)
      (fun (right : Nat.lt base (Nat.add address width)) => @False.elim {claim}
        (ir_byte_world_false_true_v1
          (@Eq.trans Bool Bool.false
            (ir_byte_overlaps_v1 (IRByteAllocationV1.mk base size owner Bool.true) address width) Bool.true
            (@Eq.symm Bool (ir_byte_overlaps_v1 (IRByteAllocationV1.mk base size owner Bool.true) address width) Bool.false apart)
            {hit}))) (@Nat.le_or_lt (Nat.add address width) base))
  (@Nat.le_or_lt (Nat.add base size) address)"))
}

fn fresh_disjoint_source() -> (&'static str, String) {
    let parts = access_parts("allocs", "address", "width", "align");
    let positive = extract(&parts, 1, "before");
    let covered = extract(&parts, 6, "before");
    (
        "ir_byte_fresh_range_disjoint_v1",
        format!(
            "def ir_byte_fresh_range_disjoint_v1
  (allocs : IRList IRByteAllocationV1) (base size owner address width align : Nat)
  (sizePositive : Nat.lt 0 size)
  (fresh : @Eq Nat (ir_byte_overlap_count_v1 allocs base size) 0)
  (before : @Eq Bool (ir_byte_accessible_v1 allocs address width align) Bool.true) :
Or (Nat.le (Nat.add base size) address) (Nat.le (Nat.add address width) base) :=
ir_byte_separation_disjoint_v1 base size owner address width sizePositive
  (ir_byte_separation_pos_of_true_v1 width {positive})
  (ir_byte_fresh_range_nonoverlap_v1 allocs base size owner address width fresh {covered})"
        ),
    )
}

const READ_PRESERVED: &str = r"def ir_byte_fresh_range_read_preserved_v1
  (bytes : Nat -> IROption Nat) (allocs : IRList IRByteAllocationV1)
  (base size owner address width align word : Nat)
  (sizePositive : Nat.lt 0 size)
  (fresh : @Eq Nat (ir_byte_overlap_count_v1 allocs base size) 0)
  (before : @Eq Bool (ir_byte_accessible_v1 allocs address width align) Bool.true) :
@Eq (IROption Nat)
  (ir_byte_read_word_v1 (ir_byte_write_word_v1 bytes address width word) size base)
  (ir_byte_read_word_v1 bytes size base) :=
ir_byte_read_write_disjoint_v1 bytes base size address width word
  (ir_byte_fresh_range_disjoint_v1 allocs base size owner address width align sizePositive fresh before)";

fn laws() -> Vec<(&'static str, String)> {
    let mut laws = [
        ("ir_byte_separation_lt_of_ltb_v1", LT_OF_LTB),
        ("ir_byte_separation_pos_of_true_v1", POS_OF_TRUE),
        ("ir_byte_separation_succ_zero_v1", SUCC_ZERO),
        ("ir_byte_separation_count_head_v1", COUNT_HEAD),
        ("ir_byte_separation_count_tail_v1", COUNT_TAIL),
        ("ir_byte_separation_false_of_not_true_v1", FALSE_OF_NOT_TRUE),
    ]
    .into_iter()
    .map(|(name, source)| (name, source.to_owned()))
    .collect::<Vec<_>>();
    laws.push(cover_overlap_source());
    laws.push((
        "ir_byte_separation_cover_nonoverlap_v1",
        COVER_NONOVERLAP.into(),
    ));
    laws.push(("ir_byte_fresh_range_nonoverlap_v1", FRESH_NONOVERLAP.into()));
    laws.push(accessible_source());
    laws.push(disjoint_source());
    laws.push(fresh_disjoint_source());
    laws.push((
        "ir_byte_fresh_range_read_preserved_v1",
        READ_PRESERVED.into(),
    ));
    laws
}

impl Specification {
    pub(super) fn add_eval_ir_byte_fresh_separation_laws_v1(&mut self) -> Result<(), SpecError> {
        for (name, source) in laws() {
            self.add_recursive_def(
                &source,
                "Checked arbitrary-address fresh-range separation and preservation",
            )
            .map_err(|error| SpecError::TypeError(format!("{name}: {error}")))?;
            self.verify_definition(name)?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "eval_ir_byte_fresh_separation_tests.rs"]
mod tests;
