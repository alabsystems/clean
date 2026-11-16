// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Range-local framing of the actual byte reader, including undefined bytes.
//! These checked equations do not assume global byte-map equality or function
//! extensionality. Typed consumers compose them with the real access rules.

use crate::spec::{SpecError, Specification};

const JOIN_CONGR: &str = r"def ir_byte_join_read_congr_v1
  (lh rh lt rt : IROption Nat)
  (head : @Eq (IROption Nat) lh rh) (tail : @Eq (IROption Nat) lt rt) :
  @Eq (IROption Nat) (ir_byte_join_read_v1 lh lt) (ir_byte_join_read_v1 rh rt) :=
@Eq.trans (IROption Nat) (ir_byte_join_read_v1 lh lt) (ir_byte_join_read_v1 rh lt)
  (ir_byte_join_read_v1 rh rt)
  (ir_eq_cong (IROption Nat) (IROption Nat) (fun (h : IROption Nat) => ir_byte_join_read_v1 h lt) lh rh head)
  (ir_eq_cong (IROption Nat) (IROption Nat) (ir_byte_join_read_v1 rh) lt rt tail)";

const ADDRESS_STEP: &str = r"def ir_byte_range_address_step_v1 (base offset : Nat) :
  @Eq Nat (Nat.add (Nat.succ base) offset) (Nat.add base (Nat.succ offset)) :=
@Eq.trans Nat (Nat.add (Nat.succ base) offset) (Nat.succ (Nat.add base offset))
  (Nat.add base (Nat.succ offset))
  (Nat.succ_add base offset)
  (@Eq.symm Nat (Nat.add base (Nat.succ offset)) (Nat.succ (Nat.add base offset)) (Nat.add_succ base offset))";

const READ_RANGE_CONGR: &str = r"def ir_byte_read_range_congr_v1
  (left right : Nat -> IROption Nat) (size base : Nat)
  (same : forall (offset : Nat), Nat.lt offset size ->
    @Eq (IROption Nat) (left (Nat.add base offset)) (right (Nat.add base offset))) :
  @Eq (IROption Nat) (ir_byte_read_word_v1 left size base) (ir_byte_read_word_v1 right size base) :=
@Nat.rec
  (fun (count : Nat) => forall (address : Nat),
    (forall (offset : Nat), Nat.lt offset count ->
      @Eq (IROption Nat) (left (Nat.add address offset)) (right (Nat.add address offset))) ->
    @Eq (IROption Nat) (ir_byte_read_word_v1 left count address) (ir_byte_read_word_v1 right count address))
  (fun (address : Nat) (_ : forall (offset : Nat), Nat.lt offset 0 ->
    @Eq (IROption Nat) (left (Nat.add address offset)) (right (Nat.add address offset))) =>
    @Eq.refl (IROption Nat) (@IROption.some Nat 0))
  (fun (count : Nat)
    (ih : forall (address : Nat),
      (forall (offset : Nat), Nat.lt offset count ->
        @Eq (IROption Nat) (left (Nat.add address offset)) (right (Nat.add address offset))) ->
      @Eq (IROption Nat) (ir_byte_read_word_v1 left count address) (ir_byte_read_word_v1 right count address)) =>
    fun (address : Nat)
      (equal : forall (offset : Nat), Nat.lt offset (Nat.succ count) ->
        @Eq (IROption Nat) (left (Nat.add address offset)) (right (Nat.add address offset))) =>
    ir_byte_join_read_congr_v1 (left address) (right address)
      (ir_byte_read_word_v1 left count (Nat.succ address))
      (ir_byte_read_word_v1 right count (Nat.succ address))
      (equal 0 (Nat.zero_lt_succ count))
      (ih (Nat.succ address) (fun (offset : Nat) (bound : Nat.lt offset count) =>
        @Eq.subst Nat
          (fun (index : Nat) => @Eq (IROption Nat) (left index) (right index))
          (Nat.add address (Nat.succ offset)) (Nat.add (Nat.succ address) offset)
          (@Eq.symm Nat (Nat.add (Nat.succ address) offset) (Nat.add address (Nat.succ offset))
            (ir_byte_range_address_step_v1 address offset))
          (equal (Nat.succ offset) (@Nat.succ_le_succ (Nat.succ offset) count bound)))))
  size base same";

const BEFORE: &str = r"def ir_byte_range_before_v1 (base size address : Nat)
  (before : Nat.lt address base) :
  @Eq Bool (ir_byte_in_range_v1 base size address) Bool.false :=
ir_eq_cong Bool Bool
  (fun (lower : Bool) => Bool.and lower (ir_nat_ltb address (Nat.add base size)))
  (ir_nat_leb base address) Bool.false
  (ir_byte_allocation_leb_false_v1 base address before)";

const AFTER: &str = r"def ir_byte_range_after_v1 (base size address : Nat)
  (after : Nat.le (Nat.add base size) address) :
  @Eq Bool (ir_byte_in_range_v1 base size address) Bool.false :=
ir_byte_allocation_and_false_v1 (ir_nat_leb base address) (ir_nat_ltb address (Nat.add base size))
  (ir_byte_allocation_ltb_false_v1 address (Nat.add base size) after)";

const DISJOINT_POINT: &str = r"def ir_byte_disjoint_range_point_v1
  (readBase readSize writeBase writeSize offset : Nat)
  (apart : Or (Nat.le (Nat.add readBase readSize) writeBase)
              (Nat.le (Nat.add writeBase writeSize) readBase))
  (inside : Nat.lt offset readSize) :
  @Eq Bool (ir_byte_in_range_v1 writeBase writeSize (Nat.add readBase offset)) Bool.false :=
Or.rec
  (fun (before : Nat.le (Nat.add readBase readSize) writeBase) =>
    ir_byte_range_before_v1 writeBase writeSize (Nat.add readBase offset)
      (@Nat.le_trans (Nat.succ (Nat.add readBase offset)) (Nat.add readBase readSize) writeBase
        (@Nat.add_lt_add_left offset readSize inside readBase) before))
  (fun (after : Nat.le (Nat.add writeBase writeSize) readBase) =>
    ir_byte_range_after_v1 writeBase writeSize (Nat.add readBase offset)
      (@Nat.le_trans (Nat.add writeBase writeSize) readBase (Nat.add readBase offset)
        after (Nat.le_add_right readBase offset))) apart";

fn disjoint_source(clear: bool) -> (&'static str, String) {
    let (name, operation, word, point) = if clear {
        (
            "ir_byte_read_clear_disjoint_v1",
            "ir_byte_clear_v1 bytes writeBase writeSize",
            "",
            "ir_byte_clear_outside_v1 bytes writeBase writeSize (Nat.add readBase offset)",
        )
    } else {
        (
            "ir_byte_read_write_disjoint_v1",
            "ir_byte_write_word_v1 bytes writeBase writeSize word",
            "(word : Nat)",
            "ir_byte_write_outside_v1 bytes writeBase writeSize word (Nat.add readBase offset)",
        )
    };
    (name, format!("def {name} (bytes : Nat -> IROption Nat)
  (readBase readSize writeBase writeSize : Nat) {word}
  (apart : Or (Nat.le (Nat.add readBase readSize) writeBase)
              (Nat.le (Nat.add writeBase writeSize) readBase)) :
  @Eq (IROption Nat) (ir_byte_read_word_v1 ({operation}) readSize readBase)
    (ir_byte_read_word_v1 bytes readSize readBase) :=
ir_byte_read_range_congr_v1 ({operation}) bytes readSize readBase
  (fun (offset : Nat) (inside : Nat.lt offset readSize) =>
    {point} (ir_byte_disjoint_range_point_v1 readBase readSize writeBase writeSize offset apart inside))"))
}

fn written(mem: &str, address: &str, word: &str) -> String {
    format!(
        "(IRByteMemoryV1.mk (ir_byte_mem_allocs_v1 {mem})
      (ir_byte_write_word_v1 (ir_byte_mem_bytes_v1 {mem}) {address} 8 {word})
      (ir_byte_mem_next_v1 {mem}))"
    )
}

fn equality(ty: &str, left: &str, right: &str) -> String {
    format!("(@Eq {ty} ({left}) ({right}))")
}

fn conjunction(parts: &[(String, String)]) -> (String, String) {
    let (mut statement, mut proof) = parts.last().cloned().expect("nonempty local proof list");
    for (next_statement, next_proof) in parts[..parts.len() - 1].iter().rev() {
        proof = format!("(@And.intro {next_statement} {statement} ({next_proof}) ({proof}))");
        statement = format!("(And {next_statement} {statement})");
    }
    (statement, proof)
}

/// Both stores and both observations name the same successive memory values.
/// No equality of the complete byte maps is required (the second store changes
/// its own interval); only the disjoint first read uses range-local framing.
fn typed_pair_source() -> (&'static str, String) {
    let first = written("mem", "address1", "word1");
    let final_mem = written(&first, "address2", "word2");
    let mut header = "def ir_byte_store_pair_eight_v1 (ctx : IRByteContextV1)
  (ty1 ty2 : IRTy) (ptr1 ptr2 value1 value2 : IRScalar)
  (align1 align2 : Nat) (mem : IRByteMemoryV1)
  (layout1 layout2 : IRByteLayoutV1) (address1 address2 word1 word2 : Nat)"
        .to_owned();
    for i in [1, 2] {
        header.push_str(&format!("
  (lane{i} : @Eq (IROption Nat) (ir_byte_lane_size_v1 ty{i}) (@IROption.some Nat 8))
  (layoutFound{i} : @Eq (IROption IRByteLayoutV1) (ir_byte_layout_v1 ctx ty{i}) (@IROption.some IRByteLayoutV1 layout{i}))
  (layoutValid{i} : @Eq Bool (Bool.and (ir_nat_eqb 8 (ir_byte_layout_size_v1 layout{i})) (ir_byte_alignment_v1 (ir_byte_layout_align_v1 layout{i}))) Bool.true)
  (pointer{i} : @Eq (IROption Nat) (ir_byte_pointer_address_v1 ptr{i}) (@IROption.some Nat address{i}))
  (access{i} : @Eq Bool (ir_byte_accessible_v1 (ir_byte_mem_allocs_v1 mem) address{i} 8
    (ir_byte_effective_align_v1 align{i} (ir_byte_layout_align_v1 layout{i}))) Bool.true)
  (fits{i} : @Eq Bool (ir_byte_value_matches_v1 ctx ty{i} value{i}) Bool.true)
  (encoded{i} : @Eq (IROption Nat) (ir_byte_scalar_word_v1 ctx value{i}) (@IROption.some Nat word{i}))
  (decoded{i} : @Eq (IROption IRScalar) (ir_byte_decode_word_v1 ctx ty{i} word{i}) (@IROption.some IRScalar value{i}))
  (bounded{i} : Nat.lt word{i} ir_byte_limit_v1)"));
    }
    header.push_str(
        "
  (apart : Or (Nat.le (Nat.add address1 8) address2) (Nat.le (Nat.add address2 8) address1))",
    );
    let mut parts = Vec::new();
    for (i, before, after) in [
        (1, "mem".to_owned(), first.clone()),
        (2, first.clone(), final_mem.clone()),
    ] {
        let align =
            format!("(ir_byte_effective_align_v1 align{i} (ir_byte_layout_align_v1 layout{i}))");
        let actual =
            format!("ir_byte_store_v1 ctx ty{i} ptr{i} value{i} align{i} Bool.false {before}");
        let inner = format!("ir_byte_store_at_v1 ctx ty{i} address{i} value{i} 8 {align} {before}");
        let expected = format!("IRByteMemoryResultV1.value IRScalar.unit_ {after}");
        parts.push((equality("IRByteMemoryResultV1", &actual, &expected), format!(
            "@Eq.trans IRByteMemoryResultV1 ({actual}) ({inner}) ({expected})
              (ir_byte_store_dispatch_eight_v1 ctx ty{i} ptr{i} value{i} align{i} {before} layout{i} address{i}
                lane{i} layoutFound{i} layoutValid{i} pointer{i})
              (ir_byte_store_at_eight_rule_v1 ctx ty{i} address{i} value{i} {align} {before} word{i}
                access{i} fits{i} encoded{i} bounded{i})")));
    }
    for i in [1, 2] {
        let read = if i == 1 {
            format!("@Eq.trans (IROption Nat)
              (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 {final_mem}) 8 address1)
              (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 {first}) 8 address1)
              (@IROption.some Nat word1)
              (ir_byte_read_write_disjoint_v1 (ir_byte_mem_bytes_v1 {first}) address1 8 address2 8 word2 apart)
              (ir_byte_read_write_eight_v1 (ir_byte_mem_bytes_v1 mem) address1 word1 bounded1)")
        } else {
            format!(
                "ir_byte_read_write_eight_v1 (ir_byte_mem_bytes_v1 {first}) address2 word2 bounded2"
            )
        };
        let align =
            format!("(ir_byte_effective_align_v1 align{i} (ir_byte_layout_align_v1 layout{i}))");
        let actual = format!("ir_byte_load_v1 ctx ty{i} ptr{i} align{i} Bool.false {final_mem}");
        let inner = format!("ir_byte_load_at_v1 ctx ty{i} address{i} 8 {align} {final_mem}");
        let expected = format!("IRByteMemoryResultV1.value value{i} {final_mem}");
        parts.push((equality("IRByteMemoryResultV1", &actual, &expected), format!(
            "@Eq.trans IRByteMemoryResultV1 ({actual}) ({inner}) ({expected})
              (ir_byte_load_dispatch_eight_v1 ctx ty{i} ptr{i} align{i} {final_mem} layout{i} address{i}
                lane{i} layoutFound{i} layoutValid{i} pointer{i})
              (ir_byte_load_at_rule_v1 ctx ty{i} address{i} 8 {align} {final_mem} word{i} value{i}
                access{i} ({read}) decoded{i} fits{i})")));
    }
    let (claim, proof) = conjunction(&parts);
    (
        "ir_byte_store_pair_eight_v1",
        format!("{header} : {claim} :=\n{proof}"),
    )
}

pub(super) fn laws() -> Vec<(&'static str, String)> {
    let mut roots = [
        ("ir_byte_join_read_congr_v1", JOIN_CONGR),
        ("ir_byte_range_address_step_v1", ADDRESS_STEP),
        ("ir_byte_read_range_congr_v1", READ_RANGE_CONGR),
        ("ir_byte_range_before_v1", BEFORE),
        ("ir_byte_range_after_v1", AFTER),
        ("ir_byte_disjoint_range_point_v1", DISJOINT_POINT),
    ]
    .into_iter()
    .map(|(name, source)| (name, source.to_owned()))
    .collect::<Vec<_>>();
    roots.push(disjoint_source(false));
    roots.push(disjoint_source(true));
    roots.push(typed_pair_source());
    roots
}

impl Specification {
    pub(super) fn add_eval_ir_byte_range_laws_v1(&mut self) -> Result<(), SpecError> {
        for (name, source) in laws() {
            self.add_recursive_def(
                &source,
                "Checked range-local byte framing; no assumed read result or native authority.",
            )
            .map_err(|error| SpecError::TypeError(format!("{name}: {error}")))?;
            self.verify_definition(name)?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "eval_ir_byte_range_tests.rs"]
mod tests;
