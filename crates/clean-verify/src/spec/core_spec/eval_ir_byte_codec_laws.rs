// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Checked compositional laws for the existing little-endian byte codec.
//!
//! The option combiner below exposes one step of the actual reader, not a
//! second memory evaluator. The congruence proof is induction on the actual
//! read width and uses pointwise byte equality, without function extensionality.
//! The eight-byte theorem reconstructs the writer's quotient digits for every
//! canonical 64-bit word, arbitrary old byte map and arbitrary natural-number
//! base. Its width is fixed, not its values. Mathematical byte addresses do not
//! imply a valid machine allocation: typed store/load roundtrips, address
//! admissibility, allocation lifetime and native fidelity remain separate.

use crate::spec::{SpecError, Specification};

const JOIN: &str = r"def ir_byte_join_read_v1 (head : IROption Nat) (tail : IROption Nat) : IROption Nat :=
@IROption.rec Nat (fun (_ : IROption Nat) => IROption Nat)
  (@IROption.none Nat)
  (fun (byte : Nat) => @Bool.rec (fun (_ : Bool) => IROption Nat)
    (@IROption.none Nat)
    (@IROption.rec Nat (fun (_ : IROption Nat) => IROption Nat)
      (@IROption.none Nat)
      (fun (rest : Nat) => @IROption.some Nat (Nat.add byte (Nat.mul 256 rest))) tail)
    (ir_nat_ltb byte 256)) head";

const READ_ZERO: &str = r"def ir_byte_read_zero_v1
  (bytes : Nat -> IROption Nat) (base : Nat) :
  @Eq (IROption Nat) (ir_byte_read_word_v1 bytes 0 base) (@IROption.some Nat 0) :=
@Eq.refl (IROption Nat) (@IROption.some Nat 0)";

const READ_SUCC: &str = r"def ir_byte_read_succ_v1
  (bytes : Nat -> IROption Nat) (size : Nat) (base : Nat) :
  @Eq (IROption Nat) (ir_byte_read_word_v1 bytes (Nat.succ size) base)
    (ir_byte_join_read_v1 (bytes base) (ir_byte_read_word_v1 bytes size (Nat.succ base))) :=
@Eq.refl (IROption Nat)
  (ir_byte_join_read_v1 (bytes base) (ir_byte_read_word_v1 bytes size (Nat.succ base)))";

const READ_CONGR: &str = r"def ir_byte_read_congr_v1
  (left : Nat -> IROption Nat) (right : Nat -> IROption Nat)
  (same : forall (address : Nat), @Eq (IROption Nat) (left address) (right address))
  (size : Nat) (base : Nat) :
  @Eq (IROption Nat) (ir_byte_read_word_v1 left size base) (ir_byte_read_word_v1 right size base) :=
@Nat.rec
  (fun (count : Nat) => forall (address : Nat), @Eq (IROption Nat)
    (ir_byte_read_word_v1 left count address) (ir_byte_read_word_v1 right count address))
  (fun (address : Nat) => @Eq.refl (IROption Nat) (@IROption.some Nat 0))
  (fun (count : Nat)
    (ih : forall (address : Nat), @Eq (IROption Nat)
      (ir_byte_read_word_v1 left count address) (ir_byte_read_word_v1 right count address)) =>
    fun (address : Nat) =>
      @Eq.trans (IROption Nat)
        (ir_byte_join_read_v1 (left address) (ir_byte_read_word_v1 left count (Nat.succ address)))
        (ir_byte_join_read_v1 (right address) (ir_byte_read_word_v1 left count (Nat.succ address)))
        (ir_byte_join_read_v1 (right address) (ir_byte_read_word_v1 right count (Nat.succ address)))
        (@Eq.subst (IROption Nat)
          (fun (head : IROption Nat) => @Eq (IROption Nat)
            (ir_byte_join_read_v1 (left address) (ir_byte_read_word_v1 left count (Nat.succ address)))
            (ir_byte_join_read_v1 head (ir_byte_read_word_v1 left count (Nat.succ address))))
          (left address) (right address) (same address)
          (@Eq.refl (IROption Nat)
            (ir_byte_join_read_v1 (left address) (ir_byte_read_word_v1 left count (Nat.succ address)))))
        (@Eq.subst (IROption Nat)
          (fun (tail : IROption Nat) => @Eq (IROption Nat)
            (ir_byte_join_read_v1 (right address) (ir_byte_read_word_v1 left count (Nat.succ address)))
            (ir_byte_join_read_v1 (right address) tail))
          (ir_byte_read_word_v1 left count (Nat.succ address))
          (ir_byte_read_word_v1 right count (Nat.succ address)) (ih (Nat.succ address))
          (@Eq.refl (IROption Nat)
            (ir_byte_join_read_v1 (right address) (ir_byte_read_word_v1 left count (Nat.succ address))))))
  size base";

const READ_SUCCESS: &str = r"def ir_byte_read_success_v1
  (bytes : Nat -> IROption Nat) (size : Nat) (base : Nat) (byte : Nat) (rest : Nat)
  (head : @Eq (IROption Nat) (bytes base) (@IROption.some Nat byte))
  (bounded : @Eq Bool (ir_nat_ltb byte 256) Bool.true)
  (tail : @Eq (IROption Nat) (ir_byte_read_word_v1 bytes size (Nat.succ base)) (@IROption.some Nat rest)) :
  @Eq (IROption Nat) (ir_byte_read_word_v1 bytes (Nat.succ size) base)
    (@IROption.some Nat (Nat.add byte (Nat.mul 256 rest))) :=
@Eq.subst (IROption Nat)
  (fun (h : IROption Nat) => @Eq (IROption Nat)
    (ir_byte_join_read_v1 h (ir_byte_read_word_v1 bytes size (Nat.succ base)))
    (@IROption.some Nat (Nat.add byte (Nat.mul 256 rest))))
  (@IROption.some Nat byte) (bytes base)
  (@Eq.symm (IROption Nat) (bytes base) (@IROption.some Nat byte) head)
  (@Eq.subst (IROption Nat)
    (fun (t : IROption Nat) => @Eq (IROption Nat)
      (ir_byte_join_read_v1 (@IROption.some Nat byte) t)
      (@IROption.some Nat (Nat.add byte (Nat.mul 256 rest))))
    (@IROption.some Nat rest) (ir_byte_read_word_v1 bytes size (Nat.succ base))
    (@Eq.symm (IROption Nat) (ir_byte_read_word_v1 bytes size (Nat.succ base)) (@IROption.some Nat rest) tail)
    (@Eq.subst Bool
      (fun (valid : Bool) => @Eq (IROption Nat)
        (@Bool.rec (fun (_ : Bool) => IROption Nat) (@IROption.none Nat)
          (@IROption.some Nat (Nat.add byte (Nat.mul 256 rest))) valid)
        (@IROption.some Nat (Nat.add byte (Nat.mul 256 rest))))
      Bool.true (ir_nat_ltb byte 256)
      (@Eq.symm Bool (ir_nat_ltb byte 256) Bool.true bounded)
      (@Eq.refl (IROption Nat) (@IROption.some Nat (Nat.add byte (Nat.mul 256 rest))))))";

const READ_MISSING: &str = r"def ir_byte_read_missing_head_v1
  (bytes : Nat -> IROption Nat) (size : Nat) (base : Nat)
  (missing : @Eq (IROption Nat) (bytes base) (@IROption.none Nat)) :
  @Eq (IROption Nat) (ir_byte_read_word_v1 bytes (Nat.succ size) base) (@IROption.none Nat) :=
@Eq.subst (IROption Nat)
  (fun (head : IROption Nat) => @Eq (IROption Nat)
    (ir_byte_join_read_v1 head (ir_byte_read_word_v1 bytes size (Nat.succ base))) (@IROption.none Nat))
  (@IROption.none Nat) (bytes base)
  (@Eq.symm (IROption Nat) (bytes base) (@IROption.none Nat) missing)
  (@Eq.refl (IROption Nat) (@IROption.none Nat))";

const WRITE_INSIDE: &str = r"def ir_byte_write_inside_v1
  (bytes : Nat -> IROption Nat) (base : Nat) (size : Nat) (word : Nat) (address : Nat)
  (inside : @Eq Bool (ir_byte_in_range_v1 base size address) Bool.true) :
  @Eq (IROption Nat) (ir_byte_write_word_v1 bytes base size word address)
    (@IROption.some Nat (Nat.mod (Nat.div word (ir_nat_pow2 (Nat.mul 8 (Nat.sub address base)))) 256)) :=
@Eq.subst Bool
  (fun (valid : Bool) => @Eq (IROption Nat)
    (@Bool.rec (fun (_ : Bool) => IROption Nat) (bytes address)
      (@IROption.some Nat (Nat.mod (Nat.div word (ir_nat_pow2 (Nat.mul 8 (Nat.sub address base)))) 256)) valid)
    (@IROption.some Nat (Nat.mod (Nat.div word (ir_nat_pow2 (Nat.mul 8 (Nat.sub address base)))) 256)))
  Bool.true (ir_byte_in_range_v1 base size address)
  (@Eq.symm Bool (ir_byte_in_range_v1 base size address) Bool.true inside)
  (@Eq.refl (IROption Nat)
    (@IROption.some Nat (Nat.mod (Nat.div word (ir_nat_pow2 (Nat.mul 8 (Nat.sub address base)))) 256)))";

const LTB_OF_LT: &str = r"def ir_byte_ltb_of_lt_v1 (a : Nat) (b : Nat) (h : Nat.lt a b) :
  @Eq Bool (ir_nat_ltb a b) Bool.true :=
@Eq.trans Bool (ir_nat_ltb a b) (ir_nat_ltb_walk a b) Bool.true
  (ir_nat_ltb_walk_eq a b)
  (@Nat.rec
    (fun (x : Nat) => forall (y : Nat), Nat.lt x y -> @Eq Bool (ir_nat_ltb_walk x y) Bool.true)
    (fun (y : Nat) => @Nat.rec
      (fun (z : Nat) => Nat.lt 0 z -> @Eq Bool (ir_nat_ltb_walk 0 z) Bool.true)
      (fun (impossible : Nat.lt 0 0) => @False.elim (@Eq Bool Bool.false Bool.true)
        (Nat.not_succ_le_zero 0 impossible))
      (fun (z : Nat) (_ : Nat.lt 0 z -> @Eq Bool (ir_nat_ltb_walk 0 z) Bool.true) =>
        fun (_ : Nat.lt 0 (Nat.succ z)) => @Eq.refl Bool Bool.true) y)
    (fun (x : Nat)
      (ih : forall (y : Nat), Nat.lt x y -> @Eq Bool (ir_nat_ltb_walk x y) Bool.true) =>
      fun (y : Nat) => @Nat.rec
        (fun (z : Nat) => Nat.lt (Nat.succ x) z -> @Eq Bool (ir_nat_ltb_walk (Nat.succ x) z) Bool.true)
        (fun (impossible : Nat.lt (Nat.succ x) 0) => @False.elim (@Eq Bool Bool.false Bool.true)
          (Nat.not_succ_le_zero (Nat.succ x) impossible))
        (fun (z : Nat)
          (_ : Nat.lt (Nat.succ x) z -> @Eq Bool (ir_nat_ltb_walk (Nat.succ x) z) Bool.true) =>
          fun (less : Nat.lt (Nat.succ x) (Nat.succ z)) =>
            ih z (Nat.le_of_succ_le_succ (Nat.succ x) z less)) y)
    a b h)";

const LEB_OF_LE: &str = r"def ir_byte_leb_of_le_v1 (a : Nat) (b : Nat) (h : Nat.le a b) :
  @Eq Bool (ir_nat_leb a b) Bool.true :=
@Eq.trans Bool (ir_nat_leb a b) (ir_nat_leb_walk a b) Bool.true
  (ir_nat_leb_walk_eq a b)
  (@Nat.rec
    (fun (x : Nat) => forall (y : Nat), Nat.le x y -> @Eq Bool (ir_nat_leb_walk x y) Bool.true)
    (fun (y : Nat) => @Nat.rec
      (fun (z : Nat) => Nat.le 0 z -> @Eq Bool (ir_nat_leb_walk 0 z) Bool.true)
      (fun (_ : Nat.le 0 0) => @Eq.refl Bool Bool.true)
      (fun (z : Nat) (_ : Nat.le 0 z -> @Eq Bool (ir_nat_leb_walk 0 z) Bool.true) =>
        fun (_ : Nat.le 0 (Nat.succ z)) => @Eq.refl Bool Bool.true) y)
    (fun (x : Nat)
      (ih : forall (y : Nat), Nat.le x y -> @Eq Bool (ir_nat_leb_walk x y) Bool.true) =>
      fun (y : Nat) => @Nat.rec
        (fun (z : Nat) => Nat.le (Nat.succ x) z -> @Eq Bool (ir_nat_leb_walk (Nat.succ x) z) Bool.true)
        (fun (impossible : Nat.le (Nat.succ x) 0) => @False.elim (@Eq Bool Bool.false Bool.true)
          (Nat.not_succ_le_zero x impossible))
        (fun (z : Nat)
          (_ : Nat.le (Nat.succ x) z -> @Eq Bool (ir_nat_leb_walk (Nat.succ x) z) Bool.true) =>
          fun (less : Nat.le (Nat.succ x) (Nat.succ z)) =>
            ih z (Nat.le_of_succ_le_succ x z less)) y)
    a b h)";

const RANGE_OFFSET: &str = r"def ir_byte_range_offset_v1 (base : Nat) (size : Nat) (offset : Nat)
  (bounded : Nat.lt offset size) :
  @Eq Bool (ir_byte_in_range_v1 base size (Nat.add base offset)) Bool.true :=
@Eq.trans Bool
  (Bool.and (ir_nat_leb base (Nat.add base offset))
    (ir_nat_ltb (Nat.add base offset) (Nat.add base size)))
  (Bool.and Bool.true (ir_nat_ltb (Nat.add base offset) (Nat.add base size))) Bool.true
  (ir_eq_cong Bool Bool
    (fun (low : Bool) => Bool.and low (ir_nat_ltb (Nat.add base offset) (Nat.add base size)))
    (ir_nat_leb base (Nat.add base offset)) Bool.true
    (ir_byte_leb_of_le_v1 base (Nat.add base offset) (Nat.le_add_right base offset)))
  (ir_byte_ltb_of_lt_v1 (Nat.add base offset) (Nat.add base size)
    (Nat.add_lt_add_left offset size bounded base))";

const WRITE_DIGIT: &str = r"def ir_byte_write_digit_v1
  (bytes : Nat -> IROption Nat) (base : Nat) (size : Nat) (word : Nat) (offset : Nat)
  (bounded : Nat.lt offset size) :
  @Eq (IROption Nat) (ir_byte_write_word_v1 bytes base size word (Nat.add base offset))
    (@IROption.some Nat (Nat.mod (Nat.div word (ir_nat_pow2 (Nat.mul 8 offset))) 256)) :=
@Eq.trans (IROption Nat)
  (ir_byte_write_word_v1 bytes base size word (Nat.add base offset))
  (@IROption.some Nat (Nat.mod (Nat.div word
    (ir_nat_pow2 (Nat.mul 8 (Nat.sub (Nat.add base offset) base)))) 256))
  (@IROption.some Nat (Nat.mod (Nat.div word (ir_nat_pow2 (Nat.mul 8 offset))) 256))
  (ir_byte_write_inside_v1 bytes base size word (Nat.add base offset)
    (ir_byte_range_offset_v1 base size offset bounded))
  (ir_eq_cong Nat (IROption Nat)
    (fun (index : Nat) => @IROption.some Nat (Nat.mod (Nat.div word (ir_nat_pow2 (Nat.mul 8 index))) 256))
    (Nat.sub (Nat.add base offset) base) offset
    (@Eq.trans Nat (Nat.sub (Nat.add base offset) base) (Nat.sub (Nat.add offset base) base) offset
      (ir_eq_cong Nat Nat (fun (address : Nat) => Nat.sub address base)
        (Nat.add base offset) (Nat.add offset base) (Nat.add_comm base offset))
      (Nat.add_sub_cancel offset base)))";

const DIV_ONE: &str = r"def ir_byte_div_one_v1 (word : Nat) : @Eq Nat (Nat.div word 1) word :=
ir_byte_div_unique_v1 word 1 word 0 (Nat.zero_lt_succ 0) (Nat.zero_lt_succ 0)
  (@Eq.symm Nat (Nat.mul word 1) word (Nat.mul_one word))";

const DIV_BELOW: &str = r"def ir_byte_div_below_v1 (word : Nat) (divisor : Nat)
  (positive : Nat.lt 0 divisor) (bounded : Nat.lt word divisor) :
  @Eq Nat (Nat.div word divisor) 0 :=
ir_byte_div_unique_v1 word divisor 0 word positive bounded
  (@Eq.symm Nat (Nat.add (Nat.mul 0 divisor) word) word
    (@Eq.trans Nat (Nat.add (Nat.mul 0 divisor) word) (Nat.add 0 word) word
      (ir_eq_cong Nat Nat (fun (zero : Nat) => Nat.add zero word)
        (Nat.mul 0 divisor) 0 (Nat.zero_mul divisor))
      (Nat.zero_add word)))";

const RADIX_STEP: &str = r"def ir_byte_radix_step_v1 (word : Nat) (divisor : Nat)
  (positive : Nat.lt 0 divisor) :
  @Eq Nat
    (Nat.add (Nat.mod (Nat.div word divisor) 256)
      (Nat.mul 256 (Nat.div word (Nat.mul divisor 256))))
    (Nat.div word divisor) :=
@Eq.trans Nat
  (Nat.add (Nat.mod (Nat.div word divisor) 256) (Nat.mul 256 (Nat.div word (Nat.mul divisor 256))))
  (Nat.add (Nat.mod (Nat.div word divisor) 256) (Nat.mul 256 (Nat.div (Nat.div word divisor) 256)))
  (Nat.div word divisor)
  (ir_eq_cong Nat Nat
    (fun (next : Nat) => Nat.add (Nat.mod (Nat.div word divisor) 256) (Nat.mul 256 next))
    (Nat.div word (Nat.mul divisor 256)) (Nat.div (Nat.div word divisor) 256)
    (@Eq.symm Nat (Nat.div (Nat.div word divisor) 256) (Nat.div word (Nat.mul divisor 256))
      (ir_byte_div_compose_v1 word divisor 256 positive (Nat.zero_lt_succ 255))))
  (@Eq.trans Nat
    (Nat.add (Nat.mod (Nat.div word divisor) 256) (Nat.mul 256 (Nat.div (Nat.div word divisor) 256)))
    (Nat.add (Nat.mul 256 (Nat.div (Nat.div word divisor) 256)) (Nat.mod (Nat.div word divisor) 256))
    (Nat.div word divisor)
    (Nat.add_comm (Nat.mod (Nat.div word divisor) 256) (Nat.mul 256 (Nat.div (Nat.div word divisor) 256)))
    (@Eq.trans Nat
      (Nat.add (Nat.mul 256 (Nat.div (Nat.div word divisor) 256)) (Nat.mod (Nat.div word divisor) 256))
      (Nat.add (Nat.mul (Nat.div (Nat.div word divisor) 256) 256) (Nat.mod (Nat.div word divisor) 256))
      (Nat.div word divisor)
      (ir_eq_cong Nat Nat (fun (product : Nat) => Nat.add product (Nat.mod (Nat.div word divisor) 256))
        (Nat.mul 256 (Nat.div (Nat.div word divisor) 256)) (Nat.mul (Nat.div (Nat.div word divisor) 256) 256)
        (Nat.mul_comm 256 (Nat.div (Nat.div word divisor) 256)))
      (Nat.div_add_mod (Nat.div word divisor) 256)))";

/// Build a fixed-width proof term, not a table of tested word values. Every
/// address, old byte map and canonical 64-bit word remains universally bound.
/// Closed widths let the kernel check the eight powers directly; symbolic
/// quotient reconstruction comes from the general checked division laws.
fn read_write_eight_source() -> String {
    let modulus = 1_u128 << 64;
    let header = format!(
        "def ir_byte_read_write_eight_v1 (bytes : Nat -> IROption Nat) (base : Nat) (word : Nat)\n\
         (bounded : Nat.lt word {modulus}) :\n\
         @Eq (IROption Nat) (ir_byte_read_word_v1 (ir_byte_write_word_v1 bytes base 8 word) 8 base)\n\
         (@IROption.some Nat word) :=\n"
    );
    let written = "(ir_byte_write_word_v1 bytes base 8 word)";
    let q8 = format!("(Nat.div word {modulus})");
    let mut tail = format!(
        "@Eq.trans (IROption Nat) (ir_byte_read_word_v1 {written} 0 (Nat.add base 8))\n\
         (@IROption.some Nat 0) (@IROption.some Nat {q8})\n\
         (ir_byte_read_zero_v1 {written} (Nat.add base 8))\n\
         (ir_eq_cong Nat (IROption Nat) (fun (value : Nat) => @IROption.some Nat value) 0 {q8}\n\
           (@Eq.symm Nat {q8} 0 (ir_byte_div_below_v1 word {modulus} (Nat.zero_lt_succ {}) bounded)))",
        modulus - 1
    );
    for i in (0..8).rev() {
        let divisor = 1_u128 << (8 * i);
        let quotient = format!("(Nat.div word {divisor})");
        let next = format!("(Nat.div word {})", divisor * 256);
        let size = 8 - i;
        let tail_size = size - 1;
        let mut offset_bound = format!("Nat.zero_le {}", 7 - i);
        for k in 0..=i {
            offset_bound = format!("@Nat.succ_le_succ {k} {} ({offset_bound})", 7 - i + k);
        }
        tail = format!(
            "@Eq.trans (IROption Nat) (ir_byte_read_word_v1 {written} {size} (Nat.add base {i}))\n\
             (@IROption.some Nat (Nat.add (Nat.mod {quotient} 256) (Nat.mul 256 {next}))) (@IROption.some Nat {quotient})\n\
             (ir_byte_read_success_v1 {written} {tail_size} (Nat.add base {i}) (Nat.mod {quotient} 256) {next}\n\
               (ir_byte_write_digit_v1 bytes base 8 word {i} ({offset_bound}))\n\
               (ir_byte_ltb_of_lt_v1 (Nat.mod {quotient} 256) 256 (Nat.mod_lt {quotient} 256 (Nat.zero_lt_succ 255)))\n\
               ({tail}))\n\
             (ir_eq_cong Nat (IROption Nat) (fun (value : Nat) => @IROption.some Nat value)\n\
               (Nat.add (Nat.mod {quotient} 256) (Nat.mul 256 {next})) {quotient}\n\
               (ir_byte_radix_step_v1 word {divisor} (Nat.zero_lt_succ {})))",
            divisor - 1
        );
    }
    format!(
        "{header}@Eq.trans (IROption Nat) (ir_byte_read_word_v1 {written} 8 base)\n\
         (@IROption.some Nat (Nat.div word 1)) (@IROption.some Nat word)\n\
         ({tail}) (ir_eq_cong Nat (IROption Nat) (fun (value : Nat) => @IROption.some Nat value) (Nat.div word 1) word (ir_byte_div_one_v1 word))"
    )
}

const LAWS: &[(&str, &str)] = &[
    ("ir_byte_join_read_v1", JOIN),
    ("ir_byte_read_zero_v1", READ_ZERO),
    ("ir_byte_read_succ_v1", READ_SUCC),
    ("ir_byte_read_congr_v1", READ_CONGR),
    ("ir_byte_read_success_v1", READ_SUCCESS),
    ("ir_byte_read_missing_head_v1", READ_MISSING),
    ("ir_byte_write_inside_v1", WRITE_INSIDE),
    ("ir_byte_ltb_of_lt_v1", LTB_OF_LT),
    ("ir_byte_leb_of_le_v1", LEB_OF_LE),
    ("ir_byte_range_offset_v1", RANGE_OFFSET),
    ("ir_byte_write_digit_v1", WRITE_DIGIT),
    ("ir_byte_div_one_v1", DIV_ONE),
    ("ir_byte_div_below_v1", DIV_BELOW),
    ("ir_byte_radix_step_v1", RADIX_STEP),
];

impl Specification {
    /// Install codec laws over the actual byte-memory definitions. The public
    /// byte-profile constructor checks each new root and its authority closure.
    pub(super) fn add_eval_ir_byte_codec_laws(&mut self) -> Result<(), SpecError> {
        for &(name, source) in LAWS {
            self.add_recursive_def(
                source,
                "Checked compositional law over the actual byte reader/writer; no native or typed-roundtrip authority.",
            )?;
            self.verify_definition(name)?;
        }
        self.add_recursive_def(
            &read_write_eight_source(),
            "Universal canonical eight-byte roundtrip over the actual reader/writer; no allocation, typed-pointer or native authority.",
        )?;
        self.verify_definition("ir_byte_read_write_eight_v1")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Name;

    fn checked(spec: &Specification, name: &str) {
        let definition = spec.get_definition(name).expect("installed codec law");
        assert!(!definition.is_axiom);
        assert!(definition.elaborated_value.is_some());
        spec.verify_definition(name).expect("kernel replay");
        let name = Name::from_string(name);
        assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
        assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
    }

    fn reject_type_mismatch(spec: &mut Specification, name: &str, source: &str) {
        let error = spec
            .add_recursive_def(source, "Adversarial codec claim")
            .expect_err(name);
        crate::test_utils::assert_type_mismatch_rejection(&error, name);
        assert!(spec.get_definition(name).is_none());
    }

    #[test]
    fn actual_byte_reader_codec_laws_are_checked() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
            for &(name, _) in LAWS {
                checked(&spec, name);
            }
            checked(&spec, "ir_byte_read_write_eight_v1");
            spec.add_recursive_def(
                r"def byte_codec_two_digits (bytes : Nat -> IROption Nat) (base : Nat) (low : Nat) (high : Nat)
  (h0 : @Eq (IROption Nat) (bytes base) (@IROption.some Nat low))
  (h1 : @Eq (IROption Nat) (bytes (Nat.succ base)) (@IROption.some Nat high))
  (b0 : @Eq Bool (ir_nat_ltb low 256) Bool.true)
  (b1 : @Eq Bool (ir_nat_ltb high 256) Bool.true) :
  @Eq (IROption Nat) (ir_byte_read_word_v1 bytes 2 base)
    (@IROption.some Nat (Nat.add low (Nat.mul 256 (Nat.add high (Nat.mul 256 0))))) :=
ir_byte_read_success_v1 bytes 1 base low (Nat.add high (Nat.mul 256 0)) h0 b0
  (ir_byte_read_success_v1 bytes 0 (Nat.succ base) high 0 h1 b1
    (ir_byte_read_zero_v1 bytes (Nat.succ (Nat.succ base))))",
                "Two arbitrary canonical digits compose through the actual reader",
            ).unwrap();
            checked(&spec, "byte_codec_two_digits");
        });
    }

    #[test]
    fn actual_eight_byte_codec_accepts_canonical_bounds() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
            let modulus = 1_u128 << 64;
            for (i, (base, word)) in [
                (0, 0),
                (17, 1),
                (4096, 0x0123_4567_89ab_cdef),
                (u128::from(u64::MAX) - 7, u128::from(u64::MAX)),
            ]
            .into_iter()
            .enumerate()
            {
                let name = format!("byte_codec_bound_case_{i}");
                let source = format!(
                    "def {name} (bytes : Nat -> IROption Nat) :\n\
                     @Eq (IROption Nat) (ir_byte_read_word_v1 (ir_byte_write_word_v1 bytes {base} 8 {word}) 8 {base})\n\
                     (@IROption.some Nat {word}) :=\n\
                     ir_byte_read_write_eight_v1 bytes {base} {word} (Nat.le_add_right {} {})",
                    word + 1,
                    modulus - word - 1,
                );
                spec.add_recursive_def(
                    &source,
                    "Closed boundary application, old bytes remain arbitrary",
                )
                .unwrap();
                checked(&spec, &name);
            }
        });
    }

    #[test]
    fn actual_codec_rejects_changed_radix_and_false_premises() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = Specification::new_eval_ir_byte_prelude_spec_v1().unwrap();
            for (name, source) in [
                ("wrong_codec_head", READ_SUCC.replace("ir_byte_join_read_v1 (bytes base)", "ir_byte_join_read_v1 (@IROption.some Nat 255)")),
                ("wrong_codec_missing", READ_MISSING.replace("(@IROption.none Nat) :=", "(@IROption.some Nat 0) :=")),
                ("wrong_codec_inside", WRITE_INSIDE.replacen("Bool.true)", "Bool.false)", 1)),
                ("wrong_codec_byte_bound", "def wrong_codec_byte_bound : @Eq (IROption Nat) (ir_byte_read_word_v1 (fun (_ : Nat) => @IROption.some Nat 256) 1 0) (@IROption.some Nat 256) := ir_byte_read_success_v1 (fun (_ : Nat) => @IROption.some Nat 256) 0 0 256 0 (@Eq.refl (IROption Nat) (@IROption.some Nat 256)) (@Eq.refl Bool Bool.true) (@Eq.refl (IROption Nat) (@IROption.some Nat 0))".into()),
            ] {
                let old_name = source.split_whitespace().nth(1).unwrap();
                let source = source.replacen(old_name, name, 1);
                reject_type_mismatch(&mut spec, name, &source);
            }
            let roundtrip = read_write_eight_source();
            let (header, proof) = roundtrip.split_once(":=").unwrap();
            let (step_header, step_proof) = RADIX_STEP.split_once(":=").unwrap();
            for (name, source) in [
                ("wrong_codec_width", format!("{}:={proof}", header.replace(") 8 base)", ") 7 base)"))),
                ("wrong_codec_radix", format!("{}:={step_proof}", step_header.replace("Nat.mul 256", "Nat.mul 255"))),
                ("wrong_codec_word_bound", "def wrong_codec_word_bound (bytes : Nat -> IROption Nat) (base : Nat) : @Eq (IROption Nat) (ir_byte_read_word_v1 (ir_byte_write_word_v1 bytes base 8 18446744073709551616) 8 base) (@IROption.some Nat 18446744073709551616) := ir_byte_read_write_eight_v1 bytes base 18446744073709551616 (Nat.le_refl 18446744073709551616)".into()),
            ] {
                let old_name = source.split_whitespace().nth(1).unwrap();
                let source = source.replacen(old_name, name, 1);
                reject_type_mismatch(&mut spec, name, &source);
            }
        });
    }
}
