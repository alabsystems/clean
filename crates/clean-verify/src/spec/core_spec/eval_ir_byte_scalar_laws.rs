// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Checked canonical-word laws for the existing byte/world scalar semantics.
//!
//! Range premises describe admissible bit patterns; they do not assume an
//! instruction's answer. The wrap proofs unfold the actual quotient and
//! substitute below-modulus or one-subtraction guards. The Add/Sub equations
//! retain the reference wrapping semantics; general range and affine
//! normalization theorems are not supplied here. No alternate arithmetic,
//! provider contract, source-language rule, or native authority is introduced.
//! Eq/Ne retain both actual operands. Select retains an arbitrary Boolean and
//! derives evaluation and carrier preservation without choosing a branch.

use crate::spec::{SpecError, Specification};

const LAWS: &[(&str, &str)] = &[
    (
        "ir_byte_div_go_below_v1",
        r"def ir_byte_div_go_below_v1 (fuel : Nat) (a : Nat) (b : Nat) (h : @Eq Bool (ir_nat_ltb a b) Bool.true) : @Eq Nat (ir_div_go fuel a b) 0 :=
@Nat.rec
  (fun (k : Nat) => @Eq Nat (ir_div_go k a b) 0)
  (@Eq.refl Nat 0)
  (fun (k : Nat) (_ih : @Eq Nat (ir_div_go k a b) 0) =>
    ir_eq_cong Bool Nat
      (fun (guard : Bool) => @Bool.rec (fun (_ : Bool) => Nat)
        (Nat.succ (ir_div_go k (Nat.sub a b) b)) 0 guard)
      (ir_nat_ltb a b) Bool.true h)
  fuel",
    ),
    (
        "ir_byte_wrap_canonical_v1",
        r"def ir_byte_wrap_canonical_v1 (width : Nat) (word : Nat) (h : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 width)) Bool.true) : @Eq Nat (ir_wrap width word) word :=
ir_eq_cong Nat Nat
  (fun (quotient : Nat) => Nat.sub word (ir_nat_mul (ir_nat_pow2 width) quotient))
  (ir_div_go word word (ir_nat_pow2 width)) 0
  (ir_byte_div_go_below_v1 word word (ir_nat_pow2 width) h)",
    ),
    (
        "ir_byte_div_go_once_v1",
        r"def ir_byte_div_go_once_v1 (fuel : Nat) (a : Nat) (b : Nat)
  (first : @Eq Bool (ir_nat_ltb a b) Bool.false)
  (rest : @Eq Bool (ir_nat_ltb (Nat.sub a b) b) Bool.true) :
  @Eq Nat (ir_div_go (Nat.succ fuel) a b) 1 :=
@Eq.trans Nat (ir_div_go (Nat.succ fuel) a b)
  (Nat.succ (ir_div_go fuel (Nat.sub a b) b)) 1
  (ir_eq_cong Bool Nat
    (fun (guard : Bool) => @Bool.rec (fun (_ : Bool) => Nat)
      (Nat.succ (ir_div_go fuel (Nat.sub a b) b)) 0 guard)
    (ir_nat_ltb a b) Bool.false first)
  (ir_eq_cong Nat Nat (fun (quotient : Nat) => Nat.succ quotient)
    (ir_div_go fuel (Nat.sub a b) b) 0
    (ir_byte_div_go_below_v1 fuel (Nat.sub a b) b rest))",
    ),
    (
        "ir_byte_wrap_once_v1",
        r"def ir_byte_wrap_once_v1 (width : Nat) (predecessor : Nat)
  (first : @Eq Bool (ir_nat_ltb (Nat.succ predecessor) (ir_nat_pow2 width)) Bool.false)
  (rest : @Eq Bool (ir_nat_ltb (Nat.sub (Nat.succ predecessor) (ir_nat_pow2 width)) (ir_nat_pow2 width)) Bool.true) :
  @Eq Nat (ir_wrap width (Nat.succ predecessor)) (Nat.sub (Nat.succ predecessor) (ir_nat_pow2 width)) :=
ir_eq_cong Nat Nat
  (fun (quotient : Nat) => Nat.sub (Nat.succ predecessor) (ir_nat_mul (ir_nat_pow2 width) quotient))
  (ir_div_go (Nat.succ predecessor) (Nat.succ predecessor) (ir_nat_pow2 width)) 1
  (ir_byte_div_go_once_v1 predecessor (Nat.succ predecessor) (ir_nat_pow2 width) first rest)",
    ),
    (
        "ir_byte_add_uint_below_v1",
        r"def ir_byte_add_uint_below_v1 (width : Nat) (a : Nat) (b : Nat)
  (h : @Eq Bool (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)) Bool.true) :
  @Eq IRStepResult (ir_binop_eval IRBinOp.add (IRTy.uint_ width) (IRScalar.int_ a) (IRScalar.int_ b))
    (IRStepResult.value (IRScalar.int_ (Nat.add a b))) :=
ir_eq_cong Nat IRStepResult (fun (word : Nat) => IRStepResult.value (IRScalar.int_ word))
  (ir_wrap width (Nat.add a b)) (Nat.add a b) (ir_byte_wrap_canonical_v1 width (Nat.add a b) h)",
    ),
    (
        "ir_byte_add_int_below_v1",
        r"def ir_byte_add_int_below_v1 (width : Nat) (a : Nat) (b : Nat)
  (h : @Eq Bool (ir_nat_ltb (Nat.add a b) (ir_nat_pow2 width)) Bool.true) :
  @Eq IRStepResult (ir_binop_eval IRBinOp.add (IRTy.int_ width) (IRScalar.int_ a) (IRScalar.int_ b))
    (IRStepResult.value (IRScalar.int_ (Nat.add a b))) :=
ir_byte_add_uint_below_v1 width a b h",
    ),
    (
        "ir_byte_sub_wrap_canonical_v1",
        r"def ir_byte_sub_wrap_canonical_v1 (width : Nat) (a : Nat) (b : Nat)
  (ha : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 width)) Bool.true)
  (hb : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 width)) Bool.true) :
  @Eq Nat (ir_sub_wrap width a b) (ir_wrap width (Nat.sub (Nat.add a (ir_nat_pow2 width)) b)) :=
@Eq.trans Nat (ir_sub_wrap width a b)
  (ir_wrap width (Nat.sub (Nat.add a (ir_nat_pow2 width)) (ir_wrap width b)))
  (ir_wrap width (Nat.sub (Nat.add a (ir_nat_pow2 width)) b))
  (ir_eq_cong Nat Nat
    (fun (word : Nat) => ir_wrap width (Nat.sub (Nat.add word (ir_nat_pow2 width)) (ir_wrap width b)))
    (ir_wrap width a) a (ir_byte_wrap_canonical_v1 width a ha))
  (ir_eq_cong Nat Nat
    (fun (word : Nat) => ir_wrap width (Nat.sub (Nat.add a (ir_nat_pow2 width)) word))
    (ir_wrap width b) b (ir_byte_wrap_canonical_v1 width b hb))",
    ),
    (
        "ir_byte_sub_uint_canonical_v1",
        r"def ir_byte_sub_uint_canonical_v1 (width : Nat) (a : Nat) (b : Nat)
  (ha : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 width)) Bool.true)
  (hb : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 width)) Bool.true) :
  @Eq IRStepResult (ir_binop_eval IRBinOp.sub (IRTy.uint_ width) (IRScalar.int_ a) (IRScalar.int_ b))
    (IRStepResult.value (IRScalar.int_ (ir_wrap width (Nat.sub (Nat.add a (ir_nat_pow2 width)) b)))) :=
ir_eq_cong Nat IRStepResult (fun (word : Nat) => IRStepResult.value (IRScalar.int_ word))
  (ir_sub_wrap width a b) (ir_wrap width (Nat.sub (Nat.add a (ir_nat_pow2 width)) b))
  (ir_byte_sub_wrap_canonical_v1 width a b ha hb)",
    ),
    (
        "ir_byte_sub_int_canonical_v1",
        r"def ir_byte_sub_int_canonical_v1 (width : Nat) (a : Nat) (b : Nat)
  (ha : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 width)) Bool.true)
  (hb : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 width)) Bool.true) :
  @Eq IRStepResult (ir_binop_eval IRBinOp.sub (IRTy.int_ width) (IRScalar.int_ a) (IRScalar.int_ b))
    (IRStepResult.value (IRScalar.int_ (ir_wrap width (Nat.sub (Nat.add a (ir_nat_pow2 width)) b)))) :=
ir_byte_sub_uint_canonical_v1 width a b ha hb",
    ),
    (
        "ir_byte_u64_fits_v1",
        r"def ir_byte_u64_fits_v1 (word : Nat) (h : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true) : @Eq Bool (ir_byte_integer_fits_v1 (IRTy.uint_ 64) word) Bool.true := h",
    ),
    (
        "ir_byte_i64_fits_v1",
        r"def ir_byte_i64_fits_v1 (word : Nat) (h : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true) : @Eq Bool (ir_byte_integer_fits_v1 (IRTy.int_ 64) word) Bool.true := h",
    ),
    (
        "ir_byte_u64_value_fits_v1",
        r"def ir_byte_u64_value_fits_v1 (ctx : IRByteContextV1) (word : Nat) (h : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true) : @Eq Bool (ir_byte_value_matches_v1 ctx (IRTy.uint_ 64) (IRScalar.int_ word)) Bool.true := ir_byte_u64_fits_v1 word h",
    ),
    (
        "ir_byte_i64_value_fits_v1",
        r"def ir_byte_i64_value_fits_v1 (ctx : IRByteContextV1) (word : Nat) (h : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 64)) Bool.true) : @Eq Bool (ir_byte_value_matches_v1 ctx (IRTy.int_ 64) (IRScalar.int_ word)) Bool.true := ir_byte_i64_fits_v1 word h",
    ),
    (
        "ir_byte_icmp_uint_eq_canonical_v1",
        r"def ir_byte_icmp_uint_eq_canonical_v1 (width a b : Nat)
  (aFits : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 width)) Bool.true)
  (bFits : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 width)) Bool.true) : @Eq IRStepResult
  (ir_icmp_eval IRICmpOp.eq_ (IRTy.uint_ width) (IRScalar.int_ a) (IRScalar.int_ b))
  (IRStepResult.value (IRScalar.bool_ (ir_nat_eqb a b))) :=
@Eq.trans IRStepResult
  (ir_icmp_eval IRICmpOp.eq_ (IRTy.uint_ width) (IRScalar.int_ a) (IRScalar.int_ b))
  (IRStepResult.value (IRScalar.bool_ (ir_nat_eqb a (ir_wrap width b))))
  (IRStepResult.value (IRScalar.bool_ (ir_nat_eqb a b)))
  (ir_eq_cong Nat IRStepResult
    (fun (x : Nat) => IRStepResult.value (IRScalar.bool_ (ir_nat_eqb x (ir_wrap width b))))
    (ir_wrap width a) a (ir_byte_wrap_canonical_v1 width a aFits))
  (ir_eq_cong Nat IRStepResult
    (fun (y : Nat) => IRStepResult.value (IRScalar.bool_ (ir_nat_eqb a y)))
    (ir_wrap width b) b (ir_byte_wrap_canonical_v1 width b bFits))",
    ),
    (
        "ir_byte_icmp_int_eq_canonical_v1",
        r"def ir_byte_icmp_int_eq_canonical_v1 (width a b : Nat)
  (aFits : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 width)) Bool.true)
  (bFits : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 width)) Bool.true) : @Eq IRStepResult
  (ir_icmp_eval IRICmpOp.eq_ (IRTy.int_ width) (IRScalar.int_ a) (IRScalar.int_ b))
  (IRStepResult.value (IRScalar.bool_ (ir_nat_eqb a b))) :=
ir_byte_icmp_uint_eq_canonical_v1 width a b aFits bFits",
    ),
    (
        "ir_byte_icmp_uint_ne_canonical_v1",
        r"def ir_byte_icmp_uint_ne_canonical_v1 (width a b : Nat)
  (aFits : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 width)) Bool.true)
  (bFits : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 width)) Bool.true) : @Eq IRStepResult
  (ir_icmp_eval IRICmpOp.ne_ (IRTy.uint_ width) (IRScalar.int_ a) (IRScalar.int_ b))
  (IRStepResult.value (IRScalar.bool_ (Bool.not (ir_nat_eqb a b)))) :=
@Eq.trans IRStepResult
  (ir_icmp_eval IRICmpOp.ne_ (IRTy.uint_ width) (IRScalar.int_ a) (IRScalar.int_ b))
  (IRStepResult.value (IRScalar.bool_ (Bool.not (ir_nat_eqb a (ir_wrap width b)))))
  (IRStepResult.value (IRScalar.bool_ (Bool.not (ir_nat_eqb a b))))
  (ir_eq_cong Nat IRStepResult
    (fun (x : Nat) => IRStepResult.value (IRScalar.bool_ (Bool.not (ir_nat_eqb x (ir_wrap width b)))))
    (ir_wrap width a) a (ir_byte_wrap_canonical_v1 width a aFits))
  (ir_eq_cong Nat IRStepResult
    (fun (y : Nat) => IRStepResult.value (IRScalar.bool_ (Bool.not (ir_nat_eqb a y))))
    (ir_wrap width b) b (ir_byte_wrap_canonical_v1 width b bFits))",
    ),
    (
        "ir_byte_icmp_int_ne_canonical_v1",
        r"def ir_byte_icmp_int_ne_canonical_v1 (width a b : Nat)
  (aFits : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 width)) Bool.true)
  (bFits : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 width)) Bool.true) : @Eq IRStepResult
  (ir_icmp_eval IRICmpOp.ne_ (IRTy.int_ width) (IRScalar.int_ a) (IRScalar.int_ b))
  (IRStepResult.value (IRScalar.bool_ (Bool.not (ir_nat_eqb a b)))) :=
ir_byte_icmp_uint_ne_canonical_v1 width a b aFits bFits",
    ),
    (
        "ir_byte_select_eval_v1",
        r"def ir_byte_select_eval_v1 (flag : Bool) (a b : IRScalar) : @Eq IRStepResult
  (ir_select_eval (IRScalar.bool_ flag) a b)
  (IRStepResult.value (@Bool.rec (fun (_ : Bool) => IRScalar) b a flag)) :=
@Bool.rec
  (fun (choice : Bool) => @Eq IRStepResult
    (ir_select_eval (IRScalar.bool_ choice) a b)
    (IRStepResult.value (@Bool.rec (fun (_ : Bool) => IRScalar) b a choice)))
  (@Eq.refl IRStepResult (IRStepResult.value b))
  (@Eq.refl IRStepResult (IRStepResult.value a)) flag",
    ),
    (
        "ir_byte_select_value_fits_v1",
        r"def ir_byte_select_value_fits_v1 (ctx : IRByteContextV1) (ty : IRTy)
  (flag : Bool) (a b : IRScalar)
  (aFits : @Eq Bool (ir_byte_value_matches_v1 ctx ty a) Bool.true)
  (bFits : @Eq Bool (ir_byte_value_matches_v1 ctx ty b) Bool.true) : @Eq Bool
  (ir_byte_value_matches_v1 ctx ty (@Bool.rec (fun (_ : Bool) => IRScalar) b a flag)) Bool.true :=
@Bool.rec
  (fun (choice : Bool) => @Eq Bool
    (ir_byte_value_matches_v1 ctx ty (@Bool.rec (fun (_ : Bool) => IRScalar) b a choice)) Bool.true)
  bFits aFits flag",
    ),
    (
        "ir_byte_select_word_eval_v1",
        r"def ir_byte_select_word_eval_v1 (flag : Bool) (a b : Nat) : @Eq IRStepResult
  (ir_select_eval (IRScalar.bool_ flag) (IRScalar.int_ a) (IRScalar.int_ b))
  (IRStepResult.value (IRScalar.int_ (@Bool.rec (fun (_ : Bool) => Nat) b a flag))) :=
@Bool.rec
  (fun (choice : Bool) => @Eq IRStepResult
    (ir_select_eval (IRScalar.bool_ choice) (IRScalar.int_ a) (IRScalar.int_ b))
    (IRStepResult.value (IRScalar.int_ (@Bool.rec (fun (_ : Bool) => Nat) b a choice))))
  (@Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ b)))
  (@Eq.refl IRStepResult (IRStepResult.value (IRScalar.int_ a))) flag",
    ),
    (
        "ir_byte_select_word_bound_v1",
        r"def ir_byte_select_word_bound_v1 (width : Nat) (flag : Bool) (a b : Nat)
  (aFits : @Eq Bool (ir_nat_ltb a (ir_nat_pow2 width)) Bool.true)
  (bFits : @Eq Bool (ir_nat_ltb b (ir_nat_pow2 width)) Bool.true) : @Eq Bool
  (ir_nat_ltb (@Bool.rec (fun (_ : Bool) => Nat) b a flag) (ir_nat_pow2 width)) Bool.true :=
@Bool.rec
  (fun (choice : Bool) => @Eq Bool
    (ir_nat_ltb (@Bool.rec (fun (_ : Bool) => Nat) b a choice) (ir_nat_pow2 width)) Bool.true)
  bFits aFits flag",
    ),
    (
        "ir_byte_icmp_uint_eq_zero_canonical_v1",
        r"def ir_byte_icmp_uint_eq_zero_canonical_v1 (width : Nat) (word : Nat) (h : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 width)) Bool.true) : @Eq IRStepResult
  (ir_icmp_eval IRICmpOp.eq_ (IRTy.uint_ width) (IRScalar.int_ word) (IRScalar.int_ 0))
  (IRStepResult.value (IRScalar.bool_ (ir_nat_eqb word 0))) :=
ir_eq_cong Nat IRStepResult
  (fun (n : Nat) => IRStepResult.value (IRScalar.bool_ (ir_nat_eqb n 0)))
  (ir_wrap width word) word (ir_byte_wrap_canonical_v1 width word h)",
    ),
    (
        "ir_byte_icmp_int_ne_zero_canonical_v1",
        r"def ir_byte_icmp_int_ne_zero_canonical_v1 (width : Nat) (word : Nat) (h : @Eq Bool (ir_nat_ltb word (ir_nat_pow2 width)) Bool.true) : @Eq IRStepResult
  (ir_icmp_eval IRICmpOp.ne_ (IRTy.int_ width) (IRScalar.int_ word) (IRScalar.int_ 0))
  (IRStepResult.value (IRScalar.bool_ (Bool.not (ir_nat_eqb word 0)))) :=
ir_eq_cong Nat IRStepResult
  (fun (n : Nat) => IRStepResult.value (IRScalar.bool_ (Bool.not (ir_nat_eqb n 0))))
  (ir_wrap width word) word (ir_byte_wrap_canonical_v1 width word h)",
    ),
    (
        "ir_byte_eqb_succ_zero_v1",
        r"def ir_byte_eqb_succ_zero_v1 (predecessor : Nat) : @Eq Bool (ir_nat_eqb (Nat.succ predecessor) 0) Bool.false := ir_nat_eqb_walk_eq (Nat.succ predecessor) 0",
    ),
    (
        "ir_byte_icmp_uint_eq_zero_positive_v1",
        r"def ir_byte_icmp_uint_eq_zero_positive_v1 (width : Nat) (predecessor : Nat) (h : @Eq Bool (ir_nat_ltb (Nat.succ predecessor) (ir_nat_pow2 width)) Bool.true) : @Eq IRStepResult
  (ir_icmp_eval IRICmpOp.eq_ (IRTy.uint_ width) (IRScalar.int_ (Nat.succ predecessor)) (IRScalar.int_ 0))
  (IRStepResult.value (IRScalar.bool_ Bool.false)) :=
@Eq.trans IRStepResult
  (ir_icmp_eval IRICmpOp.eq_ (IRTy.uint_ width) (IRScalar.int_ (Nat.succ predecessor)) (IRScalar.int_ 0))
  (IRStepResult.value (IRScalar.bool_ (ir_nat_eqb (Nat.succ predecessor) 0)))
  (IRStepResult.value (IRScalar.bool_ Bool.false))
  (ir_byte_icmp_uint_eq_zero_canonical_v1 width (Nat.succ predecessor) h)
  (ir_eq_cong Bool IRStepResult (fun (b : Bool) => IRStepResult.value (IRScalar.bool_ b))
    (ir_nat_eqb (Nat.succ predecessor) 0) Bool.false (ir_byte_eqb_succ_zero_v1 predecessor))",
    ),
    (
        "ir_byte_icmp_int_ne_zero_positive_v1",
        r"def ir_byte_icmp_int_ne_zero_positive_v1 (width : Nat) (predecessor : Nat) (h : @Eq Bool (ir_nat_ltb (Nat.succ predecessor) (ir_nat_pow2 width)) Bool.true) : @Eq IRStepResult
  (ir_icmp_eval IRICmpOp.ne_ (IRTy.int_ width) (IRScalar.int_ (Nat.succ predecessor)) (IRScalar.int_ 0))
  (IRStepResult.value (IRScalar.bool_ Bool.true)) :=
@Eq.trans IRStepResult
  (ir_icmp_eval IRICmpOp.ne_ (IRTy.int_ width) (IRScalar.int_ (Nat.succ predecessor)) (IRScalar.int_ 0))
  (IRStepResult.value (IRScalar.bool_ (Bool.not (ir_nat_eqb (Nat.succ predecessor) 0))))
  (IRStepResult.value (IRScalar.bool_ Bool.true))
  (ir_byte_icmp_int_ne_zero_canonical_v1 width (Nat.succ predecessor) h)
  (ir_eq_cong Bool IRStepResult (fun (b : Bool) => IRStepResult.value (IRScalar.bool_ (Bool.not b)))
    (ir_nat_eqb (Nat.succ predecessor) 0) Bool.false (ir_byte_eqb_succ_zero_v1 predecessor))",
    ),
];

impl Specification {
    /// Install real quantified scalar lemmas after the byte-profile types.
    /// The public byte-profile constructor rechecks and audits every new root.
    pub(super) fn add_eval_ir_byte_scalar_laws_v1(&mut self) -> Result<(), SpecError> {
        for &(name, source) in LAWS {
            self.add_recursive_def(
                source,
                "Canonical bit-pattern theorem over actual EvalIR arithmetic; no instruction-answer, provider, or native-fidelity axiom.",
            )
            .map_err(|error| match error {
                SpecError::ParseError(detail) => SpecError::ParseError(format!("{name}: {detail}")),
                SpecError::ElabError(detail) => SpecError::ElabError(format!("{name}: {detail}")),
                SpecError::TypeError(detail) => SpecError::TypeError(format!("{name}: {detail}")),
                SpecError::EnvError(detail) => SpecError::EnvError(format!("{name}: {detail}")),
                other => other,
            })?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "eval_ir_byte_scalar_laws_tests.rs"]
mod tests;
