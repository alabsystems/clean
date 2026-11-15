// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Input-only, width-generic unsigned comparisons on actual integer carriers.
//!
//! These fixed laws eliminate the actual evaluator's two `ir_wrap` calls using
//! canonical input bounds. Signed and unsigned nominal carriers remain exact;
//! the opcode, not the carrier, selects unsigned bit-pattern comparison. The
//! result is the original Nat observer, not a supplied answer or branch proof.
//! Ordinary ByteV1 supplies every prerequisite. This opt-in extension changes
//! no evaluator, default profile, cache, resource limit, or admission authority.

use super::{preflight, register_rows_and_check};
use crate::spec::{SpecError, Specification};

// Each expansion is an immutable proof source, not an operation/evaluator API.
// Keep symbolic operands inside both congruences: no full-width wrap reduction.
macro_rules! unsigned_law {
    ($name:literal, $op:literal, $answer:literal, $middle:literal,
     $left:literal, $right:literal) => {
        concat!(
            "def ",
            $name,
            " (width a b : Nat)\n",
            "  (aBound : Nat.lt a (ir_nat_pow2 width))\n",
            "  (bBound : Nat.lt b (ir_nat_pow2 width)) :\n",
            "@Eq IRStepResult\n",
            "  (ir_icmp_eval IRICmpOp.",
            $op,
            " (IRTy.uint_ width) (IRScalar.int_ a) (IRScalar.int_ b))\n",
            "  (IRStepResult.value (IRScalar.bool_ (",
            $answer,
            "))) :=\n",
            "@Eq.trans IRStepResult\n",
            "  (ir_icmp_eval IRICmpOp.",
            $op,
            " (IRTy.uint_ width) (IRScalar.int_ a) (IRScalar.int_ b))\n",
            "  (IRStepResult.value (IRScalar.bool_ (",
            $middle,
            ")))\n",
            "  (IRStepResult.value (IRScalar.bool_ (",
            $answer,
            ")))\n",
            "  (ir_eq_cong Nat IRStepResult\n",
            "    (fun (x : Nat) => IRStepResult.value (IRScalar.bool_ (",
            $left,
            ")))\n",
            "    (ir_wrap width a) a\n",
            "    (ir_byte_wrap_canonical_v1 width a\n",
            "      (ir_byte_ltb_of_lt_v1 a (ir_nat_pow2 width) aBound)))\n",
            "  (ir_eq_cong Nat IRStepResult\n",
            "    (fun (y : Nat) => IRStepResult.value (IRScalar.bool_ (",
            $right,
            ")))\n",
            "    (ir_wrap width b) b\n",
            "    (ir_byte_wrap_canonical_v1 width b\n",
            "      (ir_byte_ltb_of_lt_v1 b (ir_nat_pow2 width) bBound)))"
        )
    };
}

macro_rules! signed_carrier_law {
    ($name:literal, $op:literal, $answer:literal, $unsigned:literal) => {
        concat!(
            "def ",
            $name,
            " (width a b : Nat)\n",
            "  (aBound : Nat.lt a (ir_nat_pow2 width))\n",
            "  (bBound : Nat.lt b (ir_nat_pow2 width)) :\n",
            "@Eq IRStepResult\n",
            "  (ir_icmp_eval IRICmpOp.",
            $op,
            " (IRTy.int_ width) (IRScalar.int_ a) (IRScalar.int_ b))\n",
            "  (IRStepResult.value (IRScalar.bool_ (",
            $answer,
            "))) :=\n",
            $unsigned,
            " width a b aBound bBound"
        )
    };
}

pub(super) const ROOTS: &[&str] = &[
    "ir_byte_icmp_uint_ult_canonical_v1",
    "ir_byte_icmp_int_ult_canonical_v1",
    "ir_byte_icmp_uint_ule_canonical_v1",
    "ir_byte_icmp_int_ule_canonical_v1",
    "ir_byte_icmp_uint_ugt_canonical_v1",
    "ir_byte_icmp_int_ugt_canonical_v1",
    "ir_byte_icmp_uint_uge_canonical_v1",
    "ir_byte_icmp_int_uge_canonical_v1",
];

pub(super) const LAWS: &[(&str, &str)] = &[
    (
        "ir_byte_icmp_uint_ult_canonical_v1",
        unsigned_law!(
            "ir_byte_icmp_uint_ult_canonical_v1",
            "ult",
            "ir_nat_ltb a b",
            "ir_nat_ltb a (ir_wrap width b)",
            "ir_nat_ltb x (ir_wrap width b)",
            "ir_nat_ltb a y"
        ),
    ),
    (
        "ir_byte_icmp_int_ult_canonical_v1",
        signed_carrier_law!(
            "ir_byte_icmp_int_ult_canonical_v1",
            "ult",
            "ir_nat_ltb a b",
            "ir_byte_icmp_uint_ult_canonical_v1"
        ),
    ),
    (
        "ir_byte_icmp_uint_ule_canonical_v1",
        unsigned_law!(
            "ir_byte_icmp_uint_ule_canonical_v1",
            "ule",
            "ir_nat_leb a b",
            "ir_nat_leb a (ir_wrap width b)",
            "ir_nat_leb x (ir_wrap width b)",
            "ir_nat_leb a y"
        ),
    ),
    (
        "ir_byte_icmp_int_ule_canonical_v1",
        signed_carrier_law!(
            "ir_byte_icmp_int_ule_canonical_v1",
            "ule",
            "ir_nat_leb a b",
            "ir_byte_icmp_uint_ule_canonical_v1"
        ),
    ),
    (
        "ir_byte_icmp_uint_ugt_canonical_v1",
        unsigned_law!(
            "ir_byte_icmp_uint_ugt_canonical_v1",
            "ugt",
            "ir_nat_ltb b a",
            "ir_nat_ltb (ir_wrap width b) a",
            "ir_nat_ltb (ir_wrap width b) x",
            "ir_nat_ltb y a"
        ),
    ),
    (
        "ir_byte_icmp_int_ugt_canonical_v1",
        signed_carrier_law!(
            "ir_byte_icmp_int_ugt_canonical_v1",
            "ugt",
            "ir_nat_ltb b a",
            "ir_byte_icmp_uint_ugt_canonical_v1"
        ),
    ),
    (
        "ir_byte_icmp_uint_uge_canonical_v1",
        unsigned_law!(
            "ir_byte_icmp_uint_uge_canonical_v1",
            "uge",
            "ir_nat_leb b a",
            "ir_nat_leb (ir_wrap width b) a",
            "ir_nat_leb (ir_wrap width b) x",
            "ir_nat_leb y a"
        ),
    ),
    (
        "ir_byte_icmp_int_uge_canonical_v1",
        signed_carrier_law!(
            "ir_byte_icmp_int_uge_canonical_v1",
            "uge",
            "ir_nat_leb b a",
            "ir_byte_icmp_uint_uge_canonical_v1"
        ),
    ),
];

pub(super) fn install_transactionally(
    spec: &mut Specification,
    rows: impl Iterator<Item = (&'static str, &'static str)> + Clone,
) -> Result<(), SpecError> {
    preflight(spec, rows.clone())?;
    let mut candidate = spec.clone();
    register_rows_and_check(&mut candidate, rows, ROOTS)?;
    *spec = candidate;
    Ok(())
}

impl Specification {
    /// Add checked actual unsigned comparisons from canonical inputs only.
    /// The clone-once transaction checks exact stored declarations and strict
    /// rooted closure before replacing the owner. Failed installs are atomic.
    pub(crate) fn install_eval_ir_unsigned_compare_laws_v1_checked(
        &mut self,
    ) -> Result<(), SpecError> {
        install_transactionally(self, LAWS.iter().copied())
    }
}
