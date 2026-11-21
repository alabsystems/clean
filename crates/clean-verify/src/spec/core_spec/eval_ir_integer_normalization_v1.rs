// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Additive, all-Nat multiplication agreement for the unchanged EvalIR model.
//! The induction reconciles the opposite addition order in the two recursive
//! definitions. Residue transport is separately opt-in and requires the
//! existing checked total-restoring division package. Neither evaluator,
//! native reduction authority, proof limit nor model admission changes here.

use super::{preflight, register_rows_and_check_described, verify_root};
use crate::spec::{SpecError, Specification};

#[cfg(test)]
#[path = "eval_ir_integer_normalization_v1_tests.rs"]
mod tests;

pub(super) const PRODUCT_ROOT: &str = "ir_nat_mul_canonical_agrees_v1";
pub(super) const PRODUCT: &[(&str, &str)] = &[(
    PRODUCT_ROOT,
    r"def ir_nat_mul_canonical_agrees_v1 (a b : Nat) :
@Eq Nat (ir_nat_mul a b) (Nat.mul a b) :=
@Nat.rec
  (fun (k : Nat) => @Eq Nat (ir_nat_mul a k) (Nat.mul a k))
  (@Eq.refl Nat 0)
  (fun (k : Nat) (ih : @Eq Nat (ir_nat_mul a k) (Nat.mul a k)) =>
    @Eq.trans Nat (Nat.add a (ir_nat_mul a k))
      (Nat.add a (Nat.mul a k)) (Nat.add (Nat.mul a k) a)
      (ir_eq_cong Nat Nat (fun (product : Nat) => Nat.add a product)
        (ir_nat_mul a k) (Nat.mul a k) ih)
      (@Nat.add_comm a (Nat.mul a k)))
  b",
)];

const RESIDUE_ROOTS: &[&str] = &[
    "ir_nat_mul_rem_total_agrees_v1",
    "ir_wrap_mul_total_agrees_v1",
];
const RESIDUES: &[(&str, &str)] = &[
    (
        "ir_nat_mul_rem_total_agrees_v1",
        r"def ir_nat_mul_rem_total_agrees_v1 (a b divisor : Nat) :
@Eq Nat (ir_nat_rem (ir_nat_mul a b) divisor)
  (ir_nat_rem_total_v1 (Nat.mul a b) divisor) :=
@Eq.trans Nat (ir_nat_rem (ir_nat_mul a b) divisor)
  (ir_nat_rem (Nat.mul a b) divisor)
  (ir_nat_rem_total_v1 (Nat.mul a b) divisor)
  (ir_eq_cong Nat Nat (fun (product : Nat) => ir_nat_rem product divisor)
    (ir_nat_mul a b) (Nat.mul a b) (ir_nat_mul_canonical_agrees_v1 a b))
  (ir_nat_rem_total_agrees_v1 (Nat.mul a b) divisor)",
    ),
    (
        "ir_wrap_mul_total_agrees_v1",
        r"def ir_wrap_mul_total_agrees_v1 (width a b : Nat) :
@Eq Nat (ir_wrap width (ir_nat_mul a b))
  (ir_nat_rem_total_v1 (Nat.mul a b) (ir_nat_pow2 width)) :=
ir_nat_mul_rem_total_agrees_v1 a b (ir_nat_pow2 width)",
    ),
];

fn install_residues_transactionally(
    spec: &mut Specification,
    rows: impl Iterator<Item = (&'static str, &'static str)> + Clone,
) -> Result<(), SpecError> {
    preflight(spec, rows.clone())?;
    // Recheck stored values and their actual rooted authority closures. The
    // presence of a familiar name, cached metadata or an axiom is insufficient.
    for root in [PRODUCT_ROOT, "ir_nat_rem_total_agrees_v1"] {
        verify_root(spec, root)?;
    }
    let mut candidate = spec.clone();
    register_rows_and_check_described(
        &mut candidate,
        rows,
        RESIDUE_ROOTS,
        "constructive all-Nat product/residue transport through unchanged EvalIR arithmetic",
    )?;
    *spec = candidate;
    Ok(())
}

impl Specification {
    pub(crate) fn add_eval_ir_integer_multiplication_law_v1(&mut self) -> Result<(), SpecError> {
        preflight(self, PRODUCT.iter().copied())?;
        register_rows_and_check_described(
            self,
            PRODUCT.iter().copied(),
            &[PRODUCT_ROOT],
            "constructive all-Nat multiplication agreement by induction and addition commutativity",
        )
    }

    pub(crate) fn install_eval_ir_integer_mul_residue_laws_v1_checked(
        &mut self,
    ) -> Result<(), SpecError> {
        install_residues_transactionally(self, RESIDUES.iter().copied())
    }
}
