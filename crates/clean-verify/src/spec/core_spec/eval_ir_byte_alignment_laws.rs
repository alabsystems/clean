// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive rounding laws for the actual byte allocator's base calculation.
//!
//! The generic laws cover every positive alignment. Eight-byte frame-slot
//! facts are specializations, not independent arithmetic models. Bounds and
//! divisibility follow from checked Euclidean decomposition and cancellation;
//! neither is supplied as an assumption. Canonical-address range, allocator
//! overlap/liveness, and native execution remain separate obligations.

use crate::spec::{SpecError, Specification};

const LAWS: &[(&str, &str)] = &[
    (
        "ir_byte_mod_unique_v1",
        r"def ir_byte_mod_unique_v1
  (n : Nat) (d : Nat) (q : Nat) (r : Nat)
  (hd : Nat.lt 0 d) (hr : Nat.lt r d)
  (heq : @Eq Nat n (Nat.add (Nat.mul q d) r)) :
@Eq Nat (Nat.mod n d) r :=
@Nat.add_left_cancel (Nat.mul q d) (Nat.mod n d) r
  (@Eq.trans Nat (Nat.add (Nat.mul q d) (Nat.mod n d)) n
    (Nat.add (Nat.mul q d) r)
    (@Eq.subst Nat
      (fun (quotient : Nat) => @Eq Nat (Nat.add (Nat.mul quotient d) (Nat.mod n d)) n)
      (Nat.div n d) q (ir_byte_div_unique_v1 n d q r hd hr heq)
      (@Nat.div_add_mod n d))
    heq)",
    ),
    (
        "ir_byte_mod_multiple_v1",
        r"def ir_byte_mod_multiple_v1 (q : Nat) (d : Nat) (positive : Nat.lt 0 d) :
@Eq Nat (Nat.mod (Nat.mul q d) d) 0 :=
ir_byte_mod_unique_v1 (Nat.mul q d) d q 0 positive positive
  (@Eq.refl Nat (Nat.mul q d))",
    ),
    (
        "ir_byte_mod_multiple_offset_v1",
        r"def ir_byte_mod_multiple_offset_v1 (q : Nat) (d : Nat) (positive : Nat.lt 0 d) :
@Eq Nat (Nat.mod (Nat.add (Nat.mul q d) d) d) 0 :=
ir_byte_mod_unique_v1 (Nat.add (Nat.mul q d) d) d (Nat.succ q) 0 positive positive
  (@Eq.symm Nat (Nat.mul (Nat.succ q) d) (Nat.add (Nat.mul q d) d)
    (ir_byte_radix_succ_mul_v1 q d))",
    ),
    (
        "ir_byte_align_above_v1",
        r"def ir_byte_align_above_v1
  (cursor : Nat) (align : Nat) (positive : Nat.lt 0 align) :
Nat.le cursor (ir_byte_aligned_base_v1 cursor align) :=
@Nat.rec
  (fun (a : Nat) => Nat.lt 0 a -> Nat.le cursor (ir_byte_aligned_base_v1 cursor a))
  (fun (impossible : Nat.lt 0 0) =>
    @False.elim (Nat.le cursor (ir_byte_aligned_base_v1 cursor 0))
      (@Nat.not_succ_le_zero 0 impossible))
  (fun (k : Nat)
    (_ih : Nat.lt 0 k -> Nat.le cursor (ir_byte_aligned_base_v1 cursor k))
    (_positive : Nat.lt 0 (Nat.succ k)) =>
    @Nat.ulpRound.le_of_add_le_add_right cursor
      (Nat.mul (Nat.div (Nat.add cursor k) (Nat.succ k)) (Nat.succ k)) k
      (@Eq.subst Nat
        (fun (lower : Nat) => Nat.le lower
          (Nat.add (Nat.mul (Nat.div (Nat.add cursor k) (Nat.succ k)) (Nat.succ k)) k))
        (Nat.add (Nat.mul (Nat.div (Nat.add cursor k) (Nat.succ k)) (Nat.succ k))
          (Nat.mod (Nat.add cursor k) (Nat.succ k)))
        (Nat.add cursor k)
        (@Nat.div_add_mod (Nat.add cursor k) (Nat.succ k))
        (@Nat.add_le_add_left (Nat.mod (Nat.add cursor k) (Nat.succ k)) k
          (@Nat.le_of_succ_le_succ (Nat.mod (Nat.add cursor k) (Nat.succ k)) k
            (@Nat.mod_lt (Nat.add cursor k) (Nat.succ k) (@Nat.zero_lt_succ k)))
          (Nat.mul (Nat.div (Nat.add cursor k) (Nat.succ k)) (Nat.succ k)))))
  align positive",
    ),
    (
        "ir_byte_align_mod_v1",
        r"def ir_byte_align_mod_v1
  (cursor : Nat) (align : Nat) (positive : Nat.lt 0 align) :
@Eq Nat (Nat.mod (ir_byte_aligned_base_v1 cursor align) align) 0 :=
ir_byte_mod_multiple_v1 (Nat.div (Nat.add cursor (Nat.sub align 1)) align) align positive",
    ),
    (
        "ir_byte_align_offset_mod_v1",
        r"def ir_byte_align_offset_mod_v1
  (cursor : Nat) (align : Nat) (positive : Nat.lt 0 align) :
@Eq Nat (Nat.mod (Nat.add (ir_byte_aligned_base_v1 cursor align) align) align) 0 :=
ir_byte_mod_multiple_offset_v1 (Nat.div (Nat.add cursor (Nat.sub align 1)) align) align positive",
    ),
    (
        "ir_byte_align_positive_v1",
        r"def ir_byte_align_positive_v1
  (cursor : Nat) (align : Nat) (alignment_positive : Nat.lt 0 align)
  (cursor_positive : Nat.lt 0 cursor) :
Nat.lt 0 (ir_byte_aligned_base_v1 cursor align) :=
@Nat.le_trans 1 cursor (ir_byte_aligned_base_v1 cursor align) cursor_positive
  (ir_byte_align_above_v1 cursor align alignment_positive)",
    ),
    (
        "ir_byte_align_eight_above_v1",
        r"def ir_byte_align_eight_above_v1 (cursor : Nat) :
Nat.le cursor (ir_byte_aligned_base_v1 cursor 8) :=
ir_byte_align_above_v1 cursor 8 (@Nat.zero_lt_succ 7)",
    ),
    (
        "ir_byte_align_eight_mod_v1",
        r"def ir_byte_align_eight_mod_v1 (cursor : Nat) :
@Eq Nat (Nat.mod (ir_byte_aligned_base_v1 cursor 8) 8) 0 :=
ir_byte_align_mod_v1 cursor 8 (@Nat.zero_lt_succ 7)",
    ),
    (
        "ir_byte_align_eight_offset_eight_mod_v1",
        r"def ir_byte_align_eight_offset_eight_mod_v1 (cursor : Nat) :
@Eq Nat (Nat.mod (Nat.add (ir_byte_aligned_base_v1 cursor 8) 8) 8) 0 :=
ir_byte_align_offset_mod_v1 cursor 8 (@Nat.zero_lt_succ 7)",
    ),
    (
        "ir_byte_align_eight_positive_v1",
        r"def ir_byte_align_eight_positive_v1 (cursor : Nat) (positive : Nat.lt 0 cursor) :
Nat.lt 0 (ir_byte_aligned_base_v1 cursor 8) :=
ir_byte_align_positive_v1 cursor 8 (@Nat.zero_lt_succ 7) positive",
    ),
];

impl Specification {
    /// Install after the actual byte-memory base definition and radix laws.
    /// A consuming constructor must independently replay and audit these roots.
    pub(super) fn add_eval_ir_byte_alignment_laws_v1(&mut self) -> Result<(), SpecError> {
        for &(name, source) in LAWS {
            self.add_recursive_def(
                source,
                "Constructive positive-alignment law for the actual byte allocator; no postalignment, allocation-success, or native-fidelity assumption.",
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
mod tests {
    use super::*;
    use clean_kernel::Name;

    fn spec() -> Specification {
        Specification::new_eval_ir_byte_prelude_spec_v1()
            .expect("actual public byte-profile prelude with quantified alignment laws")
    }

    fn assert_checked(spec: &Specification, name: &str) {
        let definition = spec.get_definition(name).expect("registered checked term");
        assert!(!definition.is_axiom);
        assert!(definition.elaborated_value.is_some());
        spec.verify_definition(name)
            .expect("independent rooted kernel replay");
        let name = Name::from_string(name);
        assert!(spec
            .env()
            .axiom_deps(&name)
            .expect("root exists")
            .is_empty());
        assert!(spec
            .env()
            .trust_marker_deps(&name)
            .expect("root exists")
            .is_empty());
    }

    fn witness(spec: &mut Specification, name: &str, source: &str) {
        spec.add_recursive_def(source, "Actual allocator-rounding theorem consumer")
            .unwrap_or_else(|error| panic!("{name}: {error}"));
        assert_checked(spec, name);
    }

    fn reject_type_mismatch(spec: &mut Specification, name: &str, source: &str) {
        let error = spec
            .add_recursive_def(source, "Deliberately invalid allocator-rounding claim")
            .expect_err("incorrect arithmetic must not be certified");
        crate::test_utils::assert_type_mismatch_rejection(&error, name);
        assert!(spec.get_definition(name).is_none());
    }

    #[test]
    fn quantified_alignment_laws_replay_without_axioms_or_trust_markers() {
        crate::test_utils::run_with_stack(|| {
            let spec = spec();
            for &(name, _) in LAWS {
                assert_checked(&spec, name);
            }
        });
    }

    #[test]
    fn actual_rounding_boundaries_and_generic_non_power_of_two_arithmetic() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = spec();
            // Mathematical rounding works for all positive divisors. These
            // facts do not override the allocator's power-of-two guard.
            for (cursor, align, expected) in [
                (0_u128, 8_u128, 0_u128),
                (1, 8, 8),
                (7, 8, 8),
                (8, 8, 8),
                (9, 8, 16),
                (17, 1, 17),
                (7, 3, 9),
                (17, 16, 32),
                // Rounding itself can exceed a canonical 64-bit address;
                // representability is a separate actual allocation guard.
                (18_446_744_073_709_551_615, 8, 18_446_744_073_709_551_616),
            ] {
                let name = format!("alignment_boundary_{cursor}_{align}");
                witness(&mut spec, &name, &format!(
                    "def {name} : @Eq Nat (ir_byte_aligned_base_v1 {cursor} {align}) {expected} := @Eq.refl Nat {expected}"
                ));
            }
            witness(
                &mut spec,
                "alignment_generic_consumer",
                r"def alignment_generic_consumer
  (cursor : Nat) (align : Nat) (positive : Nat.lt 0 align) :
Nat.le cursor (ir_byte_aligned_base_v1 cursor align) :=
ir_byte_align_above_v1 cursor align positive",
            );
            witness(
                &mut spec,
                "alignment_positive_consumer",
                r"def alignment_positive_consumer
  (cursor : Nat) (positive : Nat.lt 0 cursor) :
Nat.lt 0 (ir_byte_aligned_base_v1 cursor 8) :=
ir_byte_align_eight_positive_v1 cursor positive",
            );
            witness(
                &mut spec,
                "alignment_two_slot_consumer",
                r"def alignment_two_slot_consumer
  (cursor : Nat) :
And (@Eq Nat (Nat.mod (ir_byte_aligned_base_v1 cursor 8) 8) 0)
    (@Eq Nat (Nat.mod (Nat.add (ir_byte_aligned_base_v1 cursor 8) 8) 8) 0) :=
@And.intro
  (@Eq Nat (Nat.mod (ir_byte_aligned_base_v1 cursor 8) 8) 0)
  (@Eq Nat (Nat.mod (Nat.add (ir_byte_aligned_base_v1 cursor 8) 8) 8) 0)
  (ir_byte_align_eight_mod_v1 cursor) (ir_byte_align_eight_offset_eight_mod_v1 cursor)",
            );
        });
    }

    #[test]
    fn rounding_down_unaligned_offsets_and_false_positivity_are_rejected() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = spec();
            // Each rejection has a checked observation of the actual result,
            // not just a failed attempt to elaborate an unknown declaration.
            for (name, actual, expected, wrong) in [
                ("rounding_down", "ir_byte_aligned_base_v1 9 8", 16, 8),
                (
                    "unaligned_offset",
                    "Nat.mod (Nat.add (ir_byte_aligned_base_v1 1 8) 1) 8",
                    1,
                    0,
                ),
                ("zero_is_not_positive", "ir_byte_aligned_base_v1 0 8", 0, 8),
            ] {
                let valid = format!("alignment_valid_{name}");
                witness(
                    &mut spec,
                    &valid,
                    &format!(
                        "def {valid} : @Eq Nat ({actual}) {expected} := @Eq.refl Nat {expected}"
                    ),
                );
                let invalid = format!("alignment_invalid_{name}");
                reject_type_mismatch(
                    &mut spec,
                    &invalid,
                    &format!("def {invalid} : @Eq Nat ({actual}) {wrong} := @Eq.refl Nat {wrong}"),
                );
            }
            witness(
                &mut spec,
                "alignment_zero_divisor_observation",
                r"def alignment_zero_divisor_observation :
@Eq Nat (ir_byte_aligned_base_v1 1 0) 0 := @Eq.refl Nat 0",
            );
            reject_type_mismatch(
                &mut spec,
                "alignment_zero_divisor_lower_bound",
                r"def alignment_zero_divisor_lower_bound :
Nat.le 1 (ir_byte_aligned_base_v1 1 0) := @Nat.le_refl 1",
            );
            reject_type_mismatch(
                &mut spec,
                "alignment_zero_cursor_positive",
                r"def alignment_zero_cursor_positive :
Nat.lt 0 (ir_byte_aligned_base_v1 0 8) := @Nat.zero_lt_succ 0",
            );
        });
    }
}
