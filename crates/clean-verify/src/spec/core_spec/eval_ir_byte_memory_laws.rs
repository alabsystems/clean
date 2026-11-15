// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pointwise framing laws for the actual versioned byte-memory definitions.
//!
//! Every equation is universally quantified and kernel checked. Range and
//! owner hypotheses are equations about the profile's real decision functions,
//! not certificate-supplied meanings. Pointwise observations avoid assuming
//! function extensionality for the persistent byte map.
//!
//! These laws do not establish typed load/store roundtrips or native allocator
//! fidelity. The next encoding obligation is radix-256 reconstruction for a
//! canonical word below 2^(8 * size), followed by the actual typed decoder and
//! access checks. In particular, preserving retired bytes does not make a dead
//! allocation accessible to a typed load.

use crate::spec::{SpecError, Specification};

const SRC_WRITE_OUTSIDE: &str = r"def ir_byte_write_outside_v1
  (bytes : Nat -> IROption Nat) (base : Nat) (size : Nat) (word : Nat) (address : Nat)
  (outside : @Eq Bool (ir_byte_in_range_v1 base size address) Bool.false) :
  @Eq (IROption Nat) (ir_byte_write_word_v1 bytes base size word address) (bytes address) :=
@Eq.subst Bool
  (fun (inside : Bool) => @Eq (IROption Nat)
    (@Bool.rec (fun (_ : Bool) => IROption Nat)
      (bytes address)
      (@IROption.some Nat (Nat.mod (Nat.div word (ir_nat_pow2 (Nat.mul 8 (Nat.sub address base)))) 256))
      inside)
    (bytes address))
  Bool.false (ir_byte_in_range_v1 base size address)
  (@Eq.symm Bool (ir_byte_in_range_v1 base size address) Bool.false outside)
  (@Eq.refl (IROption Nat) (bytes address))";

const SRC_CLEAR_OUTSIDE: &str = r"def ir_byte_clear_outside_v1
  (bytes : Nat -> IROption Nat) (base : Nat) (size : Nat) (address : Nat)
  (outside : @Eq Bool (ir_byte_in_range_v1 base size address) Bool.false) :
  @Eq (IROption Nat) (ir_byte_clear_v1 bytes base size address) (bytes address) :=
@Eq.subst Bool
  (fun (inside : Bool) => @Eq (IROption Nat)
    (@Bool.rec (fun (_ : Bool) => IROption Nat) (bytes address) (@IROption.none Nat) inside)
    (bytes address))
  Bool.false (ir_byte_in_range_v1 base size address)
  (@Eq.symm Bool (ir_byte_in_range_v1 base size address) Bool.false outside)
  (@Eq.refl (IROption Nat) (bytes address))";

const SRC_RETIRE_BYTES: &str = r"def ir_byte_retire_bytes_v1
  (owner : Nat) (mem : IRByteMemoryV1) (address : Nat) :
  @Eq (IROption Nat)
    (ir_byte_mem_bytes_v1 (ir_byte_retire_v1 owner mem) address)
    (ir_byte_mem_bytes_v1 mem address) :=
@Eq.refl (IROption Nat) (ir_byte_mem_bytes_v1 mem address)";

const SRC_RETIRE_NEXT: &str = r"def ir_byte_retire_next_v1
  (owner : Nat) (mem : IRByteMemoryV1) :
  @Eq Nat (ir_byte_mem_next_v1 (ir_byte_retire_v1 owner mem)) (ir_byte_mem_next_v1 mem) :=
@Eq.refl Nat (ir_byte_mem_next_v1 mem)";

const SRC_RETIRE_READ_WORD: &str = r"def ir_byte_retire_read_word_v1
  (owner : Nat) (mem : IRByteMemoryV1) (size : Nat) (address : Nat) :
  @Eq (IROption Nat)
    (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 (ir_byte_retire_v1 owner mem)) size address)
    (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) size address) :=
@Eq.refl (IROption Nat) (ir_byte_read_word_v1 (ir_byte_mem_bytes_v1 mem) size address)";

// The conclusion mentions the actual recursive allocation transformation.
// Equality substitution discharges the owner comparison, and Bool induction
// handles arbitrary incoming liveness (including already retired allocations).
const SRC_RETIRE_CONS_OTHER: &str = r"def ir_byte_retire_cons_other_v1
  (owner : Nat) (base : Nat) (size : Nat) (allocationOwner : Nat) (live : Bool)
  (tail : IRList IRByteAllocationV1)
  (different : @Eq Bool (ir_nat_eqb owner allocationOwner) Bool.false) :
  @Eq (IRList IRByteAllocationV1)
    (ir_byte_retire_allocs_v1 owner
      (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk base size allocationOwner live) tail))
    (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk base size allocationOwner live)
      (ir_byte_retire_allocs_v1 owner tail)) :=
@Eq.subst Bool
  (fun (same : Bool) => @Eq (IRList IRByteAllocationV1)
    (@IRList.cons IRByteAllocationV1
      (IRByteAllocationV1.mk base size allocationOwner (Bool.and live (Bool.not same)))
      (ir_byte_retire_allocs_v1 owner tail))
    (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk base size allocationOwner live)
      (ir_byte_retire_allocs_v1 owner tail)))
  Bool.false (ir_nat_eqb owner allocationOwner)
  (@Eq.symm Bool (ir_nat_eqb owner allocationOwner) Bool.false different)
  (@Bool.rec
    (fun (wasLive : Bool) => @Eq (IRList IRByteAllocationV1)
      (@IRList.cons IRByteAllocationV1
        (IRByteAllocationV1.mk base size allocationOwner (Bool.and wasLive (Bool.not Bool.false)))
        (ir_byte_retire_allocs_v1 owner tail))
      (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk base size allocationOwner wasLive)
        (ir_byte_retire_allocs_v1 owner tail)))
    (@Eq.refl (IRList IRByteAllocationV1)
      (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk base size allocationOwner Bool.false)
        (ir_byte_retire_allocs_v1 owner tail)))
    (@Eq.refl (IRList IRByteAllocationV1)
      (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk base size allocationOwner Bool.true)
        (ir_byte_retire_allocs_v1 owner tail))) live)";

const SRC_RETIRE_CONS_SAME: &str = r"def ir_byte_retire_cons_same_v1
  (owner : Nat) (base : Nat) (size : Nat) (allocationOwner : Nat) (live : Bool)
  (tail : IRList IRByteAllocationV1)
  (sameOwner : @Eq Bool (ir_nat_eqb owner allocationOwner) Bool.true) :
  @Eq (IRList IRByteAllocationV1)
    (ir_byte_retire_allocs_v1 owner
      (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk base size allocationOwner live) tail))
    (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk base size allocationOwner Bool.false)
      (ir_byte_retire_allocs_v1 owner tail)) :=
@Eq.subst Bool
  (fun (same : Bool) => @Eq (IRList IRByteAllocationV1)
    (@IRList.cons IRByteAllocationV1
      (IRByteAllocationV1.mk base size allocationOwner (Bool.and live (Bool.not same)))
      (ir_byte_retire_allocs_v1 owner tail))
    (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk base size allocationOwner Bool.false)
      (ir_byte_retire_allocs_v1 owner tail)))
  Bool.true (ir_nat_eqb owner allocationOwner)
  (@Eq.symm Bool (ir_nat_eqb owner allocationOwner) Bool.true sameOwner)
  (@Bool.rec
    (fun (wasLive : Bool) => @Eq (IRList IRByteAllocationV1)
      (@IRList.cons IRByteAllocationV1
        (IRByteAllocationV1.mk base size allocationOwner (Bool.and wasLive (Bool.not Bool.true)))
        (ir_byte_retire_allocs_v1 owner tail))
      (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk base size allocationOwner Bool.false)
        (ir_byte_retire_allocs_v1 owner tail)))
    (@Eq.refl (IRList IRByteAllocationV1)
      (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk base size allocationOwner Bool.false)
        (ir_byte_retire_allocs_v1 owner tail)))
    (@Eq.refl (IRList IRByteAllocationV1)
      (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk base size allocationOwner Bool.false)
        (ir_byte_retire_allocs_v1 owner tail))) live)";

const LAWS: &[(&str, &str)] = &[
    ("ir_byte_write_outside_v1", SRC_WRITE_OUTSIDE),
    ("ir_byte_clear_outside_v1", SRC_CLEAR_OUTSIDE),
    ("ir_byte_retire_bytes_v1", SRC_RETIRE_BYTES),
    ("ir_byte_retire_next_v1", SRC_RETIRE_NEXT),
    ("ir_byte_retire_read_word_v1", SRC_RETIRE_READ_WORD),
    ("ir_byte_retire_cons_other_v1", SRC_RETIRE_CONS_OTHER),
    ("ir_byte_retire_cons_same_v1", SRC_RETIRE_CONS_SAME),
];

impl Specification {
    /// Install quantified framing laws after the actual byte definitions.
    /// The byte-profile constructor subsequently audits every installed root's
    /// complete axiom and trust-marker closure alongside the evaluator itself.
    pub(super) fn add_eval_ir_byte_memory_laws(&mut self) -> Result<(), SpecError> {
        for &(name, source) in LAWS {
            self.add_recursive_def(
                source,
                "Kernel-checked universally quantified framing law for the actual byte-memory profile; no native/runtime fidelity authority.",
            )?;
            self.verify_definition(name)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Name;

    fn assert_checked(spec: &Specification, name: &str) {
        let declaration = spec.get_definition(name).expect("installed declaration");
        assert!(!declaration.is_axiom);
        assert!(declaration.elaborated_value.is_some());
        spec.verify_definition(name)
            .expect("independent kernel replay");
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

    #[test]
    fn byte_profile_installs_universal_framing_laws() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = Specification::new_eval_ir_byte_prelude_spec_v1()
                .expect("actual byte-profile constructor");
            for &(name, _) in LAWS {
                assert_checked(&spec, name);
            }
            // A consumer with an arbitrary incoming byte map and arbitrary
            // stored word composes two real mutations, rather than replaying
            // a concrete fixture's reflexivity witness.
            spec.add_recursive_def(
                r"def byte_laws_composed_frame
  (bytes : Nat -> IROption Nat) (base : Nat) (size : Nat) (word : Nat) (address : Nat)
  (outside : @Eq Bool (ir_byte_in_range_v1 base size address) Bool.false) :
  @Eq (IROption Nat)
    (ir_byte_clear_v1 (ir_byte_write_word_v1 bytes base size word) base size address)
    (bytes address) :=
@Eq.trans (IROption Nat)
  (ir_byte_clear_v1 (ir_byte_write_word_v1 bytes base size word) base size address)
  (ir_byte_write_word_v1 bytes base size word address) (bytes address)
  (ir_byte_clear_outside_v1 (ir_byte_write_word_v1 bytes base size word) base size address outside)
  (ir_byte_write_outside_v1 bytes base size word address outside)",
                "Compose checked framing laws through actual write and clear operations",
            )
            .expect("quantified consuming theorem");
            assert_checked(&spec, "byte_laws_composed_frame");
        });
    }

    #[test]
    fn framing_hypotheses_and_preserved_fields_cannot_be_mutated() {
        crate::test_utils::run_with_stack(|| {
            let spec = Specification::new_eval_ir_byte_prelude_spec_v1()
                .expect("actual byte-profile constructor");
            for (name, source) in [
                (
                    "wrong_inside_write",
                    SRC_WRITE_OUTSIDE.replace("Bool.false", "Bool.true"),
                ),
                (
                    "wrong_inside_clear",
                    SRC_CLEAR_OUTSIDE.replace("Bool.false", "Bool.true"),
                ),
                (
                    "wrong_retire_cursor",
                    SRC_RETIRE_NEXT.replace(
                        "@Eq.refl Nat (ir_byte_mem_next_v1 mem)",
                        "@Eq.refl Nat (Nat.succ (ir_byte_mem_next_v1 mem))",
                    ),
                ),
                (
                    "wrong_other_owner",
                    SRC_RETIRE_CONS_OTHER.replace("Bool.false different", "Bool.true different"),
                ),
            ] {
                let mut candidate = spec.clone();
                let original_name = source.split_whitespace().nth(1).expect("declaration name");
                let changed = source.replacen(original_name, name, 1);
                let error = candidate
                    .add_recursive_def(&changed, "Adversarial changed theorem candidate")
                    .expect_err("changed framing claim must not be accepted");
                assert!(
                    matches!(error, SpecError::ElabError(_) | SpecError::TypeError(_)),
                    "{name} must fail checking, not parsing, lookup, or a resource limit: {error}"
                );
            }
        });
    }
}
