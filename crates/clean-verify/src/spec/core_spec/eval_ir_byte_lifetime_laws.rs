// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Checked allocation-lifetime framing for the actual byte-memory profile.
//!
//! A surviving-cover witness identifies a real list entry, its actual covering
//! decision and its owner inequality. It is not an assumption that retirement
//! preserves accessibility. List induction proves that fact while preserving
//! the actual overlap count, including overlaps with already dead allocations.
//! These laws do not yet establish whole-machine owner/frame validity or native
//! allocator fidelity.

use crate::spec::{SpecError, Specification};

const AND_TRUE: &str = r"def ir_byte_lifetime_and_true_v1 (b : Bool) : @Eq Bool (Bool.and b Bool.true) b :=
@Bool.rec (fun (x : Bool) => @Eq Bool (Bool.and x Bool.true) x)
  (@Eq.refl Bool Bool.false) (@Eq.refl Bool Bool.true) b";

const OR_TRUE: &str = r"def ir_byte_lifetime_or_true_v1 (b : Bool) : @Eq Bool (Bool.or b Bool.true) Bool.true :=
@Bool.rec (fun (x : Bool) => @Eq Bool (Bool.or x Bool.true) Bool.true)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) b";

const OR_HEAD: &str = r"def ir_byte_lifetime_or_head_v1 (head : Bool) (tail : Bool)
  (h : @Eq Bool head Bool.true) : @Eq Bool (Bool.or head tail) Bool.true :=
ir_eq_cong Bool Bool (fun (b : Bool) => Bool.or b tail) head Bool.true h";

const OR_TAIL: &str = r"def ir_byte_lifetime_or_tail_v1 (head : Bool) (tail : Bool)
  (h : @Eq Bool tail Bool.true) : @Eq Bool (Bool.or head tail) Bool.true :=
@Eq.trans Bool (Bool.or head tail) (Bool.or head Bool.true) Bool.true
  (ir_eq_cong Bool Bool (fun (b : Bool) => Bool.or head b) tail Bool.true h)
  (ir_byte_lifetime_or_true_v1 head)";

const SURVIVING_COVER: &str = r"def ir_byte_surviving_cover_v1
  (owner : Nat) (allocs : IRList IRByteAllocationV1) (base : Nat) (size : Nat) : Prop :=
@IRList.rec IRByteAllocationV1 (fun (_ : IRList IRByteAllocationV1) => Prop)
  False
  (fun (a : IRByteAllocationV1) (_ : IRList IRByteAllocationV1) (ih : Prop) =>
    Or (And (@Eq Bool (ir_nat_eqb owner (ir_byte_alloc_owner_v1 a)) Bool.false)
      (@Eq Bool (ir_byte_cover_v1 a base size) Bool.true)) ih) allocs";

const SURVIVING_HEAD: &str = r"def ir_byte_surviving_cover_head_v1
  (owner : Nat) (a : IRByteAllocationV1) (tail : IRList IRByteAllocationV1)
  (base : Nat) (size : Nat)
  (different : @Eq Bool (ir_nat_eqb owner (ir_byte_alloc_owner_v1 a)) Bool.false)
  (covers : @Eq Bool (ir_byte_cover_v1 a base size) Bool.true) :
ir_byte_surviving_cover_v1 owner (@IRList.cons IRByteAllocationV1 a tail) base size :=
@Or.inl
  (And (@Eq Bool (ir_nat_eqb owner (ir_byte_alloc_owner_v1 a)) Bool.false)
    (@Eq Bool (ir_byte_cover_v1 a base size) Bool.true))
  (ir_byte_surviving_cover_v1 owner tail base size)
  (@And.intro (@Eq Bool (ir_nat_eqb owner (ir_byte_alloc_owner_v1 a)) Bool.false)
    (@Eq Bool (ir_byte_cover_v1 a base size) Bool.true) different covers)";

const SURVIVING_TAIL: &str = r"def ir_byte_surviving_cover_tail_v1
  (owner : Nat) (a : IRByteAllocationV1) (tail : IRList IRByteAllocationV1)
  (base : Nat) (size : Nat)
  (witness : ir_byte_surviving_cover_v1 owner tail base size) :
ir_byte_surviving_cover_v1 owner (@IRList.cons IRByteAllocationV1 a tail) base size :=
@Or.inr
  (And (@Eq Bool (ir_nat_eqb owner (ir_byte_alloc_owner_v1 a)) Bool.false)
    (@Eq Bool (ir_byte_cover_v1 a base size) Bool.true))
  (ir_byte_surviving_cover_v1 owner tail base size) witness";

const OVERLAP_COUNT: &str = r"def ir_byte_retire_overlap_count_v1
  (owner : Nat) (allocs : IRList IRByteAllocationV1) (base : Nat) (size : Nat) :
@Eq Nat (ir_byte_overlap_count_v1 (ir_byte_retire_allocs_v1 owner allocs) base size)
  (ir_byte_overlap_count_v1 allocs base size) :=
@IRList.rec IRByteAllocationV1
  (fun (xs : IRList IRByteAllocationV1) => @Eq Nat
    (ir_byte_overlap_count_v1 (ir_byte_retire_allocs_v1 owner xs) base size)
    (ir_byte_overlap_count_v1 xs base size))
  (@Eq.refl Nat 0)
  (fun (a : IRByteAllocationV1) (tail : IRList IRByteAllocationV1)
    (ih : @Eq Nat (ir_byte_overlap_count_v1 (ir_byte_retire_allocs_v1 owner tail) base size)
      (ir_byte_overlap_count_v1 tail base size)) =>
    ir_eq_cong Nat Nat
      (fun (count : Nat) => @Bool.rec (fun (_ : Bool) => Nat) count (Nat.succ count)
        (ir_byte_overlaps_v1 a base size))
      (ir_byte_overlap_count_v1 (ir_byte_retire_allocs_v1 owner tail) base size)
      (ir_byte_overlap_count_v1 tail base size) ih) allocs";

// This is exactly the allocation row constructed by ir_byte_retire_allocs_v1.
// The generated proofs must convert against that existing definition; this
// source helper neither installs an alternative retirement operation nor reads
// certificate-controlled allocation meanings.
fn retired_row(a: &str, same: &str) -> String {
    format!(
        "(IRByteAllocationV1.mk (ir_byte_alloc_base_v1 {a}) (ir_byte_alloc_size_v1 {a}) \
         (ir_byte_alloc_owner_v1 {a}) (Bool.and (ir_byte_alloc_live_v1 {a}) (Bool.not {same})))"
    )
}

fn retire_cover_source() -> String {
    let comparison = "(ir_nat_eqb owner (ir_byte_alloc_owner_v1 a))";
    let retired = retired_row("a", comparison);
    let symbolic = retired_row("a", "same");
    let range = "(Bool.and (ir_nat_leb (ir_byte_alloc_base_v1 a) base) (ir_nat_leb (Nat.add base size) (Nat.add (ir_byte_alloc_base_v1 a) (ir_byte_alloc_size_v1 a))))";
    format!(
        "def ir_byte_retire_cover_other_v1 (owner : Nat) (a : IRByteAllocationV1) (base : Nat) (size : Nat)\n\
         (different : @Eq Bool {comparison} Bool.false) :\n\
         @Eq Bool (ir_byte_cover_v1 {retired} base size) (ir_byte_cover_v1 a base size) :=\n\
         @Eq.subst Bool (fun (same : Bool) => @Eq Bool (ir_byte_cover_v1 {symbolic} base size) (ir_byte_cover_v1 a base size))\n\
           Bool.false {comparison} (@Eq.symm Bool {comparison} Bool.false different)\n\
           (ir_eq_cong Bool Bool (fun (live : Bool) => Bool.and (ir_byte_alloc_valid_v1 a) (Bool.and live {range}))\n\
             (Bool.and (ir_byte_alloc_live_v1 a) Bool.true) (ir_byte_alloc_live_v1 a)\n\
             (ir_byte_lifetime_and_true_v1 (ir_byte_alloc_live_v1 a)))"
    )
}

/// Generate the two list inductions, sharing their construction but retaining
/// explicit actual before/after cover endpoints in each checked declaration.
fn cover_sound_source(retired: bool) -> (&'static str, String) {
    let name = if retired {
        "ir_byte_surviving_cover_retired_v1"
    } else {
        "ir_byte_surviving_cover_original_v1"
    };
    let any_cover = |xs: &str| {
        if retired {
            format!("(ir_byte_any_cover_v1 (ir_byte_retire_allocs_v1 owner {xs}) base size)")
        } else {
            format!("(ir_byte_any_cover_v1 {xs} base size)")
        }
    };
    let different = "(@Eq Bool (ir_nat_eqb owner (ir_byte_alloc_owner_v1 a)) Bool.false)";
    let covers = "(@Eq Bool (ir_byte_cover_v1 a base size) Bool.true)";
    let pair = format!("(And {different} {covers})");
    let tail_witness = "(ir_byte_surviving_cover_v1 owner tail base size)";
    let row = if retired {
        retired_row("a", "(ir_nat_eqb owner (ir_byte_alloc_owner_v1 a))")
    } else {
        "a".into()
    };
    let row_cover = format!("(ir_byte_cover_v1 {row} base size)");
    let head_proof = if retired {
        format!(
            "@Eq.trans Bool {row_cover} (ir_byte_cover_v1 a base size) Bool.true\n\
             (ir_byte_retire_cover_other_v1 owner a base size (@And.left {different} {covers} head))\n\
             (@And.right {different} {covers} head)"
        )
    } else {
        format!("@And.right {different} {covers} head")
    };
    let tail_cover = any_cover("tail");
    let cons_cover = format!("(Bool.or {row_cover} {tail_cover})");
    (
        name,
        format!(
            "def {name} (owner : Nat) (allocs : IRList IRByteAllocationV1) (base : Nat) (size : Nat)\n\
             (witness : ir_byte_surviving_cover_v1 owner allocs base size) : @Eq Bool {} Bool.true :=\n\
             @IRList.rec IRByteAllocationV1\n\
               (fun (xs : IRList IRByteAllocationV1) => ir_byte_surviving_cover_v1 owner xs base size -> @Eq Bool {} Bool.true)\n\
               (fun (impossible : False) => @False.elim (@Eq Bool Bool.false Bool.true) impossible)\n\
               (fun (a : IRByteAllocationV1) (tail : IRList IRByteAllocationV1)\n\
                 (ih : ir_byte_surviving_cover_v1 owner tail base size -> @Eq Bool {tail_cover} Bool.true) =>\n\
                 fun (present : Or {pair} {tail_witness}) =>\n\
                 @Or.rec {pair} {tail_witness}\n\
                   (fun (_ : Or {pair} {tail_witness}) => @Eq Bool {cons_cover} Bool.true)\n\
                   (fun (head : {pair}) => ir_byte_lifetime_or_head_v1 {row_cover} {tail_cover} ({head_proof}))\n\
                   (fun (inTail : {tail_witness}) => ir_byte_lifetime_or_tail_v1 {row_cover} {tail_cover} (ih inTail))\n\
                   present) allocs witness",
            any_cover("allocs"),
            any_cover("xs"),
        ),
    )
}

fn accessible_source() -> String {
    let old_count = "(ir_byte_overlap_count_v1 allocs base size)";
    let new_count = "(ir_byte_overlap_count_v1 (ir_byte_retire_allocs_v1 owner allocs) base size)";
    let old_cover = "(ir_byte_any_cover_v1 allocs base size)";
    let new_cover = "(ir_byte_any_cover_v1 (ir_byte_retire_allocs_v1 owner allocs) base size)";
    let access = |count: &str, cover: &str| {
        format!(
            "(Bool.and (ir_nat_pos base) (Bool.and (ir_nat_pos size)\n\
             (Bool.and (ir_nat_leb (Nat.add base size) ir_byte_limit_v1)\n\
             (Bool.and (ir_byte_alignment_v1 align)\n\
             (Bool.and (ir_nat_eqb (Nat.mod base align) 0)\n\
             (Bool.and (ir_nat_eqb {count} 1) {cover}))))))"
        )
    };
    format!(
        "def ir_byte_accessible_retire_other_v1\n\
         (owner : Nat) (allocs : IRList IRByteAllocationV1) (base : Nat) (size : Nat) (align : Nat)\n\
         (before : @Eq Bool (ir_byte_accessible_v1 allocs base size align) Bool.true)\n\
         (survives : ir_byte_surviving_cover_v1 owner allocs base size) :\n\
         @Eq Bool (ir_byte_accessible_v1 (ir_byte_retire_allocs_v1 owner allocs) base size align) Bool.true :=\n\
         @Eq.trans Bool (ir_byte_accessible_v1 (ir_byte_retire_allocs_v1 owner allocs) base size align)\n\
           {} Bool.true\n\
           (ir_eq_cong Nat Bool (fun (count : Nat) => {}) {new_count} {old_count}\n\
             (ir_byte_retire_overlap_count_v1 owner allocs base size))\n\
           (@Eq.trans Bool {} (ir_byte_accessible_v1 allocs base size align) Bool.true\n\
             (ir_eq_cong Bool Bool (fun (covered : Bool) => {}) {new_cover} {old_cover}\n\
               (@Eq.trans Bool {new_cover} Bool.true {old_cover}\n\
                 (ir_byte_surviving_cover_retired_v1 owner allocs base size survives)\n\
                 (@Eq.symm Bool {old_cover} Bool.true (ir_byte_surviving_cover_original_v1 owner allocs base size survives))))\n\
             before)",
        access(old_count, new_cover),
        access("count", new_cover),
        access(old_count, new_cover),
        access(old_count, "covered"),
    )
}

fn laws() -> Vec<(&'static str, String)> {
    let mut laws = vec![
        ("ir_byte_lifetime_and_true_v1", AND_TRUE.into()),
        ("ir_byte_lifetime_or_true_v1", OR_TRUE.into()),
        ("ir_byte_lifetime_or_head_v1", OR_HEAD.into()),
        ("ir_byte_lifetime_or_tail_v1", OR_TAIL.into()),
        ("ir_byte_surviving_cover_v1", SURVIVING_COVER.into()),
        ("ir_byte_surviving_cover_head_v1", SURVIVING_HEAD.into()),
        ("ir_byte_surviving_cover_tail_v1", SURVIVING_TAIL.into()),
        ("ir_byte_retire_overlap_count_v1", OVERLAP_COUNT.into()),
        ("ir_byte_retire_cover_other_v1", retire_cover_source()),
    ];
    laws.push(cover_sound_source(false));
    laws.push(cover_sound_source(true));
    laws.push(("ir_byte_accessible_retire_other_v1", accessible_source()));
    laws
}

impl Specification {
    /// Install checked lifetime facts into an existing byte-profile environment.
    /// This does not change memory definitions or supply machine-world validity.
    pub(super) fn add_eval_ir_byte_lifetime_laws_v1(&mut self) -> Result<(), SpecError> {
        for (name, source) in laws() {
            self.add_recursive_def(
                &source,
                "Checked lifetime framing over actual allocations, overlap and coverage decisions",
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
        Specification::new_eval_ir_byte_prelude_spec_v1().expect("actual published byte profile")
    }

    fn checked(spec: &Specification, name: &str) {
        let definition = spec
            .get_definition(name)
            .expect("installed checked declaration");
        assert!(!definition.is_axiom);
        assert!(definition.elaborated_value.is_some());
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

    fn reject(spec: &mut Specification, name: &str, source: &str) {
        let error = spec
            .add_recursive_def(source, "Invalid lifetime claim")
            .expect_err("malformed ownership or access must not be certified");
        crate::test_utils::assert_type_mismatch_rejection(&error, name);
        assert!(spec.get_definition(name).is_none());
    }

    #[test]
    fn lifetime_laws_check_without_axioms_or_trust_markers() {
        crate::test_utils::run_with_stack(|| {
            let spec = spec();
            for (name, _) in laws() {
                checked(&spec, name);
            }
        });
    }

    #[test]
    fn retirement_preserves_access_to_a_caller_beyond_two_prefix_entries() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = spec();
            spec.add_recursive_def(
                r"def lifetime_arbitrary_prefix
  (owner : Nat) (first : IRByteAllocationV1) (second : IRByteAllocationV1)
  (caller : IRByteAllocationV1) (tail : IRList IRByteAllocationV1)
  (base : Nat) (size : Nat) (align : Nat)
  (different : @Eq Bool (ir_nat_eqb owner (ir_byte_alloc_owner_v1 caller)) Bool.false)
  (covers : @Eq Bool (ir_byte_cover_v1 caller base size) Bool.true)
  (before : @Eq Bool (ir_byte_accessible_v1
    (@IRList.cons IRByteAllocationV1 first (@IRList.cons IRByteAllocationV1 second
      (@IRList.cons IRByteAllocationV1 caller tail))) base size align) Bool.true) :
@Eq Bool (ir_byte_accessible_v1 (ir_byte_retire_allocs_v1 owner
  (@IRList.cons IRByteAllocationV1 first (@IRList.cons IRByteAllocationV1 second
    (@IRList.cons IRByteAllocationV1 caller tail)))) base size align) Bool.true :=
ir_byte_accessible_retire_other_v1 owner
  (@IRList.cons IRByteAllocationV1 first (@IRList.cons IRByteAllocationV1 second
    (@IRList.cons IRByteAllocationV1 caller tail))) base size align before
  (ir_byte_surviving_cover_tail_v1 owner first
    (@IRList.cons IRByteAllocationV1 second (@IRList.cons IRByteAllocationV1 caller tail)) base size
    (ir_byte_surviving_cover_tail_v1 owner second (@IRList.cons IRByteAllocationV1 caller tail) base size
      (ir_byte_surviving_cover_head_v1 owner caller tail base size different covers)))",
                "Actual caller-slot accessibility with arbitrary prefix records and tail",
            ).expect("quantified non-head caller theorem");
            checked(&spec, "lifetime_arbitrary_prefix");
            spec.add_recursive_def(
                r"def lifetime_distinct_owner_example : @Eq Bool
  (ir_byte_accessible_v1 (ir_byte_retire_allocs_v1 2
    (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 16 8 1 Bool.true)
      (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 32 8 2 Bool.true)
        (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 64 8 3 Bool.true)
          (@IRList.nil IRByteAllocationV1))))) 64 8 8) Bool.true :=
lifetime_arbitrary_prefix 2 (IRByteAllocationV1.mk 16 8 1 Bool.true)
  (IRByteAllocationV1.mk 32 8 2 Bool.true) (IRByteAllocationV1.mk 64 8 3 Bool.true)
  (@IRList.nil IRByteAllocationV1) 64 8 8 (@Eq.refl Bool Bool.false)
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)",
                "Inhabited caller/callee allocation lifetime example through the generic theorem",
            )
            .expect("nonvacuous positive application");
            checked(&spec, "lifetime_distinct_owner_example");
        });
    }

    #[test]
    fn lifetime_rejects_same_owner_dead_cover_and_overlapping_records() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = spec();
            for (name, source) in [
                (
                    "lifetime_bad_owner",
                    r"def lifetime_bad_owner : ir_byte_surviving_cover_v1 3 (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 64 8 3 Bool.true) (@IRList.nil IRByteAllocationV1)) 64 8 := ir_byte_surviving_cover_head_v1 3 (IRByteAllocationV1.mk 64 8 3 Bool.true) (@IRList.nil IRByteAllocationV1) 64 8 (@Eq.refl Bool Bool.false) (@Eq.refl Bool Bool.true)",
                ),
                (
                    "lifetime_bad_live",
                    r"def lifetime_bad_live : ir_byte_surviving_cover_v1 2 (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 64 8 3 Bool.false) (@IRList.nil IRByteAllocationV1)) 64 8 := ir_byte_surviving_cover_head_v1 2 (IRByteAllocationV1.mk 64 8 3 Bool.false) (@IRList.nil IRByteAllocationV1) 64 8 (@Eq.refl Bool Bool.false) (@Eq.refl Bool Bool.true)",
                ),
                (
                    "lifetime_bad_overlap",
                    r"def lifetime_bad_overlap : @Eq Bool (ir_byte_accessible_v1 (ir_byte_retire_allocs_v1 2 (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 64 8 3 Bool.true) (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 64 8 2 Bool.true) (@IRList.nil IRByteAllocationV1)))) 64 8 8) Bool.true := ir_byte_accessible_retire_other_v1 2 (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 64 8 3 Bool.true) (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 64 8 2 Bool.true) (@IRList.nil IRByteAllocationV1))) 64 8 8 (@Eq.refl Bool Bool.true) (ir_byte_surviving_cover_head_v1 2 (IRByteAllocationV1.mk 64 8 3 Bool.true) (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 64 8 2 Bool.true) (@IRList.nil IRByteAllocationV1)) 64 8 (@Eq.refl Bool Bool.false) (@Eq.refl Bool Bool.true))",
                ),
                (
                    "lifetime_bad_alignment",
                    r"def lifetime_bad_alignment : @Eq Bool (ir_byte_accessible_v1 (ir_byte_retire_allocs_v1 2 (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 65 8 3 Bool.true) (@IRList.nil IRByteAllocationV1))) 65 8 8) Bool.true := ir_byte_accessible_retire_other_v1 2 (@IRList.cons IRByteAllocationV1 (IRByteAllocationV1.mk 65 8 3 Bool.true) (@IRList.nil IRByteAllocationV1)) 65 8 8 (@Eq.refl Bool Bool.true) (ir_byte_surviving_cover_head_v1 2 (IRByteAllocationV1.mk 65 8 3 Bool.true) (@IRList.nil IRByteAllocationV1) 65 8 (@Eq.refl Bool Bool.false) (@Eq.refl Bool Bool.true))",
                ),
            ] {
                reject(&mut spec, name, source);
            }
        });
    }
}
