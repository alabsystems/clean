// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive Euclidean arithmetic for the actual byte codec's Nat.div/mod.
//!
//! Quotient uniqueness is proved from the checked Euclidean decomposition and
//! remainder bound, not supplied as a premise. Composition then uses that
//! uniqueness. All operands remain universally quantified; these are not
//! concrete byte examples or an alternative evaluator. Byte-memory roundtrips,
//! source translation, and native execution require separate consuming proofs.

use crate::spec::{SpecError, Specification};

const LAWS: &[(&str, &str)] = &[
    (
        "ir_byte_radix_succ_mul_v1",
        r"def ir_byte_radix_succ_mul_v1 (q : Nat) (d : Nat) :
@Eq Nat (Nat.mul (Nat.succ q) d) (Nat.add (Nat.mul q d) d) :=
@Eq.trans Nat (Nat.mul (Nat.succ q) d) (Nat.add d (Nat.mul q d))
  (Nat.add (Nat.mul q d) d) (@Nat.succ_mul q d) (@Nat.add_comm d (Nat.mul q d))",
    ),
    (
        "ir_byte_radix_separated_v1",
        r"def ir_byte_radix_separated_v1
  (d : Nat) (q : Nat) (p : Nat) (r : Nat) (s : Nat)
  (hr : Nat.lt r d) (hqp : Nat.lt q p) :
Nat.lt (Nat.add (Nat.mul q d) r) (Nat.add (Nat.mul p d) s) :=
let hlow : Nat.lt (Nat.add (Nat.mul q d) r) (Nat.mul (Nat.succ q) d) :=
  @Eq.subst Nat
    (fun (bound : Nat) => Nat.lt (Nat.add (Nat.mul q d) r) bound)
    (Nat.add (Nat.mul q d) d) (Nat.mul (Nat.succ q) d)
    (@Eq.symm Nat (Nat.mul (Nat.succ q) d) (Nat.add (Nat.mul q d) d)
      (ir_byte_radix_succ_mul_v1 q d))
    (@Nat.add_lt_add_left r d hr (Nat.mul q d));
@Nat.le_trans (Nat.succ (Nat.add (Nat.mul q d) r)) (Nat.mul (Nat.succ q) d)
  (Nat.add (Nat.mul p d) s) hlow
  (@Nat.le_trans (Nat.mul (Nat.succ q) d) (Nat.mul p d)
    (Nat.add (Nat.mul p d) s)
    (@Nat.mul_le_mul_right (Nat.succ q) p d hqp)
    (@Nat.le_add_right (Nat.mul p d) s))",
    ),
    (
        "ir_byte_radix_quotient_le_v1",
        r"def ir_byte_radix_quotient_le_v1
  (d : Nat) (q : Nat) (p : Nat) (r : Nat) (s : Nat)
  (hs : Nat.lt s d)
  (heq : @Eq Nat (Nat.add (Nat.mul q d) r) (Nat.add (Nat.mul p d) s)) :
Nat.le q p :=
@Or.rec (Nat.le q p) (Nat.lt p q)
  (fun (_ : Or (Nat.le q p) (Nat.lt p q)) => Nat.le q p)
  (fun (hle : Nat.le q p) => hle)
  (fun (hlt : Nat.lt p q) =>
    @False.elim (Nat.le q p)
      (@Nat.lt_irrefl (Nat.add (Nat.mul p d) s)
        (@Eq.subst Nat
          (fun (bound : Nat) => Nat.lt (Nat.add (Nat.mul p d) s) bound)
          (Nat.add (Nat.mul q d) r) (Nat.add (Nat.mul p d) s) heq
          (ir_byte_radix_separated_v1 d p q s r hs hlt))))
  (@Nat.le_or_lt q p)",
    ),
    (
        "ir_byte_div_unique_v1",
        r"def ir_byte_div_unique_v1
  (n : Nat) (d : Nat) (q : Nat) (r : Nat)
  (hd : Nat.lt 0 d) (hr : Nat.lt r d)
  (heq : @Eq Nat n (Nat.add (Nat.mul q d) r)) :
@Eq Nat (Nat.div n d) q :=
let hdecomp : @Eq Nat
  (Nat.add (Nat.mul (Nat.div n d) d) (Nat.mod n d))
  (Nat.add (Nat.mul q d) r) :=
  @Eq.trans Nat (Nat.add (Nat.mul (Nat.div n d) d) (Nat.mod n d)) n
    (Nat.add (Nat.mul q d) r) (@Nat.div_add_mod n d) heq;
@Nat.le_antisymm (Nat.div n d) q
  (ir_byte_radix_quotient_le_v1 d (Nat.div n d) q (Nat.mod n d) r hr hdecomp)
  (ir_byte_radix_quotient_le_v1 d q (Nat.div n d) r (Nat.mod n d)
    (@Nat.mod_lt n d hd)
    (@Eq.symm Nat (Nat.add (Nat.mul (Nat.div n d) d) (Nat.mod n d))
      (Nat.add (Nat.mul q d) r) hdecomp))",
    ),
    (
        "ir_byte_radix_mul_positive_v1",
        r"def ir_byte_radix_mul_positive_v1
  (d : Nat) (b : Nat) (hd : Nat.lt 0 d) (hb : Nat.lt 0 b) :
Nat.lt 0 (Nat.mul d b) :=
@Nat.le_trans 1 d (Nat.mul d b) hd
  (@Eq.subst Nat (fun (lower : Nat) => Nat.le lower (Nat.mul d b))
    (Nat.mul d 1) d (@Nat.mul_one d)
    (@Nat.mul_le_mul_left 1 b d hb))",
    ),
    (
        "ir_byte_radix_mul_swap_v1",
        r"def ir_byte_radix_mul_swap_v1 (t : Nat) (b : Nat) (d : Nat) :
@Eq Nat (Nat.mul (Nat.mul t b) d) (Nat.mul t (Nat.mul d b)) :=
@Eq.trans Nat (Nat.mul (Nat.mul t b) d) (Nat.mul t (Nat.mul b d))
  (Nat.mul t (Nat.mul d b)) (@Nat.mul_assoc t b d)
  (ir_eq_cong Nat Nat (fun (factor : Nat) => Nat.mul t factor)
    (Nat.mul b d) (Nat.mul d b) (@Nat.mul_comm b d))",
    ),
    (
        "ir_byte_radix_expand_v1",
        r"def ir_byte_radix_expand_v1
  (t : Nat) (b : Nat) (s : Nat) (d : Nat) (r : Nat) :
@Eq Nat (Nat.add (Nat.mul (Nat.add (Nat.mul t b) s) d) r)
  (Nat.add (Nat.mul t (Nat.mul d b)) (Nat.add (Nat.mul s d) r)) :=
@Eq.trans Nat
  (Nat.add (Nat.mul (Nat.add (Nat.mul t b) s) d) r)
  (Nat.add (Nat.add (Nat.mul (Nat.mul t b) d) (Nat.mul s d)) r)
  (Nat.add (Nat.mul t (Nat.mul d b)) (Nat.add (Nat.mul s d) r))
  (ir_eq_cong Nat Nat (fun (product : Nat) => Nat.add product r)
    (Nat.mul (Nat.add (Nat.mul t b) s) d)
    (Nat.add (Nat.mul (Nat.mul t b) d) (Nat.mul s d))
    (@Nat.right_distrib (Nat.mul t b) s d))
  (@Eq.trans Nat
    (Nat.add (Nat.add (Nat.mul (Nat.mul t b) d) (Nat.mul s d)) r)
    (Nat.add (Nat.add (Nat.mul t (Nat.mul d b)) (Nat.mul s d)) r)
    (Nat.add (Nat.mul t (Nat.mul d b)) (Nat.add (Nat.mul s d) r))
    (ir_eq_cong Nat Nat
      (fun (product : Nat) => Nat.add (Nat.add product (Nat.mul s d)) r)
      (Nat.mul (Nat.mul t b) d) (Nat.mul t (Nat.mul d b))
      (ir_byte_radix_mul_swap_v1 t b d))
    (@Nat.add_assoc (Nat.mul t (Nat.mul d b)) (Nat.mul s d) r))",
    ),
    (
        "ir_byte_radix_compose_decomposition_v1",
        r"def ir_byte_radix_compose_decomposition_v1
  (n : Nat) (d : Nat) (b : Nat) (q : Nat) (r : Nat) (t : Nat) (s : Nat)
  (hd : Nat.lt 0 d) (hb : Nat.lt 0 b) (hr : Nat.lt r d) (hs : Nat.lt s b)
  (hn : @Eq Nat n (Nat.add (Nat.mul q d) r))
  (hq : @Eq Nat q (Nat.add (Nat.mul t b) s)) :
@Eq Nat (Nat.div n (Nat.mul d b)) t :=
let hresidual : Nat.lt (Nat.add (Nat.mul s d) r) (Nat.mul d b) :=
  @Eq.subst Nat (fun (bound : Nat) => Nat.lt (Nat.add (Nat.mul s d) r) bound)
    (Nat.mul b d) (Nat.mul d b) (@Nat.mul_comm b d)
    (ir_byte_radix_separated_v1 d s b r 0 hr hs);
let hdecomp : @Eq Nat n
  (Nat.add (Nat.mul t (Nat.mul d b)) (Nat.add (Nat.mul s d) r)) :=
  @Eq.trans Nat n (Nat.add (Nat.mul q d) r)
    (Nat.add (Nat.mul t (Nat.mul d b)) (Nat.add (Nat.mul s d) r))
    hn
    (@Eq.trans Nat (Nat.add (Nat.mul q d) r)
      (Nat.add (Nat.mul (Nat.add (Nat.mul t b) s) d) r)
      (Nat.add (Nat.mul t (Nat.mul d b)) (Nat.add (Nat.mul s d) r))
      (ir_eq_cong Nat Nat (fun (quotient : Nat) => Nat.add (Nat.mul quotient d) r)
        q (Nat.add (Nat.mul t b) s) hq)
      (ir_byte_radix_expand_v1 t b s d r));
ir_byte_div_unique_v1 n (Nat.mul d b) t (Nat.add (Nat.mul s d) r)
  (ir_byte_radix_mul_positive_v1 d b hd hb) hresidual hdecomp",
    ),
    (
        "ir_byte_div_compose_v1",
        r"def ir_byte_div_compose_v1
  (n : Nat) (d : Nat) (b : Nat) (hd : Nat.lt 0 d) (hb : Nat.lt 0 b) :
@Eq Nat (Nat.div (Nat.div n d) b) (Nat.div n (Nat.mul d b)) :=
@Eq.symm Nat (Nat.div n (Nat.mul d b)) (Nat.div (Nat.div n d) b)
  (ir_byte_radix_compose_decomposition_v1 n d b
    (Nat.div n d) (Nat.mod n d) (Nat.div (Nat.div n d) b) (Nat.mod (Nat.div n d) b)
    hd hb (@Nat.mod_lt n d hd) (@Nat.mod_lt (Nat.div n d) b hb)
    (@Eq.symm Nat (Nat.add (Nat.mul (Nat.div n d) d) (Nat.mod n d)) n
      (@Nat.div_add_mod n d))
    (@Eq.symm Nat
      (Nat.add (Nat.mul (Nat.div (Nat.div n d) b) b) (Nat.mod (Nat.div n d) b))
      (Nat.div n d) (@Nat.div_add_mod (Nat.div n d) b)))",
    ),
];

impl Specification {
    /// Install quantified radix laws in the ordinary, checked EvalIR prelude.
    /// The byte-profile constructor audits every newly installed root as well.
    pub(super) fn add_eval_ir_byte_radix_laws_v1(&mut self) -> Result<(), SpecError> {
        for &(name, source) in LAWS {
            self.add_recursive_def(
                source,
                "Constructive Euclidean law over actual Nat.div/mod, not a byte codec or native-fidelity assumption.",
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
        let mut spec = Specification::new_eval_ir_prelude_spec().expect("ordinary EvalIR prelude");
        spec.add_eval_ir_byte_radix_laws_v1()
            .expect("real quantified Euclidean laws");
        spec
    }

    fn assert_checked(spec: &Specification, name: &str) {
        let definition = spec
            .get_definition(name)
            .expect("registered checked declaration");
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

    fn reject_type_mismatch(spec: &mut Specification, name: &str, source: &str) {
        let error = spec
            .add_recursive_def(source, "Adversarial radix-law mutation")
            .expect_err("wrong arithmetic premise or conclusion must be rejected");
        crate::test_utils::assert_type_mismatch_rejection(&error, name);
        assert!(spec.get_definition(name).is_none());
    }

    #[test]
    fn quantified_radix_laws_are_kernel_checked_without_axioms() {
        crate::test_utils::run_with_stack(|| {
            let spec = spec();
            for &(name, _) in LAWS {
                assert_checked(&spec, name);
            }
        });
    }

    #[test]
    fn radix_composition_consumes_arbitrary_words() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = spec();
            spec.add_recursive_def(
                r"def radix_three_divisions (n : Nat) (a : Nat) (b : Nat) (c : Nat)
  (ha : Nat.lt 0 a) (hb : Nat.lt 0 b) (hc : Nat.lt 0 c) :
@Eq Nat (Nat.div (Nat.div (Nat.div n a) b) c) (Nat.div n (Nat.mul (Nat.mul a b) c)) :=
@Eq.trans Nat (Nat.div (Nat.div (Nat.div n a) b) c)
  (Nat.div (Nat.div n (Nat.mul a b)) c) (Nat.div n (Nat.mul (Nat.mul a b) c))
  (ir_eq_cong Nat Nat (fun (q : Nat) => Nat.div q c)
    (Nat.div (Nat.div n a) b) (Nat.div n (Nat.mul a b))
    (ir_byte_div_compose_v1 n a b ha hb))
  (ir_byte_div_compose_v1 n (Nat.mul a b) c (ir_byte_radix_mul_positive_v1 a b ha hb) hc)",
                "Composition of checked division theorems at arbitrary operands",
            )
            .expect("quantified consumer");
            assert_checked(&spec, "radix_three_divisions");
        });
    }

    #[test]
    fn radix_laws_reject_wrong_remainders_and_denominators() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = spec();
            for (name, source) in [
                (
                    "radix_bad_positive",
                    r"def radix_bad_positive (n : Nat) : @Eq Nat (Nat.div (Nat.div n 0) 1) (Nat.div n 0) := ir_byte_div_compose_v1 n 0 1 (@Nat.zero_lt_succ 0) (@Nat.zero_lt_succ 0)",
                ),
                (
                    "radix_bad_remainder",
                    r"def radix_bad_remainder : @Eq Nat (Nat.div 9 3) 2 := ir_byte_div_unique_v1 9 3 2 3 (@Nat.zero_lt_succ 2) (@Nat.zero_lt_succ 2) (@Eq.refl Nat 9)",
                ),
                (
                    "radix_bad_decomposition",
                    r"def radix_bad_decomposition : @Eq Nat (Nat.div 9 3) 2 := ir_byte_div_unique_v1 9 3 2 0 (@Nat.zero_lt_succ 2) (@Nat.zero_lt_succ 2) (@Eq.refl Nat 9)",
                ),
                (
                    "radix_bad_product",
                    r"def radix_bad_product (n : Nat) : @Eq Nat (Nat.div (Nat.div n 2) 3) (Nat.div n 5) := ir_byte_div_compose_v1 n 2 3 (@Nat.zero_lt_succ 1) (@Nat.zero_lt_succ 2)",
                ),
            ] {
                reject_type_mismatch(&mut spec, name, source);
            }
        });
    }
}
