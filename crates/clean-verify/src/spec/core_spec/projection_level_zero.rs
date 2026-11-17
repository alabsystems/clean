// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Semantic-zero reflection for the canonical raw level classifier.
//!
//! All five Level constructors are covered at the all-ones valuation. Only
//! Boolean true is preserved by universe substitution; a parameter-to-zero
//! caller constructively refutes preservation of false. The bound consumer
//! composes actual semantic order transport with this Boolean bridge.
//! No projection typing, declaration admission or Rust refinement is claimed.
//!
//! Independent proof provenance and retained failures:
//! scratch/projection_level_zero_bridge.md. The explicit port records are
//! checked separately from their later full-spec registration and replay.
//! Register after add_universe_geq_core: ugeq_level_zero and ugeq_natMax_right
//! are the last prerequisites; this module does not depend on projection typing.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// Twelve proofs and one computational valuation definition. Every entry uses
// an explicit checked record; the data definition is not a logical proof root.
const DECLARATIONS: &[(&str, &str, &str)] = &[
    (
        "projection_bound_instantiated_zero",
        r"forall (s : Name -> Level) (field : Level) (result : Level)
 (bound : levelLeqSem field result)
 (zero : levelEqSem (substL s result) Level.zero),
 levelEqSem (substL s field) Level.zero",
        r"fun (s : Name -> Level) (field : Level) (result : Level)
 (bound : levelLeqSem field result)
 (zero : levelEqSem (substL s result) Level.zero) =>
 fun (rho : Name -> Nat) => le_zero_eq_zero
  (evalL rho (substL s field)) (evalL rho (substL s result))
  (levelLeq_subst_stable s field result bound rho) (zero rho)",
    ),
    (
        "level_zero_ones",
        r"forall (_name : Name),
 Nat",
        r"fun (_name : Name) =>
 Nat.succ Nat.zero",
    ),
    (
        "imaxNat_zero_right",
        r"forall (a : Nat) (b : Nat),
 @Eq Nat (imaxNat a b) Nat.zero -> @Eq Nat b Nat.zero",
        r"fun (a : Nat) (b : Nat) =>
 @Nat.rec (fun (b0 : Nat) => @Eq Nat (imaxNat a b0) Nat.zero -> @Eq Nat b0 Nat.zero)
  (fun (_h : @Eq Nat (imaxNat a Nat.zero) Nat.zero) => @Eq.refl Nat Nat.zero)
  (fun (k : Nat) (_ih : @Eq Nat (imaxNat a k) Nat.zero -> @Eq Nat k Nat.zero)
    (h : @Eq Nat (imaxNat a (Nat.succ k)) Nat.zero) =>
    le_zero_eq_zero (Nat.succ k) (natMax a (Nat.succ k))
      (ugeq_natMax_right a (Nat.succ k)) h) b",
    ),
    (
        "level_is_zero_of_evalL_ones",
        r"forall (l : Level),
 @Eq Nat (evalL level_zero_ones l) Nat.zero -> @Eq Bool (level_is_zero l) Bool.true",
        r"fun (l : Level) =>
 @Level.rec (fun (l0 : Level) => @Eq Nat (evalL level_zero_ones l0) Nat.zero ->
   @Eq Bool (level_is_zero l0) Bool.true)
  (fun (_h : @Eq Nat (evalL level_zero_ones Level.zero) Nat.zero) => @Eq.refl Bool Bool.true)
  (fun (a : Level) (_ih : @Eq Nat (evalL level_zero_ones a) Nat.zero ->
      @Eq Bool (level_is_zero a) Bool.true)
    (h : @Eq Nat (evalL level_zero_ones (Level.succ a)) Nat.zero) =>
    nat_zero_ne_succ_prop (evalL level_zero_ones a)
      (@Eq Bool (level_is_zero (Level.succ a)) Bool.true)
      (Eq.symm Nat (Nat.succ (evalL level_zero_ones a)) Nat.zero h))
  (fun (a : Level) (b : Level)
    (iha : @Eq Nat (evalL level_zero_ones a) Nat.zero -> @Eq Bool (level_is_zero a) Bool.true)
    (ihb : @Eq Nat (evalL level_zero_ones b) Nat.zero -> @Eq Bool (level_is_zero b) Bool.true)
    (h : @Eq Nat (evalL level_zero_ones (Level.max a b)) Nat.zero) =>
    Eq.trans Bool (Bool.and (level_is_zero a) (level_is_zero b))
      (Bool.and Bool.true (level_is_zero b)) Bool.true
      (Eq.cong Bool Bool (fun (x : Bool) => Bool.and x (level_is_zero b))
        (level_is_zero a) Bool.true
        (iha (le_zero_eq_zero (evalL level_zero_ones a)
          (natMax (evalL level_zero_ones a) (evalL level_zero_ones b))
          (le_natMax_left (evalL level_zero_ones a) (evalL level_zero_ones b)) h)))
      (ihb (le_zero_eq_zero (evalL level_zero_ones b)
        (natMax (evalL level_zero_ones a) (evalL level_zero_ones b))
        (ugeq_natMax_right (evalL level_zero_ones a) (evalL level_zero_ones b)) h)))
  (fun (a : Level) (b : Level)
    (_iha : @Eq Nat (evalL level_zero_ones a) Nat.zero -> @Eq Bool (level_is_zero a) Bool.true)
    (ihb : @Eq Nat (evalL level_zero_ones b) Nat.zero -> @Eq Bool (level_is_zero b) Bool.true)
    (h : @Eq Nat (evalL level_zero_ones (Level.imax a b)) Nat.zero) =>
    ihb (imaxNat_zero_right (evalL level_zero_ones a) (evalL level_zero_ones b) h))
  (fun (n : Name) (h : @Eq Nat (evalL level_zero_ones (Level.param n)) Nat.zero) =>
    nat_zero_ne_succ_prop Nat.zero (@Eq Bool (level_is_zero (Level.param n)) Bool.true)
      (Eq.symm Nat (Nat.succ Nat.zero) Nat.zero h)) l",
    ),
    (
        "level_is_zero_evalL_reflect",
        r"forall (l : Level) (zero : levelEqSem l Level.zero),
 @Eq Bool (level_is_zero l) Bool.true",
        r"fun (l : Level) (zero : levelEqSem l Level.zero) =>
 level_is_zero_of_evalL_ones l (zero level_zero_ones)",
    ),
    (
        "level_is_zero_substL_true",
        r"forall (s : Name -> Level) (l : Level)
 (zero : @Eq Bool (level_is_zero l) Bool.true),
 @Eq Bool (level_is_zero (substL s l)) Bool.true",
        r"fun (s : Name -> Level) (l : Level)
 (zero : @Eq Bool (level_is_zero l) Bool.true) =>
 level_is_zero_evalL_reflect (substL s l) (fun (rho : Name -> Nat) =>
  Eq.trans Nat (evalL rho (substL s l))
   (evalL (fun (n : Name) => evalL rho (s n)) l) Nat.zero
   (evalL_substL rho s l)
   (ugeq_level_zero l zero (fun (n : Name) => evalL rho (s n))))",
    ),
    (
        "projection_bound_instantiated_bool_zero",
        r"forall (s : Name -> Level)
 (field : Level) (result : Level) (bound : levelLeqSem field result)
 (zero : @Eq Bool (level_is_zero (substL s result)) Bool.true),
 @Eq Bool (level_is_zero (substL s field)) Bool.true",
        r"fun (s : Name -> Level)
 (field : Level) (result : Level) (bound : levelLeqSem field result)
 (zero : @Eq Bool (level_is_zero (substL s result)) Bool.true) =>
 level_is_zero_evalL_reflect (substL s field)
  (projection_bound_instantiated_zero s field result bound
    (ugeq_level_zero (substL s result) zero))",
    ),
    (
        "level_zero_nested_imax_caller",
        r"@Eq Bool (level_is_zero (Level.imax (Level.param Name.anonymous)
  (Level.max Level.zero Level.zero))) Bool.true",
        r"level_is_zero_evalL_reflect
  (Level.imax (Level.param Name.anonymous) (Level.max Level.zero Level.zero))
  (fun (_rho : Name -> Nat) => @Eq.refl Nat Nat.zero)",
    ),
    (
        "level_zero_substitution_caller",
        r"forall (s : Name -> Level),
 @Eq Bool (level_is_zero (substL s (Level.imax (Level.param Name.anonymous)
  (Level.max Level.zero Level.zero)))) Bool.true",
        r"fun (s : Name -> Level) =>
 level_is_zero_substL_true s
  (Level.imax (Level.param Name.anonymous) (Level.max Level.zero Level.zero))
  level_zero_nested_imax_caller",
    ),
    (
        "level_zero_parameter_before",
        r"@Eq Bool (level_is_zero (Level.param Name.anonymous)) Bool.false",
        r"@Eq.refl Bool Bool.false",
    ),
    (
        "level_zero_parameter_after",
        r"@Eq Bool (level_is_zero (substL (fun (_n : Name) => Level.zero)
  (Level.param Name.anonymous))) Bool.true",
        r"@Eq.refl Bool Bool.true",
    ),
    (
        "level_zero_false_preservation_refuted",
        r"forall (preserved : forall (s : Name -> Level) (l : Level),
  @Eq Bool (level_is_zero l) Bool.false ->
  @Eq Bool (level_is_zero (substL s l)) Bool.false),
 Empty",
        r"fun (preserved : forall (s : Name -> Level) (l : Level),
  @Eq Bool (level_is_zero l) Bool.false ->
  @Eq Bool (level_is_zero (substL s l)) Bool.false) =>
 bool_false_ne_true_t Empty (Eq.symm Bool Bool.true Bool.false
  (preserved (fun (_n : Name) => Level.zero) (Level.param Name.anonymous)
    level_zero_parameter_before))",
    ),
    (
        "level_zero_bound_parameter_caller",
        r"@Eq Bool (level_is_zero (substL (fun (_n : Name) => Level.zero)
  (Level.param Name.anonymous))) Bool.true",
        r"projection_bound_instantiated_bool_zero (fun (_n : Name) => Level.zero)
  (Level.param Name.anonymous) (Level.param Name.anonymous)
  (fun (rho : Name -> Nat) => @Le.refl (rho Name.anonymous)) level_zero_parameter_after",
    ),
];

#[cfg(test)]
const PROOF_ROOTS: &[&str] = &[
    "projection_bound_instantiated_zero",
    "imaxNat_zero_right",
    "level_is_zero_of_evalL_ones",
    "level_is_zero_evalL_reflect",
    "level_is_zero_substL_true",
    "projection_bound_instantiated_bool_zero",
    "level_zero_nested_imax_caller",
    "level_zero_substitution_caller",
    "level_zero_parameter_before",
    "level_zero_parameter_after",
    "level_zero_false_preservation_refuted",
    "level_zero_bound_parameter_caller",
];

impl Specification {
    pub(super) fn add_projection_level_zero(&mut self) -> Result<(), SpecError> {
        for &(name, type_src, value_src) in DECLARATIONS {
            if name == "level_zero_ones" {
                // Computational data must unfold at symbolic parameters. The
                // theorem helper intentionally makes non-Prop values opaque.
                self.add_recursive_def(
                    &format!("def {name} : {type_src} := {value_src}"),
                    "Transparent all-ones valuation data for actual computation.",
                )?;
                continue;
            }
            super::acceptance_in::theorem(
                self,
                name,
                type_src,
                value_src,
                "Canonical raw-level semantic-zero reflection, true-direction substitution, and actual semantic-bound transport. Explicit checked value; no projection-output typing or admission assumption. level_zero_ones is valuation data.",
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spec::types::{AxiomCategory, ProofStatus};
    use crate::test_utils::{build_spec_with_stack, run_with_stack};
    use clean_kernel::{ConstantKind, ExprKind, Name};

    const REFUSALS: &[&str] = &[
        r"def level_zero_forged_false_preserved :
 @Eq Bool (level_is_zero (substL (fun (_n : Name) => Level.zero)
  (Level.param Name.anonymous))) Bool.false := @Eq.refl Bool Bool.false",
        r"def level_zero_forged_imax_left_only :
 @Eq Bool (level_is_zero (Level.imax Level.zero (Level.succ Level.zero))) Bool.true :=
 level_is_zero_evalL_reflect (Level.imax Level.zero (Level.succ Level.zero))
  (fun (_rho : Name -> Nat) => @Eq.refl Nat Nat.zero)",
        r"def level_zero_forged_zero_valuation :
 @Eq Bool (level_is_zero (Level.param Name.anonymous)) Bool.true :=
 level_is_zero_of_evalL_ones (Level.param Name.anonymous)
  (@Eq.refl Nat (evalL (fun (_n : Name) => Nat.zero) (Level.param Name.anonymous)))",
    ];

    #[test]
    fn projection_level_zero_records_and_controls_parse() {
        assert_eq!(DECLARATIONS.len(), 13);
        assert_eq!(PROOF_ROOTS.len(), 12);
        assert_eq!(REFUSALS.len(), 3);
        let names: std::collections::HashSet<_> =
            DECLARATIONS.iter().map(|entry| entry.0).collect();
        assert_eq!(names.len(), DECLARATIONS.len());
        for root in PROOF_ROOTS {
            assert!(names.contains(root), "{root}");
        }
        assert!(!PROOF_ROOTS.contains(&"level_zero_ones"));
        for &(name, type_src, value_src) in DECLARATIONS {
            clean_parser::parse_decl(&format!("def {name} : {type_src} := {value_src}"))
                .expect("explicit level-zero record parses");
        }
        for source in REFUSALS {
            clean_parser::parse_decl(source).expect("negative level-zero control parses");
        }
    }

    #[test]
    fn projection_level_zero_registered_values_recheck_without_axioms() {
        run_with_stack(|| {
            let spec = build_spec_with_stack();
            for &(name, type_src, value_src) in DECLARATIONS {
                let definition = spec
                    .definitions()
                    .get(name)
                    .expect("registered declaration");
                let kernel_name = Name::from_string(name);
                let constant = spec
                    .env()
                    .get_const(&kernel_name)
                    .expect("actual kernel root");
                let ty = definition.elaborated_type.as_ref().expect("checked type");
                let value = definition.elaborated_value.as_ref().expect("checked value");
                assert!(!definition.is_axiom, "{name}");
                assert_ne!(constant.kind, ConstantKind::Axiom, "{name}");
                assert_eq!(definition.category, AxiomCategory::DerivedLemma, "{name}");
                if name == "level_zero_ones" {
                    assert_eq!(constant.kind, ConstantKind::Definition, "{name}");
                    let source = format!("def {name} : {type_src} := {value_src}");
                    assert_eq!(definition.type_src, source, "{name}");
                    assert_eq!(
                        definition.value_src.as_deref(),
                        Some(source.as_str()),
                        "{name}"
                    );
                } else {
                    assert_eq!(
                        definition.proof_status,
                        ProofStatus::DerivedProved,
                        "{name}"
                    );
                    assert_eq!(definition.type_src, type_src, "{name}");
                    assert_eq!(definition.value_src.as_deref(), Some(value_src), "{name}");
                }
                assert_eq!(&constant.type_, ty, "{name}");
                assert_eq!(constant.value.as_ref(), Some(value), "{name}");
                assert!(
                    !matches!(value.kind(), ExprKind::Const(n, _) if n == &kernel_name),
                    "{name}"
                );
                spec.verify_definition(name)
                    .expect("actual registered value rechecks");
                assert!(
                    spec.env()
                        .axiom_deps(&kernel_name)
                        .expect("domain closure")
                        .is_empty(),
                    "{name}"
                );
                assert!(
                    spec.env()
                        .foundational_axiom_deps(&kernel_name)
                        .expect("foundational closure")
                        .is_empty(),
                    "{name}"
                );
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                    "{name}"
                );
            }
        });
    }

    #[test]
    fn projection_level_zero_data_registration_distinguishes_opacity() {
        run_with_stack(|| {
            // No full-spec/cache dependency: actual registration APIs, exact
            // valuation record, and only its Nat/Eq/Name bootstrap prerequisites.
            let mut spec = Specification::new_empty();
            spec.add_foundation_types()
                .expect("actual foundation bootstrap");
            spec.add_inductive(
                "inductive Name : Type\n| anonymous : Name\n| str : Name -> Nat -> Name",
                "The actual two-constructor name carrier needed by the valuation.",
            )
            .expect("name carrier");
            let &(name, type_src, value_src) = DECLARATIONS
                .iter()
                .find(|entry| entry.0 == "level_zero_ones")
                .expect("actual valuation record");

            // This reproduces the former incorrect registration: a non-Prop
            // theorem-helper value is intentionally opaque, even with a body.
            super::super::acceptance_in::theorem(
                &mut spec,
                "opaque_level_zero_ones",
                type_src,
                value_src,
                "Negative registration control: computational data through theorem API.",
            )
            .expect("checked opaque value");
            assert_eq!(
                spec.env()
                    .get_const(&Name::from_string("opaque_level_zero_ones"))
                    .expect("opaque root")
                    .kind,
                ConstantKind::Opaque
            );
            let error = spec.add_recursive_def(
                "def opaque_level_zero_ones_forged (n : Name) : @Eq Nat (opaque_level_zero_ones n) (Nat.succ Nat.zero) := @Eq.refl Nat (Nat.succ Nat.zero)",
                "An opaque valuation must not be unfolded by definitional equality.",
            ).expect_err("old opaque data registration cannot support this computation");
            assert!(format!("{error:?}").contains("Type mismatch"), "{error:?}");
            assert!(!spec
                .definitions()
                .contains_key("opaque_level_zero_ones_forged"));
            assert!(spec
                .env()
                .get_const(&Name::from_string("opaque_level_zero_ones_forged"))
                .is_none());

            // Same exact type/value, actual transparent registration API used
            // by the production data branch. The symbolic caller must compute.
            spec.add_recursive_def(
                &format!("def {name} : {type_src} := {value_src}"),
                "Actual transparent valuation data registration.",
            )
            .expect("transparent valuation");
            assert_eq!(
                spec.env()
                    .get_const(&Name::from_string(name))
                    .expect("transparent root")
                    .kind,
                ConstantKind::Definition
            );
            spec.add_recursive_def(
                "def transparent_level_zero_ones_computes (n : Name) : @Eq Nat (level_zero_ones n) (Nat.succ Nat.zero) := @Eq.refl Nat (Nat.succ Nat.zero)",
                "Actual symbolic valuation computation after transparent registration.",
            ).expect("transparent symbolic computation");
            spec.verify_definition("transparent_level_zero_ones_computes")
                .expect("independent actual kernel value/type check");
            let root = Name::from_string("transparent_level_zero_ones_computes");
            assert!(spec
                .env()
                .axiom_deps(&root)
                .expect("domain closure")
                .is_empty());
            assert!(spec
                .env()
                .foundational_axiom_deps(&root)
                .expect("foundational closure")
                .is_empty());
        });
    }

    #[test]
    fn projection_level_zero_rejects_three_false_endpoints() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for source in REFUSALS {
                let clean_parser::SurfaceDecl::Def { name, .. } =
                    clean_parser::parse_decl(source).expect("negative control parses")
                else {
                    panic!("expected a definition");
                };
                let kernel_name = name.qualify_under(&Default::default()).into_name();
                // Legacy record-key projection only; exact kernel identity is checked separately.
                assert!(
                    !spec.definitions().contains_key(
                        &name
                            .qualify_under(&Default::default())
                            .into_name()
                            .to_string()
                    ),
                    "{name}"
                );
                assert!(spec.env().get_const(&kernel_name).is_none(), "{name}");
                let error = spec
                    .add_recursive_def(source, "Reject false zero-classifier endpoints.")
                    .expect_err("the intended false endpoint must not register");
                assert!(format!("{error:?}").contains("Type mismatch"), "{error:?}");
                assert!(
                    !spec.definitions().contains_key(
                        &name
                            .qualify_under(&Default::default())
                            .into_name()
                            .to_string()
                    ),
                    "{name}"
                );
                assert!(spec.env().get_const(&kernel_name).is_none(), "{name}");
            }
        });
    }
}
