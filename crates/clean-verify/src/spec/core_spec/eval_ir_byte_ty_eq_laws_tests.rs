// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Native checks for exact structural type reflection, not source identity.

use crate::spec::Specification;
use clean_kernel::Name;

const ROOTS: &[&str] = &[
    "ir_byte_nat_eqb_sound_walk_v1",
    "ir_byte_nat_eqb_sound_v1",
    "ir_byte_type_equality_sound_v1",
];

const NESTED_REFLECTION: &str = r"def byte_ty_eq_closed_nested_reflection_v1 :
  Eq IRTy
    (IRTy.array_ (IRTy.ref_ (IRTy.fatslice_ (IRTy.struct_ 9))) 3)
    (IRTy.array_ (IRTy.ref_ (IRTy.fatslice_ (IRTy.struct_ 9))) 3) :=
  ir_byte_type_equality_sound_v1
    (IRTy.array_ (IRTy.ref_ (IRTy.fatslice_ (IRTy.struct_ 9))) 3)
    (IRTy.array_ (IRTy.ref_ (IRTy.fatslice_ (IRTy.struct_ 9))) 3)
    (Eq.refl Bool Bool.true)";

const NOMINAL_REFLECTION: &str = r"def byte_ty_eq_closed_nominal_reflection_v1 :
  Eq IRTy (IRTy.enum_ 10) (IRTy.enum_ 10) :=
  ir_byte_type_equality_sound_v1
    (IRTy.enum_ 10) (IRTy.enum_ 10) (Eq.refl Bool Bool.true)";

fn specification() -> Specification {
    crate::eval_ir::build_byte_prelude_spec_v1_with_stack()
        .expect("actual registered Byte extraction/type-equality vocabulary")
}

fn checked(spec: &Specification, name: &str) {
    let def = spec.get_definition(name).expect("value-bearing proof root");
    assert!(!def.is_axiom && def.elaborated_value.is_some());
    spec.verify_definition(name)
        .expect("actual Clean kernel check");
    let name = Name::from_string(name);
    // Both dependency closures must be empty, not merely within an allowlist.
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
}

fn add(spec: &mut Specification, source: &str) {
    spec.add_recursive_def(
        source,
        "Closed model fixture with computed inputs, not Rust source binding",
    )
    .unwrap_or_else(|error| panic!("{source}: {error}"));
    checked(spec, source.split_whitespace().nth(1).unwrap());
}

fn rejected(spec: &mut Specification, name: &str, source: &str) {
    let error = spec
        .add_recursive_def(source, "Unchanged-proof incorrect conclusion control")
        .expect_err("wrong conclusion must be rejected");
    crate::test_utils::assert_type_mismatch_rejection(&error, name);
    assert!(spec.get_definition(name).is_none());
}

#[test]
fn byte_ty_eq_generic_laws_are_checked_and_axiom_free() {
    crate::test_utils::run_with_stack(|| {
        let spec = specification();
        for root in ROOTS {
            checked(&spec, root);
        }
    });
}

#[test]
fn byte_ty_eq_has_inhabited_nested_and_nominal_applications() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        add(&mut spec, NESTED_REFLECTION);
        add(&mut spec, NOMINAL_REFLECTION);
    });
}

#[test]
fn byte_ty_eq_unchanged_proofs_refuse_wrong_nominal_conclusions() {
    crate::test_utils::run_with_stack(|| {
        let mut spec = specification();
        for (source, positive, wrong, old, new) in [
            (
                NESTED_REFLECTION,
                "byte_ty_eq_closed_nested_reflection_v1",
                "byte_ty_eq_wrong_nested_reflection_v1",
                "(IRTy.array_ (IRTy.ref_ (IRTy.fatslice_ (IRTy.struct_ 9))) 3) :=\n",
                "(IRTy.array_ (IRTy.ref_ (IRTy.fatslice_ (IRTy.struct_ 10))) 3) :=\n",
            ),
            (
                NOMINAL_REFLECTION,
                "byte_ty_eq_closed_nominal_reflection_v1",
                "byte_ty_eq_wrong_nominal_reflection_v1",
                "(IRTy.enum_ 10) (IRTy.enum_ 10) :=\n",
                "(IRTy.enum_ 10) (IRTy.enum_ 11) :=\n",
            ),
        ] {
            add(&mut spec, source);
            assert_eq!(source.matches(old).count(), 1);
            assert_eq!(source.matches(&format!("def {positive} :")).count(), 1);
            let mutated = source.replacen(positive, wrong, 1).replacen(old, new, 1);
            assert_ne!(source, mutated);
            assert_eq!(
                source.split_once(":=\n").unwrap().1,
                mutated.split_once(":=\n").unwrap().1,
            );
            rejected(&mut spec, wrong, &mutated);
        }
    });
}
