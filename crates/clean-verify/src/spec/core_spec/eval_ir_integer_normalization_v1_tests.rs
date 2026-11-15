// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Applications use the actual stored universal proofs. Independent endpoint
//! arithmetic supplies test expectations, never premises to the installed laws.

use super::{install_residues_transactionally, PRODUCT_ROOT, RESIDUES, RESIDUE_ROOTS};
use crate::spec::{SpecError, Specification};
use clean_kernel::{BigNat, Expr, Name};
use std::sync::OnceLock;

use super::super::total_division_test_support::*;

fn normalized() -> &'static Specification {
    static SPEC: OnceLock<Specification> = OnceLock::new();
    SPEC.get_or_init(|| {
        let mut owner = total().clone();
        owner
            .install_eval_ir_integer_mul_residue_laws_v1()
            .expect("actual public checked product/residue extension");
        owner
    })
}

fn nat128(value: u128) -> Expr {
    Expr::bignat_lit(BigNat::from_limbs(vec![value as u64, (value >> 64) as u64]))
}

fn trans(left: Expr, middle: Expr, right: Expr, first: Expr, second: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![clean_kernel::Level::succ(clean_kernel::Level::zero())],
        ),
        [constant("Nat"), left, middle, right, first, second],
    )
}

fn product_proof(a: Expr, b: Expr, answer: Expr) -> (Expr, Expr) {
    let raw = app("ir_nat_mul", [a.clone(), b.clone()]);
    let canonical = app("Nat.mul", [a.clone(), b.clone()]);
    let proof = trans(
        raw.clone(),
        canonical,
        answer.clone(),
        app(PRODUCT_ROOT, [a, b]),
        reflexivity(answer),
    );
    (raw, proof)
}

fn residue_proof(a: Expr, b: Expr, divisor: Expr, answer: Expr) -> (Expr, Expr) {
    let raw = app(
        "ir_nat_rem",
        [app("ir_nat_mul", [a.clone(), b.clone()]), divisor.clone()],
    );
    let total = app(
        "ir_nat_rem_total_v1",
        [app("Nat.mul", [a.clone(), b.clone()]), divisor.clone()],
    );
    let proof = trans(
        raw.clone(),
        total,
        answer.clone(),
        app(RESIDUE_ROOTS[0], [a, b, divisor]),
        reflexivity(answer),
    );
    (raw, proof)
}

fn wrap_proof(width: u64, a: Expr, b: Expr, answer: Expr) -> (Expr, Expr) {
    let width = Expr::nat_lit(width);
    let raw = app(
        "ir_wrap",
        [width.clone(), app("ir_nat_mul", [a.clone(), b.clone()])],
    );
    let total = app(
        "ir_nat_rem_total_v1",
        [
            app("Nat.mul", [a.clone(), b.clone()]),
            app("ir_nat_pow2", [width.clone()]),
        ],
    );
    let proof = trans(
        raw.clone(),
        total,
        answer.clone(),
        app(RESIDUE_ROOTS[1], [width, a, b]),
        reflexivity(answer),
    );
    (raw, proof)
}

#[test]
fn integer_normalization_quantified_product_and_residue_have_no_answer_premises() {
    crate::test_utils::run_with_stack(|| {
        let spec = normalized();
        for (claim, proof) in [
            (
                "forall (a b : Nat), Eq Nat (ir_nat_mul a b) (Nat.mul a b)",
                "fun (a b : Nat) => ir_nat_mul_canonical_agrees_v1 a b",
            ),
            (
                "forall (a b divisor : Nat), Eq Nat (ir_nat_rem (ir_nat_mul a b) divisor) (ir_nat_rem_total_v1 (Nat.mul a b) divisor)",
                "fun (a b divisor : Nat) => ir_nat_mul_rem_total_agrees_v1 a b divisor",
            ),
            (
                "forall (width a b : Nat), Eq Nat (ir_wrap width (ir_nat_mul a b)) (ir_nat_rem_total_v1 (Nat.mul a b) (ir_nat_pow2 width))",
                "fun (width a b : Nat) => ir_wrap_mul_total_agrees_v1 width a b",
            ),
        ] {
            replay(spec, &elaborate(spec, claim), &elaborate(spec, proof), true);
        }
        let info = spec
            .env()
            .get_const(&Name::from_string(PRODUCT_ROOT))
            .unwrap();
        let audit = spec
            .env()
            .audit_certification(&info.type_, &constant(PRODUCT_ROOT));
        assert!(audit.is_certified(), "{audit:#?}");
        for dependency in [
            PRODUCT_ROOT,
            "Nat.rec",
            "Nat.add_comm",
            "ir_nat_mul",
            "Nat.mul",
        ] {
            assert!(
                audit.dependencies.contains(&Name::from_string(dependency)),
                "{dependency}: {audit:#?}"
            );
        }
    });
}

#[test]
fn integer_normalization_public_installation_preserves_original_storage_and_defaults() {
    crate::test_utils::run_with_stack(|| {
        let before = total();
        let after = normalized();
        assert_eq!(
            after.definitions().len(),
            before.definitions().len() + RESIDUES.len()
        );
        previous_unchanged(before, after);
        for root in RESIDUE_ROOTS.iter().copied().chain([PRODUCT_ROOT]) {
            super::super::verify_storage(after, root).expect("strict actual stored value");
            let audit = super::super::verify_root(after, root).expect("actual rooted closure");
            assert!(audit.dependencies.contains(&Name::from_string(root)));
            assert!(after
                .env()
                .axiom_deps(&Name::from_string(root))
                .unwrap()
                .is_empty());
            assert!(after
                .env()
                .trust_marker_deps(&Name::from_string(root))
                .unwrap()
                .is_empty());
        }
        let ordinary = crate::eval_ir::build_byte_prelude_spec_v1_with_stack().unwrap();
        assert!(ordinary.get_definition(PRODUCT_ROOT).is_some());
        for absent in RESIDUE_ROOTS.iter().copied().chain([
            "ir_nat_rem_total_v1",
            "ir_nat_rem_total_agrees_v1",
            "ir_rem_agrees_at_fuel",
        ]) {
            assert!(
                ordinary.get_definition(absent).is_none(),
                "default must not install {absent}"
            );
        }
        for name in ["ir_nat_mul", "ir_nat_rem", "ir_wrap", "ir_nat_pow2"] {
            assert_eq!(
                ordinary.env().get_const(&Name::from_string(name)),
                after.env().get_const(&Name::from_string(name))
            );
        }
    });
}

#[test]
fn integer_normalization_small_products_divisor_zero_and_width_zero_match_independent_arithmetic() {
    crate::test_utils::run_with_stack(|| {
        let spec = normalized();
        for a in 0..=8_u64 {
            for b in 0..=8_u64 {
                let product = a * b;
                let (raw, proof) =
                    product_proof(Expr::nat_lit(a), Expr::nat_lit(b), Expr::nat_lit(product));
                replay(spec, &equality(raw, Expr::nat_lit(product)), &proof, true);
                for divisor in 0..=4_u64 {
                    // Preserve EvalIR's zero-divisor result without assuming
                    // an unproved bridge to canonical Nat.mod.
                    let answer = if divisor == 0 {
                        product
                    } else {
                        product % divisor
                    };
                    let (raw, proof) = residue_proof(
                        Expr::nat_lit(a),
                        Expr::nat_lit(b),
                        Expr::nat_lit(divisor),
                        Expr::nat_lit(answer),
                    );
                    replay(spec, &equality(raw, Expr::nat_lit(answer)), &proof, true);
                }
                for width in 0..=4_u64 {
                    let answer = product % (1_u64 << width);
                    let (raw, proof) = wrap_proof(
                        width,
                        Expr::nat_lit(a),
                        Expr::nat_lit(b),
                        Expr::nat_lit(answer),
                    );
                    replay(spec, &equality(raw, Expr::nat_lit(answer)), &proof, true);
                }
            }
        }
    });
}

#[test]
fn integer_normalization_full64_products_and_wrapped_results_use_both_checked_bridges() {
    crate::test_utils::run_with_stack(|| {
        let spec = normalized();
        for (a, b) in [
            (0, u64::MAX),
            (u64::MAX, 2),
            (1_u64 << 63, u64::MAX),
            (u64::MAX, u64::MAX),
        ] {
            let product = u128::from(a) * u128::from(b);
            let (raw, proof) = product_proof(Expr::nat_lit(a), Expr::nat_lit(b), nat128(product));
            replay(spec, &equality(raw, nat128(product)), &proof, true);
            for width in [0, 8, 32, 64] {
                let answer = nat128(product % (1_u128 << width));
                let (raw, proof) =
                    wrap_proof(width, Expr::nat_lit(a), Expr::nat_lit(b), answer.clone());
                replay(spec, &equality(raw.clone(), answer), &proof, true);
                let audit = spec.env().audit_certification(
                    &equality(raw, nat128(product % (1_u128 << width))),
                    &proof,
                );
                assert!(audit
                    .dependencies
                    .contains(&Name::from_string(PRODUCT_ROOT)));
                assert!(audit
                    .dependencies
                    .contains(&Name::from_string("ir_nat_rem_total_agrees_v1")));
            }
        }
    });
}

#[test]
fn integer_normalization_wrong_product_residue_width_and_operands_are_semantic_refusals() {
    crate::test_utils::run_with_stack(|| {
        let spec = normalized();
        let (raw, proof) = product_proof(Expr::nat_lit(7), Expr::nat_lit(9), Expr::nat_lit(63));
        replay(
            spec,
            &equality(raw.clone(), Expr::nat_lit(63)),
            &proof,
            true,
        );
        replay(spec, &equality(raw, Expr::nat_lit(62)), &proof, false);
        let (raw, proof) = residue_proof(
            Expr::nat_lit(7),
            Expr::nat_lit(9),
            Expr::nat_lit(5),
            Expr::nat_lit(3),
        );
        replay(spec, &equality(raw.clone(), Expr::nat_lit(3)), &proof, true);
        replay(spec, &equality(raw, Expr::nat_lit(4)), &proof, false);
        let (raw, proof) = wrap_proof(5, Expr::nat_lit(7), Expr::nat_lit(9), Expr::nat_lit(31));
        replay(spec, &equality(raw, Expr::nat_lit(31)), &proof, true);
        for (width, a, b) in [(4, 7, 9), (5, 6, 9), (5, 7, 8)] {
            let wrong = app(
                "ir_wrap",
                [
                    Expr::nat_lit(width),
                    app("ir_nat_mul", [Expr::nat_lit(a), Expr::nat_lit(b)]),
                ],
            );
            replay(spec, &equality(wrong, Expr::nat_lit(31)), &proof, false);
        }
    });
}

#[test]
fn integer_normalization_missing_total_package_and_name_collisions_are_atomic() {
    crate::test_utils::run_with_stack(|| {
        let mut missing = positive().clone();
        let before = missing.clone();
        let error = missing
            .install_eval_ir_integer_mul_residue_laws_v1()
            .unwrap_err();
        assert!(
            matches!(error, SpecError::UnknownDefinition(ref name) if name == "ir_nat_rem_total_agrees_v1"),
            "{error:?}"
        );
        owner_unchanged(&before, &missing);
        for root in RESIDUE_ROOTS {
            let mut collided = total().clone();
            collided
                .add_recursive_def(
                    &format!("def {root} : Nat := 0"),
                    "actual incompatible prior owner",
                )
                .unwrap();
            let before = collided.clone();
            let error = collided
                .install_eval_ir_integer_mul_residue_laws_v1()
                .unwrap_err();
            assert!(
                matches!(error, SpecError::EnvError(ref message) if message.contains(root) && message.contains("name collision")),
                "{error:?}"
            );
            owner_unchanged(&before, &collided);
        }
    });
}

#[test]
fn integer_normalization_late_false_proof_does_not_publish_a_partial_package() {
    crate::test_utils::run_with_stack(|| {
        let mut owner = total().clone();
        let before = owner.clone();
        let rows = [
            RESIDUES[0],
            (
                RESIDUE_ROOTS[1],
                "def ir_wrap_mul_total_agrees_v1 (width a b : Nat) : Eq Nat 0 1 := Eq.refl Nat 0",
            ),
        ];
        let error = install_residues_transactionally(&mut owner, rows.into_iter()).unwrap_err();
        crate::test_utils::assert_type_mismatch_rejection(&error, "ir_wrap_mul_total_agrees_v1");
        owner_unchanged(&before, &owner);
    });
}
