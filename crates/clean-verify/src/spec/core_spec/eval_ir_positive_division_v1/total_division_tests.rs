// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use super::{install_transactionally, rows, sources, ROOTS};
use crate::spec::SpecError;
use clean_kernel::{BigNat, Expr, Name};

use super::super::total_division_test_support::*;

const EXISTING_PREREQUISITES: [&str; 21] = [
    "ir_bool_false_ne_true",
    "ir_div_agrees_at_fuel",
    "ir_div_go",
    "ir_dm_go",
    "ir_dm_quot",
    "ir_dm_rem",
    "ir_eq_cong",
    "ir_nat_div",
    "ir_nat_ltb",
    "ir_nat_ltb_walk",
    "ir_nat_ltb_walk_eq",
    "ir_nat_ltb_walk_self_lt_add_succ",
    "ir_nat_ltb_walk_zero_right",
    "ir_nat_mul",
    "ir_nat_mul_zero_left",
    "ir_nat_rem",
    "ir_nat_shl",
    "ir_rem_agrees_at_fuel",
    "nat_add_assoc_local",
    "nat_add_succ_left",
    "nat_add_zero_left",
];

const EXPECTED: [&str; 17] = [
    "ir_nat_ltb_succ_walk",
    "ir_nat_ltb_walk_pred_left",
    "ir_nat_ltb_walk_drop_add_left",
    "ir_nat_shl_index_lt",
    "ir_dm_fuel_always_suffices",
    "ir_div_agrees_unconditional",
    "ir_rem_agrees_unconditional",
    "ir_nat_divmod_total_v1",
    "ir_nat_div_total_v1",
    "ir_nat_rem_total_v1",
    "ir_div_go_zero_divisor_v1",
    "ir_nat_div_zero_divisor_v1",
    "ir_nat_rem_zero_divisor_v1",
    "ir_nat_div_total_agrees_v1",
    "ir_nat_rem_total_agrees_v1",
    "ir_nat_rem_total_positive_bound_v1",
    "ir_nat_rem_positive_bound_v1",
];

#[test]
fn total_division_public_installation_has_exact_checked_roots_and_preserves_defaults() {
    crate::test_utils::run_with_stack(|| {
        assert_eq!(rows().map(|(name, _)| name).collect::<Vec<_>>(), EXPECTED);
        let before = positive();
        for name in EXISTING_PREREQUISITES {
            assert!(
                before.env().get_const(&Name::from_string(name)).is_some(),
                "actual prerequisite {name}"
            );
        }
        assert_eq!(
            rows().next(),
            Some((
                "ir_nat_ltb_succ_walk",
                super::super::super::eval_ir_lzd_fresh::ltb_succ_walk_source()
            )),
            "one original checked prerequisite source owner"
        );
        let after = total();
        assert_eq!(
            after.definitions().len(),
            before.definitions().len() + EXPECTED.len()
        );
        previous_unchanged(before, after);
        for name in EXPECTED {
            super::super::verify_storage(after, name).expect("strict stored row recheck");
            let key = Name::from_string(name);
            assert!(after.env().axiom_deps(&key).expect("real row").is_empty());
            assert!(after
                .env()
                .trust_marker_deps(&key)
                .expect("real row")
                .is_empty());
        }
        for root in ROOTS {
            let info = after.env().get_const(&Name::from_string(root)).unwrap();
            replay(after, &info.type_, &constant(root), true);
            let audit = after
                .env()
                .audit_certification(&info.type_, &constant(root));
            assert!(audit.dependencies.contains(&Name::from_string(root)));
        }
        let default = crate::eval_ir::build_byte_prelude_spec_v1_with_stack().unwrap();
        for name in EXPECTED {
            assert!(default.env().get_const(&Name::from_string(name)).is_none());
        }
        for name in ["ir_nat_div", "ir_nat_rem", "ir_div_go", "ir_wrap"] {
            assert_eq!(
                default.env().get_const(&Name::from_string(name)),
                before.env().get_const(&Name::from_string(name))
            );
        }
        for (name, source) in sources::UNCONDITIONAL {
            assert_eq!(super::super::source_for_probe(name), Some(*source));
        }
    });
}

#[test]
fn total_division_symbolic_all_nat_and_explicit_zero_consumers_have_no_answer_premise() {
    crate::test_utils::run_with_stack(|| {
        let spec = total();
        for (operation, law) in [
            ("div", "ir_nat_div_total_agrees_v1"),
            ("rem", "ir_nat_rem_total_agrees_v1"),
        ] {
            for divisor in ["divisor", "Nat.succ divisor", "0"] {
                let claim = elaborate(
                    spec,
                    &format!(
                        "forall (word divisor : Nat), @Eq Nat (ir_nat_{operation} word ({divisor})) (ir_nat_{operation}_total_v1 word ({divisor}))"
                    ),
                );
                let proof = elaborate(
                    spec,
                    &format!("fun (word divisor : Nat) => {law} word ({divisor})"),
                );
                replay(spec, &claim, &proof, true);
            }
            let claim = elaborate(
                spec,
                &format!("forall (word : Nat), @Eq Nat (ir_nat_{operation}_total_v1 word 0) word"),
            );
            let proof = elaborate(spec, "fun (word : Nat) => @Eq.refl Nat word");
            replay(spec, &claim, &proof, true);
        }
    });
}

#[test]
fn total_division_positive_remainder_bounds_are_symbolic_without_an_answer_premise() {
    crate::test_utils::run_with_stack(|| {
        let spec = total();
        for (operation, law) in [
            ("ir_nat_rem_total_v1", "ir_nat_rem_total_positive_bound_v1"),
            ("ir_nat_rem", "ir_nat_rem_positive_bound_v1"),
        ] {
            // Two natural inputs only: neither the remainder nor its fit is
            // a hypothesis. The positive modulus is explicitly succ divisor.
            let claim = elaborate(
                spec,
                &format!(
                    "forall (word divisor : Nat), @Eq Bool (ir_nat_ltb ({operation} word (Nat.succ divisor)) (Nat.succ divisor)) Bool.true"
                ),
            );
            let proof = elaborate(
                spec,
                &format!("fun (word divisor : Nat) => {law} word divisor"),
            );
            replay(spec, &claim, &proof, true);
            let audit = spec.env().audit_certification(&claim, &proof);
            assert!(audit.dependencies.contains(&Name::from_string(law)));
            assert!(spec
                .env()
                .axiom_deps(&Name::from_string(law))
                .unwrap()
                .is_empty());
            assert!(spec
                .env()
                .trust_marker_deps(&Name::from_string(law))
                .unwrap()
                .is_empty());
        }
    });
}

#[test]
fn total_division_positive_remainder_bounds_cover_small_and_full64_moduli() {
    crate::test_utils::run_with_stack(|| {
        let spec = total();
        for (word, divisor) in [(0, 1), (9, 2), (17, 5), (u64::MAX, 1), (u64::MAX, u64::MAX)] {
            let remainder = word % divisor;
            assert!(remainder < divisor, "independent host remainder bound");
            for (operation, law) in [
                ("ir_nat_rem_total_v1", "ir_nat_rem_total_positive_bound_v1"),
                ("ir_nat_rem", "ir_nat_rem_positive_bound_v1"),
            ] {
                let claim = elaborate(
                    spec,
                    &format!(
                        "@Eq Bool (ir_nat_ltb ({operation} {word} {divisor}) {divisor}) Bool.true"
                    ),
                );
                let proof = app(law, [Expr::nat_lit(word), Expr::nat_lit(divisor - 1)]);
                replay(spec, &claim, &proof, true);
            }
        }
    });
}

#[test]
fn total_division_positive_bound_cannot_authorize_zero_smaller_bound_or_quotient() {
    crate::test_utils::run_with_stack(|| {
        let spec = total();
        for (operation, law) in [
            ("ir_nat_rem_total_v1", "ir_nat_rem_total_positive_bound_v1"),
            ("ir_nat_rem", "ir_nat_rem_positive_bound_v1"),
        ] {
            let valid = elaborate(
                spec,
                &format!("@Eq Bool (ir_nat_ltb ({operation} 1 2) 2) Bool.true"),
            );
            let proof = app(law, [Expr::nat_lit(1), Expr::nat_lit(1)]);
            replay(spec, &valid, &proof, true);
            for (word, divisor, bound) in [(1, 0, 0), (1, 2, 1)] {
                let claim = elaborate(
                    spec,
                    &format!(
                        "@Eq Bool (ir_nat_ltb ({operation} {word} {divisor}) {bound}) Bool.true"
                    ),
                );
                replay(spec, &claim, &proof, false);
            }
        }
        let proof = app(
            "ir_nat_rem_total_positive_bound_v1",
            [Expr::nat_lit(17), Expr::nat_lit(0)],
        );
        let quotient = elaborate(
            spec,
            "@Eq Bool (ir_nat_ltb (ir_nat_div_total_v1 17 1) 1) Bool.true",
        );
        replay(spec, &quotient, &proof, false);
    });
}

#[test]
fn total_division_affordable_differentials_and_full64_endpoints_compute_independently() {
    crate::test_utils::run_with_stack(|| {
        let spec = total();
        for (word, divisor) in [
            (0, 0),
            (7, 0),
            (0, 3),
            (2, 5),
            (17, 5),
            (31, 2),
            (u64::MAX, 1),
            (u64::MAX, 2),
            (u64::MAX, 8),
            (u64::MAX, u64::MAX),
        ] {
            let answers = word
                .checked_div(divisor)
                .zip(word.checked_rem(divisor))
                .map_or([word, word], |(quotient, remainder)| [quotient, remainder]);
            for (operation, answer) in ["div", "rem"].into_iter().zip(answers) {
                let lhs = app(
                    &format!("ir_nat_{operation}_total_v1"),
                    [Expr::nat_lit(word), Expr::nat_lit(divisor)],
                );
                replay(
                    spec,
                    &equality(lhs.clone(), Expr::nat_lit(answer)),
                    &reflexivity(Expr::nat_lit(answer)),
                    true,
                );
                if word <= 31 {
                    let original = app(
                        &format!("ir_nat_{operation}"),
                        [Expr::nat_lit(word), Expr::nat_lit(divisor)],
                    );
                    replay(
                        spec,
                        &equality(original.clone(), Expr::nat_lit(answer)),
                        &reflexivity(Expr::nat_lit(answer)),
                        true,
                    );
                    let agreement = app(
                        &format!("ir_nat_{operation}_total_agrees_v1"),
                        [Expr::nat_lit(word), Expr::nat_lit(divisor)],
                    );
                    replay(spec, &equality(original, lhs), &agreement, true);
                }
            }
        }
    });
}

#[test]
fn total_division_beyond_4200_bits_uses_universal_depth_and_zero_branch_not_bounded_wrapper() {
    crate::test_utils::run_with_stack(|| {
        let spec = total();
        // Exact limb construction, not the restoring evaluator or a computed
        // pow2 answer: dividend=2^4201+7, quotient-by-two=2^4200+3, remainder=1.
        let mut word_limbs = vec![0; 66];
        word_limbs[0] = 7;
        word_limbs[65] = 1_u64 << 41;
        let word = Expr::bignat_lit(BigNat::from_limbs(word_limbs));
        let mut quotient_limbs = vec![0; 66];
        quotient_limbs[0] = 3;
        quotient_limbs[65] = 1_u64 << 40;
        let quotient = Expr::bignat_lit(BigNat::from_limbs(quotient_limbs));
        for (operation, divisor, answer) in [
            ("div", 2, quotient),
            ("rem", 2, Expr::nat_lit(1)),
            ("div", 0, word.clone()),
            ("rem", 0, word.clone()),
        ] {
            let lhs = app(
                &format!("ir_nat_{operation}_total_v1"),
                [word.clone(), Expr::nat_lit(divisor)],
            );
            replay(
                spec,
                &equality(lhs, answer.clone()),
                &reflexivity(answer),
                true,
            );
        }
    });
}

#[test]
fn total_division_false_quotient_remainder_operand_and_projection_controls_are_typed_refusals() {
    crate::test_utils::run_with_stack(|| {
        let spec = total();
        for (operation, word, divisor, actual, forged) in [
            ("div", 17, 5, 3, 4),
            ("rem", 17, 5, 2, 3),
            ("div", 17, 0, 17, 0),
            ("rem", 17, 0, 17, 0),
            ("div", 18, 5, 3, 2),
            ("rem", 18, 5, 3, 2),
            ("div", 17, 6, 2, 3),
            ("rem", 17, 6, 5, 2),
        ] {
            let lhs = app(
                &format!("ir_nat_{operation}_total_v1"),
                [Expr::nat_lit(word), Expr::nat_lit(divisor)],
            );
            replay(
                spec,
                &equality(lhs.clone(), Expr::nat_lit(actual)),
                &reflexivity(Expr::nat_lit(actual)),
                true,
            );
            replay(
                spec,
                &equality(lhs, Expr::nat_lit(forged)),
                &reflexivity(Expr::nat_lit(forged)),
                false,
            );
        }
    });
}

#[test]
fn total_division_collisions_missing_substrate_and_late_false_source_preserve_the_owner() {
    crate::test_utils::run_with_stack(|| {
        let base = positive();
        for name in [EXPECTED[0], EXPECTED[14], EXPECTED[15], EXPECTED[16]] {
            let mut spec = base.clone();
            spec.add_recursive_def(&format!("def {name} : Nat := 0"), "actual conflicting name")
                .unwrap();
            let before = spec.clone();
            let error = spec
                .install_eval_ir_total_restoring_division_laws_v1()
                .unwrap_err();
            assert!(
                matches!(error, SpecError::EnvError(ref detail) if detail.contains(name) && detail.contains("name collision")),
                "{error:?}"
            );
            owner_unchanged(&before, &spec);
        }
        let mut spec = total().clone();
        let before = spec.clone();
        assert!(matches!(
            spec.install_eval_ir_total_restoring_division_laws_v1(),
            Err(SpecError::EnvError(_))
        ));
        owner_unchanged(&before, &spec);
        let mut missing = crate::eval_ir::build_byte_prelude_spec_v1_with_stack().unwrap();
        let before = missing.clone();
        let error = missing
            .install_eval_ir_total_restoring_division_laws_v1()
            .unwrap_err();
        assert!(
            matches!(error, SpecError::UnknownDefinition(ref name) if name == "ir_div_agrees_at_fuel"),
            "{error:?}"
        );
        owner_unchanged(&before, &missing);
        let mut spec = base.clone();
        let before = spec.clone();
        let mut corrupted = rows().collect::<Vec<_>>();
        corrupted[14].1 = "def ir_nat_rem_total_agrees_v1 : @Eq Nat 0 1 := @Eq.refl Nat 0";
        let error = install_transactionally(&mut spec, corrupted.iter().copied()).unwrap_err();
        assert!(
            matches!(&error, SpecError::TypeError(_) | SpecError::ElabError(_)),
            "false source, not resource/lookup/syntax: {error:?}"
        );
        let detail = error.to_string().to_ascii_lowercase();
        assert!(
            detail.contains("ir_nat_rem_total_agrees_v1") && detail.contains("type mismatch"),
            "{detail}"
        );
        for refusal in [
            "budget",
            "heartbeat",
            "recursion limit",
            "unknown identifier",
            "parse error",
        ] {
            assert!(
                !detail.contains(refusal),
                "not a mathematical refusal: {detail}"
            );
        }
        owner_unchanged(&before, &spec);
    });
}
