// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use super::{build_fresh, construction_override, Package};
use crate::eval_ir::{shared_specification_with_stack, EvalIrVocabulary};
use crate::spec::{SpecError, Specification};
use clean_kernel::Name;
use std::sync::{atomic::Ordering, Barrier};

#[cfg(test)]
#[path = "eval_ir_canonical_arithmetic_test_support.rs"]
mod support;
use support::{run_child, same_definition, same_definitions, strict_root, ROOTS};

const PACKAGE: Package = Package::CanonicalArithmeticByteV1;
const PROBE: &str = "CLEAN_CANONICAL_ARITHMETIC_REUSE_TEST";

fn arithmetic() -> Result<Specification, SpecError> {
    crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack()
}
fn retained() -> &'static Specification {
    PACKAGE
        .cell()
        .value
        .get()
        .expect("complete checked profile")
}
fn attempts() -> usize {
    PACKAGE.attempts().load(Ordering::SeqCst)
}

#[test]
fn canonical_arithmetic_concurrent_public_consumers_initialize_once() {
    const NAME: &str = "eval_ir::package_reuse::canonical_arithmetic_tests::canonical_arithmetic_concurrent_public_consumers_initialize_once";
    if let Ok(mode) = std::env::var(PROBE) {
        assert_eq!(mode, "concurrent");
        assert!(!construction_override());
        assert!(PACKAGE.cell().value.get().is_none());
        assert_eq!(attempts(), 0);
        let barrier = Barrier::new(4);
        std::thread::scope(|scope| {
            let workers = (0..4)
                .map(|_| {
                    scope.spawn(|| {
                        barrier.wait();
                        let owned = arithmetic().expect("actual public composite factory");
                        assert!(owned.get_definition(ROOTS[20]).is_some());
                        assert!(!std::ptr::eq(&owned, retained()));
                        retained() as *const Specification as usize
                    })
                })
                .collect::<Vec<_>>();
            let addresses = workers
                .into_iter()
                .map(|worker| worker.join().unwrap())
                .collect::<Vec<_>>();
            assert!(addresses.iter().all(|address| *address == addresses[0]));
        });
        assert_eq!(attempts(), 1, "one complete checked composition");
        crate::test_utils::run_with_stack(|| {
            for root in ROOTS {
                strict_root(retained(), root);
            }
        });
        println!("CANONICAL_ARITHMETIC_COMPLETED concurrent");
    } else {
        let stdout = run_child(NAME, PROBE, "concurrent");
        assert!(
            stdout.contains("CANONICAL_ARITHMETIC_COMPLETED concurrent"),
            "the child half ran to its last assertion: {stdout}"
        );
    }
}

#[test]
fn canonical_arithmetic_owned_clones_match_original_installers_and_isolate_legacy_profiles() {
    crate::test_utils::run_with_stack(|| {
        let mut owned = arithmetic().expect("complete public arithmetic profile");
        let sibling = arithmetic().unwrap();
        let byte = shared_specification_with_stack(EvalIrVocabulary::ByteV1).unwrap();
        let positive = crate::build_positive_division_byte_prelude_spec_v1_with_stack().unwrap();
        let shifted = crate::build_u64_shift_by_three_byte_prelude_spec_v1_with_stack().unwrap();
        let bounded =
            crate::build_u64_shift_by_three_output_bounds_byte_prelude_spec_v1_with_stack()
                .unwrap();
        let mut independent = bounded.clone();
        independent.install_eval_ir_bounded_add_laws_v1().unwrap();
        independent
            .install_eval_ir_unsigned_compare_laws_v1()
            .unwrap();
        // The original independent installers remain an exact subset of the
        // larger XOR/AND/division/shift package. Audit the added roots below.
        for (name, before) in independent.definitions() {
            same_definition(before, retained().get_definition(name).unwrap());
        }
        same_definitions(retained(), &owned);
        assert_eq!(
            retained().definitions().len(),
            byte.definitions().len() + 128
        );
        assert_eq!(
            retained().definitions().len(),
            bounded.definitions().len() + 60
        );
        for previous in [byte, &positive, &shifted, &bounded] {
            for (name, before) in previous.definitions() {
                let after = owned
                    .get_definition(name)
                    .expect("prior stored declaration retained");
                same_definition(before, after);
                assert_eq!(
                    previous.env().get_const(&Name::from_string(name)),
                    owned.env().get_const(&Name::from_string(name))
                );
                assert_eq!(
                    previous
                        .env()
                        .declaration_verification(&Name::from_string(name)),
                    owned
                        .env()
                        .declaration_verification(&Name::from_string(name))
                );
            }
            for root in &ROOTS[9..] {
                // Product agreement belongs to the ordinary ByteV1 owner.
                if *root == "ir_nat_mul_canonical_agrees_v1" {
                    strict_root(previous, root);
                    continue;
                }
                assert!(
                    previous.get_definition(root).is_none(),
                    "legacy profile: {root}"
                );
            }
        }
        for root in ROOTS {
            strict_root(retained(), root);
        }
        owned
            .env_mut()
            .set_option("arithmetic-owned".into(), Some("private".into()));
        owned
            .add_recursive_def("def arithmetic_owned_private : Nat := 19", "owned only")
            .unwrap();
        owned.definitions_mut().remove(ROOTS[20]).unwrap();
        for untouched in [retained(), byte, &positive, &shifted, &bounded, &sibling] {
            assert!(untouched.env().get_option("arithmetic-owned").is_none());
            assert!(untouched
                .get_definition("arithmetic_owned_private")
                .is_none());
            assert!(untouched
                .env()
                .get_const(&Name::from_string("arithmetic_owned_private"))
                .is_none());
        }
        assert!(retained().get_definition(ROOTS[20]).is_some());
        assert!(sibling.get_definition(ROOTS[20]).is_some());
    });
}

#[test]
fn canonical_arithmetic_cold_refused_workers_leave_package_and_defaults_retryable() {
    const NAME: &str = "eval_ir::package_reuse::canonical_arithmetic_tests::canonical_arithmetic_cold_refused_workers_leave_package_and_defaults_retryable";
    if let Ok(mode) = std::env::var(PROBE) {
        assert_eq!(mode, "cold-budget");
        assert_eq!(attempts(), 0);
        for budget in ["not-a-budget", "1"] {
            std::env::set_var("CLEAN_SPEC_DECL_BUDGET", budget);
            let before = attempts();
            let error = arithmetic().expect_err("explicit refusal precedes cache admission");
            if budget == "1" {
                assert!(
                    matches!(&error, SpecError::DeclarationBudgetExhausted { declaration, limit: 1 } if !declaration.is_empty()),
                    "{error:?}"
                );
            } else {
                assert!(
                    matches!(&error, SpecError::ParseError(detail) if detail.contains("CLEAN_SPEC_DECL_BUDGET")),
                    "{error:?}"
                );
            }
            assert_eq!(attempts(), before + 1);
            assert!(PACKAGE.cell().value.get().is_none());
            assert!(crate::eval_ir::BYTE_V1.value.get().is_none());
            assert_eq!(clean_kernel::tc::declaration_budget_limit(), 0);
            assert!(!clean_kernel::tc::declaration_budget_exhausted());
        }
        std::env::remove_var("CLEAN_SPEC_DECL_BUDGET");
        let before = attempts();
        drop(arithmetic().expect("ordinary retry builds a complete profile"));
        assert_eq!(attempts(), before + 1);
        assert!(retained().get_definition(ROOTS[20]).is_some());
        println!("CANONICAL_ARITHMETIC_COMPLETED cold-budget");
    } else {
        let stdout = run_child(NAME, PROBE, "cold-budget");
        assert!(
            stdout.contains("CANONICAL_ARITHMETIC_COMPLETED cold-budget"),
            "the child half ran to its last assertion: {stdout}"
        );
    }
}

#[test]
fn canonical_arithmetic_warm_reuse_respects_invalid_tiny_and_strict_live_overrides() {
    const NAME: &str = "eval_ir::package_reuse::canonical_arithmetic_tests::canonical_arithmetic_warm_reuse_respects_invalid_tiny_and_strict_live_overrides";
    if let Ok(mode) = std::env::var(PROBE) {
        assert_eq!(mode, "warm-overrides");
        assert!(!construction_override());
        assert_eq!(attempts(), 0);
        drop(arithmetic().expect("warm ordinary profile"));
        assert_eq!(attempts(), 1);
        let address = retained() as *const Specification as usize;
        let budgets = vec![std::ffi::OsString::from("not-a-budget"), "1".into()];
        #[cfg(unix)]
        let budgets = {
            use std::os::unix::ffi::OsStringExt;
            let mut budgets = budgets;
            budgets.push(std::ffi::OsString::from_vec(vec![0xff]));
            budgets
        };
        // Only this exact single-threaded child changes its environment, after
        // each actual construction worker has joined; sibling tests never do.
        for budget in budgets {
            std::env::set_var("CLEAN_SPEC_DECL_BUDGET", &budget);
            assert!(construction_override());
            let before = attempts();
            let error = arithmetic().expect_err("warm owner cannot hide fresh refusal");
            if budget == std::ffi::OsStr::new("1") {
                assert!(
                    matches!(&error, SpecError::DeclarationBudgetExhausted { declaration, limit: 1 } if !declaration.is_empty()),
                    "{error:?}"
                );
            } else {
                assert!(
                    matches!(&error, SpecError::ParseError(detail) if detail.contains("CLEAN_SPEC_DECL_BUDGET")),
                    "{error:?}"
                );
            }
            assert_eq!(attempts(), before + 1);
            assert_eq!(retained() as *const Specification as usize, address);
            assert_eq!(clean_kernel::tc::declaration_budget_limit(), 0);
            assert!(!clean_kernel::tc::declaration_budget_exhausted());
        }
        std::env::remove_var("CLEAN_SPEC_DECL_BUDGET");
        std::env::set_var("CLEAN_STRICT_PROOF_QUALITY", "1");
        assert!(construction_override());
        let before = attempts();
        let requested = arithmetic();
        assert_eq!(attempts(), before + 1);
        let fresh = build_fresh(PACKAGE);
        assert_eq!(attempts(), before + 2);
        match (requested, fresh) {
            (Ok(requested), Ok(fresh)) => {
                same_definitions(&fresh, &requested);
                assert!(!std::ptr::eq(&requested, retained()));
                crate::test_utils::run_with_stack(move || {
                    for root in ROOTS {
                        strict_root(&requested, root);
                    }
                });
            }
            (Err(requested), Err(fresh)) => {
                assert_eq!(format!("{requested:?}"), format!("{fresh:?}"))
            }
            other => panic!(
                "fresh-policy mismatch: {:?} / {:?}",
                other.0.err(),
                other.1.err()
            ),
        }
        assert_eq!(retained() as *const Specification as usize, address);
        std::env::remove_var("CLEAN_STRICT_PROOF_QUALITY");
        assert!(!construction_override());
        let before = attempts();
        let recovered = arithmetic().expect("ordinary reuse after fresh override removal");
        assert_eq!(attempts(), before);
        assert_eq!(retained() as *const Specification as usize, address);
        same_definitions(retained(), &recovered);
        println!("CANONICAL_ARITHMETIC_COMPLETED warm-overrides");
    } else {
        let stdout = run_child(NAME, PROBE, "warm-overrides");
        assert!(
            stdout.contains("CANONICAL_ARITHMETIC_COMPLETED warm-overrides"),
            "the child half ran to its last assertion: {stdout}"
        );
    }
}
