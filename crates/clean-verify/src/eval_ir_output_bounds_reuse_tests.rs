// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use super::{build_fresh, construction_override, Package};
use crate::eval_ir::{shared_specification_with_stack, EvalIrVocabulary};
use crate::spec::{SpecError, Specification};
use clean_kernel::{ConstantKind, Declaration, Expr, KernelTypeError, Level, Name, TypeChecker};
use std::sync::{atomic::Ordering, Barrier};

const PACKAGE: Package = Package::U64ShiftByThreeOutputBoundsByteV1;
const PROBE: &str = "CLEAN_OUTPUT_BOUNDS_REUSE_TEST";
const LAWS: [&str; 7] = [
    "ir_nat_mul_le_right_v1",
    "ir_nat_quot_lt_of_decomposition_v1",
    "ir_dm_quot_lt_v1",
    "ir_nat_add_sub_lt_of_lt_le_v1",
    "ir_positive_division_u64_fill_quotient_by_three_v1",
    "ir_byte_lshr_u64_by_three_result_bound_v1",
    "ir_byte_ashr_i64_by_three_result_bound_v1",
];

fn bounded() -> Result<Specification, SpecError> {
    crate::build_u64_shift_by_three_output_bounds_byte_prelude_spec_v1_with_stack()
}

fn retained() -> &'static Specification {
    PACKAGE
        .cell()
        .value
        .get()
        .expect("complete retained package")
}

fn attempts() -> usize {
    PACKAGE.attempts().load(Ordering::SeqCst)
}

fn strict_root(spec: &Specification, name: &str) {
    let key = Name::from_string(name);
    let info = spec.env().get_const(&key).expect("actual stored law");
    let definition = spec.get_definition(name).expect("actual spec metadata");
    let value = info
        .value
        .as_ref()
        .expect("stored proof body, not an axiom");
    assert_eq!(info.kind, ConstantKind::Definition);
    assert!(!definition.is_axiom);
    assert_eq!(definition.elaborated_type.as_ref(), Some(&info.type_));
    assert_eq!(definition.elaborated_value.as_ref(), Some(value));
    assert!(!info.type_.has_fvar_quick());
    assert!(!value.has_fvar_quick());
    spec.verify_definition(name)
        .expect("exact stored proof replay");
    spec.env()
        .check_decl_readonly_strict(&Declaration::Definition {
            name: key.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value: value.clone(),
            is_reducible: info.is_reducible,
        })
        .expect("strict immutable declaration check");
    let term = Expr::const_(
        key.clone(),
        info.level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect::<Vec<_>>(),
    );
    let mut checker = TypeChecker::new(spec.env());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker
        .check_type(&term, &info.type_)
        .expect("strict stored endpoint");
    assert!(!checker.heartbeat_spent());
    let audit = spec.env().audit_certification(&info.type_, &term);
    assert!(audit.is_certified(), "{name}: {audit:#?}");
    assert!(audit.dependencies.contains(&key));
    assert!(spec
        .env()
        .axiom_deps(&key)
        .expect("root closure")
        .is_empty());
    assert!(spec
        .env()
        .trust_marker_deps(&key)
        .expect("root closure")
        .is_empty());
}

fn same_definitions(expected: &Specification, actual: &Specification) {
    assert_eq!(expected.definitions().len(), actual.definitions().len());
    for (name, before) in expected.definitions() {
        let after = actual.get_definition(name).expect("complete owned clone");
        assert_eq!(before.elaborated_type, after.elaborated_type, "{name}");
        assert_eq!(before.elaborated_value, after.elaborated_value, "{name}");
        assert_eq!(before.proof_status, after.proof_status, "{name}");
        assert_eq!(before.is_axiom, after.is_axiom, "{name}");
        assert_eq!(
            expected.env().get_const(&Name::from_string(name)),
            actual.env().get_const(&Name::from_string(name))
        );
    }
}

/// Runs the exact test `name` alone in a fresh process with `PROBE=mode` and
/// returns its stdout once that process passed exactly that one test. The
/// caller asserts the completion line its own child half printed, so the
/// parent half of every probe test fails at its own site.
fn run_child(name: &str, mode: &str) -> String {
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args([name, "--exact", "--test-threads=1", "--nocapture"])
        .env(PROBE, mode)
        .env_remove("CLEAN_SPEC_DECL_BUDGET")
        .env_remove("CLEAN_STRICT_PROOF_QUALITY")
        .output()
        .expect("execute isolated public-package consumer");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "{mode}: {stdout}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        stdout.contains("1 passed; 0 failed"),
        "nonvacuous exact child result: {stdout}"
    );
    stdout.into_owned()
}

#[test]
fn output_bounds_concurrent_public_consumers_initialize_once() {
    const NAME: &str = "eval_ir::package_reuse::output_bounds_tests::output_bounds_concurrent_public_consumers_initialize_once";
    if let Ok(mode) = std::env::var(PROBE) {
        assert_eq!(mode, "concurrent");
        assert!(!construction_override());
        assert!(PACKAGE.cell().value.get().is_none());
        assert_eq!(attempts(), 0);
        for parent in [
            Package::PositiveDivisionByteV1,
            Package::U64ShiftByThreeByteV1,
        ] {
            assert!(parent.cell().value.get().is_none());
            assert_eq!(parent.attempts().load(Ordering::SeqCst), 0);
        }
        let barrier = Barrier::new(4);
        std::thread::scope(|scope| {
            let workers = (0..4)
                .map(|_| {
                    scope.spawn(|| {
                        barrier.wait();
                        let owned = bounded().expect("ordinary concurrent public factory");
                        assert!(owned.get_definition(LAWS[6]).is_some());
                        assert!(
                            !std::ptr::eq(&owned, retained()),
                            "owned result, not shared mutation"
                        );
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
        assert_eq!(
            attempts(),
            1,
            "one complete successful checked construction"
        );
        for (parent, name) in [
            (Package::PositiveDivisionByteV1, "ir_div_agrees_at_fuel"),
            (
                Package::U64ShiftByThreeByteV1,
                "ir_byte_ashr_i64_by_three_v1",
            ),
        ] {
            assert_eq!(parent.attempts().load(Ordering::SeqCst), 1);
            let checked = parent.cell().value.get().expect("complete checked parent");
            assert_eq!(
                checked.env().get_const(&Name::from_string(name)),
                retained().env().get_const(&Name::from_string(name)),
                "extension preserves the actual checked parent declaration"
            );
        }
        crate::test_utils::run_with_stack(|| {
            for name in LAWS {
                strict_root(retained(), name);
            }
        });
        println!("OUTPUT_BOUNDS_REUSE_COMPLETED concurrent");
    } else {
        let stdout = run_child(NAME, "concurrent");
        assert!(
            stdout.contains("OUTPUT_BOUNDS_REUSE_COMPLETED concurrent"),
            "actual child assertions: {stdout}"
        );
    }
}

#[test]
fn output_bounds_owned_clones_preserve_fixed_profiles_and_default_byte() {
    crate::test_utils::run_with_stack(|| {
        let mut owned = bounded().expect("public bounded-shift owner");
        let sibling = bounded().expect("another owned clone");
        let byte = shared_specification_with_stack(EvalIrVocabulary::ByteV1).unwrap();
        let positive = crate::build_positive_division_byte_prelude_spec_v1_with_stack().unwrap();
        let shifted = crate::build_u64_shift_by_three_byte_prelude_spec_v1_with_stack().unwrap();
        assert_eq!(
            retained().definitions().len(),
            byte.definitions().len() + 68
        );
        assert_eq!(
            retained().definitions().len(),
            shifted.definitions().len() + LAWS.len()
        );
        same_definitions(retained(), &owned);
        for name in LAWS {
            assert!(
                byte.get_definition(name).is_none(),
                "default Byte unchanged: {name}"
            );
            assert!(
                positive.get_definition(name).is_none(),
                "positive profile unchanged: {name}"
            );
            assert!(
                shifted.get_definition(name).is_none(),
                "unbounded shift profile unchanged: {name}"
            );
            strict_root(retained(), name);
        }
        owned
            .env_mut()
            .set_option("bounded-package-owned".into(), Some("private".into()));
        owned
            .add_recursive_def(
                "def bounded_package_private_extension : Nat := 19",
                "owned clone only",
            )
            .unwrap();
        owned.definitions_mut().remove(LAWS[6]).unwrap();
        for untouched in [retained(), byte, &positive, &shifted, &sibling] {
            assert!(untouched
                .env()
                .get_option("bounded-package-owned")
                .is_none());
            assert!(untouched
                .get_definition("bounded_package_private_extension")
                .is_none());
            assert!(untouched
                .env()
                .get_const(&Name::from_string("bounded_package_private_extension"))
                .is_none());
        }
        assert!(sibling.get_definition(LAWS[6]).is_some());
        assert!(retained().get_definition(LAWS[6]).is_some());
    });
}

#[test]
fn output_bounds_warm_cache_honors_invalid_tiny_and_strict_live_overrides() {
    const NAME: &str = "eval_ir::package_reuse::output_bounds_tests::output_bounds_warm_cache_honors_invalid_tiny_and_strict_live_overrides";
    if let Ok(mode) = std::env::var(PROBE) {
        assert_eq!(mode, "overrides");
        assert!(!construction_override());
        assert_eq!(attempts(), 0);
        drop(bounded().expect("warm ordinary public factory before changing policy"));
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
        // Only this exact single-threaded child mutates the process environment;
        // every construction worker has joined before its next change.
        for budget in budgets {
            std::env::set_var("CLEAN_SPEC_DECL_BUDGET", &budget);
            assert!(construction_override());
            let before = attempts();
            let error = bounded().expect_err("warm hit must not hide a refused fresh policy");
            if budget == std::ffi::OsStr::new("1") {
                assert!(
                    matches!(&error, SpecError::DeclarationBudgetExhausted { declaration, limit: 1 } if !declaration.is_empty()),
                    "typed resource unknown, not worker/type error: {error:?}"
                );
            } else {
                assert!(
                    matches!(&error, SpecError::ParseError(detail) if detail.contains("CLEAN_SPEC_DECL_BUDGET")),
                    "malformed including nonUTF8 never becomes the default: {error:?}"
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
        let requested = bounded();
        assert_eq!(
            attempts(),
            before + 1,
            "strict policy runs fresh, never the warm owner"
        );
        let direct = build_fresh(PACKAGE);
        assert_eq!(attempts(), before + 2);
        match (requested, direct) {
            (Ok(requested), Ok(direct)) => {
                same_definitions(&direct, &requested);
                assert!(!std::ptr::eq(&requested, retained()));
                crate::test_utils::run_with_stack(move || {
                    strict_root(&requested, LAWS[5]);
                    strict_root(&requested, LAWS[6]);
                });
            }
            (Err(requested), Err(direct)) => {
                assert_eq!(format!("{requested:?}"), format!("{direct:?}"))
            }
            other => panic!(
                "public strict path differs from original fresh builder: {:?} / {:?}",
                other.0.err(),
                other.1.err()
            ),
        }
        assert_eq!(retained() as *const Specification as usize, address);
        std::env::remove_var("CLEAN_STRICT_PROOF_QUALITY");
        assert!(!construction_override());
        let before = attempts();
        let recovered = bounded().expect("ordinary warm reuse after removing live override");
        assert_eq!(
            attempts(),
            before,
            "no reinitialization after refused fresh requests"
        );
        assert_eq!(retained() as *const Specification as usize, address);
        assert!(!std::ptr::eq(&recovered, retained()));
        same_definitions(retained(), &recovered);
        println!("OUTPUT_BOUNDS_REUSE_COMPLETED overrides");
    } else {
        let stdout = run_child(NAME, "overrides");
        assert!(
            stdout.contains("OUTPUT_BOUNDS_REUSE_COMPLETED overrides"),
            "actual child assertions: {stdout}"
        );
    }
}

fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_str(name), args)
}

fn eq_bool(left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [Expr::const_str("Bool"), left, right],
    )
}

fn bool_refl(value: &str) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::const_str("Bool"), Expr::const_str(value)],
    )
}

#[test]
fn warm_output_bound_library_does_not_certify_false_operation_bounds() {
    crate::test_utils::run_with_stack(|| {
        let spec = bounded().expect("public checked bound library");
        let proof = app(LAWS[5], [Expr::nat_lit(8), bool_refl("Bool.true")]);
        let quotient = app(
            "ir_dm_quot",
            [app(
                "ir_dm_go",
                [
                    Expr::nat_lit(1),
                    Expr::nat_lit(8),
                    Expr::nat_lit(64),
                    Expr::nat_lit(8),
                    app("IRDivMod.mk", [Expr::nat_lit(8), Expr::nat_lit(0)]),
                ],
            )],
        );
        let actual = app(
            "ir_nat_ltb",
            [quotient.clone(), app("ir_nat_pow2", [Expr::nat_lit(64)])],
        );
        let mut checker = TypeChecker::new(spec.env());
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        let valid = eq_bool(actual, Expr::const_str("Bool.true"));
        checker
            .check_type(&proof, &valid)
            .expect("actual restoring quotient bound");
        assert!(spec
            .env()
            .audit_certification(&valid, &proof)
            .is_certified());
        // Actual quotient(8,64,8)=1, so narrowing the limit to one is false.
        // An independently checked literal normal form establishes this is
        // a mathematical mismatch, not a lookup/fuel/resource refusal.
        let false_bound = app("ir_nat_ltb", [quotient, Expr::nat_lit(1)]);
        checker
            .check_type(
                &bool_refl("Bool.false"),
                &eq_bool(false_bound.clone(), Expr::const_str("Bool.false")),
            )
            .expect("independent false normal form");
        let forged = eq_bool(false_bound, Expr::const_str("Bool.true"));
        let error = checker
            .check_type(&proof, &forged)
            .expect_err("fixed checked library cannot certify a different false endpoint");
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "actual false endpoint: {error:?}"
        );
        assert!(!checker.heartbeat_spent());
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        assert!(!spec
            .env()
            .audit_certification(&forged, &proof)
            .is_certified());
    });
}
