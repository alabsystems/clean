// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use super::{build_fresh, construction_override, Package};
use crate::eval_ir::{
    build_on_stack, shared_specification_with_stack, EvalIrVocabulary, VocabularyCell,
};
use crate::spec::{SpecError, Specification};
use clean_kernel::{Expr, KernelTypeError, Level, Name, TypeChecker};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Barrier,
};

fn positive() -> Specification {
    crate::build_positive_division_byte_prelude_spec_v1_with_stack()
        .expect("public checked positive-division package")
}

fn shifted() -> Specification {
    crate::build_u64_shift_by_three_byte_prelude_spec_v1_with_stack()
        .expect("public checked full64 shift package")
}

fn root(spec: &Specification, name: &str) {
    let key = Name::from_string(name);
    let info = spec.env().get_const(&key).expect("actual stored root");
    let term = Expr::const_(
        key.clone(),
        info.level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect::<Vec<_>>(),
    );
    let audit = spec.env().audit_certification(&info.type_, &term);
    assert!(
        audit.is_certified(),
        "actual stored package closure: {audit:#?}"
    );
    assert!(audit.dependencies.contains(&key));
    assert!(spec.env().axiom_deps(&key).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&key).unwrap().is_empty());
}

#[test]
fn package_concurrent_complete_initialization_has_one_success() {
    const PROBE: &str = "CLEAN_PACKAGE_CONCURRENT_TEST";
    const NAME: &str =
        "eval_ir::package_reuse::tests::package_concurrent_complete_initialization_has_one_success";
    if let Ok(marker) = std::env::var(PROBE) {
        assert_eq!(marker, "cold");
        let package = Package::PositiveDivisionByteV1;
        assert!(package.cell().value.get().is_none());
        assert_eq!(package.attempts().load(Ordering::SeqCst), 0);
        let barrier = Barrier::new(8);
        std::thread::scope(|scope| {
            let handles = (0..8)
                .map(|_| {
                    scope.spawn(|| {
                        barrier.wait();
                        let owned = positive();
                        assert!(owned.get_definition("ir_div_agrees_at_fuel").is_some());
                        package.cell().value.get().unwrap() as *const Specification as usize
                    })
                })
                .collect::<Vec<_>>();
            let addresses = handles
                .into_iter()
                .map(|handle| handle.join().unwrap())
                .collect::<Vec<_>>();
            assert!(addresses.iter().all(|address| *address == addresses[0]));
        });
        assert_eq!(package.attempts().load(Ordering::SeqCst), 1);
        root(package.cell().value.get().unwrap(), "ir_div_agrees_at_fuel");
        println!("PACKAGE_CONCURRENT_COMPLETED");
    } else {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([NAME, "--exact", "--test-threads=1", "--nocapture"])
            .env(PROBE, "cold")
            .env_remove("CLEAN_SPEC_DECL_BUDGET")
            .env_remove("CLEAN_STRICT_PROOF_QUALITY")
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            output.status.success(),
            "cold concurrent child failed:\n{stdout}\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(stdout.contains("PACKAGE_CONCURRENT_COMPLETED"));
        assert!(
            stdout.contains("1 passed; 0 failed"),
            "actual cold concurrent assertions executed: {stdout}"
        );
    }
}

#[test]
fn package_errors_and_worker_panics_leave_no_cached_partial_owner() {
    let seed = positive();
    let cell = VocabularyCell::new();
    let error = cell
        .get_or_try_init(|| {
            Err(SpecError::DeclarationBudgetExhausted {
                declaration: "package-test-exhausted-root".into(),
                limit: 17,
            })
        })
        .unwrap_err();
    assert!(
        matches!(error, SpecError::DeclarationBudgetExhausted { declaration, limit: 17 }
        if declaration == "package-test-exhausted-root")
    );
    assert!(cell.value.get().is_none());
    let error = cell
        .get_or_try_init(|| {
            build_on_stack("package-panic-test", "package test", || {
                panic!("intentional checked-package worker panic")
            })
        })
        .unwrap_err();
    assert!(
        matches!(error, SpecError::EnvError(message) if message == "package test specification thread panicked")
    );
    assert!(cell.value.get().is_none());
    let first = cell
        .get_or_try_init(|| Ok(seed.clone()))
        .expect("successful retry after both errors");
    let second = cell
        .get_or_try_init(|| panic!("successful initialization must not repeat"))
        .expect("successful retry is now retained");
    assert!(std::ptr::eq(first, second));
    root(second, "ir_div_agrees_at_fuel");
}

#[test]
fn package_poisoned_initialization_lock_remains_fail_closed() {
    let cell = VocabularyCell::new();
    std::thread::scope(|scope| {
        assert!(scope
            .spawn(|| {
                let _lock = cell.initializing.lock().unwrap();
                panic!("intentional initializer-owner panic");
            })
            .join()
            .is_err());
    });
    let attempts = AtomicUsize::new(0);
    let error = cell
        .get_or_try_init(|| {
            attempts.fetch_add(1, Ordering::SeqCst);
            panic!("a poisoned initializer must not execute its builder")
        })
        .unwrap_err();
    assert!(matches!(error, SpecError::EnvError(message)
        if message == "EvalIR vocabulary initialization lock poisoned"));
    assert_eq!(attempts.load(Ordering::SeqCst), 0);
    assert!(cell.value.get().is_none());
}

#[test]
fn fixed_package_profiles_and_owned_clones_are_isolated_from_default_byte() {
    let default = shared_specification_with_stack(EvalIrVocabulary::ByteV1).unwrap();
    let default_count = default.definitions().len();
    let mut owned = positive();
    let sibling = positive();
    let shift = shifted();
    let positive_cache = Package::PositiveDivisionByteV1.cell().value.get().unwrap();
    let shift_cache = Package::U64ShiftByThreeByteV1.cell().value.get().unwrap();
    assert!(!std::ptr::eq(positive_cache, shift_cache));
    assert_eq!(positive_cache.definitions().len(), default_count + 50);
    assert_eq!(shift_cache.definitions().len(), default_count + 61);
    for name in [
        "ir_bool_false_ne_true",
        "ir_div_agrees_at_fuel",
        "ir_byte_ashr_i64_by_three_v1",
    ] {
        assert!(
            default.get_definition(name).is_none(),
            "default Byte remains unchanged: {name}"
        );
    }
    assert!(positive_cache
        .get_definition("ir_byte_ashr_i64_by_three_v1")
        .is_none());
    owned
        .env_mut()
        .set_option("package-reuse-private".into(), Some("isolated".into()));
    owned
        .add_recursive_def(
            "def package_reuse_private_extension : Nat := 19",
            "owned clone only",
        )
        .unwrap();
    owned
        .definitions_mut()
        .remove("ir_div_agrees_at_fuel")
        .unwrap();
    for untouched in [default, positive_cache, shift_cache, &sibling, &shift] {
        assert!(untouched
            .env()
            .get_option("package-reuse-private")
            .is_none());
        assert!(untouched
            .get_definition("package_reuse_private_extension")
            .is_none());
        assert!(untouched
            .env()
            .get_const(&Name::from_string("package_reuse_private_extension"))
            .is_none());
    }
    assert!(sibling.get_definition("ir_div_agrees_at_fuel").is_some());
    assert!(positive_cache
        .get_definition("ir_div_agrees_at_fuel")
        .is_some());
    assert_eq!(default.definitions().len(), default_count);
    root(positive_cache, "ir_div_agrees_at_fuel");
    root(shift_cache, "ir_byte_ashr_i64_by_three_v1");
}

fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_str(name), args)
}

fn actual_operation(op: &str, ty: &str, word: u64, amount: u64) -> Expr {
    app(
        "ir_binop_eval",
        [
            Expr::const_str(op),
            app(ty, [Expr::nat_lit(64)]),
            app("IRScalar.int_", [Expr::nat_lit(word)]),
            app("IRScalar.int_", [Expr::nat_lit(amount)]),
        ],
    )
}

fn result(answer: u64) -> Expr {
    app(
        "IRStepResult.value",
        [app("IRScalar.int_", [Expr::nat_lit(answer)])],
    )
}

fn equation(left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [Expr::const_str("IRStepResult"), left, right],
    )
}

#[test]
fn warm_checked_package_does_not_certify_forged_actual_operation_endpoints() {
    let spec = shifted();
    let term = Expr::const_str("ir_byte_lshr_u64_max_by_three_v1");
    let answer = 2_305_843_009_213_693_951;
    let mut checker = TypeChecker::new(spec.env());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    let actual = actual_operation("IRBinOp.lshr", "IRTy.uint_", u64::MAX, 3);
    let claim = equation(actual.clone(), result(answer));
    checker.check_type(&term, &claim).unwrap();
    assert!(!checker.heartbeat_spent());
    assert!(spec.env().audit_certification(&claim, &term).is_certified());
    // Full64 admission above uses the checked law, never naive division of
    // MAX. Mutation controls use genuinely distinct small normal forms so
    // incomplete/astronomical conversion cannot masquerade as a rejection.
    let fits = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::const_str("Bool"), Expr::const_str("Bool.true")],
    );
    let term = app("ir_byte_lshr_u64_by_three_v1", [Expr::nat_lit(8), fits]);
    checker
        .check_type(
            &term,
            &equation(
                actual_operation("IRBinOp.lshr", "IRTy.uint_", 8, 3),
                result(1),
            ),
        )
        .unwrap();
    for (opcode, word, amount, actual_answer, forged_answer) in [
        ("IRBinOp.lshr", 8, 3, 1, 0),
        ("IRBinOp.lshr", 16, 3, 2, 1),
        ("IRBinOp.lshr", 8, 4, 0, 1),
        ("IRBinOp.shl", 8, 3, 64, 1),
    ] {
        let actual = actual_operation(opcode, "IRTy.uint_", word, amount);
        let expected = result(actual_answer);
        let normal = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [Expr::const_str("IRStepResult"), expected.clone()],
        );
        checker
            .check_type(&normal, &equation(actual.clone(), expected))
            .unwrap();
        let forged = equation(actual, result(forged_answer));
        let error = checker.check_type(&term, &forged).unwrap_err();
        assert!(
            matches!(error, KernelTypeError::TypeMismatch { .. }),
            "actual false endpoint, not resource/lookup: {error:?}"
        );
        assert!(!checker.heartbeat_spent());
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        assert!(!spec
            .env()
            .audit_certification(&forged, &term)
            .is_certified());
    }
}

#[test]
fn package_warm_cache_honors_live_construction_overrides() {
    const PROBE: &str = "CLEAN_PACKAGE_WARM_OVERRIDE_TEST";
    const NAME: &str =
        "eval_ir::package_reuse::tests::package_warm_cache_honors_live_construction_overrides";
    if let Ok(mode) = std::env::var(PROBE) {
        assert!(matches!(mode.as_str(), "budget" | "strict"));
        let request = |package| match package {
            Package::PositiveDivisionByteV1 => {
                crate::build_positive_division_byte_prelude_spec_v1_with_stack()
            }
            Package::U64ShiftByThreeByteV1 => {
                crate::build_u64_shift_by_three_byte_prelude_spec_v1_with_stack()
            }
            Package::U64ShiftByThreeOutputBoundsByteV1 => {
                crate::build_u64_shift_by_three_output_bounds_byte_prelude_spec_v1_with_stack()
            }
            Package::CanonicalArithmeticByteV1 => {
                crate::build_canonical_arithmetic_byte_prelude_spec_v1_with_stack()
            }
        };
        assert!(
            !construction_override(),
            "child must warm under the ordinary policy first"
        );
        drop(positive());
        drop(shifted());
        let before = [
            Package::PositiveDivisionByteV1,
            Package::U64ShiftByThreeByteV1,
        ]
        .map(|package| package.cell().value.get().unwrap() as *const Specification as usize);
        // Only this exact single-threaded child changes its environment, after
        // every construction worker has joined; parent/sibling tests never do.
        if mode == "budget" {
            std::env::set_var("CLEAN_SPEC_DECL_BUDGET", "not-a-budget");
        } else {
            std::env::set_var("CLEAN_STRICT_PROOF_QUALITY", "1");
        }
        assert!(construction_override());
        for (index, package) in [
            Package::PositiveDivisionByteV1,
            Package::U64ShiftByThreeByteV1,
        ]
        .into_iter()
        .enumerate()
        {
            let attempts = package.attempts().load(Ordering::SeqCst);
            let owned = request(package);
            assert_eq!(
                package.attempts().load(Ordering::SeqCst),
                attempts + 1,
                "live override must execute fresh construction before any warm hit"
            );
            let fresh = build_fresh(package);
            assert_eq!(package.attempts().load(Ordering::SeqCst), attempts + 2);
            if mode == "budget" {
                assert!(
                    matches!(&owned, Err(SpecError::ParseError(message)) if message.contains("CLEAN_SPEC_DECL_BUDGET")),
                    "malformed budget must fail before construction for {package:?}; actual error: {:?}",
                    owned.as_ref().err()
                );
            }
            match (owned, fresh) {
                (Ok(owned), Ok(fresh)) => {
                    assert_eq!(owned.definitions().len(), fresh.definitions().len())
                }
                (Err(owned), Err(fresh)) => assert_eq!(format!("{owned:?}"), format!("{fresh:?}")),
                other => panic!(
                    "{package:?} warm override differs: public error {:?}; fresh error {:?}",
                    other.0.err(),
                    other.1.err()
                ),
            }
            assert_eq!(
                package.cell().value.get().unwrap() as *const Specification as usize,
                before[index],
                "override must neither replace nor corrupt an ordinary-policy cached owner"
            );
        }
        if mode == "budget" {
            std::env::set_var("CLEAN_SPEC_DECL_BUDGET", "1");
            assert!(construction_override());
            for (index, package) in [
                Package::PositiveDivisionByteV1,
                Package::U64ShiftByThreeByteV1,
            ]
            .into_iter()
            .enumerate()
            {
                let attempts = package.attempts().load(Ordering::SeqCst);
                let error = match request(package) {
                    Err(error) => error,
                    Ok(owner) => panic!(
                        "tiny-budget {package:?} unexpectedly returned {} definitions",
                        owner.definitions().len()
                    ),
                };
                assert!(
                    matches!(&error, SpecError::DeclarationBudgetExhausted { declaration, limit: 1 }
                        if !declaration.is_empty()),
                    "numeric budget is typed unknown, not type/lookup/worker failure: {error:?}"
                );
                assert_eq!(package.attempts().load(Ordering::SeqCst), attempts + 1);
                assert_eq!(
                    package.cell().value.get().unwrap() as *const Specification as usize,
                    before[index],
                    "tiny-budget failure must not replace the retained complete owner"
                );
            }
            std::env::remove_var("CLEAN_SPEC_DECL_BUDGET");
        } else {
            std::env::remove_var("CLEAN_STRICT_PROOF_QUALITY");
        }
        assert!(!construction_override());
        let default_count = shared_specification_with_stack(EvalIrVocabulary::ByteV1)
            .unwrap()
            .definitions()
            .len();
        for (index, package) in [
            Package::PositiveDivisionByteV1,
            Package::U64ShiftByThreeByteV1,
        ]
        .into_iter()
        .enumerate()
        {
            let attempts = package.attempts().load(Ordering::SeqCst);
            let owned = request(package).expect("ordinary warm reuse after override removal");
            let retained = package.cell().value.get().unwrap();
            assert_eq!(package.attempts().load(Ordering::SeqCst), attempts);
            assert_eq!(retained as *const Specification as usize, before[index]);
            assert!(!std::ptr::eq(&owned, retained), "return an owned clone");
            let is_shift = package == Package::U64ShiftByThreeByteV1;
            assert_eq!(
                owned.definitions().len(),
                default_count + if is_shift { 61 } else { 50 }
            );
            assert_eq!(owned.definitions().len(), retained.definitions().len());
            assert!(owned.get_definition("ir_div_agrees_at_fuel").is_some());
            assert_eq!(
                owned
                    .get_definition("ir_byte_ashr_i64_by_three_v1")
                    .is_some(),
                is_shift
            );
            for (name, expected) in retained.definitions() {
                let actual = owned.get_definition(name).expect("exact cloned profile");
                assert_eq!(actual.elaborated_type, expected.elaborated_type);
                assert_eq!(actual.elaborated_value, expected.elaborated_value);
                assert_eq!(actual.is_axiom, expected.is_axiom);
                assert_eq!(actual.proof_status, expected.proof_status);
            }
        }
        println!("PACKAGE_WARM_OVERRIDE_COMPLETED {mode}");
    } else {
        for mode in ["budget", "strict"] {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args([NAME, "--exact", "--test-threads=1", "--nocapture"])
                .env(PROBE, mode)
                .env_remove("CLEAN_SPEC_DECL_BUDGET")
                .env_remove("CLEAN_STRICT_PROOF_QUALITY")
                .output()
                .unwrap();
            let stdout = String::from_utf8_lossy(&output.stdout);
            assert!(
                output.status.success(),
                "{mode} child failed:\n{stdout}\n{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert!(
                stdout.contains(&format!("PACKAGE_WARM_OVERRIDE_COMPLETED {mode}")),
                "child executed the warm override assertions"
            );
            assert!(
                stdout.contains("1 passed; 0 failed"),
                "exact child test actually executed: {stdout}"
            );
        }
    }
}
