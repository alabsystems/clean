// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

use super::*;

const PROBE: &str = "CLEAN_EVALIR_WORKER_BUDGET_TEST";

type Builder = fn() -> Result<Specification, SpecError>;

fn builders() -> [Builder; 7] {
    [
        build_spec_with_stack,
        build_prelude_spec_with_stack,
        build_byte_prelude_spec_v1_with_stack,
        build_positive_division_byte_prelude_spec_v1_with_stack,
        build_u64_shift_by_three_byte_prelude_spec_v1_with_stack,
        build_u64_shift_by_three_output_bounds_byte_prelude_spec_v1_with_stack,
        build_canonical_arithmetic_byte_prelude_spec_v1_with_stack,
    ]
}

#[test]
fn public_worker_builders_refuse_malformed_and_tiny_budgets_before_cache_admission() {
    const NAME: &str = "eval_ir::worker_budget_tests::public_worker_builders_refuse_malformed_and_tiny_budgets_before_cache_admission";
    if let Ok(mode) = std::env::var(PROBE) {
        assert!(matches!(mode.as_str(), "malformed" | "tiny" | "nonutf8"));
        assert!(construction_override());
        assert_eq!(clean_kernel::tc::declaration_budget_limit(), 0);
        for build in builders() {
            let error = match build() {
                Err(error) => error,
                Ok(owner) => panic!(
                    "explicit invalid/tiny budget admitted {} definitions",
                    owner.definitions().len()
                ),
            };
            match mode.as_str() {
                "tiny" => assert!(
                    matches!(&error, SpecError::DeclarationBudgetExhausted { declaration, limit: 1 } if !declaration.is_empty()),
                    "typed resource unknown: {error:?}"
                ),
                _ => assert!(
                    matches!(&error, SpecError::ParseError(detail) if detail.contains("CLEAN_SPEC_DECL_BUDGET")),
                    "requested malformed limit is not a default: {error:?}"
                ),
            }
            assert_eq!(clean_kernel::tc::declaration_budget_limit(), 0);
            assert!(!clean_kernel::tc::declaration_budget_exhausted());
            for cell in [&DEPENDENCY_SCOPED, &PRELUDE, &BYTE_V1] {
                assert!(
                    cell.value.get().is_none(),
                    "a refused build is never cached"
                );
            }
        }
        println!("PUBLIC_WORKER_BUDGET_COMPLETED {mode}");
    } else {
        let cases = vec![
            ("malformed", std::ffi::OsString::from("not-a-budget")),
            ("tiny", "1".into()),
        ];
        #[cfg(unix)]
        let cases = {
            use std::os::unix::ffi::OsStringExt;
            let mut cases = cases;
            cases.push(("nonutf8", std::ffi::OsString::from_vec(vec![0xff])));
            cases
        };
        for (mode, budget) in cases {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args([NAME, "--exact", "--test-threads=1", "--nocapture"])
                .env(PROBE, mode)
                .env("CLEAN_SPEC_DECL_BUDGET", budget)
                .env_remove("CLEAN_STRICT_PROOF_QUALITY")
                .output()
                .unwrap();
            let stdout = String::from_utf8_lossy(&output.stdout);
            assert!(
                output.status.success(),
                "{mode}: {stdout}\n{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert!(stdout.contains(&format!("PUBLIC_WORKER_BUDGET_COMPLETED {mode}")));
            assert!(
                stdout.contains("1 passed; 0 failed"),
                "actual isolated assertions executed: {stdout}"
            );
        }
    }
}

#[test]
fn explicit_worker_budget_scopes_preserve_caller_nested_and_nonbudget_panic_policy() {
    const NAME: &str = "eval_ir::worker_budget_tests::explicit_worker_budget_scopes_preserve_caller_nested_and_nonbudget_panic_policy";
    if let Ok(mode) = std::env::var(PROBE) {
        assert_eq!(mode, "scopes");
        assert_eq!(std::env::var("CLEAN_SPEC_DECL_BUDGET").unwrap(), "17");
        clean_kernel::tc::set_declaration_budget(5);
        let error = build_on_stack("evalir-budget-outer", "outer budget probe", || {
            assert_eq!(clean_kernel::tc::declaration_budget_limit(), 17);
            let nested = build_on_stack("evalir-budget-nested", "nested budget probe", || {
                assert_eq!(clean_kernel::tc::declaration_budget_limit(), 17);
                assert!(!clean_kernel::tc::declaration_budget_exhausted());
                Err(SpecError::EnvError("nested sentinel".into()))
            })
            .unwrap_err();
            assert!(matches!(nested, SpecError::EnvError(detail) if detail == "nested sentinel"));
            assert_eq!(clean_kernel::tc::declaration_budget_limit(), 17);
            Err(SpecError::EnvError("outer sentinel".into()))
        })
        .unwrap_err();
        assert!(matches!(error, SpecError::EnvError(detail) if detail == "outer sentinel"));
        assert_eq!(clean_kernel::tc::declaration_budget_limit(), 5);
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        let error = build_on_stack("evalir-budget-panic", "budget panic probe", || {
            assert_eq!(clean_kernel::tc::declaration_budget_limit(), 17);
            panic!("intentional nonbudget worker panic")
        })
        .unwrap_err();
        assert!(
            matches!(error, SpecError::EnvError(detail) if detail == "budget panic probe specification thread panicked")
        );
        assert_eq!(clean_kernel::tc::declaration_budget_limit(), 5);
        clean_kernel::tc::clear_declaration_budget();
        println!("WORKER_BUDGET_SCOPES_COMPLETED");
    } else {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([NAME, "--exact", "--test-threads=1", "--nocapture"])
            .env(PROBE, "scopes")
            .env("CLEAN_SPEC_DECL_BUDGET", "17")
            .env_remove("CLEAN_STRICT_PROOF_QUALITY")
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            output.status.success(),
            "{stdout}\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(stdout.contains("WORKER_BUDGET_SCOPES_COMPLETED"));
        assert!(
            stdout.contains("1 passed; 0 failed"),
            "actual isolated assertions executed: {stdout}"
        );
    }
}
