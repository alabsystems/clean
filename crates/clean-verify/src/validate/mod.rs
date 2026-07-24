// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cross-Validation Between Specification and Implementation
//!
//! This module validates that the Rust kernel implementation matches
//! the clean specification. The approach is:
//!
//! 1. Generate test inputs (expressions, types)
//! 2. Run them through both the spec model and the Rust implementation
//! 3. Compare results
//!
//! Any mismatch indicates a bug in either the spec or the implementation.

mod test_cases;
mod test_cases_advanced;
mod test_cases_def_eq;
#[cfg(test)]
mod tests;

use crate::spec::Specification;
use crate::{CrossValidationMismatch, CrossValidationSummary};
use clean_kernel::{Environment, Expr, TypeChecker};

/// Cross-validator for spec vs implementation
pub struct CrossValidator<'a> {
    _spec: &'a Specification,
    env: Environment,
}

/// Result of validation
#[derive(Debug)]
pub struct ValidationResult {
    /// Input that was tested
    pub input: String,
    /// Spec result
    pub spec_result: SpecResult,
    /// Implementation result
    pub impl_result: ImplResult,
    /// Do they match?
    pub matches: bool,
}

/// Result from the specification
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum SpecResult {
    /// Type inference succeeded
    TypeInferred(Expr),
    /// Type checking succeeded
    TypeChecked,
    /// Error
    Error(String),
}

/// Result from the implementation
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum ImplResult {
    /// Type inference succeeded
    TypeInferred(Expr),
    /// Type checking succeeded
    TypeChecked,
    /// Error
    Error(String),
}

impl<'a> CrossValidator<'a> {
    /// Create a new validator
    #[must_use]
    pub fn new(spec: &'a Specification) -> Self {
        CrossValidator {
            _spec: spec,
            env: spec.env().clone(),
        }
    }

    /// Generate all cross-validation test cases by combining the three suites.
    fn generate_test_cases(&self) -> Vec<TestCase> {
        let mut cases = self.generate_type_test_cases();
        cases.extend(self.generate_def_eq_test_cases());
        cases.extend(self.generate_advanced_test_cases());
        cases
    }

    /// Run validation on all test cases
    #[must_use]
    pub fn run_validation(&self) -> CrossValidationSummary {
        let test_cases = self.generate_test_cases();
        let mut matching = 0;
        let mut mismatches = Vec::new();

        for case in &test_cases {
            let result = self.validate_case(case);
            if result.matches {
                matching += 1;
            } else {
                mismatches.push(CrossValidationMismatch {
                    input: result.input,
                    spec_result: format!("{:?}", result.spec_result),
                    impl_result: format!("{:?}", result.impl_result),
                });
            }
        }

        CrossValidationSummary {
            total_cases: test_cases.len(),
            matching,
            mismatches,
        }
    }

    /// Validate a single test case
    fn validate_case(&self, case: &TestCase) -> ValidationResult {
        match case {
            TestCase::TypeInfer(src) => {
                let impl_result = self.run_impl_infer(src);
                let spec_result = self.run_spec_infer(src);
                let matches = self.results_match(&spec_result, &impl_result);

                ValidationResult {
                    input: src.clone(),
                    spec_result,
                    impl_result,
                    matches,
                }
            }
            TestCase::TypeCheck(src, ty) => {
                let impl_result = self.run_impl_check(src, ty);
                let spec_result = self.run_spec_check(src, ty);
                let matches = self.results_match(&spec_result, &impl_result);

                ValidationResult {
                    input: format!("{src} : {ty}"),
                    spec_result,
                    impl_result,
                    matches,
                }
            }
            TestCase::ShouldFail(src) => {
                let impl_result = self.run_impl_infer(src);
                let spec_result = self.run_spec_infer(src);

                // Both should fail
                let matches = matches!(&spec_result, SpecResult::Error(_))
                    && matches!(&impl_result, ImplResult::Error(_));

                ValidationResult {
                    input: src.clone(),
                    spec_result,
                    impl_result,
                    matches,
                }
            }
            TestCase::DefEq(src1, src2) => {
                let result = self.run_def_eq_check(src1, src2, true);
                ValidationResult {
                    input: format!("{src1} ≡ {src2}"),
                    spec_result: if result {
                        SpecResult::TypeChecked
                    } else {
                        SpecResult::Error("not def eq".to_string())
                    },
                    impl_result: if result {
                        ImplResult::TypeChecked
                    } else {
                        ImplResult::Error("not def eq".to_string())
                    },
                    matches: result,
                }
            }
            TestCase::NotDefEq(src1, src2) => {
                let result = self.run_def_eq_check(src1, src2, false);
                ValidationResult {
                    input: format!("{src1} ≢ {src2}"),
                    spec_result: if result {
                        SpecResult::TypeChecked
                    } else {
                        SpecResult::Error("unexpectedly def eq".to_string())
                    },
                    impl_result: if result {
                        ImplResult::TypeChecked
                    } else {
                        ImplResult::Error("unexpectedly def eq".to_string())
                    },
                    matches: result,
                }
            }
        }
    }

    /// Check definitional equality of two expressions
    fn run_def_eq_check(&self, src1: &str, src2: &str, expect_equal: bool) -> bool {
        use clean_elab::ElabCtx;
        use clean_parser::parse_expr;

        // Parse both expressions
        let Ok(surface1) = parse_expr(src1) else {
            return false;
        };
        let Ok(surface2) = parse_expr(src2) else {
            return false;
        };

        // Use SEPARATE elaboration contexts - de Bruijn indices should make
        // alpha-equivalent expressions structurally identical
        let mut ctx1 = ElabCtx::new(&self.env);
        let Ok(expr1) = ctx1.elaborate(&surface1) else {
            return false;
        };
        let mut ctx2 = ElabCtx::new(&self.env);
        let Ok(expr2) = ctx2.elaborate(&surface2) else {
            return false;
        };

        // Check definitional equality
        // Note: Both expressions should be closed (no free variables) for simple test cases
        let tc = TypeChecker::with_mode(&self.env, self.env.mode());

        // First reduce both to WHNF to see what we're comparing
        let whnf1 = tc.whnf(&expr1);
        let whnf2 = tc.whnf(&expr2);

        // Debug output for failing cases
        #[cfg(test)]
        {
            if expect_equal && !tc.is_def_eq(&whnf1, &whnf2) {
                eprintln!("DEBUG: {src1} vs {src2}");
                eprintln!("  expr1 = {expr1:?}");
                eprintln!("  expr2 = {expr2:?}");
                eprintln!("  whnf1 = {whnf1:?}");
                eprintln!("  whnf2 = {whnf2:?}");
            }
        }

        let is_eq = tc.is_def_eq(&whnf1, &whnf2);

        if expect_equal {
            is_eq
        } else {
            !is_eq
        }
    }

    /// Run type inference on the implementation
    fn run_impl_infer(&self, src: &str) -> ImplResult {
        use clean_elab::ElabCtx;
        use clean_parser::parse_expr;

        // Parse
        let surface = match parse_expr(src) {
            Ok(s) => s,
            Err(e) => return ImplResult::Error(format!("Parse error: {e}")),
        };

        // Elaborate
        let mut ctx = ElabCtx::new(&self.env);
        let expr = match ctx.elaborate(&surface) {
            Ok(e) => e,
            Err(e) => return ImplResult::Error(format!("Elaboration error: {e}")),
        };

        // Type check
        let tc = TypeChecker::with_mode(&self.env, self.env.mode());
        match tc.infer_type(&expr) {
            Ok(ty) => ImplResult::TypeInferred(ty),
            Err(e) => ImplResult::Error(format!("Type error: {e:?}")),
        }
    }

    /// Run type checking on the implementation
    fn run_impl_check(&self, src: &str, ty_src: &str) -> ImplResult {
        use clean_elab::ElabCtx;
        use clean_parser::parse_expr;

        // Parse expression
        let surface = match parse_expr(src) {
            Ok(s) => s,
            Err(e) => return ImplResult::Error(format!("Parse error (expr): {e}")),
        };

        // Parse type
        let ty_surface = match parse_expr(ty_src) {
            Ok(s) => s,
            Err(e) => return ImplResult::Error(format!("Parse error (type): {e}")),
        };

        // Elaborate both
        let mut ctx = ElabCtx::new(&self.env);
        let expr = match ctx.elaborate(&surface) {
            Ok(e) => e,
            Err(e) => return ImplResult::Error(format!("Elaboration error (expr): {e}")),
        };

        let mut ctx = ElabCtx::new(&self.env);
        let expected_ty = match ctx.elaborate(&ty_surface) {
            Ok(e) => e,
            Err(e) => return ImplResult::Error(format!("Elaboration error (type): {e}")),
        };

        // Type check
        let tc = TypeChecker::with_mode(&self.env, self.env.mode());
        match tc.infer_type(&expr) {
            Ok(actual_ty) => {
                if tc.is_def_eq(&actual_ty, &expected_ty) {
                    ImplResult::TypeChecked
                } else {
                    ImplResult::Error(format!(
                        "Type mismatch: expected {expected_ty:?}, got {actual_ty:?}"
                    ))
                }
            }
            Err(e) => ImplResult::Error(format!("Type error: {e:?}")),
        }
    }

    /// Run type inference on the specification via cert-verified path.
    ///
    /// Unlike `run_impl_infer` (release-mode fast path with no cert), this
    /// infers the type with certificate generation and then cross-validates
    /// through the micro-checker. A micro-checker disagreement produces a
    /// real mismatch instead of the previous tautological pass-through.
    fn run_spec_infer(&self, src: &str) -> SpecResult {
        use clean_elab::ElabCtx;
        use clean_kernel::micro::cross_validate_with_micro;
        use clean_parser::parse_expr;

        // Parse
        let surface = match parse_expr(src) {
            Ok(s) => s,
            Err(e) => return SpecResult::Error(format!("Parse error: {e}")),
        };

        // Elaborate
        let mut ctx = ElabCtx::new(&self.env);
        let expr = match ctx.elaborate(&surface) {
            Ok(e) => e,
            Err(e) => return SpecResult::Error(format!("Elaboration error: {e}")),
        };

        // Type infer WITH certificate
        let tc = TypeChecker::with_mode(&self.env, self.env.mode());
        match tc.infer_type_with_cert(&expr) {
            Ok((ty, cert)) => match cross_validate_with_micro(&expr, &ty, &cert) {
                Ok(_) => SpecResult::TypeInferred(ty),
                Err(e) => SpecResult::Error(format!("Micro-checker disagreement: {e:?}")),
            },
            Err(e) => SpecResult::Error(format!("Type error: {e:?}")),
        }
    }

    /// Run type checking on the specification via cert-verified path.
    ///
    /// Infers the type with certificate, cross-validates through the
    /// micro-checker, then checks the inferred type matches the expected type.
    fn run_spec_check(&self, src: &str, ty: &str) -> SpecResult {
        use clean_elab::ElabCtx;
        use clean_kernel::micro::cross_validate_with_micro;
        use clean_parser::parse_expr;

        // Parse expression
        let surface = match parse_expr(src) {
            Ok(s) => s,
            Err(e) => return SpecResult::Error(format!("Parse error (expr): {e}")),
        };

        // Parse type
        let ty_surface = match parse_expr(ty) {
            Ok(s) => s,
            Err(e) => return SpecResult::Error(format!("Parse error (type): {e}")),
        };

        // Elaborate both
        let mut ctx = ElabCtx::new(&self.env);
        let expr = match ctx.elaborate(&surface) {
            Ok(e) => e,
            Err(e) => return SpecResult::Error(format!("Elaboration error (expr): {e}")),
        };

        let mut ctx = ElabCtx::new(&self.env);
        let expected_ty = match ctx.elaborate(&ty_surface) {
            Ok(e) => e,
            Err(e) => return SpecResult::Error(format!("Elaboration error (type): {e}")),
        };

        // Type infer WITH certificate
        let tc = TypeChecker::with_mode(&self.env, self.env.mode());
        match tc.infer_type_with_cert(&expr) {
            Ok((actual_ty, cert)) => match cross_validate_with_micro(&expr, &actual_ty, &cert) {
                Ok(_) => {
                    if tc.is_def_eq(&actual_ty, &expected_ty) {
                        SpecResult::TypeChecked
                    } else {
                        SpecResult::Error(format!(
                            "Type mismatch: expected {expected_ty:?}, got {actual_ty:?}"
                        ))
                    }
                }
                Err(e) => SpecResult::Error(format!("Micro-checker disagreement: {e:?}")),
            },
            Err(e) => SpecResult::Error(format!("Type error: {e:?}")),
        }
    }

    /// Check if spec and impl results match
    fn results_match(&self, spec: &SpecResult, impl_: &ImplResult) -> bool {
        match (spec, impl_) {
            (SpecResult::TypeInferred(spec_ty), ImplResult::TypeInferred(impl_ty)) => {
                let tc = TypeChecker::with_mode(&self.env, self.env.mode());
                tc.is_def_eq(spec_ty, impl_ty)
            }
            (SpecResult::TypeChecked, ImplResult::TypeChecked)
            | (SpecResult::Error(_), ImplResult::Error(_)) => true,
            _ => false,
        }
    }
}

/// A test case for cross-validation
#[derive(Debug, Clone)]
enum TestCase {
    /// Infer the type of an expression
    TypeInfer(String),
    /// Check that an expression has a given type
    TypeCheck(String, String),
    /// This expression should fail type checking
    ShouldFail(String),
    /// Check that two expressions are definitionally equal
    DefEq(String, String),
    /// Check that two expressions are NOT definitionally equal
    NotDefEq(String, String),
}
