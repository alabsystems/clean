// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rule-based FFI verifier that applies focused verification rules to parsed
//! extern contracts.

use std::collections::{BTreeSet, HashSet};

use super::helpers::abi_can_unwind;
use super::types::{FfiBoundarySpec, FfiFunctionContract, FfiParam, FfiTypeRef};
use super::verifier_type_rules::{apply_type_rules, push_violation};

/// Focused FFI verification rules applied to parsed extern contracts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FfiRule {
    /// Raw pointers must be explicitly constrained to reject null values.
    NullPointerCheck,
    /// Boundary types must have a verifiable layout and aligned access contract.
    SizeAlignment,
    /// Borrowed Rust values must not escape across the foreign boundary.
    LifetimeEscape,
    /// Calls and callbacks must not unwind across the boundary.
    UnwindSafety,
    /// Signatures must not depend on thread-affine or thread-opaque behavior.
    ThreadSafety,
}

/// Severity assigned to an [`FfiViolation`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FfiViolationSeverity {
    /// A soundness issue that should reject the boundary.
    Error,
    /// A conservative warning where the current spec lacks enough thread metadata.
    Warning,
}

/// Structured violation emitted by [`FfiVerifier`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct FfiViolation {
    /// Rule that produced the violation.
    pub rule: FfiRule,
    /// Severity of the violation.
    pub severity: FfiViolationSeverity,
    /// Human-readable explanation of the issue.
    pub description: String,
    /// Logical location within the extern declaration.
    pub location: String,
}

/// Rule-based verifier for [`FfiBoundarySpec`].
#[derive(Debug, Default, Clone, Copy)]
pub struct FfiVerifier;

impl FfiVerifier {
    /// Create a verifier.
    #[must_use]
    pub fn new() -> Self {
        Self
    }

    /// Apply all focused verification rules to the parsed FFI boundary spec.
    #[must_use]
    pub fn apply_rules(&self, spec: &FfiBoundarySpec) -> Vec<FfiViolation> {
        let mut violations = BTreeSet::new();

        for block in &spec.extern_blocks {
            for function in &block.functions {
                self.apply_function_rules(spec, function, &mut violations);
            }
        }

        violations.into_iter().collect()
    }

    fn apply_function_rules(
        &self,
        spec: &FfiBoundarySpec,
        function: &FfiFunctionContract,
        violations: &mut BTreeSet<FfiViolation>,
    ) {
        self.apply_unwind_rule(function, violations);

        for param in &function.inputs {
            let location = format!("extern fn `{}` parameter `{}`", function.name, param.name);
            self.apply_pointer_rules_for_param(function, param, &location, violations);
            apply_type_rules(
                spec,
                &param.ty,
                function,
                &location,
                &mut HashSet::new(),
                violations,
            );
        }

        if let Some(output) = &function.output {
            let location = format!("extern fn `{}` return value", function.name);
            self.apply_pointer_rules_for_output(function, output, &location, violations);
            apply_type_rules(
                spec,
                output,
                function,
                &location,
                &mut HashSet::new(),
                violations,
            );
        }
    }

    fn apply_pointer_rules_for_param(
        &self,
        function: &FfiFunctionContract,
        param: &FfiParam,
        location: &str,
        violations: &mut BTreeSet<FfiViolation>,
    ) {
        if !matches!(param.ty, FfiTypeRef::RawPointer { .. }) {
            return;
        }

        match function.pointer_precondition_flags(&param.name) {
            Some((true, aligned, _initialized)) => {
                if !aligned {
                    push_violation(
                        violations,
                        FfiRule::SizeAlignment,
                        FfiViolationSeverity::Error,
                        format!(
                            "raw pointer parameter `{}` must guarantee aligned memory at the FFI boundary",
                            param.name
                        ),
                        location,
                    );
                }
            }
            Some((false, aligned, _initialized)) => {
                push_violation(
                    violations,
                    FfiRule::NullPointerCheck,
                    FfiViolationSeverity::Error,
                    format!(
                        "raw pointer parameter `{}` must have an explicit non-null contract",
                        param.name
                    ),
                    location,
                );
                if !aligned {
                    push_violation(
                        violations,
                        FfiRule::SizeAlignment,
                        FfiViolationSeverity::Error,
                        format!(
                            "raw pointer parameter `{}` must guarantee aligned memory at the FFI boundary",
                            param.name
                        ),
                        location,
                    );
                }
            }
            None => {
                push_violation(
                    violations,
                    FfiRule::NullPointerCheck,
                    FfiViolationSeverity::Error,
                    format!(
                        "raw pointer parameter `{}` is missing an explicit non-null contract",
                        param.name
                    ),
                    location,
                );
                push_violation(
                    violations,
                    FfiRule::SizeAlignment,
                    FfiViolationSeverity::Error,
                    format!(
                        "raw pointer parameter `{}` is missing an explicit alignment contract",
                        param.name
                    ),
                    location,
                );
            }
        }
    }

    fn apply_pointer_rules_for_output(
        &self,
        function: &FfiFunctionContract,
        output: &FfiTypeRef,
        location: &str,
        violations: &mut BTreeSet<FfiViolation>,
    ) {
        if !matches!(output, FfiTypeRef::RawPointer { .. }) {
            return;
        }

        match function.pointer_postcondition_flags() {
            Some((true, aligned, _initialized)) => {
                if !aligned {
                    push_violation(
                        violations,
                        FfiRule::SizeAlignment,
                        FfiViolationSeverity::Error,
                        "raw pointer return values must guarantee aligned memory before Rust uses them",
                        location,
                    );
                }
            }
            Some((false, aligned, _initialized)) => {
                push_violation(
                    violations,
                    FfiRule::NullPointerCheck,
                    FfiViolationSeverity::Error,
                    "raw pointer return values must have an explicit non-null contract",
                    location,
                );
                if !aligned {
                    push_violation(
                        violations,
                        FfiRule::SizeAlignment,
                        FfiViolationSeverity::Error,
                        "raw pointer return values must guarantee aligned memory before Rust uses them",
                        location,
                    );
                }
            }
            None => {
                push_violation(
                    violations,
                    FfiRule::NullPointerCheck,
                    FfiViolationSeverity::Error,
                    "raw pointer return values are missing an explicit non-null contract",
                    location,
                );
                push_violation(
                    violations,
                    FfiRule::SizeAlignment,
                    FfiViolationSeverity::Error,
                    "raw pointer return values are missing an explicit alignment contract",
                    location,
                );
            }
        }
    }

    fn apply_unwind_rule(
        &self,
        function: &FfiFunctionContract,
        violations: &mut BTreeSet<FfiViolation>,
    ) {
        let location = format!("extern fn `{}`", function.name);
        if abi_can_unwind(&function.abi) {
            push_violation(
                violations,
                FfiRule::UnwindSafety,
                FfiViolationSeverity::Error,
                format!("ABI `{}` may unwind across the FFI boundary", function.abi),
                &location,
            );
        }

        if !function.has_no_unwind_postcondition() {
            push_violation(
                violations,
                FfiRule::UnwindSafety,
                FfiViolationSeverity::Error,
                "extern function is missing an explicit no-unwind postcondition",
                &location,
            );
        }
    }
}
