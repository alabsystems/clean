// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structural FFI boundary checker: derives safety obligations from extern
//! declarations and validates that required contracts are present.

use std::collections::{BTreeSet, HashSet};

use super::error::FfiBoundaryViolation;
use super::helpers::{abi_can_unwind, is_ffi_primitive_name, is_known_rust_owned_type};
use super::types::{
    FfiBoundarySpec, FfiFunctionContract, FfiSafetyCheck, FfiTypeDecl, FfiTypeDeclKind, FfiTypeRef,
    FfiValueTarget,
};

/// Checker for extern function declarations.
#[derive(Debug, Default, Clone, Copy)]
pub struct FfiBoundaryChecker;

impl FfiBoundaryChecker {
    /// Create a checker.
    #[must_use]
    pub fn new() -> Self {
        Self
    }

    /// Derive the safety obligations implied by the extern declarations.
    #[must_use]
    pub fn required_checks(&self, spec: &FfiBoundarySpec) -> Vec<FfiSafetyCheck> {
        let mut checks = BTreeSet::new();
        for block in &spec.extern_blocks {
            for function in &block.functions {
                self.collect_function_checks(spec, function, &mut checks);
            }
        }
        checks.into_iter().collect()
    }

    /// Validate that all extern declarations satisfy the FFI boundary rules.
    pub fn validate(&self, spec: &FfiBoundarySpec) -> Result<(), Vec<FfiBoundaryViolation>> {
        let mut violations = BTreeSet::new();
        for block in &spec.extern_blocks {
            for function in &block.functions {
                self.validate_function(spec, function, &mut violations);
            }
        }

        if violations.is_empty() {
            Ok(())
        } else {
            Err(violations.into_iter().collect())
        }
    }

    fn collect_function_checks(
        &self,
        spec: &FfiBoundarySpec,
        function: &FfiFunctionContract,
        checks: &mut BTreeSet<FfiSafetyCheck>,
    ) {
        checks.insert(FfiSafetyCheck::NoUnwinding {
            function: function.name.clone(),
        });

        for param in &function.inputs {
            self.collect_type_checks(
                spec,
                &param.ty,
                function,
                Some(FfiValueTarget::Param(param.name.clone())),
                &mut HashSet::new(),
                checks,
            );
        }

        if let Some(output) = &function.output {
            self.collect_type_checks(
                spec,
                output,
                function,
                Some(FfiValueTarget::ReturnValue),
                &mut HashSet::new(),
                checks,
            );
        }
    }

    fn collect_type_checks(
        &self,
        spec: &FfiBoundarySpec,
        ty: &FfiTypeRef,
        function: &FfiFunctionContract,
        target: Option<FfiValueTarget>,
        visited: &mut HashSet<String>,
        checks: &mut BTreeSet<FfiSafetyCheck>,
    ) {
        match ty {
            FfiTypeRef::Primitive(_) | FfiTypeRef::Unit | FfiTypeRef::Unsupported(_) => {}
            FfiTypeRef::RawPointer { inner, .. } => {
                if let Some(target) = target.clone() {
                    checks.insert(FfiSafetyCheck::PointerValidity {
                        function: function.name.clone(),
                        target,
                        non_null: true,
                        aligned: true,
                        initialized: true,
                    });
                }
                self.collect_type_checks(spec, inner, function, None, visited, checks);
            }
            FfiTypeRef::Reference { inner, .. } => {
                if let Some(target) = target.clone() {
                    checks.insert(FfiSafetyCheck::Lifetime {
                        function: function.name.clone(),
                        target,
                        no_dangling: true,
                    });
                }
                self.collect_type_checks(spec, inner, function, None, visited, checks);
            }
            FfiTypeRef::Array { inner, .. } | FfiTypeRef::Slice(inner) => {
                self.collect_type_checks(spec, inner, function, None, visited, checks);
            }
            FfiTypeRef::Tuple(items) => {
                for item in items {
                    self.collect_type_checks(spec, item, function, None, visited, checks);
                }
            }
            FfiTypeRef::BareFunction { inputs, output, .. } => {
                for input in inputs {
                    self.collect_type_checks(spec, input, function, None, visited, checks);
                }
                if let Some(output) = output {
                    self.collect_type_checks(spec, output, function, None, visited, checks);
                }
            }
            FfiTypeRef::Named(name) => {
                self.collect_named_type_checks(spec, name, function, visited, checks);
            }
        }
    }

    fn collect_named_type_checks(
        &self,
        spec: &FfiBoundarySpec,
        name: &str,
        function: &FfiFunctionContract,
        visited: &mut HashSet<String>,
        checks: &mut BTreeSet<FfiSafetyCheck>,
    ) {
        let Some(decl) = spec.resolve_type(name) else {
            return;
        };

        if !visited.insert(decl.name.clone()) {
            return;
        }

        self.collect_decl_checks(spec, decl, function, visited, checks);
        visited.remove(&decl.name);
    }

    fn collect_decl_checks(
        &self,
        spec: &FfiBoundarySpec,
        decl: &FfiTypeDecl,
        function: &FfiFunctionContract,
        visited: &mut HashSet<String>,
        checks: &mut BTreeSet<FfiSafetyCheck>,
    ) {
        match &decl.kind {
            FfiTypeDeclKind::Struct { fields } | FfiTypeDeclKind::Union { fields } => {
                checks.insert(FfiSafetyCheck::TypeLayoutCompatibility {
                    function: function.name.clone(),
                    ty: decl.name.clone(),
                    requires_repr_c: true,
                });
                for field in fields {
                    self.collect_type_checks(spec, &field.ty, function, None, visited, checks);
                }
            }
            FfiTypeDeclKind::Enum { variants } => {
                checks.insert(FfiSafetyCheck::TypeLayoutCompatibility {
                    function: function.name.clone(),
                    ty: decl.name.clone(),
                    requires_repr_c: true,
                });
                for variant in variants {
                    for field in &variant.fields {
                        self.collect_type_checks(spec, &field.ty, function, None, visited, checks);
                    }
                }
            }
            FfiTypeDeclKind::Alias { target } => {
                self.collect_type_checks(spec, target, function, None, visited, checks);
            }
        }
    }

    fn validate_function(
        &self,
        spec: &FfiBoundarySpec,
        function: &FfiFunctionContract,
        violations: &mut BTreeSet<FfiBoundaryViolation>,
    ) {
        if abi_can_unwind(&function.abi) {
            violations.insert(FfiBoundaryViolation::UnwindAbi {
                function: function.name.clone(),
                abi: function.abi.clone(),
            });
        }

        if !function.has_no_unwind_postcondition() {
            violations.insert(FfiBoundaryViolation::MissingNoUnwind {
                function: function.name.clone(),
            });
        }

        if function.variadic {
            violations.insert(FfiBoundaryViolation::NonFfiSafeType {
                function: function.name.clone(),
                position: "signature".to_string(),
                ty: "variadic arguments".to_string(),
                reason: "variadic extern functions are not supported by this verifier".to_string(),
            });
        }

        for param in &function.inputs {
            if matches!(param.ty, FfiTypeRef::RawPointer { .. })
                && !function.has_pointer_precondition(&param.name)
            {
                violations.insert(FfiBoundaryViolation::MissingPointerPrecondition {
                    function: function.name.clone(),
                    param: param.name.clone(),
                });
            }

            self.validate_type(
                spec,
                &param.ty,
                function,
                &format!("parameter `{}`", param.name),
                &mut HashSet::new(),
                violations,
            );
        }

        if let Some(output) = &function.output {
            if matches!(output, FfiTypeRef::RawPointer { .. })
                && !function.has_pointer_postcondition()
            {
                violations.insert(FfiBoundaryViolation::MissingPointerPostcondition {
                    function: function.name.clone(),
                });
            }

            self.validate_type(
                spec,
                output,
                function,
                "return type",
                &mut HashSet::new(),
                violations,
            );
        }
    }

    fn validate_type(
        &self,
        spec: &FfiBoundarySpec,
        ty: &FfiTypeRef,
        function: &FfiFunctionContract,
        position: &str,
        visited: &mut HashSet<String>,
        violations: &mut BTreeSet<FfiBoundaryViolation>,
    ) {
        match ty {
            FfiTypeRef::Primitive(_) | FfiTypeRef::Unit => {}
            FfiTypeRef::Unsupported(rendered) => {
                violations.insert(FfiBoundaryViolation::NonFfiSafeType {
                    function: function.name.clone(),
                    position: position.to_string(),
                    ty: rendered.clone(),
                    reason: "Rust-specific or unsupported type syntax is not FFI-safe".to_string(),
                });
            }
            FfiTypeRef::RawPointer { inner, .. } | FfiTypeRef::Array { inner, .. } => {
                self.validate_type(spec, inner, function, position, visited, violations);
            }
            FfiTypeRef::Reference { .. } => {
                violations.insert(FfiBoundaryViolation::ReferenceAcrossFfi {
                    function: function.name.clone(),
                    position: position.to_string(),
                    ty: ty.display_name(),
                });
            }
            FfiTypeRef::Slice(_) => {
                violations.insert(FfiBoundaryViolation::NonFfiSafeType {
                    function: function.name.clone(),
                    position: position.to_string(),
                    ty: ty.display_name(),
                    reason: "slices use Rust fat-pointer metadata across FFI".to_string(),
                });
            }
            FfiTypeRef::Tuple(items) => {
                if items.is_empty() {
                    return;
                }
                violations.insert(FfiBoundaryViolation::NonFfiSafeType {
                    function: function.name.clone(),
                    position: position.to_string(),
                    ty: ty.display_name(),
                    reason: "tuples do not provide a portable C ABI layout".to_string(),
                });
            }
            FfiTypeRef::BareFunction {
                abi,
                inputs,
                output,
            } => {
                if abi == "Rust" || abi_can_unwind(abi) {
                    violations.insert(FfiBoundaryViolation::NonFfiSafeType {
                        function: function.name.clone(),
                        position: position.to_string(),
                        ty: ty.display_name(),
                        reason:
                            "function pointers crossing FFI must use a non-unwinding extern ABI"
                                .to_string(),
                    });
                }
                for input in inputs {
                    self.validate_type(spec, input, function, position, visited, violations);
                }
                if let Some(output) = output {
                    self.validate_type(spec, output, function, position, visited, violations);
                }
            }
            FfiTypeRef::Named(name) => {
                self.validate_named_type(spec, name, ty, function, position, visited, violations);
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn validate_named_type(
        &self,
        spec: &FfiBoundarySpec,
        name: &str,
        _ty: &FfiTypeRef,
        function: &FfiFunctionContract,
        position: &str,
        visited: &mut HashSet<String>,
        violations: &mut BTreeSet<FfiBoundaryViolation>,
    ) {
        if is_ffi_primitive_name(name) {
            return;
        }
        if is_known_rust_owned_type(name) {
            violations.insert(FfiBoundaryViolation::NonFfiSafeType {
                function: function.name.clone(),
                position: position.to_string(),
                ty: name.to_string(),
                reason: "owned Rust container types do not have a stable C layout".to_string(),
            });
            return;
        }

        let Some(decl) = spec.resolve_type(name) else {
            violations.insert(FfiBoundaryViolation::UnknownType {
                function: function.name.clone(),
                position: position.to_string(),
                ty: name.to_string(),
            });
            return;
        };

        if !visited.insert(decl.name.clone()) {
            return;
        }

        if decl.is_generic {
            violations.insert(FfiBoundaryViolation::NonFfiSafeType {
                function: function.name.clone(),
                position: position.to_string(),
                ty: decl.name.clone(),
                reason: "generic types cannot be proven FFI-safe without monomorphized layout"
                    .to_string(),
            });
            visited.remove(&decl.name);
            return;
        }

        match &decl.kind {
            FfiTypeDeclKind::Struct { fields } | FfiTypeDeclKind::Union { fields } => {
                if !decl.repr_c {
                    violations.insert(FfiBoundaryViolation::MissingReprC {
                        function: function.name.clone(),
                        position: position.to_string(),
                        ty: decl.name.clone(),
                    });
                }
                for field in fields {
                    self.validate_type(spec, &field.ty, function, position, visited, violations);
                }
            }
            FfiTypeDeclKind::Enum { variants } => {
                if !decl.repr_c {
                    violations.insert(FfiBoundaryViolation::MissingReprC {
                        function: function.name.clone(),
                        position: position.to_string(),
                        ty: decl.name.clone(),
                    });
                }
                if variants.iter().any(|variant| !variant.fields.is_empty()) {
                    violations.insert(FfiBoundaryViolation::NonFfiSafeType {
                        function: function.name.clone(),
                        position: position.to_string(),
                        ty: decl.name.clone(),
                        reason: "data-carrying enums do not provide a portable C ABI layout"
                            .to_string(),
                    });
                }
                for variant in variants {
                    for field in &variant.fields {
                        self.validate_type(
                            spec, &field.ty, function, position, visited, violations,
                        );
                    }
                }
            }
            FfiTypeDeclKind::Alias { target } => {
                self.validate_type(spec, target, function, position, visited, violations);
            }
        }

        visited.remove(&decl.name);
    }
}
