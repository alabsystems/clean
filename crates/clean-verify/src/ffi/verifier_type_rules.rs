// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type-level verification rules for FFI boundary safety.
//!
//! These functions recursively walk FFI type references and named type
//! declarations, emitting rule violations for layout, lifetime, thread-safety,
//! and unwind concerns.

use std::collections::{BTreeSet, HashSet};

use super::helpers::{
    abi_can_unwind, is_ffi_primitive_name, is_known_rust_owned_type, is_thread_affine_rust_type,
};
use super::types::{FfiBoundarySpec, FfiFunctionContract, FfiTypeDeclKind, FfiTypeRef};
use super::verifier::{FfiRule, FfiViolation, FfiViolationSeverity};

pub(crate) fn push_violation(
    violations: &mut BTreeSet<FfiViolation>,
    rule: FfiRule,
    severity: FfiViolationSeverity,
    description: impl Into<String>,
    location: impl Into<String>,
) {
    violations.insert(FfiViolation {
        rule,
        severity,
        description: description.into(),
        location: location.into(),
    });
}

pub(crate) fn apply_type_rules(
    spec: &FfiBoundarySpec,
    ty: &FfiTypeRef,
    function: &FfiFunctionContract,
    location: &str,
    visited: &mut HashSet<String>,
    violations: &mut BTreeSet<FfiViolation>,
) {
    match ty {
        FfiTypeRef::Primitive(_) | FfiTypeRef::Unit => {}
        FfiTypeRef::Unsupported(rendered) => {
            if is_thread_affine_rust_type(rendered) {
                push_violation(
                    violations,
                    FfiRule::ThreadSafety,
                    FfiViolationSeverity::Error,
                    format!(
                        "type `{rendered}` is thread-affine and cannot be safely shared through an extern boundary"
                    ),
                    location,
                );
            }
            push_violation(
                violations,
                FfiRule::SizeAlignment,
                FfiViolationSeverity::Error,
                format!(
                    "type `{rendered}` uses unsupported Rust-only syntax, so its layout and alignment cannot be verified"
                ),
                location,
            );
        }
        FfiTypeRef::RawPointer { inner, .. } | FfiTypeRef::Array { inner, .. } => {
            apply_type_rules(spec, inner, function, location, visited, violations);
        }
        FfiTypeRef::Reference { .. } => {
            push_violation(
                violations,
                FfiRule::LifetimeEscape,
                FfiViolationSeverity::Error,
                format!(
                    "Rust reference `{}` may let a borrow escape across the extern boundary",
                    ty.display_name()
                ),
                location,
            );
        }
        FfiTypeRef::Slice(inner) => {
            push_violation(
                violations,
                FfiRule::SizeAlignment,
                FfiViolationSeverity::Error,
                format!(
                    "slice type `{}` carries Rust fat-pointer metadata and has no portable C layout",
                    ty.display_name()
                ),
                location,
            );
            apply_type_rules(spec, inner, function, location, visited, violations);
        }
        FfiTypeRef::Tuple(items) => {
            if !items.is_empty() {
                push_violation(
                    violations,
                    FfiRule::SizeAlignment,
                    FfiViolationSeverity::Error,
                    format!(
                        "tuple type `{}` does not provide a stable C ABI layout",
                        ty.display_name()
                    ),
                    location,
                );
            }
            for item in items {
                apply_type_rules(spec, item, function, location, visited, violations);
            }
        }
        FfiTypeRef::BareFunction {
            abi,
            inputs,
            output,
        } => {
            apply_bare_fn_rules(
                ty, abi, inputs, output, spec, function, location, visited, violations,
            );
        }
        FfiTypeRef::Named(name) => {
            apply_named_type_rules(spec, name, function, location, visited, violations);
        }
    }
}

fn apply_bare_fn_rules(
    ty: &FfiTypeRef,
    abi: &str,
    inputs: &[FfiTypeRef],
    output: &Option<Box<FfiTypeRef>>,
    spec: &FfiBoundarySpec,
    function: &FfiFunctionContract,
    location: &str,
    visited: &mut HashSet<String>,
    violations: &mut BTreeSet<FfiViolation>,
) {
    if abi == "Rust" || abi_can_unwind(abi) {
        push_violation(
            violations,
            FfiRule::UnwindSafety,
            FfiViolationSeverity::Error,
            format!(
                "callback type `{}` must use a non-unwinding foreign ABI",
                ty.display_name()
            ),
            location,
        );
    }
    push_violation(
        violations,
        FfiRule::ThreadSafety,
        FfiViolationSeverity::Warning,
        format!(
            "callback type `{}` may be invoked from foreign threads without an explicit thread-affinity contract",
            ty.display_name()
        ),
        location,
    );
    for input in inputs {
        apply_type_rules(spec, input, function, location, visited, violations);
    }
    if let Some(output) = output {
        apply_type_rules(spec, output, function, location, visited, violations);
    }
}

pub(crate) fn apply_named_type_rules(
    spec: &FfiBoundarySpec,
    name: &str,
    function: &FfiFunctionContract,
    location: &str,
    visited: &mut HashSet<String>,
    violations: &mut BTreeSet<FfiViolation>,
) {
    if is_ffi_primitive_name(name) {
        return;
    }
    if is_known_rust_owned_type(name) {
        push_violation(
            violations,
            FfiRule::SizeAlignment,
            FfiViolationSeverity::Error,
            format!("owned Rust type `{name}` does not provide a stable C ABI layout"),
            location,
        );
        if is_thread_affine_rust_type(name) {
            push_violation(
                violations,
                FfiRule::ThreadSafety,
                FfiViolationSeverity::Error,
                format!(
                    "owned Rust type `{name}` is thread-affine and cannot cross the extern boundary safely"
                ),
                location,
            );
        }
        return;
    }

    let Some(decl) = spec.resolve_type(name) else {
        if is_thread_affine_rust_type(name) {
            push_violation(
                violations,
                FfiRule::ThreadSafety,
                FfiViolationSeverity::Error,
                format!(
                    "type `{name}` is thread-affine and cannot be trusted across the extern boundary"
                ),
                location,
            );
        }
        push_violation(
            violations,
            FfiRule::SizeAlignment,
            FfiViolationSeverity::Error,
            format!(
                "type `{name}` has no local FFI declaration, so its layout and alignment cannot be verified"
            ),
            location,
        );
        return;
    };

    if !visited.insert(decl.name.clone()) {
        return;
    }

    if decl.is_generic {
        push_violation(
            violations,
            FfiRule::SizeAlignment,
            FfiViolationSeverity::Error,
            format!(
                "generic type `{}` cannot be verified for a stable FFI layout",
                decl.name
            ),
            location,
        );
        visited.remove(&decl.name);
        return;
    }

    match &decl.kind {
        FfiTypeDeclKind::Struct { fields } | FfiTypeDeclKind::Union { fields } => {
            if !decl.repr_c {
                push_violation(
                    violations,
                    FfiRule::SizeAlignment,
                    FfiViolationSeverity::Error,
                    format!(
                        "type `{}` is missing #[repr(C)], so its size/alignment is not stable for FFI",
                        decl.name
                    ),
                    location,
                );
            }
            for field in fields {
                apply_type_rules(spec, &field.ty, function, location, visited, violations);
            }
        }
        FfiTypeDeclKind::Enum { variants } => {
            if !decl.repr_c {
                push_violation(
                    violations,
                    FfiRule::SizeAlignment,
                    FfiViolationSeverity::Error,
                    format!(
                        "type `{}` is missing #[repr(C)], so its size/alignment is not stable for FFI",
                        decl.name
                    ),
                    location,
                );
            }
            if variants.iter().any(|variant| !variant.fields.is_empty()) {
                push_violation(
                    violations,
                    FfiRule::SizeAlignment,
                    FfiViolationSeverity::Error,
                    format!(
                        "enum `{}` carries data and does not provide a portable C ABI layout",
                        decl.name
                    ),
                    location,
                );
            }
            for variant in variants {
                for field in &variant.fields {
                    apply_type_rules(spec, &field.ty, function, location, visited, violations);
                }
            }
        }
        FfiTypeDeclKind::Alias { target } => {
            apply_type_rules(spec, target, function, location, visited, violations);
        }
    }

    visited.remove(&decl.name);
}
