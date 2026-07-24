// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! FFI Bridge — resolves `@[extern]` and `@[implementedBy]` at compile time.
//!
//! When the compiler encounters a declaration with `@[extern "c_func"]`, it
//! needs to emit a C `extern` forward declaration instead of generating code.
//! When it encounters `@[implementedBy realImpl]`, it needs to redirect
//! function calls from the opaque axiom to the real implementation.
//!
//! This module provides:
//! - [`ExternDecl`]: A resolved extern function with its C signature
//! - [`ImplementedByMap`]: Lookup table from axiom names to implementations
//! - [`FfiBridge`]: Unified facade for resolving both extern and implementedBy
//!
//! # Lean 4 Reference
//!
//! Lean 4's `@[extern]` generates entries in the `ExternAttrData` persistent
//! extension (lean4/src/Lean/Compiler/ExternAttr.lean). The C backend reads
//! these when emitting calls to external functions (EmitC.lean:emitExternCall).
//!
//! `@[implementedBy]` stores a mapping in `ImplementedByAttr` (ImplementedBy.lean).
//! During LCNF compilation, calls to the axiom are replaced with calls to the
//! implementation (LCNF/ReduceAux.lean:reduceMatcher).

use clean_kernel::{Environment, Name};
use std::collections::HashMap;

use crate::ir::IRType;
use crate::lcnf::{ExternAttr, Param};
use crate::to_ir::expr_to_ir_type;

/// A resolved extern C function declaration.
///
/// Generated from `@[extern "c_func_name"]` on a Lean declaration.
/// Used by the C emitter to produce `extern` forward declarations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternDecl {
    /// The Lean declaration name (e.g., `IO.Handle.mk`).
    pub lean_name: Name,
    /// The C symbol name (e.g., `clean_io_handle_mk`).
    pub c_name: String,
    /// The backend identifier (e.g., `"c"`, `"all"`).
    pub backend: String,
    /// Parameter types (IR-level).
    pub param_types: Vec<IRType>,
    /// Return type (IR-level).
    pub return_type: IRType,
}

/// Maps axiom/opaque declarations to their `@[implementedBy]` targets.
///
/// At runtime, calls to the axiom are redirected to the implementation.
/// The kernel type-checks against the axiom's type, but the compiler
/// generates code that calls the implementation.
#[derive(Debug, Clone, Default)]
pub struct ImplementedByMap {
    /// axiom_name -> implementation_name
    entries: HashMap<Name, Name>,
}

impl ImplementedByMap {
    /// Create a new empty map.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Build from a kernel Environment's `@[implementedBy]` registry.
    #[must_use]
    pub fn from_env(env: &Environment) -> Self {
        let mut entries = HashMap::new();
        // The kernel Environment stores implemented_by as Name -> Name.
        // We iterate all constants and check if they have implementedBy bindings.
        for constant in env.constants() {
            if let Some(impl_name) = env.get_implemented_by(&constant.name) {
                entries.insert(constant.name.clone(), impl_name.clone());
            }
        }
        Self { entries }
    }

    /// Register a mapping from axiom to implementation.
    pub fn register(&mut self, axiom: Name, implementation: Name) {
        self.entries.insert(axiom, implementation);
    }

    /// Resolve: if `name` has an `@[implementedBy]` target, return it.
    #[must_use]
    pub fn resolve(&self, name: &Name) -> Option<&Name> {
        self.entries.get(name)
    }

    /// Check if a declaration has an `@[implementedBy]` binding.
    #[must_use]
    pub fn has_binding(&self, name: &Name) -> bool {
        self.entries.contains_key(name)
    }

    /// Number of registered bindings.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the map is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Iterate all bindings.
    pub fn iter(&self) -> impl Iterator<Item = (&Name, &Name)> {
        self.entries.iter()
    }
}

/// Unified FFI bridge for resolving extern and implementedBy at compile time.
///
/// Constructed once from the kernel `Environment` and passed through the
/// compiler pipeline. The C emitter consults this to:
/// 1. Emit `extern` forward declarations for `@[extern]` functions
/// 2. Redirect calls from axioms to their `@[implementedBy]` targets
#[derive(Debug, Clone)]
pub struct FfiBridge {
    /// Resolved extern C declarations.
    extern_decls: Vec<ExternDecl>,
    /// Axiom-to-implementation redirects.
    implemented_by: ImplementedByMap,
    /// Quick lookup: Lean name -> index into extern_decls.
    extern_index: HashMap<Name, usize>,
}

impl FfiBridge {
    /// Build an FFI bridge from a kernel Environment.
    ///
    /// Scans all constants for `@[extern]` and `@[implementedBy]` attributes
    /// and resolves them into compiler-ready data structures.
    #[must_use]
    pub fn from_env(env: &Environment) -> Self {
        let implemented_by = ImplementedByMap::from_env(env);
        let mut extern_decls = Vec::new();
        let mut extern_index = HashMap::new();

        for constant in env.constants() {
            if let Some(c_name) = env.get_extern(&constant.name) {
                // Extract parameter types from the constant's type signature.
                let (param_types, return_type) = extract_signature(&constant.type_);
                let idx = extern_decls.len();
                extern_decls.push(ExternDecl {
                    lean_name: constant.name.clone(),
                    c_name: c_name.clone(),
                    backend: "c".to_owned(),
                    param_types,
                    return_type,
                });
                extern_index.insert(constant.name.clone(), idx);
            }
        }

        Self {
            extern_decls,
            implemented_by,
            extern_index,
        }
    }

    /// Build an FFI bridge from LCNF extern declarations directly.
    ///
    /// Used when LCNF declarations are available but the full kernel
    /// Environment is not (e.g., unit tests, standalone compilation).
    pub fn from_lcnf_externs(
        externs: &[(Name, &[Param], &clean_kernel::Expr, &ExternAttr)],
    ) -> Self {
        let mut extern_decls = Vec::new();
        let mut extern_index = HashMap::new();

        for (lean_name, params, return_ty, attr) in externs {
            for entry in &attr.entries {
                if is_c_backend(&entry.backend) {
                    let param_types: Vec<IRType> = params
                        .iter()
                        .map(|p| expr_to_ir_type(&p.ty).unwrap_or(IRType::Object))
                        .collect();
                    let return_type = expr_to_ir_type(return_ty).unwrap_or(IRType::Object);
                    let idx = extern_decls.len();
                    extern_decls.push(ExternDecl {
                        lean_name: (*lean_name).clone(),
                        c_name: entry.name.clone(),
                        backend: entry.backend.clone(),
                        param_types,
                        return_type,
                    });
                    extern_index.insert((*lean_name).clone(), idx);
                }
            }
        }

        Self {
            extern_decls,
            implemented_by: ImplementedByMap::new(),
            extern_index,
        }
    }

    /// Get all resolved extern declarations.
    pub fn extern_decls(&self) -> &[ExternDecl] {
        &self.extern_decls
    }

    /// Look up an extern declaration by Lean name.
    #[must_use]
    pub fn get_extern(&self, name: &Name) -> Option<&ExternDecl> {
        self.extern_index
            .get(name)
            .map(|&idx| &self.extern_decls[idx])
    }

    /// Check if a declaration has an `@[extern]` binding.
    #[must_use]
    pub fn is_extern(&self, name: &Name) -> bool {
        self.extern_index.contains_key(name)
    }

    /// Resolve an `@[implementedBy]` redirect.
    ///
    /// If `name` is an axiom with `@[implementedBy impl_name]`, returns
    /// `Some(impl_name)`. The compiler should emit a call to `impl_name`
    /// instead of `name`.
    #[must_use]
    pub fn resolve_implemented_by(&self, name: &Name) -> Option<&Name> {
        self.implemented_by.resolve(name)
    }

    /// Resolve a function call target through both extern and implementedBy.
    ///
    /// Returns the effective call target:
    /// - If `name` has `@[implementedBy impl]`, returns `CallTarget::Redirect(impl)`
    /// - If `name` has `@[extern "c_func"]`, returns `CallTarget::Extern(c_func)`
    /// - Otherwise, returns `CallTarget::Direct(name)`
    #[must_use]
    pub fn resolve_call<'a>(&'a self, name: &'a Name) -> CallTarget<'a> {
        if let Some(impl_name) = self.implemented_by.resolve(name) {
            // Check if the implementation itself is extern
            if let Some(ext) = self.get_extern(impl_name) {
                CallTarget::Extern(ext)
            } else {
                CallTarget::Redirect(impl_name)
            }
        } else if let Some(ext) = self.get_extern(name) {
            CallTarget::Extern(ext)
        } else {
            CallTarget::Direct(name)
        }
    }

    /// Get the implementedBy map for inspection/debugging.
    pub fn implemented_by_map(&self) -> &ImplementedByMap {
        &self.implemented_by
    }

    /// Number of extern declarations.
    #[must_use]
    pub fn num_externs(&self) -> usize {
        self.extern_decls.len()
    }

    /// Number of implementedBy bindings.
    #[must_use]
    pub fn num_implemented_by(&self) -> usize {
        self.implemented_by.len()
    }
}

/// Resolved call target for a function reference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallTarget<'a> {
    /// Call the function directly (no FFI involvement).
    Direct(&'a Name),
    /// Redirect to an `@[implementedBy]` target (still Lean code).
    Redirect(&'a Name),
    /// Call a C extern function.
    Extern(&'a ExternDecl),
}

/// Extract parameter and return types from a Lean function type expression.
///
/// Walks through nested Pi types to collect parameter types, with the
/// final non-Pi type as the return type.
fn extract_signature(ty: &clean_kernel::Expr) -> (Vec<IRType>, IRType) {
    use clean_kernel::ExprKind;

    let mut params = Vec::new();
    let mut current = ty.clone();

    loop {
        match current.kind() {
            ExprKind::Pi(_, domain, body) => {
                let ir_type = expr_to_ir_type(domain.as_ref()).unwrap_or(IRType::Object);
                params.push(ir_type);
                current = body.as_ref().clone();
            }
            _ => {
                let return_type = expr_to_ir_type(&current).unwrap_or(IRType::Object);
                return (params, return_type);
            }
        }
    }
}

fn is_c_backend(backend: &str) -> bool {
    backend.eq_ignore_ascii_case("c") || backend.eq_ignore_ascii_case("all")
}

#[cfg(test)]
mod tests;
