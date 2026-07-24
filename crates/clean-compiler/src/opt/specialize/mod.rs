// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Function Specialization Pass for L5CNF.
//!
//! Creates optimized versions of functions based on constant arguments.
//! Essential for typeclass-heavy code like Mathlib.
//!
//! # Algorithm Overview
//!
//! Based on Lean 4's `src/Lean/Compiler/LCNF/Specialize.lean`:
//!
//! 1. **Ground value tracking**: Identify let-bindings that don't depend on runtime parameters
//! 2. **Specialization candidates**: Find function calls with ground arguments
//! 3. **Key construction**: Create unique keys for each specialization
//! 4. **Specialized declaration generation**: Create new functions with ground args inlined
//!
//! # Specialization Categories (SpecParamInfo)
//!
//! - `FixedInst`: Typeclass instance arguments (always specialized)
//! - `FixedHO`: Higher-order function arguments (with `@[specialize]`)
//! - `FixedNeutral`: Computationally irrelevant but depended upon
//! - `User`: Explicitly marked with `@[specialize arg]`
//! - `Other`: Not specialized
//!
//! # Example
//!
//! Before:
//! ```text
//! def foo [Add α] (x : α) := x + x
//!
//! let _inst := Nat.instAddNat
//! let _result := foo _inst 42
//! ```
//!
//! After:
//! ```text
//! def foo_Nat_add (x : Nat) := Nat.add x x
//!
//! let _result := foo_Nat_add 42
//! ```
//!
//! Part of #1039 - Function specialization pass.

pub(crate) mod candidate;
pub(crate) mod context;
pub(crate) mod substitute;
pub(crate) mod transform;

use crate::lcnf::{Decl, DeclValue};
use clean_kernel::Name;
use std::collections::HashMap;

// Re-export public types
pub use context::{GroundValue, SpecCacheKey, SpecKey};

// Re-export internal items for tests (accessible via `use super::*;`)
#[cfg(test)]
pub(crate) use candidate::{
    arg_to_spec_key, build_spec_key, create_specialized_decl, has_specializable_ground_args,
    let_value_to_ground,
};
#[cfg(test)]
pub(crate) use transform::is_code_ground;

use context::{SpecContext, SpecState};
use transform::{specialize_code, specialize_code_with_index};

/// Information about which parameters qualify for specialization.
///
/// Based on Lean 4's `SpecParamInfo` from `LCNF/SpecInfo.lean`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecParamInfo {
    /// Typeclass instance parameter (always specialized).
    FixedInst,
    /// Higher-order function parameter (specialized with `@[specialize]`).
    FixedHO,
    /// Computationally irrelevant parameter with forward dependencies.
    FixedNeutral,
    /// User-specified via `@[specialize arg]`.
    User,
    /// Not specialized.
    Other,
}

impl SpecParamInfo {
    /// Returns true if this parameter causes specialization to occur.
    pub fn causes_specialization(self) -> bool {
        matches!(self, Self::FixedInst | Self::FixedHO | Self::User)
    }
}

/// Entry in the specialization registry.
#[derive(Debug, Clone)]
pub struct SpecEntry {
    /// Declaration name.
    pub decl_name: Name,
    /// Parameter specialization info.
    pub params_info: Vec<SpecParamInfo>,
    /// True if already specialized.
    pub already_specialized: bool,
}

/// Registry of specialization information for declarations.
///
/// Maps declaration names to their `SpecEntry`, which describes which
/// parameters are eligible for specialization.
#[derive(Debug, Clone, Default)]
pub struct SpecRegistry {
    entries: HashMap<Name, SpecEntry>,
}

impl SpecRegistry {
    /// Create a new empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register specialization info for a declaration.
    pub fn register(&mut self, entry: SpecEntry) {
        self.entries.insert(entry.decl_name.clone(), entry);
    }

    /// Look up specialization info for a declaration.
    pub fn get(&self, name: &Name) -> Option<&SpecEntry> {
        self.entries.get(name)
    }
}

/// Index for O(1) declaration lookup by name.
///
/// Used by the batch specialization API to look up target declarations.
#[derive(Debug, Clone, Default)]
pub struct DeclIndex<'a> {
    index: HashMap<Name, &'a Decl>,
}

impl<'a> DeclIndex<'a> {
    /// Create a new declaration index from a slice of declarations.
    pub fn new(decls: &'a [Decl]) -> Self {
        let index = decls.iter().map(|d| (d.name.clone(), d)).collect();
        Self { index }
    }

    /// Look up a declaration by name.
    pub fn get(&self, name: &Name) -> Option<&'a Decl> {
        self.index.get(name).copied()
    }
}

/// Configuration for the specialization pass.
#[derive(Debug, Clone)]
pub struct SpecConfig {
    /// Specialize typeclass instances (default: true).
    pub specialize_instances: bool,
    /// Specialize higher-order functions (default: false, requires @[specialize]).
    pub specialize_higher_order: bool,
    /// Maximum specialization depth to prevent unbounded recursion.
    pub max_depth: u32,
}

impl Default for SpecConfig {
    fn default() -> Self {
        Self {
            specialize_instances: true,
            specialize_higher_order: false,
            max_depth: 5,
        }
    }
}

/// Run function specialization on a declaration.
///
/// Returns the potentially modified declaration and any generated specialized declarations.
pub fn specialize(decl: &Decl, config: &SpecConfig) -> (Decl, Vec<Decl>) {
    let mut state = SpecState::new();

    let body = match &decl.body {
        DeclValue::Code(code) => {
            let mut ctx = SpecContext::new(decl.name.clone());
            // Add parameters to scope (they're not ground since they vary at runtime)
            for param in &decl.params {
                ctx.scope.insert(param.fvar_id);
            }
            let specialized = specialize_code(&mut ctx, &mut state, code, config);
            DeclValue::Code(Box::new(specialized))
        }
        DeclValue::Extern(attr) => DeclValue::Extern(attr.clone()),
    };

    let result = Decl {
        name: decl.name.clone(),
        level_params: decl.level_params.clone(),
        ty: decl.ty.clone(),
        params: decl.params.clone(),
        body,
        recursive: decl.recursive,
    };

    (result, state.generated_decls)
}

/// Run function specialization directly on code.
pub fn specialize_in_code(code: &crate::lcnf::Code, config: &SpecConfig) -> crate::lcnf::Code {
    let mut ctx = SpecContext::new(Name::anon());
    let mut state = SpecState::new();
    specialize_code(&mut ctx, &mut state, code, config)
}

/// Run function specialization on all declarations (batch API).
///
/// This is the preferred entry point for specialization as it has access to all
/// declarations for generating specialized versions.
///
/// Returns: All input declarations (potentially modified) plus any generated
/// specialized declarations.
pub fn specialize_all(decls: &[Decl], config: &SpecConfig) -> Vec<Decl> {
    let decl_index = DeclIndex::new(decls);
    let mut state = SpecState::new();
    let mut result = Vec::with_capacity(decls.len() * 2);

    // Phase 1: Process each declaration, identifying specialization candidates
    for decl in decls {
        let body = match &decl.body {
            DeclValue::Code(code) => {
                let mut ctx = SpecContext::new(decl.name.clone());
                for param in &decl.params {
                    ctx.scope.insert(param.fvar_id);
                }
                let specialized =
                    specialize_code_with_index(&mut ctx, &mut state, code, config, &decl_index);
                DeclValue::Code(Box::new(specialized))
            }
            DeclValue::Extern(attr) => DeclValue::Extern(attr.clone()),
        };

        result.push(Decl {
            name: decl.name.clone(),
            level_params: decl.level_params.clone(),
            ty: decl.ty.clone(),
            params: decl.params.clone(),
            body,
            recursive: decl.recursive,
        });
    }

    // Phase 2: Append generated specialized declarations
    result.extend(state.generated_decls);

    result
}

#[cfg(test)]
mod tests;
