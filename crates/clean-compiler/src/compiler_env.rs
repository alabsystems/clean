// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unified compiler environment for pipeline stages.
//!
//! `CompilerEnv` provides shared, read-only access to declaration metadata
//! that multiple pipeline stages need: declaration lookup by name, constructor
//! metadata, and function arities. Before this module, each stage (boxing,
//! ir_checker, emitters) independently rebuilt its own lookup structures from
//! the flat `&[IRDecl]` slice.
//!
//! # Usage
//!
//! Build once after `to_ir` produces `Vec<IRDecl>`, then pass `&CompilerEnv`
//! to downstream stages:
//!
//! ```text
//! let env = CompilerEnv::from_decls(&ir_decls, ctor_env, inductive_env);
//! let boxed = explicit_boxing_with_env(&ir_decls, &env, &boxing_config);
//! check_decls_with_env(&boxed, &env)?;
//! ```
//!
//! Part of #1970.

use crate::ir::IRDecl;
use crate::to_ir::CtorMeta;
use clean_kernel::Name;
use std::collections::HashMap;

/// Unified environment shared across compiler pipeline stages.
///
/// Constructed once from IR declarations and optional kernel metadata,
/// then borrowed by boxing, IR checking, and emission stages.
#[derive(Debug, Clone)]
pub struct CompilerEnv {
    /// O(1) declaration lookup: name -> index into the decls slice.
    decl_index: HashMap<Name, usize>,
    /// Function arities (parameter count) for each declaration.
    arities: HashMap<Name, u16>,
    /// Constructor metadata: constructor name -> tag + field layout.
    ctor_env: HashMap<Name, CtorMeta>,
    /// Inductive type metadata: inductive name -> first constructor's layout.
    inductive_env: HashMap<Name, CtorMeta>,
}

impl CompilerEnv {
    /// Build a `CompilerEnv` from IR declarations and constructor metadata.
    ///
    /// The `decl_index` and `arities` maps are derived from `decls`. The
    /// constructor and inductive maps are passed through from `to_ir` or
    /// `build_ctor_env`.
    pub fn new(
        decls: &[IRDecl],
        ctor_env: HashMap<Name, CtorMeta>,
        inductive_env: HashMap<Name, CtorMeta>,
    ) -> Self {
        let decl_index: HashMap<Name, usize> = decls
            .iter()
            .enumerate()
            .map(|(i, d)| (d.name.clone(), i))
            .collect();
        let arities: HashMap<Name, u16> = decls
            .iter()
            .map(|d| (d.name.clone(), d.params.len() as u16))
            .collect();
        Self {
            decl_index,
            arities,
            ctor_env,
            inductive_env,
        }
    }

    /// Build a `CompilerEnv` from declarations only (no constructor metadata).
    ///
    /// Suitable when constructor metadata is unavailable (e.g., tests that
    /// build IR directly without a kernel `Environment`).
    pub fn from_decls(decls: &[IRDecl]) -> Self {
        Self::new(decls, HashMap::new(), HashMap::new())
    }

    /// Look up a declaration's index in the original slice by name.
    ///
    /// Returns `None` if the name is not in the environment (e.g., external
    /// function not included in the compilation unit).
    #[inline]
    pub fn get_decl_index(&self, name: &Name) -> Option<usize> {
        self.decl_index.get(name).copied()
    }

    /// Look up a declaration by name from the provided slice.
    ///
    /// Callers pass the same `&[IRDecl]` used to construct this env.
    #[inline]
    pub fn get_decl<'a>(&self, name: &Name, decls: &'a [IRDecl]) -> Option<&'a IRDecl> {
        self.decl_index.get(name).map(|&i| &decls[i])
    }

    /// Look up the arity (parameter count) of a named function.
    #[inline]
    pub fn get_arity(&self, name: &Name) -> Option<u16> {
        self.arities.get(name).copied()
    }

    /// Look up constructor metadata by constructor name.
    #[inline]
    pub fn get_ctor_meta(&self, name: &Name) -> Option<&CtorMeta> {
        self.ctor_env.get(name)
    }

    /// Look up inductive type metadata by type name.
    #[inline]
    pub fn get_inductive_meta(&self, name: &Name) -> Option<&CtorMeta> {
        self.inductive_env.get(name)
    }

    /// Number of declarations in the environment.
    #[inline]
    pub fn len(&self) -> usize {
        self.decl_index.len()
    }

    /// Whether the environment is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.decl_index.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{IRBody, IRDecl, IRType, VarId};
    use clean_kernel::Name;

    fn mk_decl(name: &str, num_params: usize) -> IRDecl {
        let params: Vec<_> = (0..num_params)
            .map(|i| (VarId(i as u32), IRType::Object))
            .collect();
        IRDecl {
            name: Name::from_string(name),
            params,
            return_type: IRType::Object,
            body: IRBody::Unreachable,
        }
    }

    #[test]
    fn test_compiler_env_from_decls_builds_index() {
        let decls = vec![mk_decl("foo", 2), mk_decl("bar", 3)];
        let env = CompilerEnv::from_decls(&decls);

        assert_eq!(env.len(), 2);
        assert!(!env.is_empty());
        assert_eq!(env.get_decl_index(&Name::from_string("foo")), Some(0));
        assert_eq!(env.get_decl_index(&Name::from_string("bar")), Some(1));
        assert_eq!(env.get_decl_index(&Name::from_string("baz")), None);
    }

    #[test]
    fn test_compiler_env_arities() {
        let decls = vec![mk_decl("foo", 2), mk_decl("bar", 3)];
        let env = CompilerEnv::from_decls(&decls);

        assert_eq!(env.get_arity(&Name::from_string("foo")), Some(2));
        assert_eq!(env.get_arity(&Name::from_string("bar")), Some(3));
        assert_eq!(env.get_arity(&Name::from_string("baz")), None);
    }

    #[test]
    fn test_compiler_env_get_decl() {
        let decls = vec![mk_decl("foo", 2), mk_decl("bar", 3)];
        let env = CompilerEnv::from_decls(&decls);

        let d = env.get_decl(&Name::from_string("foo"), &decls);
        assert!(d.is_some());
        assert_eq!(d.unwrap().params.len(), 2);
    }

    #[test]
    fn test_compiler_env_ctor_meta() {
        let decls = vec![mk_decl("foo", 1)];
        let mut ctor_env = HashMap::new();
        ctor_env.insert(
            Name::from_string("Prod.mk"),
            CtorMeta {
                num_params: 0,
                tag: 0,
                field_types: vec![IRType::Object, IRType::Object],
                num_scalars: 0,
                num_objects: 2,
            },
        );
        let env = CompilerEnv::new(&decls, ctor_env, HashMap::new());

        assert!(env.get_ctor_meta(&Name::from_string("Prod.mk")).is_some());
        assert_eq!(
            env.get_ctor_meta(&Name::from_string("Prod.mk"))
                .unwrap()
                .num_objects,
            2
        );
        assert!(env.get_ctor_meta(&Name::from_string("List.nil")).is_none());
    }

    #[test]
    fn test_compiler_env_empty() {
        let env = CompilerEnv::from_decls(&[]);
        assert!(env.is_empty());
        assert_eq!(env.len(), 0);
    }
}
