// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Builder state: types, struct, and internal bookkeeping.

use std::collections::HashMap;
use std::sync::Arc;

use crate::env::Environment;
use crate::expr::{Expr, FVarId};
use crate::mode::CleanMode;

use super::super::{CertError, ProofCert};
use super::cache::WhnfCache;

/// Opaque handle to a verified certificate node.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NodeId(pub(crate) u32);

impl NodeId {
    pub(super) fn index(self) -> usize {
        self.0 as usize
    }

    pub(super) fn raw(self) -> u32 {
        self.0
    }
}

/// Result of adding a node - either success with ID or early failure.
pub type BuildResult = Result<NodeId, CertError>;

#[derive(Debug, Clone)]
pub(crate) struct BuildNode {
    pub(crate) cert: ProofCert,
    pub(crate) computed_type: Expr,
}

/// Incremental certificate builder with fail-fast verification.
pub struct CertBuilder<'env> {
    pub(super) env: &'env Environment,
    pub(super) context: Vec<Expr>,
    pub(super) fvar_types: HashMap<FVarId, Expr>,
    pub(super) mode: CleanMode,
    pub(super) nodes: Vec<BuildNode>,
    pub(super) whnf_cache: Option<Arc<WhnfCache>>,
}

impl<'env> CertBuilder<'env> {
    /// Create a new CertBuilder inheriting the environment mode
    ///
    /// REQUIRES: `env` is a well-formed environment
    /// ENSURES: Returns a fresh builder with empty context and no nodes
    pub fn new(env: &'env Environment) -> Self {
        Self {
            env,
            context: Vec::new(),
            fvar_types: HashMap::new(),
            mode: env.mode(),
            nodes: Vec::new(),
            whnf_cache: None,
        }
    }

    /// Create a new CertBuilder with specified mode
    pub fn with_mode(env: &'env Environment, mode: CleanMode) -> Self {
        Self {
            env,
            context: Vec::new(),
            fvar_types: HashMap::new(),
            mode,
            nodes: Vec::new(),
            whnf_cache: None,
        }
    }

    /// Attach a shared WHNF cache for batch-style reuse across builders.
    #[must_use]
    pub fn with_whnf_cache(mut self, whnf_cache: Arc<WhnfCache>) -> Self {
        self.whnf_cache = Some(whnf_cache);
        self
    }

    /// Get the current type-checking mode
    pub fn mode(&self) -> CleanMode {
        self.mode
    }

    /// Register a free variable with its type
    pub fn register_fvar(&mut self, id: FVarId, ty: Expr) -> Result<(), CertError> {
        if let Some(existing) = self.fvar_types.get(&id) {
            if !self.def_eq(existing, &ty) {
                return Err(CertError::TypeMismatch {
                    expected: Box::new(existing.clone()),
                    actual: Box::new(ty),
                    location: format!("FVar {id:?}"),
                });
            }
        }
        self.fvar_types.insert(id, ty);
        Ok(())
    }

    /// Returns the computed type of the node with the given ID.
    ///
    /// # Panics
    /// Panics if `id` is not a valid NodeId from this builder.
    pub fn type_of(&self, id: NodeId) -> &Expr {
        &self.nodes[id.index()].computed_type
    }

    /// Returns the computed type of the node, or `None` if the ID is invalid.
    pub fn try_type_of(&self, id: NodeId) -> Option<&Expr> {
        self.nodes.get(id.index()).map(|n| &n.computed_type)
    }

    /// Number of certificate nodes built so far
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Check if no nodes have been built
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    // Internal helpers

    pub(super) fn validate_node_id(&self, id: NodeId, context: &str) -> Result<(), CertError> {
        if id.index() >= self.nodes.len() {
            return Err(CertError::InvalidCert(format!(
                "{}: Invalid NodeId {} (only {} nodes built)",
                context,
                id.raw(),
                self.nodes.len()
            )));
        }
        Ok(())
    }

    pub(super) fn add_node(&mut self, cert: ProofCert, computed_type: Expr) -> BuildResult {
        let id = NodeId(self.nodes.len() as u32);
        self.nodes.push(BuildNode {
            cert,
            computed_type,
        });
        Ok(id)
    }

    pub(super) fn push_binder(&mut self, ty: Expr) {
        self.context.push(ty);
    }

    pub(super) fn pop_binder(&mut self) {
        self.context.pop();
    }
}
