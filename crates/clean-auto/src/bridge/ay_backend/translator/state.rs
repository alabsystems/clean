// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::sync::Arc;

use ay::{FuncDecl, Sort, Term};
use clean_kernel::{Expr, FVarId};
use hashbrown::HashMap;

/// Collision-safe base for existential-witness FVar placeholders (#2848).
pub(super) const SKOLEM_FVAR_BASE: u64 = 1_u64 << 62;

/// clean-specific translation state behind interior mutability.
pub(super) struct LeanTranslationState {
    /// Kernel expression -> ay term cache.
    pub(super) expr_to_term: HashMap<Expr, Term>,
    /// Registered FVars with their ay sorts.
    pub(super) registered_fvars: HashMap<FVarId, Sort>,
    /// Cached UF declarations for FVar-headed applications.
    pub(super) fvar_func_decls: HashMap<FVarId, FuncDecl>,
    /// Cached string literal constants by value.
    pub(super) string_constants: HashMap<Arc<str>, Term>,
    /// Monotonic counter for fresh skolem names.
    pub(super) next_skolem_id: usize,
    /// Counter for internal existential-witness FVar placeholders (#2848).
    pub(super) next_internal_fvar: u64,
}

impl Default for LeanTranslationState {
    fn default() -> Self {
        Self {
            expr_to_term: HashMap::default(),
            registered_fvars: HashMap::default(),
            fvar_func_decls: HashMap::default(),
            string_constants: HashMap::default(),
            next_skolem_id: 0,
            next_internal_fvar: SKOLEM_FVAR_BASE,
        }
    }
}
