// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Conversion from kernel Expr to L5CNF.
//!
//! This module implements the first stage of compilation: converting
//! elaborated kernel expressions into A-normal form (L5CNF).
//!
//! # Key transformations
//!
//! 1. **De Bruijn to FVar**: Convert bound variables to explicit free variables
//! 2. **A-normalization**: Ensure all intermediate results are let-bound
//! 3. **Application flattening**: Convert curried applications to argument lists
//! 4. **Type erasure marking**: Identify computationally irrelevant terms
//!
//! # Example
//!
//! Input (kernel Expr):
//! ```text
//! λ (x : Nat), Nat.add x 1
//! ```
//!
//! Output (L5CNF):
//! ```text
//! fun f (x : Nat) : Nat :=
//!   let _1 := 1
//!   let _2 := Nat.add x _1
//!   return _2
//! ```

pub mod codata_recognize;
mod lower;
pub(crate) mod mentions;
#[cfg(test)]
mod tests;

use crate::lcnf::{Code, FunDecl, LetDecl, LetValue};
use clean_kernel::{Environment, Expr, FVarId, Name};

pub use lower::{constant_to_decl, expr_to_code, is_erasable};

/// Counter for generating fresh FVarIds.
#[derive(Debug, Default)]
pub struct FVarIdGen {
    next: u64,
}

impl FVarIdGen {
    /// Create a new generator starting from 0.
    pub fn new() -> Self {
        Self { next: 0 }
    }

    /// Generate a fresh FVarId.
    pub fn fresh(&mut self) -> FVarId {
        let id = FVarId::new(self.next);
        self.next += 1;
        id
    }
}

/// Context for L5CNF conversion.
///
/// Tracks the mapping from de Bruijn indices to FVarIds and collects
/// let-bindings during A-normalization.
pub struct LcnfContext<'a> {
    /// Environment for looking up constants.
    pub(crate) env: &'a Environment,
    /// Generator for fresh FVarIds.
    fvar_gen: FVarIdGen,
    /// Stack mapping de Bruijn indices to FVarIds.
    /// Index 0 is the innermost binder.
    pub(crate) bvar_stack: Vec<FVarId>,
    /// Accumulated local declarations in source order.
    pending: Vec<PendingLocal>,
}

enum PendingLocal {
    Let(LetDecl),
    Fun(FunDecl),
}

impl<'a> LcnfContext<'a> {
    /// Create a new conversion context.
    ///
    /// The context is declaration-name-agnostic: recursive eliminations
    /// (`Nat.rec`, `List.rec`, ..) are lowered by synthesizing a LOCAL
    /// recursive function (`lower::rec_apply_parts`), never by a self-call
    /// back to the enclosing declaration — the retired `with_self_name`
    /// constructor existed only for the old `Nat.rec` special case, whose
    /// `self_name(pred)` IH under-applied multi-parameter declarations.
    pub fn new(env: &'a Environment) -> Self {
        Self {
            env,
            fvar_gen: FVarIdGen::new(),
            bvar_stack: Vec::new(),
            pending: Vec::new(),
        }
    }

    /// Generate a fresh free-variable id.
    pub(crate) fn fresh_fvar(&mut self) -> FVarId {
        self.fvar_gen.fresh()
    }

    /// Look up a bound variable by de Bruijn index.
    pub(crate) fn lookup_bvar(&self, idx: u32) -> Option<FVarId> {
        let len = self.bvar_stack.len();
        if (idx as usize) < len {
            Some(self.bvar_stack[len - 1 - idx as usize])
        } else {
            None
        }
    }

    /// Push a new binder onto the stack.
    pub(crate) fn push_binder(&mut self) -> FVarId {
        let fvar = self.fresh_fvar();
        self.bvar_stack.push(fvar);
        fvar
    }

    /// Pop a binder from the stack.
    pub(crate) fn pop_binder(&mut self) {
        self.bvar_stack.pop();
    }

    /// Add a let-binding and return the bound FVarId.
    pub(crate) fn add_let(&mut self, name: Name, ty: Expr, value: LetValue) -> FVarId {
        let fvar = self.fresh_fvar();
        self.pending
            .push(PendingLocal::Let(LetDecl::new(fvar, name, ty, value)));
        fvar
    }

    /// Add a local function declaration.
    pub(crate) fn add_fun(&mut self, decl: FunDecl) {
        self.pending.push(PendingLocal::Fun(decl));
    }

    fn take_pending(&mut self) -> Vec<PendingLocal> {
        std::mem::take(&mut self.pending)
    }

    fn restore_pending(&mut self, pending: Vec<PendingLocal>) {
        debug_assert!(self.pending.is_empty());
        self.pending = pending;
    }

    /// Restore an outer pending scope after a *failed* lowering attempt,
    /// discarding any locals the aborted scope accumulated.
    ///
    /// Success paths must keep using [`Self::restore_pending`], whose
    /// `debug_assert` guards against silently dropping real let-bindings.
    /// On an error path the partial locals belong to the branch that just
    /// failed to lower, so discarding them is the correct (and panic-free)
    /// cleanup: the lowering error still propagates to the caller.
    fn abandon_pending(&mut self, outer: Vec<PendingLocal>) {
        self.pending = outer;
    }

    /// Take accumulated let-bindings.
    #[cfg(test)]
    pub(crate) fn take_lets(&mut self) -> Vec<LetDecl> {
        self.take_pending()
            .into_iter()
            .filter_map(|local| match local {
                PendingLocal::Let(decl) => Some(decl),
                PendingLocal::Fun(_) => None,
            })
            .collect()
    }

    /// Wrap a terminal with accumulated local declarations.
    pub(crate) fn wrap_lets(&mut self, terminal: Code) -> Code {
        let pending = self.take_pending();
        pending
            .into_iter()
            .rev()
            .fold(terminal, |body, local| match local {
                PendingLocal::Let(decl) => Code::let_bind(decl, body),
                PendingLocal::Fun(decl) => Code::fun(decl, body),
            })
    }
}
