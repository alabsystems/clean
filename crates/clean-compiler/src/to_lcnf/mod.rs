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
mod decision_layout;
pub use decision_layout::decidable_projects_bool;
#[cfg(test)]
mod generic_cases_minor_tests;
mod lower;
pub(crate) mod mentions;
mod mutual_rec;
mod rec_commute;
mod rec_ih;
#[cfg(test)]
mod rec_ih_tests;
mod rec_select;
#[cfg(test)]
mod rec_select_tests;
mod rec_wf;
#[cfg(test)]
mod rec_wf_tests;
mod scoped_application_type;
#[cfg(test)]
mod scoped_application_type_tests;
mod sink_ih;
#[cfg(test)]
mod sink_ih_tests;
#[cfg(test)]
mod tests;
mod uint_decision;

use crate::implemented_by::CodeMeaning;
use crate::lcnf::{Code, FunDecl, LetDecl, LetValue};
use clean_kernel::{Environment, Expr, FVarId, Name};
use std::collections::{HashMap, HashSet};

pub(crate) use rec_ih::syntactic_action;

pub use lower::{
    constant_to_decl, constant_to_decl_in_runtime_closure, constant_to_decl_with_meaning,
    expr_to_code, is_erasable,
};
pub use mentions::code_called_constant_names;

/// Counter for generating fresh FVarIds.
#[derive(Debug, Default)]
pub(crate) struct FVarIdGen {
    next: u64,
}

impl FVarIdGen {
    /// Create a new generator starting from 0.
    pub(crate) fn new() -> Self {
        Self { next: 0 }
    }

    /// Generate a fresh FVarId.
    pub(crate) fn fresh(&mut self) -> FVarId {
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
    /// Local types with enclosing de Bruijn variables resolved to stable ids.
    local_types: HashMap<FVarId, Expr>,
    /// Local functions added via `add_fun` in this lowering context.
    local_funs: HashSet<FVarId>,
    /// Accumulated local declarations in source order.
    pending: Vec<PendingLocal>,
    /// What the lowered code means: which body a reference to an
    /// `@[implemented_by]` declaration runs.
    pub(crate) meaning: CodeMeaning,
    /// Rules at this body's compilation point, before later source attributes.
    pub(crate) csimp_rules: Vec<clean_kernel::env::csimp::Rule>,
    /// Induction-hypothesis placeholders of the recursors being lowered
    /// (`rec_ih`): each stands for a call of its synthesized `go`.
    ih_refs: HashMap<FVarId, rec_ih::IhRef>,
    /// The IH applications already bound on the current path, scoped like
    /// `pending` (`rec_ih::ih_value`).
    ih_memo: HashMap<rec_ih::MemoKey, FVarId>,
    /// `ih_memo`'s keys in insertion order, so a scope can drop its own.
    ih_memo_log: Vec<rec_ih::MemoKey>,
}

/// The pending locals of an enclosing scope, set aside by
/// [`LcnfContext::take_pending`] while a nested scope (a branch, a local
/// function body) is lowered, with the point its IH memo must return to.
struct PendingScope {
    locals: Vec<PendingLocal>,
    memo_mark: usize,
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
        Self::with_meaning(env, CodeMeaning::LeanCompiled)
    }

    /// [`Self::new`] for code that means `meaning`
    /// ([`CodeMeaning::KernelValue`]: no reference is substituted).
    pub(crate) fn with_meaning(env: &'a Environment, meaning: CodeMeaning) -> Self {
        Self {
            env,
            fvar_gen: FVarIdGen::new(),
            bvar_stack: Vec::new(),
            local_types: HashMap::new(),
            local_funs: HashSet::new(),
            pending: Vec::new(),
            meaning,
            csimp_rules: clean_kernel::env::csimp::rules_for(env, None),
            ih_refs: HashMap::new(),
            ih_memo: HashMap::new(),
            ih_memo_log: Vec::new(),
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
    #[cfg(test)]
    pub(crate) fn push_binder(&mut self) -> FVarId {
        let fvar = self.fresh_fvar();
        self.bvar_stack.push(fvar);
        fvar
    }

    /// Record a parameter's type before entering its binder scope.
    pub(crate) fn push_typed_binder(&mut self, ty: &Expr) -> FVarId {
        let ty = self.resolve_local_type(ty);
        let fvar = self.fresh_fvar();
        self.local_types.insert(fvar, ty);
        self.bvar_stack.push(fvar);
        fvar
    }

    pub(crate) fn resolve_local_type(&self, ty: &Expr) -> Expr {
        let locals: Vec<_> = self
            .bvar_stack
            .iter()
            .rev()
            .map(|id| Expr::fvar(*id))
            .collect();
        ty.instantiate_rev(&locals)
    }

    pub(crate) fn record_local_type(&mut self, fvar: FVarId, ty: &Expr) {
        let local_ty = self.resolve_local_type(ty);
        self.local_types.insert(fvar, local_ty);
    }

    pub(crate) fn local_type(&self, fvar: FVarId) -> Option<&Expr> {
        self.local_types.get(&fvar)
    }

    pub(crate) fn is_local_fun(&self, fvar: FVarId) -> bool {
        self.local_funs.contains(&fvar)
    }

    /// Pop a binder from the stack.
    pub(crate) fn pop_binder(&mut self) {
        self.bvar_stack.pop();
    }

    /// Add a let-binding and return the bound FVarId.
    pub(crate) fn add_let(&mut self, name: Name, ty: Expr, value: LetValue) -> FVarId {
        let fvar = self.fresh_fvar();
        let local_ty = self.resolve_local_type(&ty);
        self.local_types.insert(fvar, local_ty);
        self.pending
            .push(PendingLocal::Let(LetDecl::new(fvar, name, ty, value)));
        fvar
    }

    /// Add a local function declaration.
    pub(crate) fn add_fun(&mut self, decl: FunDecl) {
        self.local_funs.insert(decl.fvar_id);
        self.pending.push(PendingLocal::Fun(decl));
    }

    /// Open a nested scope: its lets are emitted inside it, and the IH
    /// applications it binds are visible only inside it.
    fn take_pending(&mut self) -> PendingScope {
        PendingScope {
            locals: std::mem::take(&mut self.pending),
            memo_mark: self.ih_memo_log.len(),
        }
    }

    fn restore_pending(&mut self, outer: PendingScope) {
        debug_assert!(self.pending.is_empty());
        self.pending = outer.locals;
        self.forget_ih_memo(outer.memo_mark);
    }

    /// Restore an outer pending scope after a *failed* lowering attempt,
    /// discarding any locals the aborted scope accumulated.
    ///
    /// Success paths must keep using [`Self::restore_pending`], whose
    /// `debug_assert` guards against silently dropping real let-bindings.
    /// On an error path the partial locals belong to the branch that just
    /// failed to lower, so discarding them is the correct (and panic-free)
    /// cleanup: the lowering error still propagates to the caller.
    fn abandon_pending(&mut self, outer: PendingScope) {
        self.pending = outer.locals;
        self.forget_ih_memo(outer.memo_mark);
    }

    fn forget_ih_memo(&mut self, mark: usize) {
        for key in self.ih_memo_log.drain(mark..) {
            self.ih_memo.remove(&key);
        }
    }

    /// Take accumulated let-bindings.
    #[cfg(test)]
    pub(crate) fn take_lets(&mut self) -> Vec<LetDecl> {
        std::mem::take(&mut self.pending)
            .into_iter()
            .filter_map(|local| match local {
                PendingLocal::Let(decl) => Some(decl),
                PendingLocal::Fun(_) => None,
            })
            .collect()
    }

    /// Wrap a terminal with accumulated local declarations.
    pub(crate) fn wrap_lets(&mut self, terminal: Code) -> Code {
        let pending = std::mem::take(&mut self.pending);
        pending
            .into_iter()
            .rev()
            .fold(terminal, |body, local| match local {
                PendingLocal::Let(decl) => Code::let_bind(decl, body),
                PendingLocal::Fun(decl) => Code::fun(decl, body),
            })
    }
}
