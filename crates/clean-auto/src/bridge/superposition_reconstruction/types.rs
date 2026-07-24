// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Types for superposition proof reconstruction: error types and symbol map.

use std::collections::HashMap;

use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind, FVarId};

use crate::superposition::{Symbol, Term};

/// Symbol type status: either a real inferred type or explicitly missing.
///
/// The superposition clausifier stores this for each symbol. Reconstruction
/// code that asks for a missing type gets an explicit error instead of a
/// fabricated `Sort 1` placeholder. Part of #2345.
#[derive(Debug, Clone)]
pub enum StoredType {
    /// Real type obtained from the kernel type checker.
    Known(Expr),
    /// Type inference failed — stores the reason string.
    Missing(String),
}

impl From<Expr> for StoredType {
    fn from(e: Expr) -> Self {
        StoredType::Known(e)
    }
}

/// Errors from superposition proof reconstruction.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ReconstructionError {
    /// A superposition symbol has no mapping to a kernel expression.
    #[error("unmapped symbol: {0}")]
    UnmappedSymbol(Symbol),

    /// A superposition variable has no kernel binding.
    #[error("unmapped variable: {0}")]
    UnmappedVariable(u32),

    /// A clause ID referenced in the proof trace was not found.
    #[error("missing clause: {0}")]
    MissingClause(u64),

    /// An input clause has no corresponding kernel hypothesis.
    #[error("missing input hypothesis for clause {0}")]
    MissingInputHypothesis(u64),

    /// The proof trace is empty or malformed.
    #[error("malformed proof trace: {0}")]
    MalformedTrace(String),

    /// Sort inference failed during proof term construction.
    #[error("sort inference failed: {0}")]
    SortInferenceFailed(String),

    /// Unsupported inference rule for reconstruction.
    #[error("unsupported inference: {0}")]
    UnsupportedInference(String),
}

/// Result type for superposition reconstruction.
pub type ReconstructionResult<T> = Result<T, ReconstructionError>;

/// Maps superposition-internal types to kernel expressions.
///
/// The superposition prover uses its own `Term`/`Symbol` representation
/// (u32-based) which is separate from the kernel's `Expr`. This struct
/// provides the bidirectional mapping needed for proof reconstruction.
#[derive(Debug, Default)]
pub struct SymbolMap {
    /// Superposition Symbol → kernel Expr (for constants/functions)
    symbol_to_expr: HashMap<Symbol, Expr>,
    /// Superposition Symbol → kernel type (known or missing). Part of #2345.
    symbol_to_type: HashMap<Symbol, StoredType>,
    /// Variable bindings from the current proof context
    var_to_expr: HashMap<u32, Expr>,
    /// Variable → type mappings
    var_to_type: HashMap<u32, Expr>,
    /// Input clause ID → kernel hypothesis FVarId
    pub(crate) input_to_fvar: HashMap<u64, FVarId>,
    /// Input clause ID → kernel hypothesis type (the proposition)
    pub(crate) input_to_type: HashMap<u64, Expr>,
    /// Skolem constant declarations: (name, type) pairs for constants
    /// introduced by Skolemization (`sk_N`). Must be declared in the
    /// kernel Environment before type-checking reconstructed proof terms.
    skolem_decls: Vec<(Name, Expr)>,
    /// Goal expression, number of goal clauses, and FVarId base.
    ///
    /// Set by `clausify_goal` so the caller can wrap the reconstruction
    /// output with `Classical.byContradiction`. The goal is the original
    /// (un-negated) proposition P; the count indicates how many input
    /// clauses correspond to the negated goal. The FVarId base is the
    /// starting FVarId used for goal clause hypotheses (default 0,
    /// configurable to avoid collision with tactic hypothesis FVarIds).
    pub(crate) goal_info: Option<(Expr, usize, u64)>,
}

impl SymbolMap {
    /// Create a new empty symbol map.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a superposition symbol with its kernel expression and type.
    ///
    /// Accepts `Expr` (auto-converts to `StoredType::Known`) or `StoredType`
    /// directly. Part of #2345.
    pub fn add_symbol(&mut self, sym: Symbol, expr: Expr, ty: impl Into<StoredType>) {
        self.symbol_to_expr.insert(sym, expr);
        self.symbol_to_type.insert(sym, ty.into());
    }

    /// Register a variable binding.
    pub fn add_variable(&mut self, var: u32, expr: Expr, ty: Expr) {
        self.var_to_expr.insert(var, expr);
        self.var_to_type.insert(var, ty);
    }

    /// Register an input clause with its kernel hypothesis.
    pub fn add_input_clause(&mut self, clause_id: u64, fvar: FVarId, prop: Expr) {
        self.input_to_fvar.insert(clause_id, fvar);
        self.input_to_type.insert(clause_id, prop);
    }

    /// Register a Skolem constant introduced by Skolemization.
    ///
    /// The clausifier calls this when creating `sk_N` constants via
    /// `nnf_skolemize`. The declaration is stored so the kernel Environment
    /// can be extended before type-checking proof terms.
    pub fn register_skolem(&mut self, name: Name, ty: Expr) {
        self.skolem_decls.push((name, ty));
    }

    /// Declare all Skolem constants as axioms in the kernel Environment.
    ///
    /// Skolem constants are opaque witnesses introduced by Skolemization.
    /// They have a type but no computable value. Declaring them as axioms
    /// allows the type checker to accept proof terms that reference them.
    pub fn declare_skolems(&self, env: &mut Environment) {
        for (name, ty) in &self.skolem_decls {
            env.add_skolem_axiom(name.clone(), ty.clone());
        }
    }

    /// Get the Skolem constant declarations.
    #[cfg(test)]
    pub fn skolem_declarations(&self) -> &[(Name, Expr)] {
        &self.skolem_decls
    }

    /// Store goal metadata for the byContradiction wrapper.
    ///
    /// Uses FVarId base 0 (goal clause FVarIds start at 0). For use
    /// with `try_superposition_prove_with_fvars` where tactic FVarIds
    /// may collide, use `set_goal_info_with_fvar_base` instead.
    #[cfg(test)]
    pub fn set_goal_info(&mut self, goal: Expr, num_goal_clauses: usize) {
        self.goal_info = Some((goal, num_goal_clauses, 0));
    }

    /// Store goal metadata with a custom FVarId base.
    ///
    /// The `fvar_base` is the starting FVarId used for goal clause
    /// hypotheses. When the superposition prover is invoked from the
    /// tactic framework, tactic-scope FVarIds (0, 1, 2, ...) may
    /// collide with the default goal clause FVarIds. Setting a high
    /// sentinel base avoids this collision.
    pub fn set_goal_info_with_fvar_base(
        &mut self,
        goal: Expr,
        num_goal_clauses: usize,
        fvar_base: u64,
    ) {
        self.goal_info = Some((goal, num_goal_clauses, fvar_base));
    }

    /// Convert a superposition `Term` to a kernel `Expr`.
    pub fn term_to_expr(&self, term: &Term) -> ReconstructionResult<Expr> {
        match term {
            Term::Var(v) => self
                .var_to_expr
                .get(v)
                .cloned()
                .ok_or(ReconstructionError::UnmappedVariable(*v)),
            Term::Const(sym) => self
                .symbol_to_expr
                .get(sym)
                .cloned()
                .ok_or(ReconstructionError::UnmappedSymbol(*sym)),
            Term::App(func, args) => {
                let func_expr = self
                    .symbol_to_expr
                    .get(func)
                    .cloned()
                    .ok_or(ReconstructionError::UnmappedSymbol(*func))?;
                let mut result = func_expr;
                for arg in args {
                    let arg_expr = self.term_to_expr(arg)?;
                    result = Expr::app(result, arg_expr);
                }
                Ok(result)
            }
        }
    }

    /// Resolve a stored symbol type, returning the known type or an error
    /// for missing types. Part of #2345.
    fn resolve_symbol_type(&self, sym: &Symbol) -> ReconstructionResult<Expr> {
        match self.symbol_to_type.get(sym) {
            Some(StoredType::Known(ty)) => Ok(ty.clone()),
            Some(StoredType::Missing(reason)) => {
                Err(ReconstructionError::SortInferenceFailed(reason.clone()))
            }
            None => Err(ReconstructionError::UnmappedSymbol(*sym)),
        }
    }

    /// Get the type of a superposition term.
    ///
    /// For `Term::App(f, args)`, peels Pi binders from the function type
    /// and substitutes each argument into the body for dependent Pi types.
    /// Returns an error if the function type has fewer Pi binders than arguments.
    /// Returns `SortInferenceFailed` if a symbol has missing type metadata
    /// (Part of #2345).
    pub fn term_type(&self, term: &Term) -> ReconstructionResult<Expr> {
        match term {
            Term::Var(v) => self
                .var_to_type
                .get(v)
                .cloned()
                .ok_or(ReconstructionError::UnmappedVariable(*v)),
            Term::Const(sym) => self.resolve_symbol_type(sym),
            Term::App(func, args) => {
                let func_type = self.resolve_symbol_type(func)?;
                let mut result_type = func_type;
                for arg in args {
                    match result_type.kind() {
                        ExprKind::Pi(_, _, body) => {
                            let arg_expr = self.term_to_expr(arg)?;
                            result_type = body.instantiate(&arg_expr);
                        }
                        _ => {
                            return Err(ReconstructionError::SortInferenceFailed(format!(
                                "non-Pi type during application type computation \
                                     (function has fewer binders than arguments): {result_type:?}"
                            )));
                        }
                    }
                }
                Ok(result_type)
            }
        }
    }
}
