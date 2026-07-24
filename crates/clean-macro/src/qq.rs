// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Qq - Type-Safe Expression Quotations
//!
//! This module provides Qq (type-safe expression quotations) from Lean 4's quote4 library.
//! Unlike syntax quotations (`` `(term) ``), Qq works at the kernel `Expr` level with
//! compile-time type safety.
//!
//! # Overview
//!
//! - `Q(α)` - Quoted type: denotes expressions of type α
//! - `q(·)` - Value quotation: construct expressions within the Q framework
//!
//! # Example
//!
//! ```text
//! -- Type-safe expression construction
//! def mkAdd (a b : Q(Nat)) : Q(Nat) := q($a + $b)
//!
//! -- Pattern matching on expressions
//! match e : Q(List Nat) with
//! | q([$x, $y]) => ...
//! | q($h :: $t) => ...
//! ```
//!
//! # Architecture
//!
//! The Qq system has three main components:
//! 1. **QuotedExpr** - Expressions paired with their expected types
//! 2. **UnquoteState** - State for converting q(·) syntax to Expr
//! 3. **QuoteState** - State for converting Expr back to syntax
//!
//! Part of #16: Qq quotation support for macro metaprogramming

use clean_kernel::{Expr, FVarId, Level, Name};
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

/// A quoted expression with type tracking.
///
/// `QuotedExpr` represents an expression `e` along with its expected type `α`,
/// written as `Q(α)` in Lean syntax. The type tracking enables compile-time
/// verification that expressions have the correct types.
///
/// # Example
///
/// ```text
/// -- In Lean syntax:
/// def x : Q(Nat) := q(42)     -- expr=42, expected_type=Nat
/// def y : Q(Bool) := q(true)  -- expr=true, expected_type=Bool
/// ```
#[derive(Debug, Clone)]
pub struct QuotedExpr {
    /// The underlying kernel expression
    pub expr: Expr,
    /// The type expression (for tracking)
    /// This is the type that `expr` is expected to have
    pub expected_type: Expr,
}

impl QuotedExpr {
    /// Create a new quoted expression with explicit type
    pub fn new(expr: Expr, expected_type: Expr) -> Self {
        Self {
            expr,
            expected_type,
        }
    }

    /// Create a quoted expression from just an expression
    /// The expected_type is set to Type (sort 0) as a placeholder
    /// that will be refined during type inference
    pub fn from_expr(expr: Expr) -> Self {
        Self {
            expr,
            // Use Type as placeholder - will be refined during inference
            expected_type: Expr::type_(),
        }
    }

    /// Get the underlying expression
    pub fn expr(&self) -> &Expr {
        &self.expr
    }

    /// Get the expected type
    pub fn expected_type(&self) -> &Expr {
        &self.expected_type
    }

    /// Extract the inner expression, consuming self
    pub fn into_expr(self) -> Expr {
        self.expr
    }
}

/// A quoted universe level.
///
/// Used for universe polymorphism in `Q(Sort u)`.
#[derive(Debug, Clone)]
pub struct QuotedLevel(pub Level);

impl QuotedLevel {
    /// Create a quoted level
    pub fn new(level: Level) -> Self {
        Self(level)
    }

    /// Get the inner level
    pub fn level(&self) -> &Level {
        &self.0
    }

    /// Extract the inner level
    pub fn into_level(self) -> Level {
        self.0
    }
}

impl From<Level> for QuotedLevel {
    fn from(level: Level) -> Self {
        Self::new(level)
    }
}

/// State for unquoting: converting q(·) syntax to kernel Expr.
///
/// During unquoting, we process antiquotations and track substitutions
/// to be applied to the final expression.
#[derive(Debug, Default)]
pub struct UnquoteState {
    /// Expression substitutions: name -> expr
    /// When we encounter `$x` in q(...), we record x -> expr here
    pub expr_subst: HashMap<Name, Expr>,

    /// Level substitutions: name -> level
    /// For universe polymorphism
    pub level_subst: HashMap<Name, Level>,

    /// Metavariables created during unquoting
    /// Used for pattern matching
    pub mvars: Vec<Name>,

    /// Type constraints from typed antiquotations $(x : τ)
    pub type_constraints: HashMap<Name, Expr>,

    /// Next fresh variable index
    next_var: usize,
}

impl UnquoteState {
    /// Create a new unquote state
    pub fn new() -> Self {
        Self::default()
    }

    /// Generate a fresh variable name for antiquotation binding
    pub fn fresh_var(&mut self) -> Name {
        let name = Name::from_string(&format!("_qq_v{}", self.next_var));
        self.next_var += 1;
        name
    }

    /// Add an expression substitution
    pub fn add_expr_subst(&mut self, name: Name, expr: Expr) {
        self.expr_subst.insert(name, expr);
    }

    /// Add a level substitution
    pub fn add_level_subst(&mut self, name: Name, level: Level) {
        self.level_subst.insert(name, level);
    }

    /// Add a type constraint from typed antiquotation
    pub fn add_type_constraint(&mut self, name: Name, ty: Expr) {
        self.type_constraints.insert(name, ty);
    }

    /// Apply accumulated substitutions to an expression
    ///
    /// Note: This performs substitution by creating FVarIds from the stored names
    /// and using subst_fvar. For level substitution, uses instantiate_level_params.
    pub fn apply_subst(&self, mut expr: Expr) -> Expr {
        // Apply expression substitutions using subst_fvar
        // The name was used to generate an FVarId, so we reconstruct it
        for (name, replacement) in &self.expr_subst {
            // Create FVarId from the name's hash for consistency
            let fvar_id = FVarId::new(name_to_id(name));
            expr = expr.subst_fvar(fvar_id, replacement);
        }
        // Apply level substitutions
        for (name, level) in &self.level_subst {
            expr = expr.instantiate_level_params(&[(name.clone(), level.clone())]);
        }
        expr
    }

    /// Check if we have an expression binding for a name
    pub fn has_expr(&self, name: &Name) -> bool {
        self.expr_subst.contains_key(name)
    }

    /// Get an expression binding
    pub fn get_expr(&self, name: &Name) -> Option<&Expr> {
        self.expr_subst.get(name)
    }

    /// Get a type constraint for a name
    pub fn get_type_constraint(&self, name: &Name) -> Option<&Expr> {
        self.type_constraints.get(name)
    }
}

/// State for quoting: converting Expr back to syntax.
///
/// Used when generating syntax representations of expressions,
/// for example in macro expansion or code generation.
#[derive(Debug, Default)]
pub struct QuoteState {
    /// Next fresh variable index for generated names
    pub next_var: usize,
}

impl QuoteState {
    /// Create a new quote state
    pub fn new() -> Self {
        Self::default()
    }

    /// Generate a fresh variable name
    pub fn fresh_name(&mut self) -> Name {
        let name = Name::from_string(&format!("_q{}", self.next_var));
        self.next_var += 1;
        name
    }
}

/// Kind of Qq quotation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QQuotationKind {
    /// Type quotation: `Q(α)`
    Type,
    /// Value quotation: `q(·)`
    Value,
}

/// Result of pattern matching a q(...) pattern against an expression
#[derive(Debug, Clone)]
pub struct QPatternMatch {
    /// Bindings from pattern variables to matched expressions
    pub bindings: HashMap<Name, QuotedExpr>,
}

impl QPatternMatch {
    /// Create a new pattern match result
    pub fn new(bindings: HashMap<Name, QuotedExpr>) -> Self {
        Self { bindings }
    }

    /// Get a binding by name
    pub fn get(&self, name: &Name) -> Option<&QuotedExpr> {
        self.bindings.get(name)
    }

    /// Check if a binding exists
    pub fn has(&self, name: &Name) -> bool {
        self.bindings.contains_key(name)
    }

    /// Number of bindings
    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }
}

/// Error type for Qq operations
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum QqError {
    /// Type mismatch in antiquotation
    #[error("type mismatch in antiquotation ${antiquot}: expected {expected:?}, got {actual:?}")]
    TypeMismatch {
        antiquot: Name,
        expected: Box<Expr>,
        actual: Box<Expr>,
    },
    /// Unbound antiquotation variable
    #[error("unbound antiquotation variable ${0}")]
    UnboundAntiquot(Name),
    /// Invalid quotation syntax
    #[error("invalid Qq syntax: {0}")]
    InvalidSyntax(String),
    /// Pattern match failed
    #[error("Qq pattern match failed")]
    PatternMatchFailed,
    /// Universe level error
    #[error("universe level error: {0}")]
    LevelError(String),
}

/// Helper: convert a Name to a u64 ID for FVarId construction
fn name_to_id(name: &Name) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    name.hash(&mut hasher);
    hasher.finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::ExprKind;

    #[test]
    fn test_quoted_expr_new() {
        let expr = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let qe = QuotedExpr::new(expr.clone(), ty.clone());

        assert!(
            matches!(qe.expr().kind(), ExprKind::Const(name, _) if name.to_string() == "Nat.zero")
        );
        assert!(
            matches!(qe.expected_type().kind(), ExprKind::Const(name, _) if name.to_string() == "Nat")
        );
    }

    #[test]
    fn test_unquote_state_fresh_var() {
        let mut state = UnquoteState::new();

        let v1 = state.fresh_var();
        let v2 = state.fresh_var();
        let v3 = state.fresh_var();

        assert_eq!(v1.to_string(), "_qq_v0");
        assert_eq!(v2.to_string(), "_qq_v1");
        assert_eq!(v3.to_string(), "_qq_v2");
    }

    #[test]
    fn test_unquote_state_expr_subst() {
        let mut state = UnquoteState::new();

        let name = Name::from_string("x");
        let expr = Expr::const_(Name::from_string("value"), vec![]);

        state.add_expr_subst(name.clone(), expr.clone());

        assert!(state.has_expr(&name));
        assert!(
            state.get_expr(&name).is_some(),
            "get_expr should find substituted expr for 'x'"
        );
    }

    #[test]
    fn test_quote_state_fresh_name() {
        let mut state = QuoteState::new();

        let n1 = state.fresh_name();
        let n2 = state.fresh_name();

        assert_eq!(n1.to_string(), "_q0");
        assert_eq!(n2.to_string(), "_q1");
    }

    #[test]
    fn test_quoted_level() {
        let level = Level::zero();
        let ql = QuotedLevel::new(level.clone());

        assert!(matches!(ql.level(), Level::Zero));
    }

    #[test]
    fn test_qq_error_display() {
        let err = QqError::UnboundAntiquot(Name::from_string("foo"));
        assert_eq!(err.to_string(), "unbound antiquotation variable $foo");

        let err = QqError::PatternMatchFailed;
        assert_eq!(err.to_string(), "Qq pattern match failed");
    }

    #[test]
    fn test_pattern_match_result() {
        let mut bindings = HashMap::new();
        let name = Name::from_string("x");
        let qe = QuotedExpr::new(
            Expr::const_(Name::from_string("val"), vec![]),
            Expr::const_(Name::from_string("Nat"), vec![]),
        );
        bindings.insert(name.clone(), qe);

        let result = QPatternMatch::new(bindings);

        assert!(result.has(&name));
        assert_eq!(result.len(), 1);
        assert!(!result.is_empty());
    }
}
