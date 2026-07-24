// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CodeFolder and CodeVisitor traits for eliminating duplicated Code traversals.
//!
//! ~48 functions across the compiler independently implement full `match code { ... }`
//! traversals over all Code variants. These traits factor out the structural
//! recursion so implementors only override per-variant behavior.
//!
//! - `CodeFolder`: transforms a Code tree (returns a new Code)
//! - `CodeVisitor`: queries a Code tree (returns an accumulated result)
//!
//! Modeled after `ExprFolder`/`ExprVisitor` from clean-kernel.
//!
//! Design: issue #2061
//! Related: designs/2026-02-27-expr-visitor-trait.md (ExprFolder/ExprVisitor precedent)

use crate::lcnf::{Alt, Arg, Cases, Code, FunDecl, LetDecl, LetValue};
use clean_kernel::{Expr, FVarId};

// =============================================================================
// CodeFolder — transform Code trees
// =============================================================================

/// Transform a Code tree by rewriting nodes.
///
/// Override per-variant methods to customize behavior; the default `fold_code`
/// implementation handles structural recursion over all Code variants,
/// including recursive descent into Fun/JoinPoint bodies and Cases alternatives.
///
/// # Example
///
/// ```text
/// struct IdentityFolder;
/// impl CodeFolder for IdentityFolder {}
/// // fold_code returns a clone of the input
/// ```
pub trait CodeFolder {
    // ════════════════════════════════════════════════════════════════════
    // Terminal methods — override for custom behavior at leaves
    // ════════════════════════════════════════════════════════════════════

    /// Transform a `Return(fvar)` node. Default: identity.
    fn fold_return(&mut self, fvar: FVarId) -> Code {
        Code::Return(fvar)
    }

    /// Transform a `Jmp { jp, args }` node. Default: identity.
    fn fold_jmp(&mut self, jp: FVarId, args: Vec<Arg>) -> Code {
        Code::Jmp { jp, args }
    }

    /// Transform an `Unreachable(ty)` node. Default: identity.
    fn fold_unreachable(&mut self, ty: Expr) -> Code {
        Code::Unreachable(ty)
    }

    // ════════════════════════════════════════════════════════════════════
    // Value-level methods — override for LetValue transformations
    // ════════════════════════════════════════════════════════════════════

    /// Transform a `LetValue` within a let binding. Default: identity.
    ///
    /// Override this to transform values within let bindings (e.g., substitution,
    /// ground parameter replacement) without overriding the entire `fold_let`.
    fn fold_let_value(&mut self, value: LetValue) -> LetValue {
        value
    }

    // ════════════════════════════════════════════════════════════════════
    // Structural methods — override to intercept specific node types
    // ════════════════════════════════════════════════════════════════════

    /// Transform a `Let(decl, body)` node. Default: transform the LetValue
    /// via `fold_let_value`, then recurse into body.
    fn fold_let(&mut self, decl: LetDecl, body: Code) -> Code {
        let new_value = self.fold_let_value(decl.value);
        Code::Let(
            LetDecl {
                value: new_value,
                ..decl
            },
            Box::new(self.fold_code(&body)),
        )
    }

    /// Transform a `Fun(decl, body)` node. Default: recurse into both
    /// the function's own body and the continuation.
    fn fold_fun(&mut self, decl: FunDecl, body: Code) -> Code {
        let new_fun_body = self.fold_code(&decl.body);
        let new_decl = FunDecl {
            body: Box::new(new_fun_body),
            ..decl
        };
        Code::Fun(new_decl, Box::new(self.fold_code(&body)))
    }

    /// Transform a `JoinPoint(decl, body)` node. Default: recurse into both
    /// the join point's own body and the continuation.
    fn fold_join_point(&mut self, decl: FunDecl, body: Code) -> Code {
        let new_jp_body = self.fold_code(&decl.body);
        let new_decl = FunDecl {
            body: Box::new(new_jp_body),
            ..decl
        };
        Code::JoinPoint(new_decl, Box::new(self.fold_code(&body)))
    }

    /// Transform a `Cases(cases)` node. Default: recurse into each alternative.
    fn fold_cases(&mut self, cases: Cases) -> Code {
        let new_alts = cases
            .alts
            .into_iter()
            .map(|alt| self.fold_alt(alt))
            .collect();
        Code::Cases(Cases {
            alts: new_alts,
            ..cases
        })
    }

    /// Transform a single case alternative. Default: recurse into body.
    fn fold_alt(&mut self, alt: Alt) -> Alt {
        match alt {
            Alt::Ctor {
                ctor_name,
                params,
                body,
            } => Alt::Ctor {
                ctor_name,
                params,
                body: Box::new(self.fold_code(&body)),
            },
            Alt::Default(body) => Alt::Default(Box::new(self.fold_code(&body))),
        }
    }

    // ════════════════════════════════════════════════════════════════════
    // Main dispatch — rarely overridden
    // ════════════════════════════════════════════════════════════════════

    /// Main entry point. Dispatches to per-variant methods.
    fn fold_code(&mut self, code: &Code) -> Code {
        match code {
            Code::Let(decl, body) => self.fold_let(decl.clone(), *body.clone()),
            Code::Fun(decl, body) => self.fold_fun(decl.clone(), *body.clone()),
            Code::JoinPoint(decl, body) => self.fold_join_point(decl.clone(), *body.clone()),
            Code::Cases(cases) => self.fold_cases(cases.clone()),
            Code::Jmp { jp, args } => self.fold_jmp(*jp, args.clone()),
            Code::Return(fvar) => self.fold_return(*fvar),
            Code::Unreachable(ty) => self.fold_unreachable(ty.clone()),
        }
    }
}

// =============================================================================
// CodeVisitor — query Code trees without transformation
// =============================================================================

/// Query a Code tree without transformation.
///
/// `Result` is the accumulated query result. `combine` merges results from
/// child nodes. Override per-variant methods to inject values at specific nodes.
///
/// For short-circuit boolean queries (e.g., "does this code contain X?"),
/// use `Result = bool` with `combine = |a, b| a || b` and override the
/// leaf method to return `true` at matching nodes.
///
/// # Example
///
/// ```text
/// struct CodeSizeCounter;
/// impl CodeVisitor for CodeSizeCounter {
///     type Result = usize;
///     fn combine(&self, a: usize, b: usize) -> usize { a + b }
///     fn visit_return(&mut self, _fvar: FVarId) -> usize { 1 }
///     fn visit_jmp(&mut self, _jp: FVarId, _args: &[Arg]) -> usize { 1 }
///     fn visit_unreachable(&mut self, _ty: &Expr) -> usize { 1 }
/// }
/// ```
pub trait CodeVisitor {
    type Result: Default;

    /// Merge results from two child sub-expressions.
    fn combine(&self, a: Self::Result, b: Self::Result) -> Self::Result;

    // ════════════════════════════════════════════════════════════════════
    // Terminal methods — override for custom behavior at leaves
    // ════════════════════════════════════════════════════════════════════

    /// Visit a `Return(fvar)` node.
    fn visit_return(&mut self, _fvar: FVarId) -> Self::Result {
        Self::Result::default()
    }

    /// Visit a `Jmp { jp, args }` node.
    fn visit_jmp(&mut self, _jp: FVarId, _args: &[Arg]) -> Self::Result {
        Self::Result::default()
    }

    /// Visit an `Unreachable(ty)` node.
    fn visit_unreachable(&mut self, _ty: &Expr) -> Self::Result {
        Self::Result::default()
    }

    // ════════════════════════════════════════════════════════════════════
    // Structural methods — override to intercept specific node types
    // ════════════════════════════════════════════════════════════════════

    /// Visit a `Let(decl, body)` node. Default: combine a per-let result
    /// with recursive visit of body.
    fn visit_let(&mut self, _decl: &LetDecl, body: &Code) -> Self::Result {
        self.visit_code(body)
    }

    /// Visit a `Fun(decl, body)` node. Default: combine visit of function body
    /// with visit of continuation.
    fn visit_fun(&mut self, decl: &FunDecl, body: &Code) -> Self::Result {
        let rf = self.visit_code(&decl.body);
        let rb = self.visit_code(body);
        self.combine(rf, rb)
    }

    /// Visit a `JoinPoint(decl, body)` node. Default: combine visit of join point
    /// body with visit of continuation.
    fn visit_join_point(&mut self, decl: &FunDecl, body: &Code) -> Self::Result {
        let rj = self.visit_code(&decl.body);
        let rb = self.visit_code(body);
        self.combine(rj, rb)
    }

    /// Visit a `Cases(cases)` node. Default: combine visit results of all alternatives.
    fn visit_cases(&mut self, cases: &Cases) -> Self::Result {
        let mut result = Self::Result::default();
        for alt in &cases.alts {
            let ra = self.visit_alt(alt);
            result = self.combine(result, ra);
        }
        result
    }

    /// Visit a single case alternative. Default: visit body.
    fn visit_alt(&mut self, alt: &Alt) -> Self::Result {
        self.visit_code(alt.body())
    }

    // ════════════════════════════════════════════════════════════════════
    // Main dispatch — rarely overridden
    // ════════════════════════════════════════════════════════════════════

    /// Main entry point. Dispatches to per-variant methods.
    fn visit_code(&mut self, code: &Code) -> Self::Result {
        match code {
            Code::Let(decl, body) => self.visit_let(decl, body),
            Code::Fun(decl, body) => self.visit_fun(decl, body),
            Code::JoinPoint(decl, body) => self.visit_join_point(decl, body),
            Code::Cases(cases) => self.visit_cases(cases),
            Code::Jmp { jp, args } => self.visit_jmp(*jp, args),
            Code::Return(fvar) => self.visit_return(*fvar),
            Code::Unreachable(ty) => self.visit_unreachable(ty),
        }
    }
}

#[cfg(test)]
mod tests;
