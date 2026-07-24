// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Function Inlining for L5CNF
//!
//! Inlines small functions at call sites to eliminate call overhead
//! and enable further optimizations.
//!
//! # Current Heuristics
//!
//! A function is inlined if:
//! 1. Its body size is below the threshold (default: 10 operations)
//! 2. Inline depth limit not exceeded (default: 5)
//!
//! # Future Enhancements (Not Yet Implemented)
//!
//! - Attribute-based inlining (`@[inline]`, `@[always_inline]`, `@[noinline]`)
//! - Specialization for constant arguments
//! - Single-use function inlining regardless of size
//!
//! # Complexity
//!
//! Care is needed to avoid exponential code growth. We use:
//! - Size threshold for automatic inlining
//! - Inline depth limit to prevent infinite expansion
//!
//! Part of #963 - Compiler IR infrastructure.

mod substitute;

use crate::code_visitor::{CodeFolder, CodeVisitor};
use crate::lcnf::{Arg, Cases, Code, Decl, DeclValue, FunDecl, LetDecl, LetValue};
use clean_kernel::{Expr, FVarId};
use std::collections::HashMap;

use substitute::{inline_call, splice_code};

/// Default threshold for function body size (in "operations").
pub const DEFAULT_INLINE_THRESHOLD: usize = 10;

/// Maximum depth for inline expansion.
pub const MAX_INLINE_DEPTH: usize = 5;

/// Maximum recursion depth for inliner traversal to avoid stack overflow.
pub(super) const MAX_INLINE_STACK_DEPTH: usize = 2048;

/// Configuration for the inliner.
#[derive(Clone, Debug)]
pub struct InlineConfig {
    /// Maximum size of function body to inline automatically.
    pub threshold: usize,
    /// Maximum inline depth.
    pub max_depth: usize,
}

impl Default for InlineConfig {
    fn default() -> Self {
        Self {
            threshold: DEFAULT_INLINE_THRESHOLD,
            max_depth: MAX_INLINE_DEPTH,
        }
    }
}

/// Compute the "size" of a Code block for inlining decisions.
///
/// Size is roughly the number of operations in the code.
pub fn code_size(code: &Code) -> usize {
    CodeSizeCounter.visit_code(code)
}

/// CodeVisitor that counts the number of nodes in a Code tree.
struct CodeSizeCounter;

impl CodeVisitor for CodeSizeCounter {
    type Result = usize;

    fn combine(&self, a: usize, b: usize) -> usize {
        a + b
    }

    fn visit_let(&mut self, _decl: &LetDecl, body: &Code) -> usize {
        1 + self.visit_code(body)
    }

    fn visit_fun(&mut self, decl: &FunDecl, body: &Code) -> usize {
        1 + self.visit_code(&decl.body) + self.visit_code(body)
    }

    fn visit_join_point(&mut self, decl: &FunDecl, body: &Code) -> usize {
        1 + self.visit_code(&decl.body) + self.visit_code(body)
    }

    fn visit_cases(&mut self, cases: &Cases) -> usize {
        1 + cases
            .alts
            .iter()
            .map(|alt| self.visit_alt(alt))
            .sum::<usize>()
    }

    fn visit_return(&mut self, _fvar: FVarId) -> usize {
        1
    }

    fn visit_jmp(&mut self, _jp: FVarId, _args: &[Arg]) -> usize {
        1
    }

    fn visit_unreachable(&mut self, _ty: &Expr) -> usize {
        1
    }
}

/// Context for inlining operations.
pub(super) struct InlineContext {
    /// Configuration.
    pub(super) config: InlineConfig,
    /// Available local functions (fvar_id -> FunDecl).
    pub(super) local_funs: HashMap<FVarId, FunDecl>,
    /// Current inline depth.
    pub(super) depth: usize,
    /// Next fresh FVarId for substitution.
    pub(super) next_fvar: u64,
}

impl InlineContext {
    fn new(config: &InlineConfig) -> Self {
        Self {
            config: config.clone(),
            local_funs: HashMap::new(),
            depth: 0,
            next_fvar: 1_000_000, // Start high to avoid conflicts
        }
    }

    pub(super) fn fresh_fvar(&mut self) -> FVarId {
        let id = FVarId::new(self.next_fvar);
        self.next_fvar += 1;
        id
    }

    /// Check if a function should be inlined.
    fn should_inline(&self, fun: &FunDecl) -> bool {
        if self.depth >= self.config.max_depth {
            return false;
        }
        let size = code_size(&fun.body);
        size <= self.config.threshold
    }
}

/// Inline functions in a declaration.
///
/// Uses default configuration.
pub fn inline_functions(decl: &Decl) -> Decl {
    inline_functions_with_config(decl, &InlineConfig::default())
}

/// Inline functions with custom configuration.
pub fn inline_functions_with_config(decl: &Decl, config: &InlineConfig) -> Decl {
    let body = match &decl.body {
        DeclValue::Code(code) => {
            let mut ctx = InlineContext::new(config);
            DeclValue::Code(Box::new(inline_in_code(&mut ctx, code)))
        }
        DeclValue::Extern(attr) => DeclValue::Extern(attr.clone()),
    };

    Decl {
        name: decl.name.clone(),
        level_params: decl.level_params.clone(),
        ty: decl.ty.clone(),
        params: decl.params.clone(),
        body,
        recursive: decl.recursive,
    }
}

/// Inline functions in a Code block directly.
pub fn inline_functions_in_code(code: &Code, config: &InlineConfig) -> Code {
    let mut ctx = InlineContext::new(config);
    inline_in_code(&mut ctx, code)
}

/// CodeFolder that traverses code, inlining small function calls.
///
/// Overrides `fold_let` (to attempt inlining at let-bindings) and `fold_fun`
/// (to register/unregister local functions for inlining). All other Code
/// variants use default structural recursion from `CodeFolder`.
struct InlineFolder<'a> {
    ctx: &'a mut InlineContext,
}

impl CodeFolder for InlineFolder<'_> {
    fn fold_let(&mut self, decl: LetDecl, body: Code) -> Code {
        if let Some(inlined) = try_inline_let(self.ctx, &decl) {
            let new_body = self.fold_code(&body);
            splice_code(inlined, decl.fvar_id, new_body)
        } else {
            Code::Let(decl, Box::new(self.fold_code(&body)))
        }
    }

    fn fold_fun(&mut self, decl: FunDecl, body: Code) -> Code {
        self.ctx.local_funs.insert(decl.fvar_id, decl.clone());
        let new_fun_body = self.fold_code(&decl.body);
        let new_decl = FunDecl {
            body: Box::new(new_fun_body),
            ..decl
        };
        let new_body = self.fold_code(&body);
        self.ctx.local_funs.remove(&new_decl.fvar_id);
        Code::Fun(new_decl, Box::new(new_body))
    }
}

/// Inline functions in a Code block.
fn inline_in_code(ctx: &mut InlineContext, code: &Code) -> Code {
    let mut folder = InlineFolder { ctx };
    folder.fold_code(code)
}

/// Try to inline a let-binding that calls a local function.
fn try_inline_let(ctx: &mut InlineContext, decl: &LetDecl) -> Option<Code> {
    // Check if this is a local function call
    let (fvar, args) = match &decl.value {
        LetValue::FVar { fvar, args } => (fvar, args),
        _ => return None,
    };

    // Look up the function (clone to avoid borrow issues)
    let fun = ctx.local_funs.get(fvar)?.clone();
    if fun.params.len() != args.len() {
        return None;
    }
    if args.iter().any(|arg| !matches!(arg, Arg::FVar(_))) {
        return None;
    }

    // Check if it should be inlined
    if !ctx.should_inline(&fun) {
        return None;
    }

    // Inline: substitute parameters with arguments
    ctx.depth += 1;
    let result = inline_call(ctx, &fun, args);
    ctx.depth -= 1;

    Some(result)
}

#[cfg(test)]
mod tests;
