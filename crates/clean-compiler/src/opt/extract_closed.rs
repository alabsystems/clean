// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ExtractClosed — Extract closed subexpressions into top-level declarations.
//!
//! A closed subexpression is a let-bound value that has no free variables
//! (all referenced FVarIds are bound within the value itself or the value
//! is a literal/erased/constant with only constant references). By extracting
//! these into top-level declarations, we:
//!
//! 1. **Enable sharing**: Identical closed values across declarations become
//!    references to the same top-level definition.
//! 2. **Reduce code size**: The closed expression is defined once, referenced
//!    many times.
//! 3. **Improve cache behavior**: Closed constants are evaluated once at
//!    module initialization.
//!
//! # Algorithm
//!
//! For each let-binding `let x : T := v; body`:
//!   1. Compute free variables of `v` relative to the declaration's parameters
//!      and all enclosing let-bindings.
//!   2. If `v` has **no** free variables (it is "closed"), extract it:
//!      - Create a new top-level declaration `_closed.N` with no parameters
//!        and body `return x` where `x` is bound to `v`.
//!      - Replace the original let-binding with:
//!        `let x : T := _closed.N (); body`
//!   3. Otherwise, keep the let-binding as-is and recurse into `body`.
//!
//! # Lean 4 Reference
//!
//! Based on `Lean.Compiler.LCNF.ExtractClosed` in
//! `src/Lean/Compiler/LCNF/Passes/ExtractClosed.lean`.
//!
//! Part of #1084 — ExtractClosed compiler pass.

use crate::lcnf::{Alt, Arg, Cases, Code, Decl, DeclValue, FunDecl, LetDecl, LetValue};
use clean_kernel::{BigNat, FVarId, Literal, Name};
use std::collections::HashSet;

/// Result of extracting closed subexpressions from a declaration.
#[derive(Debug, Clone)]
pub struct ExtractResult {
    /// The transformed declaration with closed values replaced by references.
    pub decl: Decl,
    /// Newly created top-level declarations for extracted closed values.
    pub extracted: Vec<Decl>,
}

/// Configuration for the ExtractClosed pass.
#[derive(Debug, Clone)]
pub struct ExtractClosedConfig {
    /// Prefix for generated declaration names.
    pub prefix: String,
}

impl Default for ExtractClosedConfig {
    fn default() -> Self {
        Self {
            prefix: "_closed".to_string(),
        }
    }
}

/// Mutable state for the extraction pass.
struct ExtractState {
    /// Counter for generating unique auxiliary declaration names.
    next_id: u32,
    /// Name prefix for extracted declarations.
    prefix: String,
    /// Accumulated extracted top-level declarations.
    extracted: Vec<Decl>,
}

impl ExtractState {
    fn new(prefix: &str) -> Self {
        Self {
            next_id: 0,
            prefix: prefix.to_string(),
            extracted: Vec::new(),
        }
    }

    /// Generate a fresh name for an extracted declaration.
    fn fresh_name(&mut self) -> Name {
        let id = self.next_id;
        self.next_id += 1;
        Name::from_string(&format!("{}.{}", self.prefix, id))
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Free variable check for LetValue
// ════════════════════════════════════════════════════════════════════════════

/// Determine whether a `LetValue` is closed (has no free variables).
///
/// A value is closed if every FVarId it references is in `bound`.
fn is_let_value_closed(value: &LetValue, bound: &HashSet<FVarId>) -> bool {
    match value {
        // Literals and erased terms are always closed.
        LetValue::Lit(_) | LetValue::Erased => true,

        // Projections reference a single structure FVar.
        LetValue::Proj { structure, .. } => bound.contains(structure),

        // Const and Ctor reference only their arguments.
        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => {
            args.iter().all(|arg| is_arg_closed(arg, bound))
        }

        // FVar application references the function FVar and its arguments.
        LetValue::FVar { fvar, args } => {
            bound.contains(fvar) && args.iter().all(|arg| is_arg_closed(arg, bound))
        }

        // Reuse references a slot and arguments.
        LetValue::Reuse { slot, args, .. } => {
            bound.contains(slot) && args.iter().all(|arg| is_arg_closed(arg, bound))
        }
    }
}

/// Check if an argument is closed with respect to `bound`.
fn is_arg_closed(arg: &Arg, bound: &HashSet<FVarId>) -> bool {
    match arg {
        Arg::FVar(fvar) => bound.contains(fvar),
        // Erased, Type, and Index arguments don't contain FVar references
        // that would make the value "open" in the LCNF sense. Type arguments
        // contain kernel Exprs which may have FVars, but those are type-level
        // and erased at runtime — we treat them as closed for extraction.
        Arg::Erased | Arg::Type(_) | Arg::Index(_) => true,
    }
}

/// Decide whether a closed value is worth extracting.
///
/// Extracting tiny immediates such as small Nat literals, erased values, or
/// nullary constructors just adds an auxiliary declaration and an extra call.
/// Keep those local; reserve extraction for values with real sharing/code-size
/// upside such as large literals or compound closed applications.
fn should_extract_closed_value(value: &LetValue) -> bool {
    match value {
        LetValue::Lit(Literal::Nat(BigNat::Small(_))) | LetValue::Erased => false,
        LetValue::Lit(Literal::Nat(BigNat::Big(_))) => true,
        LetValue::Lit(Literal::String(s)) => !s.is_empty(),
        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => !args.is_empty(),
        LetValue::Proj { .. } | LetValue::FVar { .. } | LetValue::Reuse { .. } => true,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Core extraction logic
// ════════════════════════════════════════════════════════════════════════════

/// Extract closed subexpressions from a single declaration.
///
/// Returns the transformed declaration and any new top-level declarations
/// created for extracted closed values.
pub fn extract_closed(decl: &Decl, config: &ExtractClosedConfig) -> ExtractResult {
    let mut state = ExtractState::new(&config.prefix);

    // The declaration's parameters are the initial set of bound variables.
    let bound: HashSet<FVarId> = decl.params.iter().map(|p| p.fvar_id).collect();

    let body = match &decl.body {
        DeclValue::Code(code) => {
            let transformed = extract_code(code, &bound, &mut state);
            DeclValue::Code(Box::new(transformed))
        }
        DeclValue::Extern(attr) => DeclValue::Extern(attr.clone()),
    };

    let new_decl = Decl {
        name: decl.name.clone(),
        level_params: decl.level_params.clone(),
        ty: decl.ty.clone(),
        params: decl.params.clone(),
        body,
        recursive: decl.recursive,
    };

    ExtractResult {
        decl: new_decl,
        extracted: state.extracted,
    }
}

/// Extract a closed let-binding into a top-level declaration.
fn extract_let_binding(
    decl: &LetDecl,
    body: &Code,
    bound: &HashSet<FVarId>,
    state: &mut ExtractState,
) -> Code {
    let aux_name = state.fresh_name();
    let aux_fvar = decl.fvar_id;

    let aux_decl = Decl {
        name: aux_name.clone(),
        level_params: vec![],
        ty: decl.ty.clone(),
        params: vec![],
        body: DeclValue::Code(Box::new(Code::Let(
            decl.clone(),
            Box::new(Code::Return(aux_fvar)),
        ))),
        recursive: false,
    };
    state.extracted.push(aux_decl);

    let replacement = LetDecl {
        fvar_id: decl.fvar_id,
        name: decl.name.clone(),
        ty: decl.ty.clone(),
        value: LetValue::Const {
            name: aux_name,
            levels: vec![],
            args: vec![],
        },
    };

    let mut new_bound = bound.clone();
    new_bound.insert(decl.fvar_id);
    Code::Let(replacement, Box::new(extract_code(body, &new_bound, state)))
}

/// Recurse into a Fun or JoinPoint body, extending bound set with params.
fn extract_fun_like(
    fun_decl: &FunDecl,
    body: &Code,
    is_fun: bool,
    bound: &HashSet<FVarId>,
    state: &mut ExtractState,
) -> Code {
    let mut param_bound = bound.clone();
    param_bound.insert(fun_decl.fvar_id);
    for param in &fun_decl.params {
        param_bound.insert(param.fvar_id);
    }
    let new_inner = extract_code(&fun_decl.body, &param_bound, state);
    let new_decl = FunDecl {
        fvar_id: fun_decl.fvar_id,
        name: fun_decl.name.clone(),
        params: fun_decl.params.clone(),
        ty: fun_decl.ty.clone(),
        body: Box::new(new_inner),
    };
    let mut new_bound = bound.clone();
    new_bound.insert(fun_decl.fvar_id);
    let cont = Box::new(extract_code(body, &new_bound, state));
    if is_fun {
        Code::Fun(new_decl, cont)
    } else {
        Code::JoinPoint(new_decl, cont)
    }
}

/// Extract closed subexpressions from a code block.
fn extract_code(code: &Code, bound: &HashSet<FVarId>, state: &mut ExtractState) -> Code {
    match code {
        Code::Let(decl, body) => {
            let is_closed = is_let_value_closed(&decl.value, &HashSet::new());
            if is_closed {
                if should_extract_closed_value(&decl.value) {
                    extract_let_binding(decl, body, bound, state)
                } else {
                    let mut new_bound = bound.clone();
                    new_bound.insert(decl.fvar_id);
                    Code::Let(
                        decl.clone(),
                        Box::new(extract_code(body, &new_bound, state)),
                    )
                }
            } else {
                let mut new_bound = bound.clone();
                new_bound.insert(decl.fvar_id);
                Code::Let(
                    decl.clone(),
                    Box::new(extract_code(body, &new_bound, state)),
                )
            }
        }
        Code::Fun(fun_decl, body) => extract_fun_like(fun_decl, body, true, bound, state),
        Code::JoinPoint(jp_decl, body) => extract_fun_like(jp_decl, body, false, bound, state),
        Code::Cases(cases) => {
            let new_alts: Vec<Alt> = cases
                .alts
                .iter()
                .map(|alt| match alt {
                    Alt::Ctor {
                        ctor_name,
                        params,
                        body,
                    } => {
                        let mut alt_bound = bound.clone();
                        for param in params {
                            alt_bound.insert(param.fvar_id);
                        }
                        Alt::Ctor {
                            ctor_name: ctor_name.clone(),
                            params: params.clone(),
                            body: Box::new(extract_code(body, &alt_bound, state)),
                        }
                    }
                    Alt::Default(body) => Alt::Default(Box::new(extract_code(body, bound, state))),
                })
                .collect();
            Code::Cases(Cases {
                type_name: cases.type_name.clone(),
                result_type: cases.result_type.clone(),
                scrutinee: cases.scrutinee,
                alts: new_alts,
            })
        }
        Code::Return(fvar) => Code::Return(*fvar),
        Code::Jmp { jp, args } => Code::Jmp {
            jp: *jp,
            args: args.clone(),
        },
        Code::Unreachable(expr) => Code::Unreachable(expr.clone()),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Public batch API
// ════════════════════════════════════════════════════════════════════════════

/// Extract closed subexpressions from multiple declarations.
///
/// Each declaration is processed independently. Extracted auxiliary
/// declarations are appended after the originating declaration, preserving
/// definition-before-use ordering.
pub fn extract_closed_decls(decls: &[Decl], config: &ExtractClosedConfig) -> Vec<Decl> {
    let mut result = Vec::new();

    for decl in decls {
        let extract_result = extract_closed(decl, config);
        result.push(extract_result.decl);
        result.extend(extract_result.extracted);
    }

    result
}

/// Extract closed subexpressions with default configuration.
pub fn extract_closed_default(decl: &Decl) -> ExtractResult {
    extract_closed(decl, &ExtractClosedConfig::default())
}
