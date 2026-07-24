// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! FindJoinPoints - Convert local functions to join points
//!
//! Identifies local functions that can be converted to join points for
//! more efficient compilation. A function can become a join point if:
//!
//! 1. It is always fully applied (no partial applications)
//! 2. It is always called in tail position (result is immediately returned)
//! 3. It does not escape (not passed as argument or returned)
//!
//! # Example
//!
//! ```text
//! fun loop (n : Nat) : Nat := ...
//! let _1 := loop 10
//! return _1
//! ```
//!
//! If `loop` is only called as above (tail call pattern), it becomes:
//!
//! ```text
//! jp loop (n : Nat) : Nat := ...
//! jmp loop 10
//! ```
//!
//! Part of #963 - Compiler IR infrastructure.

use crate::lcnf::{Alt, Arg, Cases, Code, Decl, DeclValue, FunDecl, LetValue};
use clean_kernel::FVarId;

/// Analysis results for a local function's usage patterns.
#[derive(Debug, Clone)]
struct FunAnalysis {
    /// The function is always called with all arguments (no partial application).
    always_fully_applied: bool,
    /// The function is always called in tail position.
    always_tail_called: bool,
    /// The function escapes (passed as argument, returned, or used non-call).
    escapes: bool,
}

impl FunAnalysis {
    fn new() -> Self {
        Self {
            always_fully_applied: true,
            always_tail_called: true,
            escapes: false,
        }
    }

    /// Check if this function can be converted to a join point.
    ///
    /// A function can become a join point if:
    /// - It is always tail-called (result immediately returned)
    /// - It is always fully applied (no partial applications)
    /// - It does not escape (not passed as argument or returned)
    fn can_be_join_point(&self) -> bool {
        self.always_tail_called && self.always_fully_applied && !self.escapes
    }
}

/// Analyze how a local function is used in its body.
///
/// Returns analysis indicating whether the function can become a join point.
fn analyze_fun_usage(body: &Code, target: FVarId, expected_arity: usize) -> FunAnalysis {
    let mut analysis = FunAnalysis::new();
    analyze_code(&mut analysis, body, target, expected_arity, true);
    analysis
}

/// Recursively analyze code for function usage.
///
/// `in_tail` indicates whether we're currently in tail position.
fn analyze_code(
    analysis: &mut FunAnalysis,
    code: &Code,
    target: FVarId,
    expected_arity: usize,
    in_tail: bool,
) {
    match code {
        Code::Let(decl, body) => {
            // Check if this is a call to target followed by return
            // A call is only a valid tail call if:
            // 1. We're in the outer tail position (in_tail is true)
            // 2. The local pattern is `let x = target(...); return x`
            let has_tail_pattern = if let LetValue::FVar { fvar, args } = &decl.value {
                if *fvar == target {
                    // Check arity
                    if args.len() != expected_arity {
                        analysis.always_fully_applied = false;
                    }
                    // Check if immediately returned
                    if let Code::Return(ret_var) = body.as_ref() {
                        *ret_var == decl.fvar_id
                    } else {
                        false
                    }
                } else {
                    false
                }
            } else {
                false
            };

            // Only a true tail call if we're in tail position AND have the tail pattern
            let is_tail_call = in_tail && has_tail_pattern;

            // Check for non-tail calls to target in the value
            check_value_for_escapes(analysis, &decl.value, target, expected_arity, is_tail_call);

            // Continue analyzing body (not in tail position if we have a let)
            if !is_tail_call {
                analyze_code(analysis, body, target, expected_arity, in_tail);
            }
        }

        Code::Fun(fdecl, body) => {
            // Check function body for references to target
            analyze_code(analysis, &fdecl.body, target, expected_arity, false);
            // Continue with outer body
            analyze_code(analysis, body, target, expected_arity, in_tail);
        }

        Code::JoinPoint(fdecl, body) => {
            // Check join point body for references to target
            // Like nested Fun, calls from inside a JoinPoint are NOT tail calls
            // for the outer scope we're analyzing
            analyze_code(analysis, &fdecl.body, target, expected_arity, false);
            // Continue with outer body
            analyze_code(analysis, body, target, expected_arity, in_tail);
        }

        Code::Cases(cases) => {
            // Check if scrutinee is the target (escape)
            if cases.scrutinee == target {
                analysis.escapes = true;
            }
            // Check each alternative
            for alt in &cases.alts {
                let alt_body = match alt {
                    Alt::Ctor { body, .. } => body,
                    Alt::Default(body) => body,
                };
                // Case alternatives are in tail position if the case is
                analyze_code(analysis, alt_body, target, expected_arity, in_tail);
            }
        }

        Code::Jmp { jp, args } => {
            // Check if target is passed as argument (escape)
            for arg in args {
                if let Arg::FVar(fvar) = arg {
                    if *fvar == target {
                        analysis.escapes = true;
                    }
                }
            }
            // Jump to target is a tail call if we're in tail position
            if *jp == target && !in_tail {
                analysis.always_tail_called = false;
            }
        }

        Code::Return(ret_var) => {
            // If returning target itself, it escapes
            if *ret_var == target {
                analysis.escapes = true;
            }
        }

        Code::Unreachable(_) => {
            // No uses here
        }
    }
}

/// Check a LetValue for escaping uses of target.
fn check_value_for_escapes(
    analysis: &mut FunAnalysis,
    value: &LetValue,
    target: FVarId,
    expected_arity: usize,
    is_known_call: bool,
) {
    match value {
        LetValue::FVar { fvar, args } if *fvar == target => {
            if !is_known_call {
                // Non-tail call
                analysis.always_tail_called = false;
                if args.len() != expected_arity {
                    analysis.always_fully_applied = false;
                }
            }
        }

        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => {
            for arg in args {
                if let Arg::FVar(fvar) = arg {
                    if *fvar == target {
                        analysis.escapes = true;
                    }
                }
            }
        }

        LetValue::FVar { args, .. } => {
            for arg in args {
                if let Arg::FVar(fvar) = arg {
                    if *fvar == target {
                        analysis.escapes = true;
                    }
                }
            }
        }

        LetValue::Proj { structure, .. } => {
            if *structure == target {
                analysis.escapes = true;
            }
        }

        LetValue::Lit(_) | LetValue::Erased => {
            // No escapes
        }

        LetValue::Reuse { slot, args, .. } => {
            if *slot == target {
                analysis.escapes = true;
            }
            for arg in args {
                if let Arg::FVar(fvar) = arg {
                    if *fvar == target {
                        analysis.escapes = true;
                    }
                }
            }
        }
    }
}

/// Find and convert eligible local functions to join points in a declaration.
pub fn find_join_points(decl: &Decl) -> Decl {
    let new_body = match &decl.body {
        DeclValue::Code(code) => DeclValue::Code(Box::new(find_join_points_in_code(code))),
        other => other.clone(),
    };

    Decl {
        name: decl.name.clone(),
        level_params: decl.level_params.clone(),
        ty: decl.ty.clone(),
        params: decl.params.clone(),
        body: new_body,
        recursive: decl.recursive,
    }
}

/// Find and convert eligible local functions to join points in code.
pub fn find_join_points_in_code(code: &Code) -> Code {
    match code {
        Code::Let(decl, body) => {
            let new_body = find_join_points_in_code(body);
            Code::Let(decl.clone(), Box::new(new_body))
        }

        Code::Fun(fdecl, body) => {
            // First, recursively process the function body
            let new_fun_body = find_join_points_in_code(&fdecl.body);
            let new_fdecl = FunDecl {
                fvar_id: fdecl.fvar_id,
                name: fdecl.name.clone(),
                params: fdecl.params.clone(),
                ty: fdecl.ty.clone(),
                body: Box::new(new_fun_body),
            };

            // Recursively process the continuation body
            let new_body = find_join_points_in_code(body);

            // Analyze if this function can become a join point
            let analysis = analyze_fun_usage(&new_body, fdecl.fvar_id, fdecl.params.len());

            if analysis.can_be_join_point() {
                // Convert to join point and transform calls to jumps
                let transformed_body = transform_calls_to_jumps(&new_body, fdecl.fvar_id);
                Code::JoinPoint(new_fdecl, Box::new(transformed_body))
            } else {
                Code::Fun(new_fdecl, Box::new(new_body))
            }
        }

        Code::JoinPoint(fdecl, body) => {
            // Recursively process
            let new_fun_body = find_join_points_in_code(&fdecl.body);
            let new_fdecl = FunDecl {
                fvar_id: fdecl.fvar_id,
                name: fdecl.name.clone(),
                params: fdecl.params.clone(),
                ty: fdecl.ty.clone(),
                body: Box::new(new_fun_body),
            };
            let new_body = find_join_points_in_code(body);
            Code::JoinPoint(new_fdecl, Box::new(new_body))
        }

        Code::Cases(cases) => {
            let new_alts: Vec<Alt> = cases
                .alts
                .iter()
                .map(|alt| match alt {
                    Alt::Ctor {
                        ctor_name,
                        params,
                        body,
                    } => Alt::Ctor {
                        ctor_name: ctor_name.clone(),
                        params: params.clone(),
                        body: Box::new(find_join_points_in_code(body)),
                    },
                    Alt::Default(body) => Alt::Default(Box::new(find_join_points_in_code(body))),
                })
                .collect();

            Code::Cases(Cases {
                type_name: cases.type_name.clone(),
                result_type: cases.result_type.clone(),
                scrutinee: cases.scrutinee,
                alts: new_alts,
            })
        }

        // Terminal nodes - no changes
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => code.clone(),
    }
}

/// Rebuild a FunDecl with a transformed body.
fn remap_fdecl(fdecl: &FunDecl, new_body: Code) -> FunDecl {
    FunDecl {
        fvar_id: fdecl.fvar_id,
        name: fdecl.name.clone(),
        params: fdecl.params.clone(),
        ty: fdecl.ty.clone(),
        body: Box::new(new_body),
    }
}

/// Transform calls to a function (now join point) into jumps.
///
/// Pattern: `let _x := f args; return _x` becomes `jmp f args`
fn transform_calls_to_jumps(code: &Code, jp_fvar: FVarId) -> Code {
    match code {
        Code::Let(decl, body) => {
            // Check for the tail call pattern
            if let LetValue::FVar { fvar, args } = &decl.value {
                if *fvar == jp_fvar {
                    if let Code::Return(ret_var) = body.as_ref() {
                        if *ret_var == decl.fvar_id {
                            return Code::Jmp {
                                jp: jp_fvar,
                                args: args.clone(),
                            };
                        }
                    }
                }
            }
            let new_body = transform_calls_to_jumps(body, jp_fvar);
            Code::Let(decl.clone(), Box::new(new_body))
        }

        Code::Fun(fdecl, body) => {
            let new_fdecl = remap_fdecl(fdecl, transform_calls_to_jumps(&fdecl.body, jp_fvar));
            Code::Fun(new_fdecl, Box::new(transform_calls_to_jumps(body, jp_fvar)))
        }

        Code::JoinPoint(fdecl, body) => {
            let new_fdecl = remap_fdecl(fdecl, transform_calls_to_jumps(&fdecl.body, jp_fvar));
            Code::JoinPoint(new_fdecl, Box::new(transform_calls_to_jumps(body, jp_fvar)))
        }

        Code::Cases(cases) => {
            let new_alts: Vec<Alt> = cases
                .alts
                .iter()
                .map(|alt| match alt {
                    Alt::Ctor {
                        ctor_name,
                        params,
                        body,
                    } => Alt::Ctor {
                        ctor_name: ctor_name.clone(),
                        params: params.clone(),
                        body: Box::new(transform_calls_to_jumps(body, jp_fvar)),
                    },
                    Alt::Default(body) => {
                        Alt::Default(Box::new(transform_calls_to_jumps(body, jp_fvar)))
                    }
                })
                .collect();

            Code::Cases(Cases {
                type_name: cases.type_name.clone(),
                result_type: cases.result_type.clone(),
                scrutinee: cases.scrutinee,
                alts: new_alts,
            })
        }

        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => code.clone(),
    }
}

#[cfg(test)]
mod tests;
