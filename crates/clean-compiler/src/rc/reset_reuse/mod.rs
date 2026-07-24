// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reset/Reuse Optimization for Reference Counting
//!
//! Implements the "resurrection hypothesis" from "Counting Immutable Beans":
//! Many objects die just before creating an object of the same kind.
//!
//! # Examples
//!
//! - Binary tree insertion: destroy old node, create new node
//! - List map: destroy head cell, create new head cell
//! - Compiler passes: rewrite AST nodes
//!
//! # Algorithm
//!
//! Three-function transformation: R, D, S
//! - R: Traverse looking for case statements
//! - D: Find last use of scrutinee in each branch
//! - S: Substitute compatible constructors with reuse
//!
//! Part of #963 - Compiler IR infrastructure.

mod d_transform;
pub(crate) mod s_transform;

use super::FVarIdAllocator;
use crate::lcnf::{Alt, Arg, Cases, Code, Decl, DeclValue, FunDecl, LetValue};
use crate::rc::borrow::BorrowMap;
use clean_kernel::{Environment, FVarId};
use d_transform::{d_transform, DCtx};
use std::collections::HashSet;

/// Configuration for reset/reuse pass.
#[derive(Clone, Debug, Default)]
pub struct ResetReuseConfig {
    /// Allow cross-family reuse (e.g., PSigma.mk → Prod.mk).
    pub cross_family: bool,
}

/// Apply reset/reuse optimization to a declaration (no borrow info).
pub fn reset_reuse(decl: &Decl) -> Decl {
    let empty_borrow = BorrowMap::new();
    reset_reuse_with_config(decl, &ResetReuseConfig::default(), &empty_borrow, None)
}

/// Apply reset/reuse optimization with custom configuration and borrow info.
///
/// Bug 22 fix: accepts `borrow_map` so classify_use can distinguish borrowed
/// vs owned parameters, matching Lean 4 ResetReuse.lean:147-167.
///
/// Part of #2081: accepts `env` for layout-based cross-family compatibility
/// checks, matching Lean 4's `mayReuse` (constructor layout comparison).
pub fn reset_reuse_with_config(
    decl: &Decl,
    config: &ResetReuseConfig,
    borrow_map: &BorrowMap,
    env: Option<&Environment>,
) -> Decl {
    let mut alloc = FVarIdAllocator::for_reset_reuse();
    let body = match &decl.body {
        DeclValue::Code(code) => {
            // Pass 1: Same family only (env not needed — same-name check suffices)
            let mut already_found = HashSet::new();
            let code1 = r_transform(
                code,
                &mut already_found,
                false,
                &mut alloc,
                borrow_map,
                None,
            );

            // Pass 2: Cross-family if enabled (needs env for layout comparison)
            // Bug 6 fix: collect existing resets from pass 1 as initial already_found
            // (Lean 4: ResetReuse.lean:280-288)
            let final_code = if config.cross_family {
                let mut already_found2 = collect_resets(&code1);
                r_transform(
                    &code1,
                    &mut already_found2,
                    true,
                    &mut alloc,
                    borrow_map,
                    env,
                )
            } else {
                code1
            };

            DeclValue::Code(Box::new(final_code))
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

/// Apply reset/reuse optimization to a Code block directly (no borrow info).
pub fn reset_reuse_in_code(code: &Code) -> Code {
    let empty_borrow = BorrowMap::new();
    let mut alloc = FVarIdAllocator::for_reset_reuse();
    let mut already_found = HashSet::new();
    r_transform(
        code,
        &mut already_found,
        false,
        &mut alloc,
        &empty_borrow,
        None,
    )
}

/// Collect all variables that are already targets of `_reset` operations.
///
/// Used to initialize `already_found` for the cross-family (relaxed) pass,
/// preventing double-reset. Matches Lean 4's `collectResets` in
/// `ResetReuse.lean:291-301`.
fn collect_resets(code: &Code) -> HashSet<FVarId> {
    let mut resets = HashSet::new();
    collect_resets_inner(code, &mut resets);
    resets
}

fn collect_resets_inner(code: &Code, resets: &mut HashSet<FVarId>) {
    match code {
        Code::Let(decl, body) => {
            // Check if this is a _reset operation: let w := _reset(x)
            if let LetValue::Const { name, args, .. } = &decl.value {
                if name.to_string().ends_with(super::pseudo_op::RESET) {
                    if let Some(Arg::FVar(target)) = args.first() {
                        resets.insert(*target);
                    }
                }
            }
            collect_resets_inner(body, resets);
        }
        Code::Fun(fun_decl, body) | Code::JoinPoint(fun_decl, body) => {
            collect_resets_inner(&fun_decl.body, resets);
            collect_resets_inner(body, resets);
        }
        Code::Cases(cases) => {
            for alt in &cases.alts {
                match alt {
                    Alt::Ctor { body, .. } => collect_resets_inner(body, resets),
                    Alt::Default(body) => collect_resets_inner(body, resets),
                }
            }
        }
        Code::Return(_) | Code::Jmp { .. } | Code::Unreachable(_) => {}
    }
}

/// R: Top-level recursion looking for case statements.
fn r_transform(
    code: &Code,
    already_found: &mut HashSet<FVarId>,
    cross_family: bool,
    alloc: &mut FVarIdAllocator,
    borrow_map: &BorrowMap,
    env: Option<&Environment>,
) -> Code {
    match code {
        Code::Cases(cases) => {
            // Check if scrutinee was already found BEFORE inserting
            // (Lean 4: ResetReuse.lean:256-257 — check then insert via withReader)
            let scrutinee_already_found = already_found.contains(&cases.scrutinee);

            // Insert scrutinee to prevent double-reset in nested cases
            already_found.insert(cases.scrutinee);

            let new_alts: Vec<Alt> = cases
                .alts
                .iter()
                .map(|alt| {
                    // Bug 23 fix: clone already_found for each branch to prevent
                    // cross-branch leakage. Lean 4 uses withReader to scope each
                    // branch independently (ResetReuse.lean:256-257).
                    let mut branch_found = already_found.clone();

                    match alt {
                        Alt::Ctor {
                            ctor_name,
                            params,
                            body,
                        } => {
                            let n = params.len();

                            // Bug 8 fix: skip scalar constructors (0 fields = no heap alloc).
                            let is_scalar = n == 0;

                            let transformed_body = r_transform(
                                body,
                                &mut branch_found,
                                cross_family,
                                alloc,
                                borrow_map,
                                env,
                            );

                            let final_body = if is_scalar || scrutinee_already_found {
                                transformed_body
                            } else {
                                let ctx = DCtx {
                                    x: cases.scrutinee,
                                    n,
                                    source_ctor: ctor_name,
                                    cross_family,
                                    borrow_map,
                                    env,
                                };
                                d_transform(&ctx, &transformed_body, &mut branch_found, alloc)
                            };

                            Alt::Ctor {
                                ctor_name: ctor_name.clone(),
                                params: params.clone(),
                                body: Box::new(final_body),
                            }
                        }
                        Alt::Default(body) => Alt::Default(Box::new(r_transform(
                            body,
                            &mut branch_found,
                            cross_family,
                            alloc,
                            borrow_map,
                            env,
                        ))),
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

        Code::Let(decl, body) => Code::Let(
            decl.clone(),
            Box::new(r_transform(
                body,
                already_found,
                cross_family,
                alloc,
                borrow_map,
                env,
            )),
        ),

        Code::Fun(fun_decl, body) => {
            let new_fun_body = r_transform(
                &fun_decl.body,
                already_found,
                cross_family,
                alloc,
                borrow_map,
                env,
            );
            let new_decl = FunDecl {
                fvar_id: fun_decl.fvar_id,
                name: fun_decl.name.clone(),
                params: fun_decl.params.clone(),
                ty: fun_decl.ty.clone(),
                body: Box::new(new_fun_body),
            };
            Code::Fun(
                new_decl,
                Box::new(r_transform(
                    body,
                    already_found,
                    cross_family,
                    alloc,
                    borrow_map,
                    env,
                )),
            )
        }

        Code::JoinPoint(jp_decl, body) => {
            let new_jp_body = r_transform(
                &jp_decl.body,
                already_found,
                cross_family,
                alloc,
                borrow_map,
                env,
            );
            let new_decl = FunDecl {
                fvar_id: jp_decl.fvar_id,
                name: jp_decl.name.clone(),
                params: jp_decl.params.clone(),
                ty: jp_decl.ty.clone(),
                body: Box::new(new_jp_body),
            };
            Code::JoinPoint(
                new_decl,
                Box::new(r_transform(
                    body,
                    already_found,
                    cross_family,
                    alloc,
                    borrow_map,
                    env,
                )),
            )
        }

        // Terminals pass through unchanged
        Code::Jmp { jp, args } => Code::Jmp {
            jp: *jp,
            args: args.clone(),
        },
        Code::Return(fvar) => Code::Return(*fvar),
        Code::Unreachable(ty) => Code::Unreachable(ty.clone()),
    }
}

#[cfg(test)]
mod tests;
