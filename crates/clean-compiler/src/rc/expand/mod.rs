// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expand Reset/Reuse Operations
//!
//! Lowers the high-level `reset`/`reuse` operations from the reset_reuse pass
//! into concrete runtime checks using join-point-based code sharing (Bug 15).
//!
//! # Algorithm
//!
//! For each `let w := reset x`:
//! 1. Create `resetjp(token, isShared)` join point with shared body
//! 2. Within the body, each `reuse w` becomes a `reusejp(final)` join point
//! 3. Fast path (refcount == 1): `jmp resetjp(x, s)`, at reuse sites set fields
//! 4. Slow path (refcount > 1): `jmp resetjp(erased, s)`, at reuse sites alloc
//!
//! Reference: Lean 4 LCNF ExpandResetReuse.lean
//! Part of #963 - Compiler IR infrastructure.

mod cleanup;
mod mask;
mod rewrite_jp;

#[cfg(test)]
mod rewrite;
#[cfg(test)]
mod slow_path;

#[cfg(test)]
mod tests;

use super::FVarIdAllocator;
use crate::lcnf::{Alt, Arg, Cases, Code, Decl, DeclValue, FunDecl, LetDecl, LetValue, Param};
use crate::rc::pseudo_op;
use crate::CodeFolder;
use clean_kernel::{Expr, FVarId, Name};

use cleanup::{build_type_map_for_code, build_type_map_for_decl, TypeMap};
use mask::{build_proj_sources_for_code, mask_for_target, ProjSources};
use rewrite_jp::{process_reset_cont, ResetContContext};

/// Expand reset/reuse operations in a declaration.
pub fn expand_reset_reuse(decl: &Decl) -> Decl {
    let mut alloc = FVarIdAllocator::for_expand_reset();
    let type_map = build_type_map_for_decl(decl);
    let proj_sources = match &decl.body {
        DeclValue::Code(code) => build_proj_sources_for_code(code),
        DeclValue::Extern(_) => ProjSources::new(),
    };
    let body = match &decl.body {
        DeclValue::Code(code) => {
            let result = search_and_expand_with_types(code, &mut alloc, &type_map, &proj_sources);
            DeclValue::Code(Box::new(result))
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

/// Expand reset/reuse operations in code directly.
pub fn expand_reset_reuse_in_code(code: &Code) -> Code {
    let mut alloc = FVarIdAllocator::for_expand_reset();
    let type_map = build_type_map_for_code(code);
    let proj_sources = build_proj_sources_for_code(code);
    search_and_expand_with_types(code, &mut alloc, &type_map, &proj_sources)
}

/// CodeFolder that searches for reset operations and expands them into
/// isShared runtime checks with fast/slow paths.
///
/// Delegates structural recursion to the CodeFolder trait. Only overrides
/// fold_let to detect and expand reset operations.
struct ResetExpander<'a> {
    alloc: &'a mut FVarIdAllocator,
    type_map: &'a TypeMap,
    proj_sources: &'a ProjSources,
}

impl CodeFolder for ResetExpander<'_> {
    /// Handle a let-binding during reset search, expanding resets when consumed.
    ///
    /// Reference: ExpandResetReuse.lean:255-259
    ///   vdecl x _ (Expr.reset n y) b => if consumed x b then expand
    fn fold_let(&mut self, decl: LetDecl, body: Code) -> Code {
        if is_reset_op(&decl.value) {
            if let LetValue::Const { args, .. } = &decl.value {
                if let Some(Arg::FVar(obj_fvar)) = args.first() {
                    if consumed(decl.fvar_id, &body) {
                        let expanded_body = self.fold_code(&body);
                        return expand_reset(
                            decl.fvar_id,
                            *obj_fvar,
                            expanded_body,
                            self.alloc,
                            self.type_map,
                            self.proj_sources,
                        );
                    }
                    // Not consumed - skip reset (eliminated by later pass)
                    return self.fold_code(&body);
                }
            }
        }
        Code::Let(decl, Box::new(self.fold_code(&body)))
    }
}

fn search_and_expand_with_types(
    code: &Code,
    alloc: &mut FVarIdAllocator,
    type_map: &TypeMap,
    proj_sources: &ProjSources,
) -> Code {
    ResetExpander {
        alloc,
        type_map,
        proj_sources,
    }
    .fold_code(code)
}

/// Check if a let-value is a reset operation.
fn is_reset_op(value: &LetValue) -> bool {
    match value {
        LetValue::Const { name, .. } => name.to_string() == pseudo_op::RESET,
        _ => false,
    }
}

/// Check if a let-value is a reuse operation.
/// Handles both:
/// - Legacy: `LetValue::Const { name: "_reuse", .. }`
/// - Native: `LetValue::Reuse { .. }` (Part of #1104)
pub(crate) fn is_reuse_op(value: &LetValue) -> bool {
    match value {
        LetValue::Const { name, .. } => name.to_string() == pseudo_op::REUSE,
        LetValue::Reuse { .. } => true,
        _ => false,
    }
}

/// Check if a let-value is a dec (reference count decrement) operation.
fn is_dec_op(value: &LetValue) -> bool {
    match value {
        LetValue::Const { name, .. } => name.to_string() == pseudo_op::DEC,
        _ => false,
    }
}

/// Check if variable `x` is consumed in all branches of `code`.
///
/// Consumption means the code contains either:
/// - `dec x` - explicit decrement
/// - `reuse x ...` - reuse in constructor
///
/// For case expressions, x must be consumed in ALL alternatives.
/// This is the Lean4 parity implementation from ExpandResetReuse.lean:44-53.
fn consumed(x: FVarId, code: &Code) -> bool {
    match code {
        Code::Let(decl, body) => {
            // Check if this is a reuse of x
            if is_reuse_op(&decl.value) {
                // Handle legacy LetValue::Const { name: "_reuse", .. }
                if let LetValue::Const { args, .. } = &decl.value {
                    if let Some(Arg::FVar(reuse_var)) = args.first() {
                        if *reuse_var == x {
                            return true;
                        }
                    }
                }
                // Handle native LetValue::Reuse { slot, .. }
                if let LetValue::Reuse { slot, .. } = &decl.value {
                    if *slot == x {
                        return true;
                    }
                }
            }
            // Check if this is a dec of x
            if is_dec_op(&decl.value) {
                if let LetValue::Const { args, .. } = &decl.value {
                    if let Some(Arg::FVar(dec_var)) = args.first() {
                        if *dec_var == x {
                            return true;
                        }
                    }
                }
            }
            // Continue searching in body
            consumed(x, body)
        }
        Code::Fun(fun_decl, body) => consumed(x, &fun_decl.body) || consumed(x, body),
        Code::JoinPoint(jp_decl, body) => consumed(x, &jp_decl.body) || consumed(x, body),
        Code::Cases(cases) => {
            // Must be consumed in ALL alternatives
            cases.alts.iter().all(|alt| match alt {
                Alt::Ctor { body, .. } => consumed(x, body),
                Alt::Default(body) => consumed(x, body),
            })
        }
        // Terminal nodes - not consumed
        Code::Return(_) | Code::Jmp { .. } | Code::Unreachable(_) => false,
    }
}

/// Expand a reset operation into a `resetjp` join-point pattern.
///
/// Bug 15 / #2059: Instead of duplicating the body for fast/slow paths,
/// creates a join point so the continuation is shared.
///
/// Transforms:
/// ```text
/// let w := reset x
/// ... (body with reuse w / dec w) ...
/// ```
///
/// Into:
/// ```text
/// jp resetjp(token, isShared):
///   ... (body with dec w → del w, reuse w → reusejp pattern) ...
/// let s := _isShared(x)
/// cases s of
/// | false =>                  // Fast path: refcount == 1
///   jmp resetjp(x, s)
/// | true =>                   // Slow path: refcount > 1
///   [inc masked projections]
///   dec x
///   jmp resetjp(erased, s)
/// ```
///
/// Reference: Lean 4 LCNF ExpandResetReuse.lean:296-318
fn expand_reset(
    reset_var: FVarId,
    obj_fvar: FVarId,
    body: Code,
    alloc: &mut FVarIdAllocator,
    type_map: &TypeMap,
    proj_sources: &ProjSources,
) -> Code {
    let mask = mask_for_target(proj_sources, obj_fvar);
    let token_ty = type_map
        .get(&obj_fvar)
        .cloned()
        .unwrap_or_else(|| Expr::const_str("_"));

    // Create isShared check variable (outer scope, before the JP)
    let is_shared_check_var = alloc.fresh().expect("FVarId allocation overflow");

    // Create isShared parameter for the resetjp (distinct from the outer check var)
    let is_shared_param = alloc.fresh().expect("FVarId allocation overflow");

    // Build combined type map including body bindings, and add reset_var's type
    // so cleanup inside the JP body can look up the token's type.
    let mut combined_type_map = type_map.clone();
    combined_type_map.extend(build_type_map_for_code(&body));
    if let Some(ty) = type_map.get(&obj_fvar) {
        combined_type_map.insert(reset_var, ty.clone());
    }

    // Process body: dec→del, reuse→reusejp (shared between fast/slow)
    let processed_body = {
        let mut ctx = ResetContContext {
            reset_var,
            is_shared: is_shared_param,
            alloc: &mut *alloc,
            type_map: &combined_type_map,
            mask: &mask,
        };
        process_reset_cont(&body, &mut ctx)
    };

    // Create resetjp(token, isShared) with processed body
    let resetjp_id = alloc.fresh().expect("FVarId allocation overflow");
    let resetjp = FunDecl::new(
        resetjp_id,
        Name::from_string("resetjp"),
        vec![
            Param::new(reset_var, Name::from_string("token"), token_ty),
            Param::new(
                is_shared_param,
                Name::from_string("isShared"),
                Expr::const_str("Bool"),
            ),
        ],
        Expr::const_str("_"),
        processed_body,
    );

    // --- Fast path: jmp resetjp(orig, isSharedCheck) ---
    let fast_path = Code::Jmp {
        jp: resetjp_id,
        args: vec![Arg::FVar(obj_fvar), Arg::FVar(is_shared_check_var)],
    };

    // --- Slow path: inc masked projections + dec orig + jmp resetjp(erased, isSharedCheck) ---
    let mut slow_path = Code::Jmp {
        jp: resetjp_id,
        args: vec![Arg::Erased, Arg::FVar(is_shared_check_var)],
    };

    // Prepend dec for original object
    slow_path = Code::let_bind(
        LetDecl::new(
            alloc.fresh().expect("FVarId allocation overflow"),
            pseudo_op::NAME_DEC.clone(),
            Expr::const_str("_"),
            LetValue::Const {
                name: pseudo_op::NAME_DEC.clone(),
                levels: vec![],
                args: vec![Arg::FVar(obj_fvar)],
            },
        ),
        slow_path,
    );

    // Prepend inc for masked projection vars — on the slow path these projections
    // need their own refcount because the parent object is being decremented.
    // (On the fast path the parent object keeps them alive.)
    for proj_fvar in mask.keys() {
        slow_path = Code::let_bind(
            LetDecl::new(
                alloc.fresh().expect("FVarId allocation overflow"),
                pseudo_op::NAME_INC.clone(),
                Expr::const_str("_"),
                LetValue::Const {
                    name: pseudo_op::NAME_INC.clone(),
                    levels: vec![],
                    args: vec![Arg::FVar(*proj_fvar)],
                },
            ),
            slow_path,
        );
    }

    // Combine: jp resetjp(token, isShared) { body } in isShared check
    Code::JoinPoint(
        resetjp,
        Box::new(Code::let_bind(
            LetDecl::new(
                is_shared_check_var,
                pseudo_op::NAME_IS_SHARED.clone(),
                Expr::const_str("Bool"),
                LetValue::Const {
                    name: pseudo_op::NAME_IS_SHARED.clone(),
                    levels: vec![],
                    args: vec![Arg::FVar(obj_fvar)],
                },
            ),
            Code::Cases(Cases {
                type_name: Name::from_string("Bool"),
                result_type: Expr::const_str("_"),
                scrutinee: is_shared_check_var,
                alts: vec![
                    Alt::Ctor {
                        ctor_name: Name::from_string("Bool.false"),
                        params: vec![],
                        body: Box::new(fast_path),
                    },
                    Alt::Ctor {
                        ctor_name: Name::from_string("Bool.true"),
                        params: vec![],
                        body: Box::new(slow_path),
                    },
                ],
            }),
        )),
    )
}
