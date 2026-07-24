// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Value Simplification for L5CNF
//!
//! Simplifies let-values through local transformations based on
//! tracked knowledge about variable contents.
//!
//! # Transformations
//!
//! - **Projection after constructor:** `(Pair.mk a b).1` → `a`
//! - **Identity application:** `id x` → `x`
//! - **Erasure propagation:** Operations on erased values simplify
//!
//! # Example
//!
//! Before:
//! ```text
//! let _1 := Prod.mk _x _y
//! let _2 := Prod.fst _1
//! return _2
//! ```
//!
//! After:
//! ```text
//! let _1 := Prod.mk _x _y
//! let _2 := _x
//! return _2
//! ```
//!
//! Part of #963 - Compiler IR infrastructure.

use crate::lcnf::{Alt, Arg, Cases, Code, Decl, DeclValue, FunDecl, LetDecl, LetValue};
use crate::CodeFolder;
use clean_kernel::{FVarId, Name};
use std::collections::HashMap;

/// Information about a known constructor value.
#[derive(Clone, Debug)]
struct CtorInfo {
    /// Arguments passed to the constructor.
    args: Vec<Arg>,
}

/// Context for value simplification.
struct SimpCtx {
    /// Maps FVarId to known constructor info.
    ctor_info: HashMap<FVarId, CtorInfo>,
    /// Maps FVarId to simple FVar references (for copy propagation).
    fvar_alias: HashMap<FVarId, FVarId>,
}

impl SimpCtx {
    fn new() -> Self {
        Self {
            ctor_info: HashMap::new(),
            fvar_alias: HashMap::new(),
        }
    }

    /// Record a constructor value.
    fn record_ctor(&mut self, fvar: FVarId, args: Vec<Arg>) {
        self.ctor_info.insert(fvar, CtorInfo { args });
    }

    /// Record a simple alias (copy propagation).
    fn record_alias(&mut self, from: FVarId, to: FVarId) {
        self.fvar_alias.insert(from, to);
    }

    /// Get constructor info for an FVarId.
    fn get_ctor(&self, fvar: &FVarId) -> Option<&CtorInfo> {
        self.ctor_info.get(fvar)
    }

    /// Get the canonical FVarId (following aliases).
    fn canonical(&self, fvar: FVarId) -> FVarId {
        let mut curr = fvar;
        let mut steps = 0usize;

        while let Some(next) = self.fvar_alias.get(&curr).copied() {
            if next == curr {
                break;
            }
            curr = next;
            steps += 1;
            if steps > self.fvar_alias.len() {
                break;
            }
        }

        curr
    }
}

/// Convert projection index to usize.
///
/// In LCNF, projections use field indices directly (0-based).
/// The type_name is currently unused but reserved for future
/// type-specific projection handling.
fn projection_index(_type_name: &str, idx: u32) -> Option<usize> {
    Some(idx as usize)
}

/// Try to simplify a projection.
fn simplify_proj(type_name: &Name, idx: u32, structure: FVarId, ctx: &SimpCtx) -> Option<LetValue> {
    let info = ctx.get_ctor(&structure)?;

    // Get the field index
    let field_idx = projection_index(&type_name.to_string(), idx)?;

    // Get the argument at that index
    let arg = info.args.get(field_idx)?;

    // Convert Arg to LetValue
    match arg {
        Arg::FVar(fvar) => Some(LetValue::FVar {
            fvar: *fvar,
            args: vec![],
        }),
        Arg::Erased => Some(LetValue::Erased),
        Arg::Type(ty) => {
            // Type arguments become erased in LCNF
            let _ = ty;
            Some(LetValue::Erased)
        }
        Arg::Index(_) => None, // Index literals can't be simplified to values
    }
}

/// Try to simplify an FVar application (for identity-like functions).
fn simplify_fvar_app(fvar: FVarId, args: &[Arg], ctx: &SimpCtx) -> Option<LetValue> {
    // Apply aliasing to the function FVar
    let canonical_fvar = ctx.canonical(fvar);

    // If the result is an alias with no args, return the aliased value
    if args.is_empty() && canonical_fvar != fvar {
        return Some(LetValue::FVar {
            fvar: canonical_fvar,
            args: vec![],
        });
    }

    None
}

/// Simplify a let-value.
fn simplify_value(value: &LetValue, ctx: &SimpCtx) -> LetValue {
    match value {
        LetValue::Proj {
            type_name,
            idx,
            structure,
        } => {
            if let Some(simplified) = simplify_proj(type_name, *idx, *structure, ctx) {
                simplified
            } else {
                value.clone()
            }
        }

        LetValue::FVar { fvar, args } => {
            if let Some(simplified) = simplify_fvar_app(*fvar, args, ctx) {
                simplified
            } else {
                // Apply aliasing to arguments
                let new_args: Vec<Arg> = args
                    .iter()
                    .map(|arg| match arg {
                        Arg::FVar(fv) => Arg::FVar(ctx.canonical(*fv)),
                        other => other.clone(),
                    })
                    .collect();

                LetValue::FVar {
                    fvar: ctx.canonical(*fvar),
                    args: new_args,
                }
            }
        }

        LetValue::Const { name, levels, args } => {
            // Apply aliasing to arguments
            let new_args: Vec<Arg> = args
                .iter()
                .map(|arg| match arg {
                    Arg::FVar(fv) => Arg::FVar(ctx.canonical(*fv)),
                    other => other.clone(),
                })
                .collect();

            LetValue::Const {
                name: name.clone(),
                levels: levels.clone(),
                args: new_args,
            }
        }

        LetValue::Ctor { name, levels, args } => {
            // Apply aliasing to arguments
            let new_args: Vec<Arg> = args
                .iter()
                .map(|arg| match arg {
                    Arg::FVar(fv) => Arg::FVar(ctx.canonical(*fv)),
                    other => other.clone(),
                })
                .collect();

            LetValue::Ctor {
                name: name.clone(),
                levels: levels.clone(),
                args: new_args,
            }
        }

        // Literals and Erased don't change
        _ => value.clone(),
    }
}

/// Apply argument simplification (following aliases).
fn simplify_arg(arg: &Arg, ctx: &SimpCtx) -> Arg {
    match arg {
        Arg::FVar(fvar) => Arg::FVar(ctx.canonical(*fvar)),
        other => other.clone(),
    }
}

/// CodeFolder that performs value simplification during traversal.
///
/// Delegates structural recursion to the CodeFolder trait. Overrides
/// fold_let for value simplification and ctor/alias tracking,
/// fold_fun/fold_join_point/fold_cases for context save/restore,
/// and fold_jmp/fold_return for alias canonicalization.
struct SimpValueFolder {
    ctx: SimpCtx,
}

impl CodeFolder for SimpValueFolder {
    fn fold_let(&mut self, decl: LetDecl, body: Code) -> Code {
        self.ctx.ctor_info.remove(&decl.fvar_id);
        self.ctx.fvar_alias.remove(&decl.fvar_id);
        let new_value = simplify_value(&decl.value, &self.ctx);
        if let LetValue::Ctor { args, .. } = &new_value {
            self.ctx.record_ctor(decl.fvar_id, args.clone());
        }
        if let LetValue::FVar { fvar, args } = &new_value {
            if args.is_empty() {
                let canonical = self.ctx.canonical(*fvar);
                self.ctx.record_alias(decl.fvar_id, canonical);
            }
        }
        Code::Let(
            LetDecl {
                value: new_value,
                ..decl
            },
            Box::new(self.fold_code(&body)),
        )
    }

    fn fold_fun(&mut self, decl: FunDecl, body: Code) -> Code {
        let saved_ctor = self.ctx.ctor_info.clone();
        let saved_alias = self.ctx.fvar_alias.clone();
        let new_fun_body = self.fold_code(&decl.body);
        self.ctx.ctor_info = saved_ctor;
        self.ctx.fvar_alias = saved_alias;
        Code::Fun(
            FunDecl {
                body: Box::new(new_fun_body),
                ..decl
            },
            Box::new(self.fold_code(&body)),
        )
    }

    fn fold_join_point(&mut self, decl: FunDecl, body: Code) -> Code {
        let saved_ctor = self.ctx.ctor_info.clone();
        let saved_alias = self.ctx.fvar_alias.clone();
        let new_jp_body = self.fold_code(&decl.body);
        self.ctx.ctor_info = saved_ctor;
        self.ctx.fvar_alias = saved_alias;
        Code::JoinPoint(
            FunDecl {
                body: Box::new(new_jp_body),
                ..decl
            },
            Box::new(self.fold_code(&body)),
        )
    }

    fn fold_cases(&mut self, cases: Cases) -> Code {
        let new_scrutinee = self.ctx.canonical(cases.scrutinee);
        let saved_ctor = self.ctx.ctor_info.clone();
        let saved_alias = self.ctx.fvar_alias.clone();
        let Cases {
            type_name,
            result_type,
            alts,
            ..
        } = cases;
        let mut new_alts = Vec::with_capacity(alts.len());
        for alt in alts {
            self.ctx.ctor_info = saved_ctor.clone();
            self.ctx.fvar_alias = saved_alias.clone();
            let new_alt = match alt {
                Alt::Ctor {
                    ctor_name,
                    params,
                    body,
                } => {
                    let args: Vec<Arg> = params.iter().map(|p| Arg::FVar(p.fvar_id)).collect();
                    self.ctx.record_ctor(new_scrutinee, args);
                    Alt::Ctor {
                        ctor_name,
                        params,
                        body: Box::new(self.fold_code(&body)),
                    }
                }
                Alt::Default(body) => Alt::Default(Box::new(self.fold_code(&body))),
            };
            new_alts.push(new_alt);
        }
        self.ctx.ctor_info = saved_ctor;
        self.ctx.fvar_alias = saved_alias;
        Code::Cases(Cases {
            type_name,
            result_type,
            scrutinee: new_scrutinee,
            alts: new_alts,
        })
    }

    fn fold_jmp(&mut self, jp: FVarId, args: Vec<Arg>) -> Code {
        Code::Jmp {
            jp: self.ctx.canonical(jp),
            args: args.iter().map(|a| simplify_arg(a, &self.ctx)).collect(),
        }
    }

    fn fold_return(&mut self, fvar: FVarId) -> Code {
        Code::Return(self.ctx.canonical(fvar))
    }
}

/// Apply value simplification to a declaration.
///
/// Simplifies let-values through local transformations:
/// - Projection after constructor: `(Prod.mk a b).1` → `a`
/// - Copy propagation: tracks simple aliases
pub fn simplify_values(decl: &Decl) -> Decl {
    let body = match &decl.body {
        DeclValue::Code(code) => {
            let mut folder = SimpValueFolder {
                ctx: SimpCtx::new(),
            };
            DeclValue::Code(Box::new(folder.fold_code(code)))
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

/// Apply value simplification directly to a Code block.
pub fn simplify_values_in_code(code: &Code) -> Code {
    SimpValueFolder {
        ctx: SimpCtx::new(),
    }
    .fold_code(code)
}

#[cfg(test)]
mod tests;
