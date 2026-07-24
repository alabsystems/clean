// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CommonJoinPointArgs — eliminate redundant join point parameters.
//!
//! When all jumps to a join point pass the same FVar for a parameter,
//! remove that parameter, substitute the common value in the body, and
//! strip the argument from all `Jmp` sites. Based on Lean 4's
//! `src/Lean/Compiler/LCNF/CommonJoinPointArgs.lean`.
//!
//! # Algorithm
//!
//! For each `JoinPoint(decl, body)`:
//! 1. Collect all `Jmp` sites that target `decl.fvar_id` within `body`.
//! 2. For each parameter position `i`, check whether every `Jmp` site
//!    passes the same `Arg` value at position `i`.
//! 3. If all sites agree, that parameter is "common" — record the mapping
//!    from the parameter's `FVarId` to the common `Arg`.
//! 4. Remove common parameters from `decl.params` and corresponding
//!    arguments from every `Jmp` targeting this join point.
//! 5. In the join point body, replace free-variable references to the
//!    removed parameter with the common value (only `Arg::FVar` can be
//!    meaningfully substituted into `FVarId` slots; `Arg::Erased` and
//!    `Arg::Type` positions are left alone since they are computationally
//!    irrelevant).
//!
//! # Example
//!
//! ```text
//! // Before: all Jmp sites pass `w` for parameter `a`
//! jp j (a : Nat) (b : Nat) := Nat.add a b
//! | True  => jmp j w y
//! | False => jmp j w z
//! // After: `a` removed, substituted with `w` in body
//! jp j (b : Nat) := Nat.add w b
//! | True  => jmp j y
//! | False => jmp j z
//! ```
//!
//! Part of #1087 - CommonJoinPointArgs compiler pass.

use crate::lcnf::{Alt, Arg, Cases, Code, Decl, DeclValue, FunDecl, LetDecl, LetValue, Param};
use clean_kernel::FVarId;
use std::collections::HashMap;

/// Collect all `Jmp` argument lists targeting a given join point.
///
/// Walks `code` and records `args` from every `Code::Jmp { jp, args }` where
/// `jp == target`. Does not descend into nested `JoinPoint` bodies (those
/// define a new scope where `target` may be shadowed).
fn collect_jmp_args(code: &Code, target: FVarId, out: &mut Vec<Vec<Arg>>) {
    match code {
        Code::Let(_, body) => collect_jmp_args(body, target, out),

        Code::Fun(decl, body) => {
            collect_jmp_args(&decl.body, target, out);
            collect_jmp_args(body, target, out);
        }

        Code::JoinPoint(decl, body) => {
            // A nested join point with the same fvar_id shadows our target;
            // do not descend into its body.
            if decl.fvar_id != target {
                collect_jmp_args(&decl.body, target, out);
            }
            collect_jmp_args(body, target, out);
        }

        Code::Cases(cases) => {
            for alt in &cases.alts {
                match alt {
                    Alt::Ctor { body, .. } => collect_jmp_args(body, target, out),
                    Alt::Default(body) => collect_jmp_args(body, target, out),
                }
            }
        }

        Code::Jmp { jp, args } => {
            if *jp == target {
                out.push(args.clone());
            }
        }

        Code::Return(_) | Code::Unreachable(_) => {}
    }
}

/// Determine which parameter positions have a common `Arg::FVar` value
/// across all jump sites.
///
/// Returns a map from parameter `FVarId` to the common `FVarId` value, for
/// every position where all sites agree on the same `Arg::FVar(v)`.
fn find_common_fvar_args(params: &[Param], all_jmp_args: &[Vec<Arg>]) -> HashMap<FVarId, FVarId> {
    if all_jmp_args.is_empty() {
        return HashMap::new();
    }

    let mut common = HashMap::new();

    for (i, param) in params.iter().enumerate() {
        // Extract the arg at position i from each Jmp site.
        let first = match all_jmp_args[0].get(i) {
            Some(arg) => arg,
            None => continue,
        };

        // We only substitute FVar-valued common args (other arg kinds
        // like Erased and Type are computationally irrelevant, and Index
        // is a literal that cannot populate an FVarId slot).
        let common_fvar = match first {
            Arg::FVar(fv) => *fv,
            _ => continue,
        };

        let all_same = all_jmp_args
            .iter()
            .all(|args| args.get(i) == Some(&Arg::FVar(common_fvar)));

        if all_same {
            common.insert(param.fvar_id, common_fvar);
        }
    }

    common
}

/// Substitute FVarId references inside a `LetValue`.
fn subst_let_value(value: &LetValue, subst: &HashMap<FVarId, FVarId>) -> LetValue {
    match value {
        LetValue::Lit(_) | LetValue::Erased => value.clone(),

        LetValue::Proj {
            type_name,
            idx,
            structure,
        } => LetValue::Proj {
            type_name: type_name.clone(),
            idx: *idx,
            structure: *subst.get(structure).unwrap_or(structure),
        },

        LetValue::Const { name, levels, args } => LetValue::Const {
            name: name.clone(),
            levels: levels.clone(),
            args: subst_args(args, subst),
        },

        LetValue::FVar { fvar, args } => LetValue::FVar {
            fvar: *subst.get(fvar).unwrap_or(fvar),
            args: subst_args(args, subst),
        },

        LetValue::Ctor { name, levels, args } => LetValue::Ctor {
            name: name.clone(),
            levels: levels.clone(),
            args: subst_args(args, subst),
        },

        LetValue::Reuse {
            slot,
            ctor_name,
            levels,
            args,
        } => LetValue::Reuse {
            slot: *subst.get(slot).unwrap_or(slot),
            ctor_name: ctor_name.clone(),
            levels: levels.clone(),
            args: subst_args(args, subst),
        },
    }
}

/// Substitute FVarId references inside an argument list.
fn subst_args(args: &[Arg], subst: &HashMap<FVarId, FVarId>) -> Vec<Arg> {
    args.iter()
        .map(|arg| match arg {
            Arg::FVar(fv) => Arg::FVar(*subst.get(fv).unwrap_or(fv)),
            other => other.clone(),
        })
        .collect()
}

/// Apply substitutions throughout a code block. Only replaces FVarId
/// references — does not touch parameter lists or join point structure.
fn subst_code(code: &Code, subst: &HashMap<FVarId, FVarId>) -> Code {
    if subst.is_empty() {
        return code.clone();
    }

    match code {
        Code::Let(decl, body) => {
            let new_value = subst_let_value(&decl.value, subst);
            let new_decl = LetDecl {
                fvar_id: decl.fvar_id,
                name: decl.name.clone(),
                ty: decl.ty.clone(),
                value: new_value,
            };
            Code::Let(new_decl, Box::new(subst_code(body, subst)))
        }

        Code::Fun(decl, body) => {
            let new_fun_body = subst_code(&decl.body, subst);
            let new_decl = FunDecl {
                fvar_id: decl.fvar_id,
                name: decl.name.clone(),
                params: decl.params.clone(),
                ty: decl.ty.clone(),
                body: Box::new(new_fun_body),
            };
            Code::Fun(new_decl, Box::new(subst_code(body, subst)))
        }

        Code::JoinPoint(decl, body) => {
            let new_jp_body = subst_code(&decl.body, subst);
            let new_decl = FunDecl {
                fvar_id: decl.fvar_id,
                name: decl.name.clone(),
                params: decl.params.clone(),
                ty: decl.ty.clone(),
                body: Box::new(new_jp_body),
            };
            Code::JoinPoint(new_decl, Box::new(subst_code(body, subst)))
        }

        Code::Cases(cases) => {
            let new_alts = cases
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
                        body: Box::new(subst_code(body, subst)),
                    },
                    Alt::Default(body) => Alt::Default(Box::new(subst_code(body, subst))),
                })
                .collect();

            Code::Cases(Cases {
                type_name: cases.type_name.clone(),
                result_type: cases.result_type.clone(),
                scrutinee: *subst.get(&cases.scrutinee).unwrap_or(&cases.scrutinee),
                alts: new_alts,
            })
        }

        Code::Jmp { jp, args } => Code::Jmp {
            jp: *subst.get(jp).unwrap_or(jp),
            args: subst_args(args, subst),
        },

        Code::Return(fvar) => Code::Return(*subst.get(fvar).unwrap_or(fvar)),

        Code::Unreachable(ty) => Code::Unreachable(ty.clone()),
    }
}

/// Rebuild a `FunDecl` with a transformed body.
fn rebuild_fun_decl(decl: &FunDecl, new_body: Code) -> FunDecl {
    FunDecl {
        fvar_id: decl.fvar_id,
        name: decl.name.clone(),
        params: decl.params.clone(),
        ty: decl.ty.clone(),
        body: Box::new(new_body),
    }
}

/// Remove arguments at given positions from all `Jmp` sites targeting `target`.
fn strip_jmp_args(code: &Code, target: FVarId, remove_positions: &[bool]) -> Code {
    match code {
        Code::Let(decl, body) => Code::Let(
            decl.clone(),
            Box::new(strip_jmp_args(body, target, remove_positions)),
        ),
        Code::Fun(decl, body) => {
            let new_decl =
                rebuild_fun_decl(decl, strip_jmp_args(&decl.body, target, remove_positions));
            Code::Fun(
                new_decl,
                Box::new(strip_jmp_args(body, target, remove_positions)),
            )
        }
        Code::JoinPoint(decl, body) => {
            let new_jp_body = if decl.fvar_id != target {
                strip_jmp_args(&decl.body, target, remove_positions)
            } else {
                *decl.body.clone()
            };
            let new_decl = rebuild_fun_decl(decl, new_jp_body);
            Code::JoinPoint(
                new_decl,
                Box::new(strip_jmp_args(body, target, remove_positions)),
            )
        }
        Code::Cases(cases) => strip_jmp_args_in_cases(cases, target, remove_positions),
        Code::Jmp { jp, args } if *jp == target => {
            let new_args = args
                .iter()
                .enumerate()
                .filter(|(i, _)| !remove_positions.get(*i).copied().unwrap_or(false))
                .map(|(_, a)| a.clone())
                .collect();
            Code::Jmp {
                jp: *jp,
                args: new_args,
            }
        }
        _ => code.clone(),
    }
}

/// Strip Jmp args inside case alternatives.
fn strip_jmp_args_in_cases(cases: &Cases, target: FVarId, remove_positions: &[bool]) -> Code {
    let new_alts = cases
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
                body: Box::new(strip_jmp_args(body, target, remove_positions)),
            },
            Alt::Default(body) => {
                Alt::Default(Box::new(strip_jmp_args(body, target, remove_positions)))
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

/// Eliminate common join point arguments from an LCNF `Code` block.
///
/// This is the main entry point for the pass. It recursively processes
/// all `JoinPoint` nodes in the code tree.
#[must_use]
pub fn eliminate_common_jp_args_in_code(code: &Code) -> Code {
    match code {
        Code::Let(decl, body) => Code::Let(
            decl.clone(),
            Box::new(eliminate_common_jp_args_in_code(body)),
        ),

        Code::Fun(decl, body) => {
            let new_fun_body = eliminate_common_jp_args_in_code(&decl.body);
            let new_decl = FunDecl {
                fvar_id: decl.fvar_id,
                name: decl.name.clone(),
                params: decl.params.clone(),
                ty: decl.ty.clone(),
                body: Box::new(new_fun_body),
            };
            Code::Fun(new_decl, Box::new(eliminate_common_jp_args_in_code(body)))
        }

        Code::JoinPoint(decl, body) => optimize_jp_common_args(decl, body),
        Code::Cases(cases) => {
            let new_alts = cases
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
                        body: Box::new(eliminate_common_jp_args_in_code(body)),
                    },
                    Alt::Default(body) => {
                        Alt::Default(Box::new(eliminate_common_jp_args_in_code(body)))
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

/// Process a single JoinPoint node: find common args, substitute, and strip.
fn optimize_jp_common_args(decl: &FunDecl, body: &Code) -> Code {
    let processed_jp_body = eliminate_common_jp_args_in_code(&decl.body);
    let processed_body = eliminate_common_jp_args_in_code(body);

    let mut all_jmp_args = Vec::new();
    collect_jmp_args(&processed_body, decl.fvar_id, &mut all_jmp_args);

    let common = find_common_fvar_args(&decl.params, &all_jmp_args);
    if common.is_empty() {
        let new_decl = rebuild_fun_decl(decl, processed_jp_body);
        return Code::JoinPoint(new_decl, Box::new(processed_body));
    }

    let remove_positions: Vec<bool> = decl
        .params
        .iter()
        .map(|p| common.contains_key(&p.fvar_id))
        .collect();
    let new_params: Vec<Param> = decl
        .params
        .iter()
        .filter(|p| !common.contains_key(&p.fvar_id))
        .cloned()
        .collect();

    let substituted_jp_body = subst_code(&processed_jp_body, &common);
    let stripped_body = strip_jmp_args(&processed_body, decl.fvar_id, &remove_positions);

    let new_decl = FunDecl {
        fvar_id: decl.fvar_id,
        name: decl.name.clone(),
        params: new_params,
        ty: decl.ty.clone(),
        body: Box::new(substituted_jp_body),
    };
    Code::JoinPoint(new_decl, Box::new(stripped_body))
}

/// Eliminate common join point arguments from an LCNF declaration.
#[must_use]
pub fn eliminate_common_jp_args(decl: &Decl) -> Decl {
    let new_body = match &decl.body {
        DeclValue::Code(code) => DeclValue::Code(Box::new(eliminate_common_jp_args_in_code(code))),
        DeclValue::Extern(attr) => DeclValue::Extern(attr.clone()),
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
