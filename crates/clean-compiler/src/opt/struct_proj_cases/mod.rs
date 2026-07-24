// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! StructProjCases — Push projections through case alternatives.
//!
//! When a join point receives a structure from case alternatives and
//! immediately projects a field from it, this pass pushes the projection
//! into each alternative. The struct construction becomes dead code
//! (removed by DCE) and the field is extracted directly.
//!
//! # Pattern
//!
//! Before:
//! ```text
//! jp _j (x : SomeStruct) :=
//!   let r := proj(x, idx)
//!   <body using r>
//! cases scrutinee of
//!   | Ctor1 a b => let s := SomeStruct.mk f1 f2; jmp _j s
//!   | Ctor2 c   => let s := SomeStruct.mk g1 g2; jmp _j s
//! ```
//!
//! After:
//! ```text
//! jp _j (r : FieldType) :=
//!   <body using r>
//! cases scrutinee of
//!   | Ctor1 a b => jmp _j f1
//!   | Ctor2 c   => jmp _j g1
//! ```
//!
//! # Applicability
//!
//! The pass fires when:
//! 1. A `JoinPoint` has exactly one parameter
//! 2. The JP body starts with a `Proj` of that parameter
//! 3. The parameter is not used elsewhere in the JP body (only via the projection)
//! 4. The continuation is a `Cases` where every alternative ends with
//!    `let s := Ctor(...); jmp jp s`
//! 5. Each constructor has enough arguments for the projected field index
//!
//! # Interaction with other passes
//!
//! - **simp_value** handles projection-after-constructor within the same scope.
//!   StructProjCases handles the inter-procedural case where a `Cases` node
//!   separates the constructor from the projection.
//! - **DCE** removes the now-dead constructor bindings after this pass.
//! - **join_points** may create the join point structure this pass targets.
//!
//! Part of #1086 - StructProjCases compiler pass.

use crate::lcnf::{Alt, Arg, Cases, Code, Decl, DeclValue, FunDecl, LetValue, Param};
use crate::CodeFolder;
use clean_kernel::FVarId;
use std::collections::HashSet;

/// Collect FVarId references in a LetValue.
fn collect_let_value_uses(value: &LetValue, uses: &mut HashSet<FVarId>) {
    match value {
        LetValue::Proj { structure, .. } => {
            uses.insert(*structure);
        }
        LetValue::FVar { fvar, args } => {
            uses.insert(*fvar);
            for arg in args {
                if let Arg::FVar(fv) = arg {
                    uses.insert(*fv);
                }
            }
        }
        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => {
            for arg in args {
                if let Arg::FVar(fv) = arg {
                    uses.insert(*fv);
                }
            }
        }
        LetValue::Reuse { slot, args, .. } => {
            uses.insert(*slot);
            for arg in args {
                if let Arg::FVar(fv) = arg {
                    uses.insert(*fv);
                }
            }
        }
        LetValue::Lit(_) | LetValue::Erased => {}
    }
}

/// Check if `target` is used in `code`, excluding a specific let-binding.
///
/// Returns true if `target` appears as a free variable reference in `code`
/// anywhere other than the let-binding with `exclude_fvar_id`.
fn is_used_in_body_excluding(code: &Code, target: FVarId, exclude_fvar_id: FVarId) -> bool {
    match code {
        Code::Let(decl, body) => {
            if decl.fvar_id != exclude_fvar_id {
                let mut uses = HashSet::new();
                collect_let_value_uses(&decl.value, &mut uses);
                if uses.contains(&target) {
                    return true;
                }
            }
            is_used_in_body_excluding(body, target, exclude_fvar_id)
        }
        Code::Fun(decl, body) | Code::JoinPoint(decl, body) => {
            is_used_in_body_excluding(&decl.body, target, exclude_fvar_id)
                || is_used_in_body_excluding(body, target, exclude_fvar_id)
        }
        Code::Cases(cases) => {
            if cases.scrutinee == target {
                return true;
            }
            cases
                .alts
                .iter()
                .any(|alt| is_used_in_body_excluding(alt.body(), target, exclude_fvar_id))
        }
        Code::Jmp { jp, args } => {
            if *jp == target {
                return true;
            }
            args.iter()
                .any(|arg| matches!(arg, Arg::FVar(fv) if *fv == target))
        }
        Code::Return(fv) => *fv == target,
        Code::Unreachable(_) => false,
    }
}

/// Information about a projection at the start of a join point body.
struct JpProjInfo {
    /// The FVarId of the join point parameter being projected.
    _param_fvar: FVarId,
    /// The projection field index.
    proj_idx: u32,
    /// The FVarId that the projection result is bound to.
    proj_result_fvar: FVarId,
    /// The type of the projection result.
    proj_result_ty: clean_kernel::Expr,
}

/// Check if a join point body starts with a projection of its single parameter,
/// and that parameter is not used elsewhere in the body.
fn detect_jp_proj(jp_decl: &FunDecl) -> Option<JpProjInfo> {
    // Must have exactly one parameter.
    if jp_decl.params.len() != 1 {
        return None;
    }
    let param = &jp_decl.params[0];

    // Body must start with a Let whose value is a Proj of the parameter.
    let Code::Let(proj_decl, _rest) = jp_decl.body.as_ref() else {
        return None;
    };
    let LetValue::Proj { idx, structure, .. } = &proj_decl.value else {
        return None;
    };

    if *structure != param.fvar_id {
        return None;
    }

    // The parameter must not be used anywhere else in the rest of the JP body.
    // It can only appear in the projection let-binding.
    if is_used_in_body_excluding(&jp_decl.body, param.fvar_id, proj_decl.fvar_id) {
        return None;
    }

    Some(JpProjInfo {
        _param_fvar: param.fvar_id,
        proj_idx: *idx,
        proj_result_fvar: proj_decl.fvar_id,
        proj_result_ty: proj_decl.ty.clone(),
    })
}

/// Information about a case alternative that constructs a struct and jumps
/// to a specific join point.
struct AltCtorJmpInfo {
    /// The FVarId of the constructed struct.
    ctor_fvar: FVarId,
    /// Arguments to the constructor.
    ctor_args: Vec<Arg>,
}

/// Check if a code block ends with `let s := Ctor(...); jmp jp s`.
fn detect_ctor_then_jmp(code: &Code, jp_fvar: FVarId) -> Option<AltCtorJmpInfo> {
    match code {
        Code::Let(decl, body) => {
            // Check if body is `jmp jp <decl.fvar_id>`
            if let Code::Jmp { jp, args } = body.as_ref() {
                if *jp == jp_fvar
                    && args.len() == 1
                    && matches!(&args[0], Arg::FVar(fv) if *fv == decl.fvar_id)
                {
                    if let LetValue::Ctor {
                        args: ctor_args, ..
                    } = &decl.value
                    {
                        return Some(AltCtorJmpInfo {
                            ctor_fvar: decl.fvar_id,
                            ctor_args: ctor_args.clone(),
                        });
                    }
                }
            }
            // Recurse through let-bindings to find the ctor+jmp at the tail.
            if let Some(info) = detect_ctor_then_jmp(body, jp_fvar) {
                // Only valid if the ctor_fvar is defined in a nested let, not this one.
                // (We already checked this one above.)
                return Some(info);
            }
            None
        }
        _ => None,
    }
}

/// Check if all case alternatives end with a ctor+jmp pattern targeting `jp_fvar`,
/// and all constructors have enough args for `field_idx`.
fn check_all_alts_ctor_jmp(
    alts: &[Alt],
    jp_fvar: FVarId,
    field_idx: u32,
) -> Option<Vec<AltCtorJmpInfo>> {
    let mut infos = Vec::with_capacity(alts.len());
    for alt in alts {
        let info = detect_ctor_then_jmp(alt.body(), jp_fvar)?;
        // Verify the constructor has enough arguments for the field index.
        if (field_idx as usize) >= info.ctor_args.len() {
            return None;
        }
        infos.push(info);
    }
    Some(infos)
}

/// Rewrite a case alternative body: replace `let s := Ctor(...); jmp jp s`
/// with `jmp jp field_arg` where `field_arg` is the projected field.
fn rewrite_alt_body(code: &Code, jp_fvar: FVarId, ctor_fvar: FVarId, field_arg: &Arg) -> Code {
    match code {
        Code::Let(decl, body) => {
            if let Code::Jmp { jp, args } = body.as_ref() {
                if *jp == jp_fvar
                    && args.len() == 1
                    && matches!(&args[0], Arg::FVar(fv) if *fv == decl.fvar_id)
                    && decl.fvar_id == ctor_fvar
                {
                    // Replace: let s := Ctor(...); jmp jp s
                    // With:    jmp jp field_arg
                    return Code::Jmp {
                        jp: jp_fvar,
                        args: vec![field_arg.clone()],
                    };
                }
            }
            // Recurse through preceding let-bindings.
            Code::Let(
                decl.clone(),
                Box::new(rewrite_alt_body(body, jp_fvar, ctor_fvar, field_arg)),
            )
        }
        other => other.clone(),
    }
}

/// CodeFolder that applies the StructProjCases transformation.
struct StructProjCasesFolder;

impl CodeFolder for StructProjCasesFolder {
    fn fold_join_point(&mut self, decl: FunDecl, body: Code) -> Code {
        // First, recursively fold sub-expressions.
        let folded_jp_body = self.fold_code(&decl.body);
        let folded_continuation = self.fold_code(&body);

        let new_decl = FunDecl {
            body: Box::new(folded_jp_body),
            ..decl
        };

        // Check if this JP+Cases matches the StructProjCases pattern.
        if let Some(proj_info) = detect_jp_proj(&new_decl) {
            if let Code::Cases(cases) = &folded_continuation {
                if let Some(alt_infos) =
                    check_all_alts_ctor_jmp(&cases.alts, new_decl.fvar_id, proj_info.proj_idx)
                {
                    // Transform: push projection into each alternative.
                    let new_alts: Vec<Alt> = cases
                        .alts
                        .iter()
                        .zip(alt_infos.iter())
                        .map(|(alt, info)| {
                            let field_arg = &info.ctor_args[proj_info.proj_idx as usize];
                            let new_body = rewrite_alt_body(
                                alt.body(),
                                new_decl.fvar_id,
                                info.ctor_fvar,
                                field_arg,
                            );
                            match alt {
                                Alt::Ctor {
                                    ctor_name, params, ..
                                } => Alt::Ctor {
                                    ctor_name: ctor_name.clone(),
                                    params: params.clone(),
                                    body: Box::new(new_body),
                                },
                                Alt::Default(_) => Alt::Default(Box::new(new_body)),
                            }
                        })
                        .collect();

                    // Rewrite the JP: remove the projection let-binding,
                    // rename the parameter to receive the field directly.
                    let Code::Let(_, rest) = new_decl.body.as_ref() else {
                        // Safety: detect_jp_proj verified this is Code::Let.
                        return Code::JoinPoint(new_decl, Box::new(folded_continuation));
                    };

                    let new_jp_decl = FunDecl {
                        params: vec![Param::new(
                            proj_info.proj_result_fvar,
                            new_decl.params[0].name.clone(),
                            proj_info.proj_result_ty,
                        )],
                        body: Box::new(rest.as_ref().clone()),
                        ..new_decl
                    };

                    let new_cases = Code::Cases(Cases {
                        alts: new_alts,
                        ..cases.clone()
                    });

                    return Code::JoinPoint(new_jp_decl, Box::new(new_cases));
                }
            }
        }

        Code::JoinPoint(new_decl, Box::new(folded_continuation))
    }
}

/// Apply the StructProjCases optimization to a declaration.
///
/// Pushes projections through case alternatives, avoiding intermediate
/// struct construction when only a single field is needed.
pub fn struct_proj_cases(decl: &Decl) -> Decl {
    let body = match &decl.body {
        DeclValue::Code(code) => DeclValue::Code(Box::new(struct_proj_cases_in_code(code))),
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

/// Apply the StructProjCases optimization directly to a Code block.
pub fn struct_proj_cases_in_code(code: &Code) -> Code {
    StructProjCasesFolder.fold_code(code)
}

#[cfg(test)]
mod tests;
