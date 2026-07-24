// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Declaration preprocessing with file-scope variable injection.

use crate::file_context::FileContext;
use clean_parser::SurfaceDecl;

/// Preprocess a declaration to include file-scope variables.
///
/// This function handles the `variable` command semantics:
/// - `Variable` declarations add their binders to the file context
/// - `Section` / `End` declarations manage scope
/// - `Theorem`, `Def`, `Axiom` declarations get accumulated variables prepended
///
/// # Arguments
///
/// * `decl` - The declaration to preprocess
/// * `file_ctx` - The file context tracking accumulated variables
///
/// # Returns
///
/// A (possibly modified) declaration with variables prepended to binders.
#[must_use]
pub fn preprocess_decl_with_context(decl: &SurfaceDecl, file_ctx: &mut FileContext) -> SurfaceDecl {
    fn merge_universe_params(file_params: &[String], decl_params: &[String]) -> Vec<String> {
        let mut out = Vec::new();
        for p in file_params {
            if !out.contains(p) {
                out.push(p.clone());
            }
        }
        for p in decl_params {
            if !out.contains(p) {
                out.push(p.clone());
            }
        }
        out
    }

    match decl {
        // Variable declarations add their binders to the context
        SurfaceDecl::Variable { binders, .. } => {
            file_ctx.add_variables(binders);
            decl.clone() // Return as-is (will be skipped during elaboration)
        }

        // Universe declarations add their names to the context
        SurfaceDecl::UniverseDecl { names, .. } => {
            file_ctx.add_universe_params(names);
            decl.clone() // Return as-is (will be skipped during elaboration)
        }

        // Section start - push scope marker
        SurfaceDecl::Section { .. } => {
            file_ctx.enter_section();
            decl.clone()
        }

        // Namespace - also acts as a scope boundary in Lean 4
        SurfaceDecl::Namespace { .. } => {
            file_ctx.enter_section();
            decl.clone()
        }

        // Theorem - prepend accumulated variables to binders
        SurfaceDecl::Theorem {
            span,
            name,
            universe_params,
            binders,
            ty,
            proof,
            attrs,
            termination,
            modifiers,
            where_decls,
            ..
        } => {
            let has_file_universes = file_ctx.has_universe_params();
            let has_file_variables = file_ctx.has_variables();
            if has_file_universes || has_file_variables {
                let new_universe_params = if has_file_universes {
                    merge_universe_params(file_ctx.current_universe_params(), universe_params)
                } else {
                    universe_params.clone()
                };
                let new_binders = if has_file_variables {
                    let mut new_binders = file_ctx.current_variables().to_vec();
                    new_binders.extend(binders.iter().cloned());
                    new_binders
                } else {
                    binders.clone()
                };
                SurfaceDecl::Theorem {
                    span: *span,
                    name: name.clone(),
                    universe_params: new_universe_params,
                    binders: new_binders,
                    ty: ty.clone(),
                    proof: proof.clone(),
                    attrs: attrs.clone(),
                    termination: termination.clone(),
                    modifiers: *modifiers,
                    where_decls: where_decls.clone(),
                }
            } else {
                decl.clone()
            }
        }

        // Def - prepend accumulated variables to binders
        SurfaceDecl::Def {
            span,
            name,
            universe_params,
            binders,
            ty,
            val,
            attrs,
            termination,
            modifiers,
            where_decls,
            ..
        } => {
            let has_file_universes = file_ctx.has_universe_params();
            let has_file_variables = file_ctx.has_variables();
            if has_file_universes || has_file_variables {
                let new_universe_params = if has_file_universes {
                    merge_universe_params(file_ctx.current_universe_params(), universe_params)
                } else {
                    universe_params.clone()
                };
                let new_binders = if has_file_variables {
                    let mut new_binders = file_ctx.current_variables().to_vec();
                    new_binders.extend(binders.iter().cloned());
                    new_binders
                } else {
                    binders.clone()
                };
                SurfaceDecl::Def {
                    span: *span,
                    name: name.clone(),
                    universe_params: new_universe_params,
                    binders: new_binders,
                    ty: ty.clone(),
                    val: val.clone(),
                    attrs: attrs.clone(),
                    termination: termination.clone(),
                    modifiers: *modifiers,
                    where_decls: where_decls.clone(),
                }
            } else {
                decl.clone()
            }
        }

        // Axiom - prepend accumulated variables to binders
        SurfaceDecl::Axiom {
            span,
            name,
            universe_params,
            binders,
            ty,
            attrs,
            modifiers,
        } => {
            let has_file_universes = file_ctx.has_universe_params();
            let has_file_variables = file_ctx.has_variables();
            if has_file_universes || has_file_variables {
                let new_universe_params = if has_file_universes {
                    merge_universe_params(file_ctx.current_universe_params(), universe_params)
                } else {
                    universe_params.clone()
                };
                let new_binders = if has_file_variables {
                    let mut new_binders = file_ctx.current_variables().to_vec();
                    new_binders.extend(binders.iter().cloned());
                    new_binders
                } else {
                    binders.clone()
                };
                SurfaceDecl::Axiom {
                    span: *span,
                    name: name.clone(),
                    universe_params: new_universe_params,
                    binders: new_binders,
                    ty: ty.clone(),
                    attrs: attrs.clone(),
                    modifiers: *modifiers,
                }
            } else {
                decl.clone()
            }
        }

        // Inductive - prepend accumulated universe params
        SurfaceDecl::Inductive {
            span,
            name,
            universe_params,
            binders,
            ty,
            ctors,
            deriving,
            modifiers,
        } => {
            if file_ctx.has_universe_params() {
                SurfaceDecl::Inductive {
                    span: *span,
                    name: name.clone(),
                    universe_params: merge_universe_params(
                        file_ctx.current_universe_params(),
                        universe_params,
                    ),
                    binders: binders.clone(),
                    ty: ty.clone(),
                    ctors: ctors.clone(),
                    deriving: deriving.clone(),
                    modifiers: *modifiers,
                }
            } else {
                decl.clone()
            }
        }

        // Coinductive - prepend accumulated universe params (#191)
        SurfaceDecl::Coinductive {
            span,
            name,
            universe_params,
            binders,
            ty,
            ctors,
            deriving,
            modifiers,
        } => {
            if file_ctx.has_universe_params() {
                SurfaceDecl::Coinductive {
                    span: *span,
                    name: name.clone(),
                    universe_params: merge_universe_params(
                        file_ctx.current_universe_params(),
                        universe_params,
                    ),
                    binders: binders.clone(),
                    ty: ty.clone(),
                    ctors: ctors.clone(),
                    deriving: deriving.clone(),
                    modifiers: *modifiers,
                }
            } else {
                decl.clone()
            }
        }

        // Structure - prepend accumulated universe params
        SurfaceDecl::Structure {
            span,
            name,
            universe_params,
            binders,
            extends,
            ty,
            ctor_name,
            fields,
            deriving,
            modifiers,
        } => {
            if file_ctx.has_universe_params() {
                SurfaceDecl::Structure {
                    span: *span,
                    name: name.clone(),
                    universe_params: merge_universe_params(
                        file_ctx.current_universe_params(),
                        universe_params,
                    ),
                    binders: binders.clone(),
                    extends: extends.clone(),
                    ty: ty.clone(),
                    ctor_name: ctor_name.clone(),
                    fields: fields.clone(),
                    deriving: deriving.clone(),
                    modifiers: *modifiers,
                }
            } else {
                decl.clone()
            }
        }

        // Class - prepend accumulated universe params
        SurfaceDecl::Class {
            span,
            name,
            universe_params,
            binders,
            extends,
            ty,
            fields,
            modifiers,
        } => {
            if file_ctx.has_universe_params() {
                SurfaceDecl::Class {
                    span: *span,
                    name: name.clone(),
                    universe_params: merge_universe_params(
                        file_ctx.current_universe_params(),
                        universe_params,
                    ),
                    binders: binders.clone(),
                    extends: extends.clone(),
                    ty: ty.clone(),
                    fields: fields.clone(),
                    modifiers: *modifiers,
                }
            } else {
                decl.clone()
            }
        }

        // Example - prepend accumulated variables (like theorems, but anonymous)
        SurfaceDecl::Example {
            span,
            binders,
            ty,
            val,
        } => {
            if file_ctx.has_variables() {
                let mut new_binders = file_ctx.current_variables().to_vec();
                new_binders.extend(binders.iter().cloned());
                SurfaceDecl::Example {
                    span: *span,
                    binders: new_binders,
                    ty: ty.clone(),
                    val: val.clone(),
                }
            } else {
                decl.clone()
            }
        }

        // Instance - prepend accumulated variables
        SurfaceDecl::Instance {
            span,
            name,
            universe_params,
            binders,
            class_type,
            fields,
            priority,
            modifiers,
        } => {
            let has_file_universes = file_ctx.has_universe_params();
            let has_file_variables = file_ctx.has_variables();
            if has_file_universes || has_file_variables {
                let new_universe_params = if has_file_universes {
                    merge_universe_params(file_ctx.current_universe_params(), universe_params)
                } else {
                    universe_params.clone()
                };
                let new_binders = if has_file_variables {
                    let mut new_binders = file_ctx.current_variables().to_vec();
                    new_binders.extend(binders.iter().cloned());
                    new_binders
                } else {
                    binders.clone()
                };
                SurfaceDecl::Instance {
                    span: *span,
                    name: name.clone(),
                    universe_params: new_universe_params,
                    binders: new_binders,
                    class_type: class_type.clone(),
                    fields: fields.clone(),
                    priority: *priority,
                    modifiers: *modifiers,
                }
            } else {
                decl.clone()
            }
        }

        // All other declarations pass through unchanged
        _ => decl.clone(),
    }
}
