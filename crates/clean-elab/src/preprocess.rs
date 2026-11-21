// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Declaration preprocessing with file-scope variable injection.

use crate::file_context::FileContext;
use clean_parser::{SurfaceDecl, SurfaceName};

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
    /// The declaration's level parameters: the file-declared universes it
    /// USES (Lean's `collectLevelParams` rule — `universe u v` followed by
    /// `class C (α : Type u)` is `C.{u}`, not `C.{u, v}`), then its own
    /// explicit `.{…}` list. `used` is `None` when
    /// [`crate::universe_occurrence::used_universe_names`] could not see the
    /// whole declaration (a tactic block, say); then EVERY declared universe
    /// is merged, which is the over-inclusive behaviour every declaration had
    /// before 2026-09-10 and can drop nothing. Over-inclusion is not free: an
    /// unused parameter on a class is a level metavariable nothing can ever
    /// solve at each `[C α]` binder, and the declaration dies at the kernel
    /// with `Type mismatch: expected C α, got C α` (module doc of
    /// `universe_occurrence`).
    fn merge_universe_params(
        file_params: &[SurfaceName],
        decl_params: &[SurfaceName],
        used: Option<&std::collections::HashSet<String>>,
    ) -> Vec<SurfaceName> {
        let mut out = Vec::new();
        for p in file_params {
            if used.is_some_and(|u| !u.contains(&p.to_string())) {
                continue;
            }
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

    // A pruning request belongs to the one declaration it was made for; the
    // arms below record a fresh one when that declaration needs it.
    file_ctx.set_pending_section_prune(decl.span(), None);

    match decl {
        // Variable declarations add their binders to the context
        SurfaceDecl::Variable {
            binders,
            span,
            visibility,
        } => {
            // `apply_variable_command` resolves Lean's binder-annotation-UPDATE
            // form (`variable (P Q a b)`, `variable {P Q}`: no type ascription,
            // so it re-binds an ALREADY-DECLARED variable in place rather than
            // declaring a new one) and appends the rest, then returns the full
            // accumulated telescope.
            //
            // The telescope is handed to `elab_variable_binders` WHOLE — prior
            // binders first, this command's after — because a later
            // `variable`'s type may reference an earlier section variable
            // (`variable {β : α → Sort*}` after `variable {α}`), and that
            // validator elaborates types; given only the new binders the
            // reference auto-binds as a bare Sort and dies with
            // TooManyArguments.
            let full = file_ctx.apply_variable_command(binders);
            SurfaceDecl::Variable {
                span: *span,
                binders: full,
                visibility: *visibility,
            }
        }

        // `include x` / `omit x` steer which section variables the FOLLOWING
        // declarations receive. They register nothing; they update the context
        // that the value-declaration arms below consult.
        SurfaceDecl::IncludeVars { names, .. } => {
            file_ctx.include_variables(names);
            decl.clone()
        }
        SurfaceDecl::OmitVars { names, .. } => {
            file_ctx.omit_variables(names);
            decl.clone()
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
                let new_binders = if has_file_variables {
                    // Lean parity: prepend only the USED section variables
                    // (dependency fixpoint + instance activation + own-binder
                    // shadowing). Prepending ALL of them registers same-file
                    // constants with phantom implicit binders; every later use
                    // then mints fresh metavariables nothing can solve, and
                    // the decl dies at the kernel with "contains free
                    // variables" (the 2026-08-15 Mathlib Logic/Basic class).
                    let selection = crate::section_var_selection::select_section_binders(
                        file_ctx.current_variables(),
                        decl,
                        Some(file_ctx.macro_ctx()),
                        file_ctx.included_variables(),
                    );
                    // An incomplete scan prepends every section variable and
                    // asks the elaboration of THIS declaration to drop the
                    // unused ones (`crate::infer::section_prune`).
                    file_ctx.set_pending_section_prune(*span, selection.prune);
                    let mut new_binders = selection.binders;
                    new_binders.extend(binders.iter().cloned());
                    new_binders
                } else {
                    binders.clone()
                };
                let new_universe_params = if has_file_universes {
                    let used = crate::universe_occurrence::used_universe_names(decl, &new_binders);
                    merge_universe_params(
                        file_ctx.current_universe_params(),
                        universe_params,
                        used.as_ref(),
                    )
                } else {
                    universe_params.clone()
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
                    modifiers: modifiers.clone(),
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
                let new_binders = if has_file_variables {
                    // Lean parity: prepend only the USED section variables
                    // (dependency fixpoint + instance activation + own-binder
                    // shadowing). Prepending ALL of them registers same-file
                    // constants with phantom implicit binders; every later use
                    // then mints fresh metavariables nothing can solve, and
                    // the decl dies at the kernel with "contains free
                    // variables" (the 2026-08-15 Mathlib Logic/Basic class).
                    let selection = crate::section_var_selection::select_section_binders(
                        file_ctx.current_variables(),
                        decl,
                        Some(file_ctx.macro_ctx()),
                        file_ctx.included_variables(),
                    );
                    // An incomplete scan prepends every section variable and
                    // asks the elaboration of THIS declaration to drop the
                    // unused ones (`crate::infer::section_prune`).
                    file_ctx.set_pending_section_prune(*span, selection.prune);
                    let mut new_binders = selection.binders;
                    new_binders.extend(binders.iter().cloned());
                    new_binders
                } else {
                    binders.clone()
                };
                let new_universe_params = if has_file_universes {
                    let used = crate::universe_occurrence::used_universe_names(decl, &new_binders);
                    merge_universe_params(
                        file_ctx.current_universe_params(),
                        universe_params,
                        used.as_ref(),
                    )
                } else {
                    universe_params.clone()
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
                    modifiers: modifiers.clone(),
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
                let new_binders = if has_file_variables {
                    // Lean parity: prepend only the USED section variables
                    // (dependency fixpoint + instance activation + own-binder
                    // shadowing). Prepending ALL of them registers same-file
                    // constants with phantom implicit binders; every later use
                    // then mints fresh metavariables nothing can solve, and
                    // the decl dies at the kernel with "contains free
                    // variables" (the 2026-08-15 Mathlib Logic/Basic class).
                    let selection = crate::section_var_selection::select_section_binders(
                        file_ctx.current_variables(),
                        decl,
                        Some(file_ctx.macro_ctx()),
                        file_ctx.included_variables(),
                    );
                    // An incomplete scan prepends every section variable and
                    // asks the elaboration of THIS declaration to drop the
                    // unused ones (`crate::infer::section_prune`).
                    file_ctx.set_pending_section_prune(*span, selection.prune);
                    let mut new_binders = selection.binders;
                    new_binders.extend(binders.iter().cloned());
                    new_binders
                } else {
                    binders.clone()
                };
                let new_universe_params = if has_file_universes {
                    let used = crate::universe_occurrence::used_universe_names(decl, &new_binders);
                    merge_universe_params(
                        file_ctx.current_universe_params(),
                        universe_params,
                        used.as_ref(),
                    )
                } else {
                    universe_params.clone()
                };
                SurfaceDecl::Axiom {
                    span: *span,
                    name: name.clone(),
                    universe_params: new_universe_params,
                    binders: new_binders,
                    ty: ty.clone(),
                    attrs: attrs.clone(),
                    modifiers: modifiers.clone(),
                }
            } else {
                decl.clone()
            }
        }

        // Opaque - prepend the section variables its header and value use, as
        // for an axiom (review r6 fix round: `variable {α} [Inhabited α]` then
        // `opaque o : α` is served by the section's instance in Lean).
        SurfaceDecl::Opaque {
            span,
            name,
            universe_params,
            binders,
            ty,
            val,
            attrs,
            modifiers,
        } => {
            let has_file_universes = file_ctx.has_universe_params();
            let has_file_variables = file_ctx.has_variables();
            if has_file_universes || has_file_variables {
                let new_binders = if has_file_variables {
                    let selection = crate::section_var_selection::select_section_binders(
                        file_ctx.current_variables(),
                        decl,
                        Some(file_ctx.macro_ctx()),
                        file_ctx.included_variables(),
                    );
                    file_ctx.set_pending_section_prune(*span, selection.prune);
                    let mut new_binders = selection.binders;
                    new_binders.extend(binders.iter().cloned());
                    new_binders
                } else {
                    binders.clone()
                };
                let new_universe_params = if has_file_universes {
                    let used = crate::universe_occurrence::used_universe_names(decl, &new_binders);
                    merge_universe_params(
                        file_ctx.current_universe_params(),
                        universe_params,
                        used.as_ref(),
                    )
                } else {
                    universe_params.clone()
                };
                SurfaceDecl::Opaque {
                    span: *span,
                    name: name.clone(),
                    universe_params: new_universe_params,
                    binders: new_binders,
                    ty: ty.clone(),
                    val: val.clone(),
                    attrs: attrs.clone(),
                    modifiers: modifiers.clone(),
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
            if file_ctx.has_universe_params() || file_ctx.has_variables() {
                let mut parameters = file_ctx.current_variables().to_vec();
                parameters.extend_from_slice(binders);
                SurfaceDecl::Inductive {
                    span: *span,
                    name: name.clone(),
                    universe_params: merge_universe_params(
                        file_ctx.current_universe_params(),
                        universe_params,
                        crate::universe_occurrence::used_universe_names(decl, &parameters).as_ref(),
                    ),
                    binders: parameters,
                    ty: ty.clone(),
                    ctors: ctors.clone(),
                    deriving: deriving.clone(),
                    modifiers: modifiers.clone(),
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
                        crate::universe_occurrence::used_universe_names(decl, binders).as_ref(),
                    ),
                    binders: binders.clone(),
                    ty: ty.clone(),
                    ctors: ctors.clone(),
                    deriving: deriving.clone(),
                    modifiers: modifiers.clone(),
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
            if file_ctx.has_universe_params() || file_ctx.has_variables() {
                let mut parameters = file_ctx.current_variables().to_vec();
                parameters.extend_from_slice(binders);
                SurfaceDecl::Structure {
                    span: *span,
                    name: name.clone(),
                    universe_params: merge_universe_params(
                        file_ctx.current_universe_params(),
                        universe_params,
                        crate::universe_occurrence::used_universe_names(decl, &parameters).as_ref(),
                    ),
                    binders: parameters,
                    extends: extends.clone(),
                    ty: ty.clone(),
                    ctor_name: ctor_name.clone(),
                    fields: fields.clone(),
                    deriving: deriving.clone(),
                    modifiers: modifiers.clone(),
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
            if file_ctx.has_universe_params() || file_ctx.has_variables() {
                let mut parameters = file_ctx.current_variables().to_vec();
                parameters.extend_from_slice(binders);
                SurfaceDecl::Class {
                    span: *span,
                    name: name.clone(),
                    universe_params: merge_universe_params(
                        file_ctx.current_universe_params(),
                        universe_params,
                        crate::universe_occurrence::used_universe_names(decl, &parameters).as_ref(),
                    ),
                    binders: parameters,
                    extends: extends.clone(),
                    ty: ty.clone(),
                    fields: fields.clone(),
                    modifiers: modifiers.clone(),
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
            compiler_attrs,
        } => {
            let has_file_universes = file_ctx.has_universe_params();
            let has_file_variables = file_ctx.has_variables();
            if has_file_universes || has_file_variables {
                let new_binders = if has_file_variables {
                    // Lean parity: prepend only the USED section variables
                    // (dependency fixpoint + instance activation + own-binder
                    // shadowing). Prepending ALL of them registers same-file
                    // constants with phantom implicit binders; every later use
                    // then mints fresh metavariables nothing can solve, and
                    // the decl dies at the kernel with "contains free
                    // variables" (the 2026-08-15 Mathlib Logic/Basic class).
                    let selection = crate::section_var_selection::select_section_binders(
                        file_ctx.current_variables(),
                        decl,
                        Some(file_ctx.macro_ctx()),
                        file_ctx.included_variables(),
                    );
                    // An incomplete scan prepends every section variable and
                    // asks the elaboration of THIS declaration to drop the
                    // unused ones (`crate::infer::section_prune`).
                    file_ctx.set_pending_section_prune(*span, selection.prune);
                    let mut new_binders = selection.binders;
                    new_binders.extend(binders.iter().cloned());
                    new_binders
                } else {
                    binders.clone()
                };
                let new_universe_params = if has_file_universes {
                    let used = crate::universe_occurrence::used_universe_names(decl, &new_binders);
                    merge_universe_params(
                        file_ctx.current_universe_params(),
                        universe_params,
                        used.as_ref(),
                    )
                } else {
                    universe_params.clone()
                };
                SurfaceDecl::Instance {
                    span: *span,
                    name: name.clone(),
                    universe_params: new_universe_params,
                    binders: new_binders,
                    class_type: class_type.clone(),
                    fields: fields.clone(),
                    priority: *priority,
                    modifiers: modifiers.clone(),
                    compiler_attrs: compiler_attrs.clone(),
                }
            } else {
                decl.clone()
            }
        }

        // All other declarations pass through unchanged
        // `#guard_msgs … in cmd`: `cmd` is an ordinary command of this
        // file and takes the section's variables and universes like any
        // other (Lean elaborates it in the same scope).
        SurfaceDecl::GuardMsgs {
            span,
            doc,
            spec,
            cmd,
        } => SurfaceDecl::GuardMsgs {
            span: *span,
            doc: doc.clone(),
            spec: spec.clone(),
            cmd: Box::new(preprocess_decl_with_context(cmd, file_ctx)),
        },

        _ => decl.clone(),
    }
}
