// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Level canonicalization for elaboration results.
//!
//! Applies level substitutions to all expressions in an `ElabResult`
//! to ensure level metavariables are resolved to concrete levels.

use clean_kernel::Expr;

use super::{DerivedInstance, ElabCtx, ElabResult};

impl<'a> ElabCtx<'a> {
    /// Canonicalize universe levels in an elaboration result.
    ///
    /// Applies level substitutions to all expressions in the result to ensure
    /// level metavariables are resolved to concrete levels.
    pub(super) fn canonicalize_levels_in_elab_result(&self, result: ElabResult) -> ElabResult {
        let canonicalize = |expr: Expr| self.metas.canonicalize_levels_in_expr(&expr);

        match result {
            ElabResult::Definition {
                name,
                universe_params,
                ty,
                val,
                modifiers,
            } => ElabResult::Definition {
                name,
                universe_params,
                ty: canonicalize(ty),
                val: canonicalize(val),
                modifiers,
            },
            ElabResult::Theorem {
                name,
                universe_params,
                ty,
                proof,
                modifiers,
            } => ElabResult::Theorem {
                name,
                universe_params,
                ty: canonicalize(ty),
                proof: canonicalize(proof),
                modifiers,
            },
            ElabResult::Axiom {
                name,
                universe_params,
                ty,
                modifiers,
            } => ElabResult::Axiom {
                name,
                universe_params,
                ty: canonicalize(ty),
                modifiers,
            },
            ElabResult::Opaque {
                name,
                universe_params,
                ty,
                val,
                modifiers,
            } => ElabResult::Opaque {
                name,
                universe_params,
                ty: canonicalize(ty),
                val: val.map(&canonicalize),
                modifiers,
            },
            ElabResult::Inductive {
                name,
                universe_params,
                num_params,
                ty,
                constructors,
                derived_instances,
                wants_deep_induction,
                modifiers,
            } => ElabResult::Inductive {
                name,
                universe_params,
                num_params,
                ty: canonicalize(ty),
                constructors: constructors
                    .into_iter()
                    .map(|(name, ty)| (name, canonicalize(ty)))
                    .collect(),
                derived_instances: derived_instances
                    .into_iter()
                    .map(|inst| DerivedInstance {
                        name: inst.name,
                        class_name: inst.class_name,
                        ty: canonicalize(inst.ty),
                        val: canonicalize(inst.val),
                        priority: inst.priority,
                        level_params: inst.level_params,
                    })
                    .collect(),
                wants_deep_induction,
                modifiers,
            },
            ElabResult::MutualInductive {
                mut decl,
                derived_instances,
                modifiers,
            } => {
                for ind_ty in &mut decl.types {
                    ind_ty.type_ = canonicalize(ind_ty.type_.clone());
                    for ctor in &mut ind_ty.constructors {
                        ctor.type_ = canonicalize(ctor.type_.clone());
                    }
                }
                ElabResult::MutualInductive {
                    decl,
                    derived_instances: derived_instances
                        .into_iter()
                        .map(|inst| DerivedInstance {
                            name: inst.name,
                            class_name: inst.class_name,
                            ty: canonicalize(inst.ty),
                            val: canonicalize(inst.val),
                            priority: inst.priority,
                            level_params: inst.level_params,
                        })
                        .collect(),
                    modifiers,
                }
            }
            ElabResult::Structure {
                name,
                universe_params,
                num_params,
                ty,
                ctor_name,
                ctor_ty,
                field_names,
                field_defaults,
                projections,
                projection_param_infos,
                parents,
                derived_instances,
                class_info,
                modifiers,
            } => ElabResult::Structure {
                name,
                universe_params,
                num_params,
                ty: canonicalize(ty),
                ctor_name,
                ctor_ty: canonicalize(ctor_ty),
                field_names,
                field_defaults: field_defaults
                    .into_iter()
                    .map(|(field, val)| (field, canonicalize(val)))
                    .collect(),
                projections: projections
                    .into_iter()
                    .map(|(name, ty, val)| (name, canonicalize(ty), canonicalize(val)))
                    .collect(),
                projection_param_infos,
                parents,
                derived_instances: derived_instances
                    .into_iter()
                    .map(|inst| DerivedInstance {
                        name: inst.name,
                        class_name: inst.class_name,
                        ty: canonicalize(inst.ty),
                        val: canonicalize(inst.val),
                        priority: inst.priority,
                        level_params: inst.level_params,
                    })
                    .collect(),
                class_info,
                modifiers,
            },
            ElabResult::Instance {
                name,
                universe_params,
                class_name,
                ty,
                val,
                priority,
                modifiers,
            } => ElabResult::Instance {
                name,
                universe_params,
                class_name,
                ty: canonicalize(ty),
                val: canonicalize(val),
                priority,
                modifiers,
            },
            ElabResult::Multiple(results) => ElabResult::Multiple(
                results
                    .into_iter()
                    .map(|r| self.canonicalize_levels_in_elab_result(r))
                    .collect(),
            ),
            cmd @ ElabResult::Command(_) => cmd,
            ElabResult::Example { ty, val } => ElabResult::Example {
                ty: canonicalize(ty),
                val: canonicalize(val),
            },
            ElabResult::Skipped => ElabResult::Skipped,
            // `Failed` holds no kernel `Expr`s (only a name string, the inner
            // surface decl, and the error), so there are no levels to canonicalize.
            failed @ ElabResult::Failed { .. } => failed,
        }
    }
}
