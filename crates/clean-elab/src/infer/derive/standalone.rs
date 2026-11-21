// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::elab_types::collect_level_params;
use super::super::{ElabCtx, ElabResult};
use crate::derive::{
    admit_generated_instance_typed, admit_registered_generated_instance_typed, DeriveRegistry,
};
use crate::ElabError;
use clean_kernel::{ConstantKind, Declaration, Expr, ExprKind, Name};
use clean_parser::{DeclModifiers, SurfaceName};

impl ElabCtx<'_> {
    /// Elaborate instances for already-declared types, including imported families.
    /// Later handlers see instances successfully checked earlier in this command.
    pub(in crate::infer) fn elab_standalone_deriving(
        &mut self,
        classes: &[SurfaceName],
        targets: &[SurfaceName],
    ) -> Result<ElabResult, ElabError> {
        let mut registry = DeriveRegistry::new();
        crate::derive_handlers::register_standalone_handlers(&mut registry);
        let mut candidate = self.env.clone();
        let mut results = Vec::new();
        let mut names = Vec::with_capacity(targets.len());
        for target in targets {
            let term = self.elab_ident(target)?;
            let ExprKind::Const(name, _) = term.kind() else {
                return Err(ElabError::Unsupported {
                    feature: format!("deriving instance requires a global type, got `{target}`"),
                });
            };
            names.push(name.clone());
        }
        let delta = names
            .iter()
            .any(|name| self.env.get_inductive(name).is_none());
        for source_class in classes {
            let class = self.resolve_derive_class(source_class)?;
            for target in &names {
                let label = target.to_string();
                let declarations = if delta {
                    vec![self.delta_derived_definition(&class, target)?]
                } else {
                    let family = candidate.get_inductive(target).ok_or_else(|| {
                        ElabError::InternalInvariant(format!("deriving lost inductive `{target}`"))
                    })?;
                    if let Some(user) =
                        self.try_user_defined_handler(target, family.num_params as usize, &class)?
                    {
                        vec![Declaration::Definition {
                            name: user.name,
                            level_params: user.level_params,
                            type_: user.ty,
                            value: user.val,
                            is_reducible: true,
                        }]
                    } else {
                        registry
                            .declarations_for(&class.to_string(), family, &candidate)
                            .map_err(|e| ElabError::Unsupported {
                                feature: e.to_string(),
                            })?
                    }
                };
                if declarations.is_empty() {
                    return Err(ElabError::Unsupported {
                        feature: format!("deriving `{class}` produced no instance for `{target}`"),
                    });
                }
                for declaration in declarations {
                    let Declaration::Definition {
                        level_params,
                        type_,
                        value,
                        ..
                    } = declaration
                    else {
                        return Err(ElabError::Unsupported {
                            feature: format!(
                                "deriving `{class}` returned a non-definition for `{target}`"
                            ),
                        });
                    };
                    // Lean generates the public instance name from the class and
                    // target at the command site, including when the handler
                    // works on a declaration imported from another namespace.
                    let component = |name: &Name| {
                        crate::private_names::user_facing_name(name)
                            .last_component()
                            .ok_or_else(|| {
                                ElabError::InternalInvariant(
                                    "anonymous class or target in deriving".into(),
                                )
                            })
                    };
                    let base = format!("inst{}{}", component(class.name())?, component(target)?);
                    let name = self.fresh_global_name_in(&base, &candidate);
                    admit_generated_instance_typed(
                        &candidate,
                        class.name(),
                        &label,
                        &name,
                        &type_,
                        &value,
                    )
                    .map_err(|e| ElabError::Unsupported {
                        feature: e.to_string(),
                    })?;
                    let instance = ElabResult::Instance {
                        name: name.clone(),
                        universe_params: level_params,
                        class_name: class.name().clone(),
                        ty: type_,
                        val: value,
                        priority: clean_kernel::env::LEAN_DEFAULT_INSTANCE_PRIORITY,
                        modifiers: DeclModifiers::default(),
                    };
                    crate::register::register_elab_result(&mut candidate, &instance)?;
                    admit_registered_generated_instance_typed(
                        &candidate,
                        class.name(),
                        &label,
                        &name,
                    )
                    .map_err(|e| ElabError::Unsupported {
                        feature: e.to_string(),
                    })?;
                    results.push(instance);
                }
            }
        }
        Ok(ElabResult::Multiple(results))
    }

    fn delta_derived_definition(
        &mut self,
        class: &SurfaceName,
        target: &Name,
    ) -> Result<Declaration, ElabError> {
        let info = self
            .env
            .get_const(target)
            .filter(|info| info.kind == ConstantKind::Definition)
            .ok_or_else(|| ElabError::Unsupported {
                feature: format!("delta deriving needs a definition: `{target}`"),
            })?;
        let levels: Vec<_> = info
            .level_params
            .iter()
            .cloned()
            .map(clean_kernel::Level::param)
            .collect();
        let folded = Expr::const_(target.clone(), levels);
        let unfolded = info.value.clone().ok_or_else(|| ElabError::Unsupported {
            feature: format!("no definition body for delta deriving on `{target}`"),
        })?;
        let (ty, value) = self.with_temporary_local_scope(|ctx| {
            let mut folded = folded;
            let mut unfolded = unfolded;
            let mut binders = Vec::new();
            // Lean's processDefDeriving opens lambdas in the definition value.
            // A definition returning a type constructor can itself be the target.
            while let ExprKind::Lam(binder, domain, body) = unfolded.kind() {
                let name = SurfaceName::unspellable("deriveParam", binders.len() as u64);
                let fvar = ctx.push_local(name, domain.as_ref().clone());
                if binder.info == clean_kernel::BinderInfo::InstImplicit {
                    ctx.push_local_instance(fvar, domain.as_ref().clone());
                }
                binders.push((*binder, domain.as_ref().clone(), fvar));
                let arg = Expr::fvar(fvar);
                folded = Expr::app(folded, arg.clone());
                unfolded = body.instantiate(&arg);
            }
            let head = match ctx.env.get_const(class.name()) {
                Some(info) if info.level_params.len() == 1 => {
                    let sort = ctx.infer_sort(&unfolded)?;
                    match ctx.class_concretize_level(class, &sort) {
                        Some(level) => Expr::const_(class.name().clone(), vec![level]),
                        None => ctx.mk_const(class.name()),
                    }
                }
                _ => ctx.mk_const(class.name()),
            };
            let goal = Expr::app(head.clone(), unfolded);
            let value =
                ctx.resolve_instance(&goal)
                    .ok_or_else(|| ElabError::FailedToSynthesize {
                        class_name: class.name().clone(),
                        goal: crate::error_render::term(&goal),
                    })?;
            let ty = Expr::app(head, folded);
            ctx.enforce_expr_type(&value, &ty)?;
            let mut ty = ctx.metas.instantiate(&ty);
            let mut value = ctx.metas.instantiate(&value);
            for (binder, domain, fvar) in binders.into_iter().rev() {
                ty = Expr::pi(binder, domain.clone(), ty.abstract_fvar(fvar));
                value = Expr::lam(binder, domain, value.abstract_fvar(fvar));
            }
            Ok((ty, value))
        })?;
        Ok(Declaration::Definition {
            name: match super::builtin_class(class.name()) {
                Some(label) => crate::derive::builtin_instance_name(target, label),
                None => crate::derive::source_handler_instance_name(class.name(), target),
            },
            level_params: collect_level_params(&[&ty, &value]),
            type_: ty,
            value,
            is_reducible: true,
        })
    }
}
