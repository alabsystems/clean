// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-ordered, checked realization of ordinary defining equations.

use std::collections::HashSet;

use clean_kernel::env::{attr_ext_idx, AttrExtState, ConstantKind};
use clean_kernel::expr::UsedConstants;
use clean_kernel::{
    ConstantInfo, Environment, EqProofBuilder, Expr, ExprKind, Level, LocalContext, Name,
    TypeChecker,
};
use clean_parser::{SurfaceDecl, SurfaceName};

use crate::declared_here::{self, AttributeSite, ElabUnit};
use crate::definition_attrs::{self, NamedAttribute};
use crate::name_resolution::{resolve_global_const_no_overload, GlobalConstResolution};
use crate::namespace::NamespaceState;
use crate::private_names::{private_to_user_name, PrivateNames};
use crate::{CommandOutput, ElabError, ElabResult, FileContext, RegisteredElabResult};

struct Equations {
    messages: Vec<String>,
    generated: Vec<ElabResult>,
}

/// Recognize the source-ordered command inside a lexical `open … in` chain.
/// A temporary namespace state resolves its names without publishing opens.
pub(crate) fn try_elaborate(
    env: &mut Environment,
    file: Option<&FileContext>,
    decl: &SurfaceDecl,
) -> Option<Result<RegisteredElabResult, ElabError>> {
    let mut inner = decl;
    while let SurfaceDecl::Open {
        body: Some(body), ..
    } = inner
    {
        inner = body;
    }
    let SurfaceDecl::PrintEquations { name, .. } = inner else {
        return None;
    };
    Some(elaborate(env, file, decl, name))
}

fn elaborate(
    env: &mut Environment,
    file: Option<&FileContext>,
    mut decl: &SurfaceDecl,
    target: &SurfaceName,
) -> Result<RegisteredElabResult, ElabError> {
    let mut namespace = file
        .map(|file| file.namespace_state().clone())
        .unwrap_or_default();
    while let SurfaceDecl::Open {
        paths,
        scoped,
        body: Some(body),
        ..
    } = decl
    {
        namespace.push_scope();
        if *scoped {
            crate::namespace::process_open_scoped(env, paths, &mut namespace);
        } else {
            crate::namespace::process_open(env, paths, &mut namespace).map_err(|error| {
                ElabError::Unsupported {
                    feature: error.to_string(),
                }
            })?;
        }
        decl = body;
    }
    let constants = resolve(
        env,
        &namespace,
        &file
            .map(FileContext::foreign_private_decls)
            .unwrap_or_default(),
        target,
    )?;
    // Module visibility and the corresponding private equation names need
    // their own source policy. Existing equations can be read in any mode.
    let owner = (!file.is_some_and(FileContext::is_module_system)).then(|| ElabUnit::of(file));
    let Equations {
        messages,
        mut generated,
    } = prepare(env, constants, owner)?;
    let output = ElabResult::Command(CommandOutput::PrintEquations(messages));
    let result = if generated.is_empty() {
        output
    } else {
        generated.push(output);
        let result = ElabResult::Multiple(generated);
        let names = crate::register::leaf_own_names(&result);
        let attrs = names
            .iter()
            .map(|name| NamedAttribute {
                name: name.clone(),
                attribute: "defeq".into(),
                site: AttributeSite::Declaration,
            })
            .collect();
        let mut checked = env.clone();
        crate::source_family_authority::register_source(&mut checked, &result)?;
        for name in &names {
            record_param_infos(&mut checked, name)?;
        }
        definition_attrs::apply(&mut checked, file, attrs)?;
        declared_here::record_declared(&mut checked, ElabUnit::of(file), names.clone());
        clean_kernel::env::csimp::record_compiled(&mut checked, names);
        *env = checked;
        result
    };
    let warning = crate::register::registration_warning_for_result(env, &result);
    Ok(RegisteredElabResult {
        result,
        warning,
        hole_contexts: Vec::new(),
    })
}

/// Used by the header-first batch, whose commands run after value bodies.
/// Realization belongs to the source-ordered driver.
pub(crate) fn read_existing(
    env: &Environment,
    namespace: &NamespaceState,
    foreign_private: &HashSet<Name>,
    target: &SurfaceName,
) -> Result<ElabResult, ElabError> {
    let constants = resolve(env, namespace, foreign_private, target)?;
    let equations = prepare(env, constants, None)?;
    Ok(ElabResult::Command(CommandOutput::PrintEquations(
        equations.messages,
    )))
}

fn resolve(
    env: &Environment,
    namespace: &NamespaceState,
    foreign_private: &HashSet<Name>,
    target: &SurfaceName,
) -> Result<Vec<Name>, ElabError> {
    match resolve_global_const_no_overload(target, namespace, env, foreign_private) {
        Ok(name) => Ok(vec![name]),
        Err(GlobalConstResolution::Ambiguous(names)) => Ok(names),
        Err(GlobalConstResolution::Unknown) => Err(ElabError::CommandFailed {
            message: format!("unknown constant '{}'", target),
        }),
    }
}

fn prepare(
    env: &Environment,
    constants: Vec<Name>,
    owner: Option<ElabUnit>,
) -> Result<Equations, ElabError> {
    let mut messages = Vec::with_capacity(constants.len());
    let mut generated = Vec::new();
    for name in constants {
        let info = env
            .get_const(&name)
            .ok_or_else(|| ElabError::UnknownIdent(name.to_string()))?;
        let tc = TypeChecker::new(env);
        if info.kind != ConstantKind::Definition
            || env.get_inductive(&name).is_some()
            || env.get_constructor(&name).is_some()
            || env.get_recursor(&name).is_some()
            || env.get_matcher_info(&name).is_some()
            || tc
                .infer_sort(&info.type_)
                .map_err(|error| kernel_error(&name, error))?
                .is_zero()
        {
            messages.push(format!("'{name}' does not have equations"));
            continue;
        }

        let equation_name = name.clone().str("eq_1");
        let existing = env.get_const(&equation_name);
        let can_generate = owner.is_some_and(|unit| declared_here::declared_by(env, unit, &name))
            && private_to_user_name(&name).is_none();
        if (can_generate || existing.is_some())
            && declared_here::simple_equation_source(env, &name)
            && info.value.as_ref().is_some_and(|value| {
                // Lowered matches and recursors need their own families.
                let mut constants = HashSet::new();
                value.used_constants_dag(UsedConstants::ConstantsOnly, &mut constants);
                constants.iter().all(|constant| {
                    env.get_recursor(constant).is_none() && env.get_matcher_info(constant).is_none()
                })
            })
        {
            let (ty, proof) = simple_equation(env, &name, info)?;
            let unexpected_equation = env.get_const(&name.clone().str("eq_2")).is_some();
            if unexpected_equation
                || existing.is_some_and(|equation| {
                    equation.kind != ConstantKind::Theorem
                        || equation.value.is_none()
                        || equation.level_params != info.level_params
                        || equation.type_ != ty
                })
            {
                return Err(ElabError::CommandFailed {
                    message: format!(
                        "equation slots for '{name}' conflict with its defining equation"
                    ),
                });
            }
            let defeq = existing.is_none() || has_defeq(env, &equation_name);
            messages.push(format!(
                "equations:\n{}",
                header(&equation_name, &info.level_params, &ty, defeq)
            ));
            if existing.is_none() {
                generated.push(ElabResult::Theorem {
                    name: equation_name,
                    universe_params: info.level_params.clone(),
                    ty,
                    proof,
                    modifiers: Default::default(),
                });
            }
            continue;
        }

        let equations =
            crate::tactic::simp::collect_declared_equations(env, &name, 0).ok_or_else(|| {
                ElabError::CommandFailed {
                    message: format!(
                        "checked equations for '{name}' are unavailable in this source context"
                    ),
                }
            })?;
        let mut message = String::from("equations:");
        for equation in equations {
            let info = env
                .get_const(&equation.name)
                .ok_or_else(|| ElabError::UnknownIdent(equation.name.to_string()))?;
            message.push('\n');
            message.push_str(&header(
                &equation.name,
                &info.level_params,
                &info.type_,
                has_defeq(env, &equation.name),
            ));
        }
        messages.push(message);
    }
    Ok(Equations {
        messages,
        generated,
    })
}

fn simple_equation(
    env: &Environment,
    name: &Name,
    definition: &ConstantInfo,
) -> Result<(Expr, Expr), ElabError> {
    let mut body = definition
        .value
        .clone()
        .ok_or_else(|| ElabError::CommandFailed {
            message: format!("definition '{name}' has no value for its equation"),
        })?;
    let mut lhs = Expr::const_(
        name.clone(),
        definition
            .level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect::<Vec<_>>(),
    );
    let mut locals = LocalContext::new();
    let mut binders = Vec::new();
    // Peel the stored lambdas. In particular, do not eta-expand a
    // function-valued alias according to the binders of its type.
    while let ExprKind::Lam(binder, domain, inner) = body.kind() {
        let domain = domain.as_ref().clone();
        let local = locals.push(Name::anon(), domain.clone(), *binder);
        binders.push((*binder, domain, local));
        let arg = Expr::fvar(local);
        lhs = Expr::app(lhs, arg.clone());
        body = inner.instantiate(&arg);
    }
    let tc = TypeChecker::with_context(env, locals);
    let alpha = tc
        .infer_type(&lhs)
        .map_err(|error| kernel_error(name, error))?;
    let universe = tc
        .infer_sort(&alpha)
        .map_err(|error| kernel_error(name, error))?;
    let eq = Expr::const_(Name::from_string("Eq"), vec![universe.clone()]);
    let mut ty = Expr::apps(eq, [alpha.clone(), lhs.clone(), body]);
    let mut proof = EqProofBuilder::mk_eq_refl(universe, alpha, lhs);
    for (binder, domain, local) in binders.into_iter().rev() {
        ty = Expr::pi(binder, domain.clone(), ty.abstract_fvar(local));
        proof = Expr::lam(binder, domain, proof.abstract_fvar(local));
    }
    Ok((ty, proof))
}

fn kernel_error(name: &Name, error: impl std::fmt::Display) -> ElabError {
    ElabError::KernelCheckFailed {
        name: name.clone(),
        detail: error.to_string(),
    }
}

fn has_defeq(env: &Environment, name: &Name) -> bool {
    env.get_ext_state::<AttrExtState>(attr_ext_idx())
        .is_some_and(|attrs| attrs.has_attr(name, &Name::from_string("defeq")))
}

fn record_param_infos(env: &mut Environment, equation: &Name) -> Result<(), ElabError> {
    let definition = crate::namespace::parent_name(equation);
    let Some(names) = env.get_typed_param_names(&definition) else {
        return Ok(());
    };
    let info = env
        .get_const(equation)
        .ok_or_else(|| ElabError::UnknownIdent(equation.to_string()))?;
    let mut ty = &info.type_;
    let mut params = Vec::new();
    for name in names {
        let ExprKind::Pi(binder, _, body) = ty.kind() else {
            break;
        };
        params.push((name.clone(), binder.info));
        ty = body;
    }
    if !params.is_empty() {
        env.add_checked_param_infos(equation, params, false)
            .map_err(|error| kernel_error(equation, error))?;
    }
    Ok(())
}

fn header(name: &Name, levels: &[Name], ty: &Expr, defeq: bool) -> String {
    let prefix = if defeq { "@[defeq] " } else { "" };
    let levels = if levels.is_empty() {
        String::new()
    } else {
        format!(
            ".{{{}}}",
            levels
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    format!(
        "{prefix}theorem {name}{levels} : {}",
        PrivateNames::UserFacing.render(ty)
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run(
        env: &mut Environment,
        file: &mut FileContext,
        source: &str,
    ) -> Result<ElabResult, ElabError> {
        let decl = clean_parser::parse_decl(source).expect("fixture parses");
        let decl = crate::preprocess_decl_with_context(&decl, file);
        crate::elaborate_decl_and_register_with_context(env, &decl, file)
    }

    #[test]
    fn print_equations_realizes_once_in_the_defining_source() {
        let mut env = Environment::with_prelude();
        let mut owner = FileContext::new();
        let mut importer = FileContext::new();
        run(&mut env, &mut owner, "def sample (n : Nat) : Nat := n").expect("definition");
        let equation = Name::from_string("sample.eq_1");
        let error = run(&mut env, &mut importer, "#print equations sample")
            .expect_err("an importer cannot realize the owner's equation");
        assert!(error.to_string().contains("unavailable"));
        assert!(env.get_const(&equation).is_none());

        let first = run(&mut env, &mut owner, "#print equations sample").expect("realization");
        let registered = env.get_const(&equation).expect("admitted theorem");
        assert!(registered.value.is_some());
        assert!(has_defeq(&env, &equation));
        assert!(declared_here::declared_by(
            &env,
            owner.elab_unit(),
            &equation
        ));
        let repeated =
            run(&mut env, &mut importer, "#print eqns sample").expect("existing equation");
        assert!(crate::register::leaf_own_names(&repeated).is_empty());
        assert_eq!(
            crate::guard_msgs::result_messages(&first),
            crate::guard_msgs::result_messages(&repeated)
        );
        run(
            &mut env,
            &mut importer,
            "theorem sample_use : sample 2 = 2 := sample.eq_1 (n := 2)",
        )
        .expect("later proof uses the admitted equation");
    }

    #[test]
    fn print_equations_resolves_a_temporary_open() {
        let mut env = Environment::with_prelude();
        let mut file = FileContext::new();
        run(&mut env, &mut file, "def EqOwner.query : Nat := 37").expect("qualified definition");
        run(
            &mut env,
            &mut file,
            "open EqOwner in #print equations query",
        )
        .expect("realization through a temporary open");
        assert!(env
            .get_const(&Name::from_string("EqOwner.query.eq_1"))
            .is_some());
        let error = run(&mut env, &mut file, "#print equations query").expect_err("open ended");
        assert!(error.to_string().contains("unknown constant"));
    }

    #[test]
    fn print_equations_reports_known_inductives_without_equations() {
        let mut env = Environment::with_prelude();
        let mut file = FileContext::new();
        let result = run(&mut env, &mut file, "#print equations Nat").expect("known inductive");
        let messages = crate::guard_msgs::result_messages(&result);
        assert_eq!(messages.len(), 1);
        assert_eq!(messages[0].text, "'Nat' does not have equations");
    }
}
