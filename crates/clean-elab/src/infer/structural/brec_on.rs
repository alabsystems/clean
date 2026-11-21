// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0

//! Generate the named course-of-values form of a checked constructor recursion.
//!
//! This covers a non-indexed monomorphic family with one fixed parameter,
//! one decreasing parameter, and a closed result type. The direct recursion
//! remains the source of the constructor branches. Each induction-hypothesis
//! use must be an application to the unchanged fixed parameter.

use clean_kernel::env::{ConstantOrigin, MatcherInfo, Reducibility};
use clean_kernel::expr::ExprFolder;
use clean_kernel::name::NameInner;
use clean_kernel::tc::{LocalContext, TypeChecker};
use clean_kernel::{BinderInfo, ConstantKind, Declaration, Environment, Expr, ExprKind, Name};
use clean_parser::DeclModifiers;

use super::case_matcher::{
    case_matcher, close_lambdas, close_pis, matcher_auxiliaries, open_lambdas, wrap_nullary, Binder,
};
use super::recursion_equations::{smart_unfolding_definition, structural_equations};
use crate::infer::ElabResult;
use crate::namespace::NamespaceState;

pub(in crate::infer) struct NamedRecursion {
    pub(in crate::infer) dependencies: Vec<ElabResult>,
    pub(in crate::infer) equations: Vec<ElabResult>,
    pub(in crate::infer) value: Expr,
    pub(in crate::infer) matchers: Vec<(Name, MatcherInfo)>,
    pub(in crate::infer) reducibilities: Vec<(Name, Reducibility)>,
}

fn named_in_family(name: &Name, family: &Name) -> bool {
    matches!(name.inner(), NameInner::Str(parent, _) if parent.as_ref() == family)
}

fn already_generated_matcher(name: &Name, family: &Name) -> bool {
    matches!(name.inner(), NameInner::Str(parent, suffix)
        if named_in_family(parent, family)
            && suffix.strip_prefix("match_").is_some_and(|ordinal|
                ordinal.parse::<u32>().is_ok()))
}

fn install_matcher(
    env: &mut Environment,
    namespace: &NamespaceState,
    dependencies: &mut Vec<ElabResult>,
    owner: &Name,
    source_family: &Name,
    matcher_family: &Name,
    ordinal: u32,
    numeric_zero: bool,
) -> Option<(Name, MatcherInfo)> {
    let name = owner.clone().str(format!("match_{ordinal}"));
    let (planned, info) = case_matcher(env, matcher_family, name.clone(), numeric_zero)?;
    let ElabResult::Definition {
        universe_params,
        ty,
        val,
        ..
    } = &planned
    else {
        return None;
    };
    let resident = env
        .constants()
        .filter(|entry| {
            already_generated_matcher(&entry.name, source_family)
                && matches!(
                    env.get_constant_origin(&entry.name),
                    None | Some(ConstantOrigin::Kernel { .. })
                )
                && entry.kind == ConstantKind::Definition
                && entry.level_params == *universe_params
                && entry.type_ == *ty
                && entry.value.as_ref() == Some(val)
                && entry.reducibility == Reducibility::Reducible
        })
        .map(|entry| &entry.name)
        .min()
        .cloned();
    if let Some(resident) = resident {
        // A sibling body elaborates against this exact staging environment.
        // Detect any conflicting metadata here before choosing the lowering.
        env.register_matcher_info(resident.clone(), info.clone())
            .ok()?;
        return Some((resident, info));
    }
    check_generated(env, &planned)?;
    env.register_matcher_info(name.clone(), info.clone()).ok()?;
    dependencies.push(planned);
    for auxiliary in matcher_auxiliaries(env, namespace, matcher_family, &name, numeric_zero)? {
        check_generated(env, &auxiliary)?;
        dependencies.push(auxiliary);
    }
    Some((name, info))
}

fn check_generated(env: &mut Environment, planned: &ElabResult) -> Option<()> {
    let declaration = match planned {
        ElabResult::Definition {
            name,
            universe_params,
            ty,
            val,
            modifiers,
        } => Declaration::Definition {
            name: name.clone(),
            level_params: universe_params.clone(),
            type_: ty.clone(),
            value: val.clone(),
            is_reducible: modifiers.is_abbrev,
        },
        ElabResult::Theorem {
            name,
            universe_params,
            ty,
            proof,
            ..
        } => Declaration::Theorem {
            name: name.clone(),
            level_params: universe_params.clone(),
            type_: ty.clone(),
            value: proof.clone(),
        },
        _ => return None,
    };
    env.add_decl(declaration).ok()
}

struct RecursiveCalls<'a> {
    parameter: Expr,
    hypotheses: &'a [Binder],
    replacements: &'a [Expr],
    refused: bool,
}

impl ExprFolder for RecursiveCalls<'_> {
    fn fold_app(&mut self, fn_: &Expr, argument: &Expr) -> Expr {
        if let Some(position) = self
            .hypotheses
            .iter()
            .position(|hypothesis| hypothesis.var() == *fn_)
        {
            if *argument == self.parameter {
                return self.replacements[position].clone();
            }
            self.refused = true;
        }
        Expr::app(self.fold_expr(fn_), self.fold_expr(argument))
    }

    fn fold_fvar(&mut self, id: clean_kernel::FVarId) -> Expr {
        let var = Expr::fvar(id);
        self.refused |= self
            .hypotheses
            .iter()
            .any(|hypothesis| hypothesis.var() == var);
        var
    }
}

pub(super) fn rewrite_recursive_calls(
    body: &Expr,
    parameter: &Binder,
    fixed: &Binder,
    hypotheses: &[Binder],
    replacements: &[Expr],
) -> Option<Expr> {
    if replacements.len() != hypotheses.len() {
        return None;
    }
    let mut rewrite = RecursiveCalls {
        parameter: parameter.var(),
        hypotheses,
        replacements,
        refused: false,
    };
    let result = rewrite.fold_expr(body);
    (!rewrite.refused).then(|| result.subst_fvar(parameter.id, &fixed.var()))
}

fn history_result(history: &Expr, count: usize, position: usize) -> Expr {
    let product = Name::from_string("PProd");
    let mut pair = history.clone();
    for _ in 0..position {
        pair = Expr::proj(product.clone(), 1, pair);
    }
    if position + 1 < count {
        pair = Expr::proj(product.clone(), 0, pair);
    }
    Expr::proj(product, 0, pair)
}

pub(super) fn use_named_nat_match(
    context: &mut LocalContext,
    result: Expr,
    matcher: Option<&Name>,
) -> Option<Expr> {
    let ExprKind::Const(head, levels) = result.get_app_fn().kind() else {
        return Some(result);
    };
    if *head != Name::from_string("Nat.casesOn") {
        return Some(result);
    }
    let args = result.get_app_args();
    let [motive, subject, zero, succ] = args.as_slice() else {
        return None;
    };
    Some(Expr::apps(
        Expr::const_(matcher?.clone(), levels.to_vec()),
        [
            (*motive).clone(),
            (*subject).clone(),
            wrap_nullary(context, (*zero).clone()),
            (*succ).clone(),
        ],
    ))
}

fn convert_minor(
    context: &mut LocalContext,
    minor: &Expr,
    constructor: &Name,
    fields: usize,
    recursive_fields: usize,
    fixed: &Binder,
    below: &Expr,
    nested_nat_matcher: Option<&Name>,
) -> Option<Expr> {
    let (binders, result) = open_lambdas(context, minor, fields + recursive_fields + 1)?;
    let branch_fields = &binders[..fields];
    let hypotheses = &binders[fields..fields + recursive_fields];
    let parameter = binders.last()?;
    let ctor = Expr::apps(
        Expr::const_(constructor.clone(), vec![]),
        branch_fields.iter().map(Binder::var),
    );
    let history = Binder::push(context, BinderInfo::Default, Expr::app(below.clone(), ctor));
    let replacements: Vec<_> = (0..hypotheses.len())
        .map(|position| history_result(&history.var(), hypotheses.len(), position))
        .collect();
    let result = rewrite_recursive_calls(&result, parameter, fixed, hypotheses, &replacements)?;
    let result = use_named_nat_match(context, result, nested_nat_matcher)?;
    let branch = close_lambdas(branch_fields, close_lambdas(&[history], result));
    Some(if fields == 0 {
        wrap_nullary(context, branch)
    } else {
        branch
    })
}

pub(in crate::infer) fn named_brec_on(
    env: &Environment,
    namespace: &NamespaceState,
    owner: &Name,
    type_: &Expr,
    value: &Expr,
) -> Option<NamedRecursion> {
    let mut context = LocalContext::new();
    let (parameters, body) = open_lambdas(&mut context, value, 2)?;
    let [fixed, major] = parameters.as_slice() else {
        return None;
    };
    let ExprKind::Const(family, levels) = major.ty.kind() else {
        return None;
    };
    if !levels.is_empty() || !named_in_family(owner, family) {
        return None;
    }
    // Ordinary local registration has no import-origin entry. An explicitly
    // imported family is outside this source lowering's supported scope.
    if !matches!(
        env.get_constant_origin(family),
        None | Some(ConstantOrigin::Kernel { .. })
    ) {
        return None;
    }
    let below_name = family.clone().str("below");
    let brec_name = family.clone().str("brecOn");
    if [below_name.clone(), brec_name.clone()].iter().any(|name| {
        !env.get_const(name)
            .is_some_and(|entry| entry.level_params.len() == 1 && entry.value.is_some())
    }) {
        return None;
    }
    let ExprKind::Const(recursor_name, _) = body.get_app_fn().kind() else {
        return None;
    };
    if *recursor_name != family.clone().str("rec") {
        return None;
    }
    let recursor = env.get_recursor(recursor_name)?;
    if recursor.num_params != 0 || recursor.num_indices != 0 || recursor.num_motives != 1 {
        return None;
    }
    let constructor_count = recursor.rules.len();
    let args = body.get_app_args();
    if constructor_count == 0
        || args.len() != constructor_count + 3
        || *args[constructor_count + 1] != major.var()
        || *args[constructor_count + 2] != fixed.var()
    {
        return None;
    }
    let result_type = TypeChecker::with_context(env, context.clone())
        .infer_type(&body)
        .ok()?;
    if result_type.has_fvar_quick() || result_type.has_loose_bvars() {
        return None;
    }
    let level = TypeChecker::new(env).infer_sort(&result_type).ok()?;
    env.check_decl_readonly_strict(&Declaration::Definition {
        name: owner.clone(),
        level_params: vec![],
        type_: type_.clone(),
        value: value.clone(),
        is_reducible: false,
    })
    .ok()?;
    let motive = Expr::lam(BinderInfo::Default, major.ty.clone(), result_type.clone());
    let below = Expr::app(
        Expr::const_(below_name, vec![level.clone()]),
        motive.clone(),
    );
    let mut dependencies = Vec::new();
    let mut staged = env.clone();
    // One ordinary Nat split can survive inside a source constructor branch.
    // The matching syntax creates its first matcher before the outer split.
    let nested = recursor.rules.iter().zip(&args[1..=constructor_count]).any(|(rule, minor)| {
        let recursive = rule.recursive_fields.iter().filter(|flag| **flag).count();
        let mut local = context.clone();
        open_lambdas(&mut local, minor, rule.num_fields as usize + recursive + 1)
            .is_some_and(|(_, body)| matches!(body.get_app_fn().kind(), ExprKind::Const(name, _) if *name == Name::from_string("Nat.casesOn")))
    });
    let mut matchers = Vec::new();
    let nested_matcher = if nested {
        let (name, info) = install_matcher(
            &mut staged,
            namespace,
            &mut dependencies,
            owner,
            family,
            &Name::from_string("Nat"),
            1,
            true,
        )?;
        matchers.push((name.clone(), info));
        Some(name)
    } else {
        None
    };
    // The structural pass revises the outer matcher to take the history
    // argument. Its predecessor is consumed by the lowering and not stored.
    let (matcher, info) = install_matcher(
        &mut staged,
        namespace,
        &mut dependencies,
        owner,
        family,
        family,
        if nested { 3 } else { 2 },
        false,
    )?;
    matchers.push((matcher.clone(), info));
    let mut branches = Vec::with_capacity(constructor_count);
    for (rule, minor) in recursor.rules.iter().zip(&args[1..=constructor_count]) {
        let mut local = context.clone();
        branches.push(convert_minor(
            &mut local,
            minor,
            &rule.constructor_name,
            rule.num_fields as usize,
            rule.recursive_fields.iter().filter(|flag| **flag).count(),
            fixed,
            &below,
            nested_matcher.as_ref(),
        )?);
    }
    let case_major = Binder::push(&mut context, BinderInfo::Default, major.ty.clone());
    let history_type = Expr::app(below, case_major.var());
    let split_result = Expr::arrow(history_type.clone(), result_type.clone());
    let split_level = TypeChecker::with_context(&staged, context.clone())
        .infer_sort(&split_result)
        .ok()?;
    let split_motive = close_lambdas(std::slice::from_ref(&case_major), split_result);
    let history = Binder::push(&mut context, BinderInfo::Default, history_type);
    let cases = Expr::apps(
        Expr::const_(matcher.clone(), vec![split_level]),
        [split_motive, case_major.var()].into_iter().chain(branches),
    );
    let function = close_lambdas(
        &[fixed.clone(), case_major.clone(), history.clone()],
        Expr::app(cases, history.var()),
    );
    let function_type = close_pis(&[fixed.clone(), case_major, history], result_type.clone());
    let function_name = owner.clone().str("_f");
    let function_height = staged.get_max_height(&function);
    let functional = ElabResult::Definition {
        name: function_name.clone(),
        universe_params: vec![],
        ty: function_type,
        val: function,
        modifiers: DeclModifiers {
            is_abbrev: true,
            ..Default::default()
        },
    };
    check_generated(&mut staged, &functional)?;
    dependencies.push(functional);
    let body = Expr::apps(
        Expr::const_(brec_name, vec![level.clone()]),
        [
            motive,
            major.var(),
            Expr::app(Expr::const_(function_name, vec![]), fixed.var()),
        ],
    );
    let wrapper = close_lambdas(&parameters, body);
    let height = staged
        .get_max_height(&wrapper)
        .max(function_height)
        .checked_add(1)?;
    let reducibility = Reducibility::Regular(height);
    staged
        .add_decl_with_reducibility(
            Declaration::Definition {
                name: owner.clone(),
                level_params: vec![],
                type_: type_.clone(),
                value: wrapper.clone(),
                is_reducible: false,
            },
            reducibility,
        )
        .ok()?;
    let mut equations = if matches!(result_type.kind(), ExprKind::Sort(level) if level.is_zero()) {
        Vec::new()
    } else {
        structural_equations(
            &context,
            owner,
            family,
            &recursor.rules,
            &args[1..=constructor_count],
            fixed,
            major,
            &result_type,
            &level,
            &matcher,
            nested_matcher.as_ref(),
        )?
    };
    if namespace.main_module().is_some() && !level.is_zero() {
        equations.push(smart_unfolding_definition(
            &context,
            owner,
            &recursor.rules,
            &args[1..=constructor_count],
            fixed,
            major,
            &result_type,
            &level,
            &matcher,
            nested_matcher.as_ref(),
            type_,
        )?);
    }
    let mut reducibilities = vec![(owner.clone(), reducibility)];
    for equation in &equations {
        check_generated(&mut staged, equation)?;
        if let ElabResult::Definition { name, .. } = equation {
            // Smart unfolding refers to the checked wrapper. The resident
            // group applies hint overrides after registration, so preserve
            // the height computed with the wrapper's final hint here.
            reducibilities.push((name.clone(), staged.get_const(name)?.reducibility));
        }
    }
    Some(NamedRecursion {
        dependencies,
        equations,
        value: wrapper,
        matchers,
        reducibilities,
    })
}

#[cfg(test)]
mod matcher_tests {
    use super::*;

    #[test]
    fn a_conflicting_resident_matcher_in_staging_declines_the_lowering() {
        let mut env = Environment::with_prelude();
        let family = Name::from_string("OtherFamily");
        let nat = Name::from_string("Nat");
        let resident = family.clone().str("earlier").str("match_1");
        let owner = family.clone().str("later");
        let (decl, mut info) = case_matcher(&env, &nat, resident.clone(), false).unwrap();
        check_generated(&mut env, &decl).unwrap();
        info.discr_names[0] = Some(Name::from_string("h"));
        info.details = None;
        env.register_matcher_info(resident.clone(), info.clone())
            .unwrap();
        let mut dependencies = Vec::new();
        assert!(install_matcher(
            &mut env,
            &NamespaceState::new(),
            &mut dependencies,
            &owner,
            &family,
            &nat,
            1,
            false,
        )
        .is_none());
        assert!(dependencies.is_empty());
        assert_eq!(env.get_matcher_info(&resident), Some(&info));
        assert!(env.get_const(&owner.str("match_1")).is_none());
    }
}
