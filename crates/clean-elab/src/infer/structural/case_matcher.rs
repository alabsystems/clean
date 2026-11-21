// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0

//! Stored dependent matchers for an exhaustive constructor split.

use clean_kernel::env::{MatcherAltInfo, MatcherDetails, MatcherInfo};
use clean_kernel::tc::LocalContext;
use clean_kernel::{BinderData, BinderInfo, Environment, Expr, ExprKind, FVarId, Level, Name};
use clean_parser::{DeclModifiers, Visibility};

use crate::infer::ElabResult;
use crate::namespace::NamespaceState;

#[derive(Clone)]
pub(super) struct Binder {
    pub(super) id: FVarId,
    info: BinderData,
    pub(super) ty: Expr,
}

impl Binder {
    pub(super) fn push(context: &mut LocalContext, info: impl Into<BinderData>, ty: Expr) -> Self {
        let info = info.into();
        let id = context.push(Name::anon(), ty.clone(), info);
        Self { id, info, ty }
    }

    pub(super) fn var(&self) -> Expr {
        Expr::fvar(self.id)
    }

    pub(super) fn close(&self, body: Expr, bind: fn(BinderData, Expr, Expr) -> Expr) -> Expr {
        bind(self.info, self.ty.clone(), body.abstract_fvar(self.id))
    }
}

pub(super) fn close_lambdas(binders: &[Binder], body: Expr) -> Expr {
    binders
        .iter()
        .rev()
        .fold(body, |body, b| b.close(body, Expr::lam))
}

pub(super) fn close_pis(binders: &[Binder], body: Expr) -> Expr {
    binders
        .iter()
        .rev()
        .fold(body, |body, b| b.close(body, Expr::pi))
}

pub(super) fn open_lambdas(
    context: &mut LocalContext,
    term: &Expr,
    count: usize,
) -> Option<(Vec<Binder>, Expr)> {
    let mut term = term.clone();
    let mut binders = Vec::with_capacity(count);
    for _ in 0..count {
        let ExprKind::Lam(info, ty, body) = term.kind() else {
            return None;
        };
        let binder = Binder::push(context, *info, ty.as_ref().clone());
        term = body.instantiate(&binder.var());
        binders.push(binder);
    }
    Some((binders, term))
}

pub(super) fn open_fields(
    context: &mut LocalContext,
    ty: &Expr,
    count: usize,
) -> Option<Vec<Binder>> {
    let mut ty = ty.clone();
    let mut fields = Vec::with_capacity(count);
    for _ in 0..count {
        let ExprKind::Pi(info, field_ty, body) = ty.kind() else {
            return None;
        };
        let field = Binder::push(context, *info, field_ty.as_ref().clone());
        ty = body.instantiate(&field.var());
        fields.push(field);
    }
    Some(fields)
}

fn constructor_pattern(
    name: &Name,
    major_type: &Expr,
    fields: &[Binder],
    numeric_zero: bool,
) -> Expr {
    if numeric_zero && *name == Name::from_string("Nat.zero") {
        let zero = Expr::nat_lit(0);
        Expr::apps(
            Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
            [
                major_type.clone(),
                zero.clone(),
                Expr::app(Expr::const_str("instOfNatNat"), zero),
            ],
        )
    } else {
        Expr::apps(
            Expr::const_(name.clone(), vec![]),
            fields.iter().map(Binder::var),
        )
    }
}

pub(super) fn wrap_nullary(context: &mut LocalContext, branch: Expr) -> Expr {
    let unit = Binder::push(context, BinderInfo::Default, Expr::const_str("Unit"));
    close_lambdas(&[unit], branch)
}

pub(super) fn case_matcher(
    env: &Environment,
    family: &Name,
    name: Name,
    numeric_zero: bool,
) -> Option<(ElabResult, MatcherInfo)> {
    let inductive = env.get_inductive(family)?;
    if inductive.num_params != 0 || inductive.num_indices != 0 || !inductive.level_params.is_empty()
    {
        return None;
    }
    let universe = Name::from_string("u_1");
    let level = Level::param(universe.clone());
    let major_type = Expr::const_(family.clone(), vec![]);
    let motive_type = Expr::arrow(major_type.clone(), Expr::sort(level.clone()));
    let mut context = LocalContext::new();
    let motive = Binder::push(&mut context, BinderInfo::Default, motive_type);
    let major = Binder::push(&mut context, BinderInfo::Default, major_type.clone());
    let mut branches = Vec::with_capacity(inductive.constructor_names.len());
    let mut branch_values = Vec::with_capacity(inductive.constructor_names.len());
    let mut alt_infos = Vec::with_capacity(inductive.constructor_names.len());
    for name in &inductive.constructor_names {
        let ctor = env.get_constructor(name)?;
        let mut branch_context = context.clone();
        let fields = open_fields(&mut branch_context, &ctor.type_, ctor.num_fields as usize)?;
        let pattern = constructor_pattern(name, &major_type, &fields, numeric_zero);
        let result = Expr::app(motive.var(), pattern);
        let branch_type = if fields.is_empty() {
            Expr::arrow(Expr::const_str("Unit"), result)
        } else {
            close_pis(&fields, result)
        };
        let branch = Binder::push(&mut context, BinderInfo::Default, branch_type);
        // The field context was cloned before creating `branch`. Reopen the
        // fields after its id so an abstraction cannot capture the branch.
        let mut branch_context = context.clone();
        let fields = open_fields(&mut branch_context, &ctor.type_, ctor.num_fields as usize)?;
        let value = if fields.is_empty() {
            Expr::app(branch.var(), Expr::const_str("Unit.unit"))
        } else {
            let call = Expr::apps(branch.var(), fields.iter().map(Binder::var));
            close_lambdas(&fields, call)
        };
        alt_infos.push(MatcherAltInfo {
            num_fields: ctor.num_fields,
            num_overlaps: 0,
            has_unit_thunk: fields.is_empty(),
        });
        branches.push(branch);
        branch_values.push(value);
    }
    let input = Binder::push(&mut context, BinderInfo::Default, major_type);
    let case_motive = close_lambdas(
        std::slice::from_ref(&input),
        Expr::app(motive.var(), input.var()),
    );
    let cases_on = Expr::const_(family.clone().str("casesOn"), vec![level]);
    let result = Expr::app(motive.var(), major.var());
    let cases = Expr::apps(
        cases_on,
        [case_motive, major.var()].into_iter().chain(branch_values),
    );
    let binders: Vec<_> = [motive, major].into_iter().chain(branches).collect();
    let definition = ElabResult::Definition {
        name,
        universe_params: vec![universe],
        ty: close_pis(&binders, result),
        val: close_lambdas(&binders, cases),
        modifiers: DeclModifiers {
            is_abbrev: true,
            ..Default::default()
        },
    };
    let details = MatcherDetails {
        alt_infos,
        overlaps: Vec::new(),
    };
    let info = MatcherInfo {
        num_params: 0,
        num_discrs: 1,
        alt_num_params: details.alt_num_params(0)?,
        u_elim_pos: Some(0),
        discr_names: vec![None],
        details: Some(details),
    };
    Some((definition, info))
}

/// The checked constructor matcher has disjoint alternatives, so its private
/// splitter is a reducible alias. Its equation statements use the same
/// checked telescope.
pub(super) fn matcher_auxiliaries(
    env: &Environment,
    namespace: &NamespaceState,
    family: &Name,
    matcher: &Name,
    numeric_zero: bool,
) -> Option<Vec<ElabResult>> {
    if namespace.main_module().is_none() {
        return Some(Vec::new());
    }
    let declaration = env.get_const(matcher)?;
    let [universe] = declaration.level_params.as_slice() else {
        return None;
    };
    let level = Level::param(universe.clone());
    let ExprKind::Pi(motive_info, motive_ty, matcher_ty) = declaration.type_.kind() else {
        return None;
    };
    let constructors = &env.get_inductive(family)?.constructor_names;
    let mut auxiliaries = Vec::with_capacity(constructors.len() + 1);
    for (index, constructor) in constructors.iter().enumerate() {
        let mut context = LocalContext::new();
        let motive = Binder::push(&mut context, *motive_info, motive_ty.as_ref().clone());
        let ty = matcher_ty.instantiate(&motive.var());
        let ExprKind::Pi(_, major_type, branch_telescope) = ty.kind() else {
            return None;
        };
        let constructor_info = env.get_constructor(constructor)?;
        let fields = open_fields(
            &mut context,
            &constructor_info.type_,
            constructor_info.num_fields as usize,
        )?;
        let pattern = constructor_pattern(constructor, major_type, &fields, numeric_zero);
        let branches = open_fields(
            &mut context,
            &branch_telescope.instantiate(&pattern),
            constructors.len(),
        )?;
        let actual = Expr::apps(
            Expr::const_(matcher.clone(), vec![level.clone()]),
            [motive.var(), pattern.clone()]
                .into_iter()
                .chain(branches.iter().map(Binder::var)),
        );
        let selected = if fields.is_empty() {
            Expr::app(branches[index].var(), Expr::const_str("Unit.unit"))
        } else {
            Expr::apps(branches[index].var(), fields.iter().map(Binder::var))
        };
        let type_ = Expr::app(motive.var(), pattern);
        let equation = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![level.clone()]),
            [type_.clone(), actual.clone(), selected],
        );
        let proof = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![level.clone()]),
            [type_, actual],
        );
        let binders: Vec<_> = [motive].into_iter().chain(fields).chain(branches).collect();
        let name = namespace.private_name(&matcher.clone().str(format!("eq_{}", index + 1)))?;
        auxiliaries.push(ElabResult::Theorem {
            name,
            universe_params: vec![universe.clone()],
            ty: close_pis(&binders, equation),
            proof: close_lambdas(&binders, proof),
            modifiers: DeclModifiers {
                visibility: Visibility::Private,
                ..Default::default()
            },
        });
    }
    let name = namespace.private_name(&matcher.clone().str("splitter"))?;
    auxiliaries.push(ElabResult::Definition {
        name,
        universe_params: vec![universe.clone()],
        ty: declaration.type_.clone(),
        val: Expr::const_(matcher.clone(), vec![level]),
        modifiers: DeclModifiers {
            visibility: Visibility::Private,
            is_abbrev: true,
            ..Default::default()
        },
    });
    Some(auxiliaries)
}
