// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0

//! Ordinary source generation of the original constructor auxiliaries.
//! Candidates enter the environment only through the existing checked admission
//! paths. The caller publishes the complete candidate environment atomically.

use crate::tc::{LocalContext, TypeChecker};
use crate::{
    BinderData, BinderInfo, Declaration, Environment, Expr, ExprKind, FVarId, Level, Multiplicity,
    Name,
};

use super::Reducibility;

#[derive(Clone)]
struct Binder {
    id: FVarId,
    info: BinderData,
    ty: Expr,
}

impl Binder {
    fn push(context: &mut LocalContext, info: impl Into<BinderData>, ty: Expr) -> Self {
        let info = info.into();
        let id = context.push(Name::anon(), ty.clone(), info);
        Self { id, info, ty }
    }

    fn var(&self) -> Expr {
        Expr::fvar(self.id)
    }

    fn close(&self, body: Expr, make: fn(BinderData, Expr, Expr) -> Expr) -> Expr {
        make(self.info, self.ty.clone(), body.abstract_fvar(self.id))
    }
}

fn close_lambdas(binders: &[Binder], body: Expr) -> Expr {
    binders
        .iter()
        .rev()
        .fold(body, |body, binder| binder.close(body, Expr::lam))
}

fn close_pis(binders: &[Binder], body: Expr) -> Expr {
    binders
        .iter()
        .rev()
        .fold(body, |body, binder| binder.close(body, Expr::pi))
}

fn open_fields_using(
    context: &mut LocalContext,
    telescope: &Expr,
    count: usize,
    forced_info: Option<BinderInfo>,
) -> Option<Vec<Binder>> {
    let mut telescope = telescope.clone();
    let mut binders = Vec::with_capacity(count);
    for _ in 0..count {
        let ExprKind::Pi(info, domain, body) = telescope.kind() else {
            return None;
        };
        let info = forced_info.map_or(*info, BinderData::from);
        let field = Binder::push(context, info, domain.as_ref().clone());
        telescope = body.instantiate(&field.var());
        binders.push(field);
    }
    Some(binders)
}

fn open_fields(context: &mut LocalContext, telescope: &Expr, count: usize) -> Option<Vec<Binder>> {
    open_fields_using(context, telescope, count, None)
}

impl Environment {
    /// Build a complete checked set for the non-indexed source profile.
    pub(super) fn checked_source_constructor_auxiliaries(&self, family: &Name) -> Option<Self> {
        let info = self.get_inductive(family)?;
        if info.all_names.len() != 1
            || info.num_params != 0
            || info.num_indices != 0
            || !info.level_params.is_empty()
            || info.is_nested
            || !info.is_large_elim
            || info.constructor_names.len() < 3
            || self.is_unsafe(family)
            || !matches!(info.type_.kind(), ExprKind::Sort(sort) if !sort.is_zero())
            || ["genCtorIdx", "backward.linearNoConfusionType"]
                .into_iter()
                .any(|option| {
                    self.get_option(option)
                        .is_some_and(|value| value.as_deref() == Some("false"))
                })
        {
            return None;
        }
        let prerequisites = [
            "Nat",
            "Nat.ble",
            "Nat.decEq",
            "Eq",
            "Eq.refl",
            "Eq.ndrec",
            "Eq.symm",
            "PULift",
            "PULift.up",
            "PULift.down",
            "cond",
            "dite",
            "Not",
            "id",
        ];
        if prerequisites
            .iter()
            .any(|name| self.get_const(&Name::from_string(name)).is_none())
        {
            return None;
        }
        let mut has_fields = false;
        for name in &info.constructor_names {
            let constructor = self.get_constructor(name)?;
            let fields = open_fields(
                &mut LocalContext::new(),
                &constructor.type_,
                constructor.num_fields as usize,
            )?;
            has_fields |= !fields.is_empty();
            for field in &fields {
                if field.ty.has_fvar_quick()
                    || field.info.mult != Multiplicity::Many
                    || TypeChecker::new(self).infer_sort(&field.ty).ok()?
                        != Level::succ(Level::zero())
                {
                    return None;
                }
            }
        }
        if !has_fields {
            return None;
        }
        let (index, hint) = constructor_index(self, family)?;
        let mut staged = self.clone();
        staged.add_decl_with_reducibility(index, hint).ok()?;
        staged.mark_protected(family.clone().str("ctorIdx"));
        eliminators(&mut staged, family)?;
        let confusion_type = linear_no_confusion_type(&staged, family)?;
        staged.add_decl(confusion_type).ok()?;
        staged.mark_protected(family.clone().str("noConfusionType"));
        let confusion = no_confusion(&staged, family)?;
        staged.add_decl(confusion).ok()?;
        constructor_no_confusions(&mut staged, family)?;
        Some(staged)
    }

    /// The ordinal uses only the checked family, including when a separate
    /// source no-confusion or eliminator construction is unavailable.
    pub(super) fn checked_source_constructor_index(&self, family: &Name) -> Option<Self> {
        let (definition, hint) = constructor_index(self, family)?;
        let info = self.get_inductive(family)?;
        let name = family.clone().str("ctorIdx");
        let mut staged = self.clone();
        staged.add_decl_with_reducibility(definition, hint).ok()?;
        staged.mark_protected(name.clone());
        if info.constructor_names.len() == 1 {
            staged.register_macro_inline(name.clone());
        }
        let enumeration = info.all_names.len() == 1
            && info.num_params == 0
            && info.num_indices == 0
            && !info.is_recursive
            && !info.constructor_names.is_empty()
            && info.constructor_names.iter().all(|name| {
                self.get_constructor(name)
                    .is_some_and(|constructor| constructor.num_fields == 0)
            });
        if enumeration {
            let alias = family.clone().str("toCtorIdx");
            let index = staged.get_const(&name)?;
            let level_params = index.level_params.clone();
            let levels: Vec<_> = level_params.iter().cloned().map(Level::param).collect();
            let declaration = Declaration::Definition {
                name: alias.clone(),
                level_params,
                type_: index.type_.clone(),
                value: Expr::const_(name.clone(), levels),
                is_reducible: true,
            };
            staged
                .add_decl_with_reducibility(declaration, Reducibility::Reducible)
                .ok()?;
            staged.mark_protected(alias.clone());
            staged.register_deprecated(alias, Some(format!("Use `{name}` instead")));
        }
        Some(staged)
    }
}

/// Build the checked source declaration's type, body, and ordinary height.
/// The caller retains its hint only after kernel admission succeeds.
fn constructor_index(env: &Environment, family: &Name) -> Option<(Declaration, Reducibility)> {
    let name = family.clone().str("ctorIdx");
    if env.get_const(&name).is_some()
        || env.is_unsafe(family)
        || env
            .get_option("genCtorIdx")
            .is_some_and(|value| value.as_deref() == Some("false"))
    {
        return None;
    }
    let inductive = env.get_inductive(family)?;
    let cases = family.clone().str("casesOn");
    if env.get_const(&cases)?.level_params.len() != inductive.level_params.len() + 1 {
        return None;
    }
    let mut result = &inductive.type_;
    while let ExprKind::Pi(_, _, body) = result.kind() {
        result = body;
    }
    if !matches!(result.kind(), ExprKind::Sort(sort) if !sort.is_zero()) {
        return None;
    }
    let constructors = inductive
        .constructor_names
        .iter()
        .map(|name| env.get_constructor(name))
        .collect::<Option<Vec<_>>>()?;
    let nat = Expr::const_str("Nat");
    let levels: Vec<_> = inductive
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect();
    let mut context = LocalContext::new();
    let parameter_count = inductive.num_params as usize;
    let mut arguments = open_fields_using(
        &mut context,
        &inductive.type_,
        parameter_count + inductive.num_indices as usize,
        Some(BinderInfo::Implicit),
    )?;
    let family_type = Expr::apps(
        Expr::const_(family.clone(), levels.clone()),
        arguments.iter().map(Binder::var),
    );
    let subject = Binder::push(&mut context, BinderInfo::Default, family_type.clone());
    let (parameters, indices) = arguments.split_at(parameter_count);
    let ordinal = if constructors.len() == 1 {
        Expr::nat_lit(0)
    } else {
        let motive = close_lambdas(
            &[indices, std::slice::from_ref(&subject)].concat(),
            nat.clone(),
        );
        let cases_levels = std::iter::once(Level::succ(Level::zero()))
            .chain(levels)
            .collect::<Vec<_>>();
        let mut value = Expr::apps(
            Expr::const_(cases, cases_levels),
            parameters
                .iter()
                .map(Binder::var)
                .chain(std::iter::once(motive))
                .chain(indices.iter().map(Binder::var))
                .chain(std::iter::once(subject.var())),
        );
        for constructor in constructors {
            let mut telescope = constructor.type_.clone();
            for parameter in parameters {
                let ExprKind::Pi(_, _, body) = telescope.kind() else {
                    return None;
                };
                telescope = body.instantiate(&parameter.var());
            }
            let fields = open_fields(
                &mut context.clone(),
                &telescope,
                constructor.num_fields as usize,
            )?;
            let branch = close_lambdas(&fields, Expr::nat_lit(constructor.constructor_idx.into()));
            value = Expr::app(value, branch);
        }
        value
    };
    let type_ = close_pis(&arguments, Expr::arrow(family_type, nat));
    arguments.push(subject);
    let value = close_lambdas(&arguments, ordinal);
    let height = env.get_max_height(&value).checked_add(1)?;
    Some((
        Declaration::Definition {
            name,
            level_params: inductive.level_params.clone(),
            type_,
            value,
            is_reducible: false,
        },
        Reducibility::Regular(height),
    ))
}

#[cfg(test)]
mod index_tests {
    use super::*;
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    #[test]
    fn source_ordinal_applies_to_parameterized_indexed_constructors() {
        let mut environment = Environment::with_prelude();
        let family = Name::from_string("SourceIndexTest");
        let first = family.clone().str("first");
        let second = family.clone().str("second");
        let universe = Name::from_string("u");
        let level = Level::param(universe.clone());
        let type_ = Expr::sort(Level::succ(level.clone()));
        let target = |parameter, index| {
            Expr::apps(
                Expr::const_(family.clone(), vec![level.clone()]),
                [parameter, Expr::nat_lit(index)],
            )
        };
        let decl = InductiveDecl {
            level_params: vec![universe],
            num_params: 1,
            types: vec![InductiveType {
                name: family.clone(),
                type_: Expr::arrow(
                    type_.clone(),
                    Expr::arrow(Expr::const_str("Nat"), type_.clone()),
                ),
                constructors: vec![
                    Constructor {
                        name: first.clone(),
                        type_: Expr::arrow(type_.clone(), target(Expr::bvar(0), 0)),
                    },
                    Constructor {
                        name: second.clone(),
                        type_: Expr::arrow(
                            type_,
                            Expr::arrow(Expr::bvar(0), target(Expr::bvar(1), 1)),
                        ),
                    },
                ],
            }],
        };
        environment.add_source_inductive(decl).unwrap();

        let nat = Expr::const_str("Nat");
        let levels = vec![Level::zero()];
        let index_name = family.str("ctorIdx");
        let index = Expr::const_(index_name.clone(), levels.clone());
        let checker = TypeChecker::new(&environment);
        let first = Expr::app(Expr::const_(first, levels.clone()), nat.clone());
        let second = Expr::apps(
            Expr::const_(second, levels),
            [nat.clone(), Expr::nat_lit(5)],
        );
        let index_of_first = Expr::apps(index.clone(), [nat.clone(), Expr::nat_lit(0), first]);
        let index_of_second = Expr::apps(index, [nat, Expr::nat_lit(1), second]);
        assert!(checker.is_def_eq(&index_of_first, &Expr::nat_lit(0)));
        assert!(checker.is_def_eq(&index_of_second, &Expr::nat_lit(1)));
        assert!(!checker.is_def_eq(&index_of_second, &Expr::nat_lit(0)));
        let index_info = environment
            .get_const(&index_name)
            .expect("checked source index");
        let ExprKind::Pi(info, _, _) = index_info.type_.kind() else {
            panic!("the index retains its family parameter")
        };
        assert_eq!(*info, BinderData::from(BinderInfo::Implicit));
    }

    #[test]
    fn source_enumeration_ordinal_emits_protected_alias_and_observes_option() {
        let mut environment = Environment::with_prelude();
        let family = Name::from_string("SourceOrdinalTest");
        let type_ = Expr::const_(family.clone(), vec![]);
        let decl = InductiveDecl {
            level_params: Vec::new(),
            num_params: 0,
            types: vec![InductiveType {
                name: family.clone(),
                type_: Expr::sort(Level::succ(Level::zero())),
                constructors: ["first", "second"]
                    .into_iter()
                    .map(|suffix| Constructor {
                        name: family.clone().str(suffix),
                        type_: type_.clone(),
                    })
                    .collect(),
            }],
        };
        let mut disabled = environment.clone();
        disabled.set_option("genCtorIdx".to_owned(), Some("false".to_owned()));
        disabled.add_source_inductive(decl.clone()).unwrap();
        environment.add_source_inductive(decl).unwrap();
        let index = family.clone().str("ctorIdx");
        let alias = family.str("toCtorIdx");
        assert_eq!(
            environment.get_const(&alias).unwrap().value,
            Some(Expr::const_(index.clone(), Vec::new())),
        );
        assert_eq!(
            environment.get_reducibility(&alias),
            Some(Reducibility::Reducible)
        );
        assert!(environment.is_deprecated(&alias));
        assert!(disabled.get_const(&index).is_none());
        assert!(disabled.get_const(&alias).is_none());
    }
}

fn nat_equality(level: &Level, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![level.clone()]),
        [Expr::const_str("Nat"), left, right],
    )
}

fn ordinal(index: usize) -> Expr {
    Expr::nat_lit(index as u64)
}

fn lookup(
    index: &Expr,
    choices: &[Expr],
    first: usize,
    table_type: &Expr,
    table_level: &Level,
) -> Expr {
    if let [only] = choices {
        return only.clone();
    }
    let middle = choices.len() / 2;
    let (low, high) = choices.split_at(middle);
    let threshold = Expr::apps(
        Expr::const_str("Nat.ble"),
        [index.clone(), ordinal(first + middle - 1)],
    );
    Expr::apps(
        Expr::const_(Name::from_string("cond"), vec![table_level.clone()]),
        [
            table_type.clone(),
            threshold,
            lookup(index, low, first, table_type, table_level),
            lookup(index, high, first + middle, table_type, table_level),
        ],
    )
}

fn add_definition(env: &mut Environment, name: Name, universe: &Name, value: Expr) -> Option<()> {
    let type_ = TypeChecker::new(env).infer_type(&value).ok()?;
    let declaration = Declaration::Definition {
        name,
        level_params: vec![universe.clone()],
        type_,
        value,
        is_reducible: true,
    };
    env.add_decl(declaration).ok()
}

fn eliminators(env: &mut Environment, family: &Name) -> Option<()> {
    let info = env.get_inductive(family)?;
    let constructors: Vec<_> = info
        .constructor_names
        .iter()
        .map(|name| env.get_constructor(name).cloned())
        .collect::<Option<_>>()?;
    let cases = family.clone().str("casesOn");
    let stored_cases = env.get_const(&cases)?;
    let [universe] = stored_cases.level_params.as_slice() else {
        return None;
    };
    let universe = universe.clone();
    let motive_level = Level::param(universe.clone());
    let one = Level::succ(Level::zero());
    let nat = Expr::const_str("Nat");
    let mut context = LocalContext::new();
    let walked = open_fields(&mut context, &stored_cases.type_, constructors.len() + 2)?;
    let [motive, subject, alts @ ..] = walked.as_slice() else {
        return None;
    };
    {
        let checker = TypeChecker::with_context(env, context.clone());
        for alt in alts {
            if checker.infer_sort(&alt.ty).ok()?.normalize() != motive_level {
                return None;
            }
        }
    }
    let table_sort = Level::max(one.clone(), motive_level.clone());
    let table_type = Expr::sort(table_sort.clone());
    let index = Binder::push(&mut context, BinderInfo::Default, nat.clone());
    let lift = |name| {
        Expr::const_(
            Name::from_string(name),
            vec![motive_level.clone(), motive_level.clone()],
        )
    };
    let choice: Vec<_> = alts
        .iter()
        .map(|alt| Expr::app(lift("PULift"), alt.ty.clone()))
        .collect();
    let level_order = Level::succ(table_sort.clone());
    let value = close_lambdas(
        &[motive.clone(), index.clone()],
        lookup(&index.var(), &choice, 0, &table_type, &level_order),
    );
    let table_name = family.clone().str("ctorElimType");
    add_definition(env, table_name.clone(), &universe, value)?;
    env.mark_protected(table_name.clone());
    let table = Expr::app(
        Expr::const_(table_name, vec![motive_level.clone()]),
        motive.var(),
    );
    let indexer = Expr::const_(family.clone().str("ctorIdx"), vec![]);
    let rank = Expr::app(indexer.clone(), subject.var());
    let subject_eq = nat_equality(&one, index.var(), rank.clone());
    let proof = Binder::push(&mut context, BinderInfo::Default, subject_eq.clone());
    let branch = Binder::push(
        &mut context,
        BinderInfo::Default,
        Expr::app(table.clone(), index.var()),
    );
    let case_motive = close_lambdas(
        std::slice::from_ref(subject),
        Expr::arrow(subject_eq, Expr::app(motive.var(), subject.var())),
    );
    let mut cases_applied = Expr::apps(
        Expr::const_(cases, vec![motive_level.clone()]),
        [case_motive, subject.var()],
    );
    for (position, (constructor, alternate)) in constructors.iter().zip(alts).enumerate() {
        let mut local = context.clone();
        let fields = open_fields(
            &mut local,
            &constructor.type_,
            constructor.num_fields as usize,
        )?;
        let equality = Binder::push(
            &mut local,
            BinderInfo::Default,
            nat_equality(&one, index.var(), ordinal(position)),
        );
        let cast = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.ndrec"),
                vec![table_sort.clone(), one.clone()],
            ),
            [
                nat.clone(),
                index.var(),
                table.clone(),
                branch.var(),
                ordinal(position),
                equality.var(),
            ],
        );
        let lowered = Expr::apps(lift("PULift.down"), [alternate.ty.clone(), cast]);
        let applied = Expr::apps(lowered, fields.iter().map(Binder::var));
        let binders: Vec<_> = fields.into_iter().chain([equality]).collect();
        cases_applied = Expr::app(cases_applied, close_lambdas(&binders, applied));
    }
    let eliminator = family.clone().str("ctorElim");
    let value = close_lambdas(
        &[
            motive.clone(),
            index,
            subject.clone(),
            proof.clone(),
            branch,
        ],
        Expr::app(cases_applied, proof.var()),
    );
    add_definition(env, eliminator.clone(), &universe, value)?;
    env.mark_protected(eliminator.clone());
    for (position, (constructor, alternate)) in constructors.iter().zip(alts).enumerate() {
        let proof = Binder::push(
            &mut context,
            BinderInfo::Default,
            nat_equality(&one, rank.clone(), ordinal(position)),
        );
        let symmetry = Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![one.clone()]),
            [nat.clone(), rank.clone(), ordinal(position), proof.var()],
        );
        let lifted = Expr::apps(lift("PULift.up"), [alternate.ty.clone(), alternate.var()]);
        let value = Expr::apps(
            Expr::const_(eliminator.clone(), vec![motive_level.clone()]),
            [
                motive.var(),
                ordinal(position),
                subject.var(),
                symmetry,
                lifted,
            ],
        );
        let value = close_lambdas(
            &[motive.clone(), subject.clone(), proof, alternate.clone()],
            value,
        );
        let name = constructor.name.clone().str("elim");
        add_definition(env, name.clone(), &universe, value)?;
        env.mark_protected(name);
    }
    Some(())
}

fn equality(carrier: &Expr, level: &Level, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![level.clone()]),
        [carrier.clone(), left, right],
    )
}

fn constructor_no_confusions(env: &mut Environment, family: &Name) -> Option<()> {
    let constructors = env.get_inductive(family)?.constructor_names.clone();
    let recursor = env.get_const(&family.clone().str("rec"))?;
    let [universe] = recursor.level_params.as_slice() else {
        return None;
    };
    let universe = universe.clone();
    let level = Level::param(universe.clone());
    let family_type = Expr::const_(family.clone(), vec![]);
    let family_sort = TypeChecker::new(env).infer_sort(&family_type).ok()?;
    for name in constructors {
        let constructor = env.get_constructor(&name)?;
        if constructor.num_fields == 0 {
            continue;
        }
        let mut context = LocalContext::new();
        let motive = Binder::push(
            &mut context,
            BinderInfo::Implicit,
            Expr::sort(level.clone()),
        );
        let fields1 = open_fields_using(
            &mut context,
            &constructor.type_,
            constructor.num_fields as usize,
            Some(BinderInfo::Implicit),
        )?;
        let fields2 = open_fields_using(
            &mut context,
            &constructor.type_,
            constructor.num_fields as usize,
            Some(BinderInfo::Implicit),
        )?;
        let constructor_term = Expr::const_(name.clone(), vec![]);
        let left = Expr::apps(constructor_term.clone(), fields1.iter().map(Binder::var));
        let right = Expr::apps(constructor_term, fields2.iter().map(Binder::var));
        let field_eqs = {
            let tc = TypeChecker::with_context(env, context.clone());
            fields1
                .iter()
                .zip(&fields2)
                .map(|(a, b)| {
                    if a.ty != b.ty {
                        return None;
                    }
                    Some(equality(
                        &a.ty,
                        &tc.infer_sort(&a.ty).ok()?,
                        a.var(),
                        b.var(),
                    ))
                })
                .collect::<Option<Vec<_>>>()?
        };
        let k_type = field_eqs
            .into_iter()
            .rev()
            .fold(motive.var(), |result, hypothesis| {
                Expr::arrow(hypothesis, result)
            });
        let proof = Binder::push(
            &mut context,
            BinderInfo::Default,
            equality(&family_type, &family_sort, left.clone(), right.clone()),
        );
        let k = Binder::push(&mut context, BinderInfo::Default, k_type);
        let result_term = Expr::apps(
            Expr::const_(family.clone().str("noConfusion"), vec![level.clone()]),
            [motive.var(), left, right, proof.var(), k.var()],
        );
        let result_term = Expr::apps(
            Expr::const_(Name::from_string("id"), vec![level.clone()]),
            [motive.var(), result_term],
        );
        let binders: Vec<_> = [motive]
            .into_iter()
            .chain(fields1)
            .chain(fields2)
            .chain([proof, k])
            .collect();
        add_definition(
            env,
            name.str("noConfusion"),
            &universe,
            close_lambdas(&binders, result_term),
        )?;
    }
    Some(())
}

fn linear_no_confusion_type(env: &Environment, family: &Name) -> Option<Declaration> {
    let info = env.get_inductive(family)?;
    let case_name = family.clone().str("casesOn");
    let cases = env.get_const(&case_name)?;
    let [universe] = cases.level_params.as_slice() else {
        return None;
    };
    let result_level = Level::param(universe.clone());
    let result_sort = Expr::sort(result_level.clone());
    let elimination_level = Level::succ(result_level);
    let family_type = Expr::const_(family.clone(), vec![]);
    let one = Level::succ(Level::zero());
    let mut context = LocalContext::new();
    let result = Binder::push(&mut context, BinderInfo::Default, result_sort.clone());
    let first = Binder::push(&mut context, BinderInfo::Default, family_type.clone());
    let second = Binder::push(&mut context, BinderInfo::Default, family_type.clone());
    let result_motive = Expr::lam(BinderInfo::Default, family_type, result_sort.clone());
    let mut body = Expr::apps(
        Expr::const_(case_name, vec![elimination_level.clone()]),
        [result_motive.clone(), first.var()],
    );
    let rank = Expr::app(
        Expr::const_(family.clone().str("ctorIdx"), vec![]),
        second.var(),
    );
    for (position, name) in info.constructor_names.iter().enumerate() {
        let constructor = env.get_constructor(name)?;
        let mut branch_context = context.clone();
        let left_fields = open_fields(
            &mut branch_context,
            &constructor.type_,
            constructor.num_fields as usize,
        )?;
        let rank_equality = nat_equality(&one, rank.clone(), ordinal(position));
        let decision = Expr::apps(
            Expr::const_str("Nat.decEq"),
            [rank.clone(), ordinal(position)],
        );
        let pos = Binder::push(
            &mut branch_context,
            BinderInfo::Default,
            rank_equality.clone(),
        );
        let neg = Binder::push(
            &mut branch_context,
            BinderInfo::Default,
            Expr::app(Expr::const_str("Not"), rank_equality.clone()),
        );
        let right_fields = open_fields(
            &mut branch_context,
            &constructor.type_,
            constructor.num_fields as usize,
        )?;
        let tc = TypeChecker::with_context(env, branch_context.clone());
        let field_equalities: Vec<_> = left_fields
            .iter()
            .zip(&right_fields)
            .map(|(left, right)| {
                if left.ty != right.ty {
                    return None;
                }
                Some(equality(
                    &left.ty,
                    &tc.infer_sort(&left.ty).ok()?,
                    left.var(),
                    right.var(),
                ))
            })
            .collect::<Option<Vec<_>>>()?;
        let continuation = field_equalities
            .into_iter()
            .rev()
            .fold(result.var(), |ty, premise| Expr::arrow(premise, ty));
        let generated_body = close_lambdas(&right_fields, Expr::arrow(continuation, result.var()));
        let yes = Expr::apps(
            Expr::const_(name.clone().str("elim"), vec![elimination_level.clone()]),
            [
                result_motive.clone(),
                second.var(),
                pos.var(),
                generated_body,
            ],
        );
        let choice = Expr::apps(
            Expr::const_(Name::from_string("dite"), vec![elimination_level.clone()]),
            [
                result_sort.clone(),
                rank_equality,
                decision,
                close_lambdas(&[pos], yes),
                close_lambdas(&[neg], result.var()),
            ],
        );
        body = Expr::app(body, close_lambdas(&left_fields, choice));
    }
    let binders = [result, first, second];
    let type_ = close_pis(&binders, result_sort);
    let value = close_lambdas(&binders, body);
    let declaration = Declaration::Definition {
        name: family.clone().str("noConfusionType"),
        level_params: vec![universe.clone()],
        type_,
        value,
        is_reducible: true,
    };
    Some(declaration)
}

fn no_confusion(env: &Environment, family: &Name) -> Option<Declaration> {
    let info = env.get_inductive(family)?;
    let cases = family.clone().str("casesOn");
    let rec = env.get_const(&family.clone().str("rec"))?;
    let [universe] = rec.level_params.as_slice() else {
        return None;
    };
    let motive_level = Level::param(universe.clone());
    let family_type = Expr::const_(family.clone(), vec![]);
    let family_level = TypeChecker::new(env).infer_sort(&family_type).ok()?;
    let mut context = LocalContext::new();
    let result = Binder::push(
        &mut context,
        BinderInfo::Implicit,
        Expr::sort(motive_level.clone()),
    );
    let left = Binder::push(&mut context, BinderInfo::Implicit, family_type.clone());
    let right = Binder::push(&mut context, BinderInfo::Implicit, family_type.clone());
    let eq = Binder::push(
        &mut context,
        BinderInfo::Default,
        equality(&family_type, &family_level, left.var(), right.var()),
    );
    let form = |a, b| {
        Expr::apps(
            Expr::const_(
                family.clone().str("noConfusionType"),
                vec![motive_level.clone()],
            ),
            [result.var(), a, b],
        )
    };
    let transport_locus = Binder::push(&mut context, BinderInfo::Implicit, family_type.clone());
    let motive = close_lambdas(
        std::slice::from_ref(&transport_locus),
        form(left.var(), transport_locus.var()),
    );
    let diagonal = close_lambdas(
        std::slice::from_ref(&transport_locus),
        form(transport_locus.var(), transport_locus.var()),
    );
    let mut cases = Expr::apps(
        Expr::const_(cases, vec![motive_level.clone()]),
        [diagonal, left.var()],
    );
    for name in &info.constructor_names {
        let constructor = env.get_constructor(name)?;
        let mut local = context.clone();
        let fields = open_fields(
            &mut local,
            &constructor.type_,
            constructor.num_fields as usize,
        )?;
        let tc = TypeChecker::with_context(env, local.clone());
        let field_levels = fields
            .iter()
            .map(|field| tc.infer_sort(&field.ty).ok())
            .collect::<Option<Vec<_>>>()?;
        let premises = fields
            .iter()
            .zip(&field_levels)
            .map(|(field, level)| equality(&field.ty, level, field.var(), field.var()));
        let ktype = premises
            .rev()
            .fold(result.var(), |tail, premise| Expr::arrow(premise, tail));
        let k = Binder::push(&mut local, BinderInfo::Default, ktype);
        let reflexivities = fields.iter().zip(field_levels).map(|(field, level)| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), vec![level]),
                [field.ty.clone(), field.var()],
            )
        });
        let handled = Expr::apps(k.var(), reflexivities);
        let minor_binders: Vec<_> = fields.into_iter().chain([k]).collect();
        cases = Expr::app(cases, close_lambdas(&minor_binders, handled));
    }
    let body = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.ndrec"),
            vec![motive_level.clone(), family_level],
        ),
        [
            family_type,
            left.var(),
            motive,
            cases,
            right.var(),
            eq.var(),
        ],
    );
    let type_result = form(left.var(), right.var());
    let binders = [result, left, right, eq];
    let type_ = close_pis(&binders, type_result);
    let value = close_lambdas(&binders, body);
    let declaration = Declaration::Definition {
        name: family.clone().str("noConfusion"),
        level_params: vec![universe.clone()],
        type_,
        value,
        is_reducible: true,
    };
    Some(declaration)
}
