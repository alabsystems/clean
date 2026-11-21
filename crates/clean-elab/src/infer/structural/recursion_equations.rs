// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0

//! Checked equation statements for the stored named structural recursion.

use clean_kernel::expr::MDataValue;
use clean_kernel::inductive::RecursorRule;
use clean_kernel::tc::LocalContext;
use clean_kernel::{BinderInfo, Expr, Level, Name};
use clean_parser::DeclModifiers;

use super::brec_on::{rewrite_recursive_calls, use_named_nat_match};
use super::case_matcher::{close_lambdas, close_pis, open_lambdas, wrap_nullary, Binder};
use crate::infer::ElabResult;

struct EquationBranch {
    fields: Vec<Binder>,
    constructor: Expr,
    rhs: Expr,
}

fn open_equation_branch(
    context: &mut LocalContext,
    owner: &Name,
    rule: &RecursorRule,
    minor: &Expr,
    fixed: &Binder,
    nested_matcher: Option<&Name>,
) -> Option<EquationBranch> {
    let fields = rule.num_fields as usize;
    if fields != rule.recursive_fields.len() {
        return None;
    }
    let recursive = rule
        .recursive_fields
        .iter()
        .filter(|is_recursive| **is_recursive)
        .count();
    let (locals, body) = open_lambdas(context, minor, fields + recursive + 1)?;
    let recursive_apply = Expr::app(Expr::const_(owner.clone(), vec![]), fixed.var());
    let replacements: Vec<_> = locals[..fields]
        .iter()
        .zip(&rule.recursive_fields)
        .filter(|(_, recursive)| **recursive)
        .map(|(field, _)| Expr::app(recursive_apply.clone(), field.var()))
        .collect();
    let result = rewrite_recursive_calls(
        &body,
        locals.last()?,
        fixed,
        &locals[fields..fields + recursive],
        &replacements,
    )?;
    let rhs = use_named_nat_match(context, result, nested_matcher)?;
    let fields = locals[..fields].to_vec();
    let constructor = Expr::apps(
        Expr::const_(rule.constructor_name.clone(), vec![]),
        fields.iter().map(Binder::var),
    );
    Some(EquationBranch {
        fields,
        constructor,
        rhs,
    })
}

fn close_case(context: &mut LocalContext, fields: &[Binder], rhs: Expr) -> Expr {
    if fields.is_empty() {
        wrap_nullary(context, rhs)
    } else {
        close_lambdas(fields, rhs)
    }
}

fn smart_unfold_annotation(name: &str, expression: Expr) -> Expr {
    Expr::mdata(
        vec![(Name::from_string(name), MDataValue::Bool(true))],
        expression,
    )
}

/// The checked direct branches already refer to the original function at
/// recursive calls. Mark the outer structural match and each of its branch
/// bodies. A nested Nat match in this lowering is retained in the branch.
pub(super) fn smart_unfolding_definition(
    context: &LocalContext,
    owner: &Name,
    rules: &[RecursorRule],
    minors: &[&Expr],
    fixed: &Binder,
    major: &Binder,
    result: &Expr,
    level: &Level,
    matcher: &Name,
    nested_matcher: Option<&Name>,
    type_: &Expr,
) -> Option<ElabResult> {
    let motive = Expr::lam(BinderInfo::Default, major.ty.clone(), result.clone());
    let alternatives = rules
        .iter()
        .zip(minors)
        .map(|(rule, minor)| {
            let mut local = context.clone();
            let branch =
                open_equation_branch(&mut local, owner, rule, minor, fixed, nested_matcher)?;
            let rhs = smart_unfold_annotation("sunfoldMatchAlt", branch.rhs);
            Some(close_case(&mut local, &branch.fields, rhs))
        })
        .collect::<Option<Vec<_>>>()?;
    let body = Expr::apps(
        Expr::const_(matcher.clone(), vec![level.clone()]),
        [motive, major.var()].into_iter().chain(alternatives),
    );
    let smart_body = smart_unfold_annotation("sunfoldMatch", body);
    Some(ElabResult::Definition {
        name: owner.clone().str("_sunfold"),
        universe_params: vec![],
        ty: type_.clone(),
        val: close_lambdas(&[fixed.clone(), major.clone()], smart_body),
        modifiers: DeclModifiers::default(),
    })
}

fn eq(level: &Level, carrier: &Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![level.clone()]),
        [carrier.clone(), lhs, rhs],
    )
}

fn refl(level: &Level, carrier: &Expr, lhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![level.clone()]),
        [carrier.clone(), lhs],
    )
}

pub(super) fn structural_equations(
    context: &LocalContext,
    owner: &Name,
    family: &Name,
    rules: &[RecursorRule],
    minors: &[&Expr],
    fixed: &Binder,
    major: &Binder,
    result: &Expr,
    level: &Level,
    matcher: &Name,
    nested_matcher: Option<&Name>,
) -> Option<Vec<ElabResult>> {
    let mut equations = Vec::with_capacity(rules.len() + 1);
    let mut alternatives = Vec::with_capacity(rules.len());
    let mut case_proofs = Vec::with_capacity(rules.len());
    let head = Expr::app(Expr::const_(owner.clone(), vec![]), fixed.var());
    for (index, (rule, minor)) in rules.iter().zip(minors).enumerate() {
        let mut local = context.clone();
        let branch = open_equation_branch(&mut local, owner, rule, minor, fixed, nested_matcher)?;
        let lhs = Expr::app(head.clone(), branch.constructor);
        let statement = eq(level, result, lhs.clone(), branch.rhs.clone());
        let proof = refl(level, result, lhs);
        case_proofs.push(close_lambdas(&branch.fields, proof.clone()));
        alternatives.push(close_case(&mut local, &branch.fields, branch.rhs));
        let binders: Vec<_> = std::iter::once(fixed.clone())
            .chain(branch.fields)
            .collect();
        equations.push(ElabResult::Theorem {
            name: owner.clone().str(format!("eq_{}", index + 1)),
            universe_params: vec![],
            ty: close_pis(&binders, statement),
            proof: close_lambdas(&binders, proof),
            modifiers: DeclModifiers::default(),
        });
    }

    let result_motive = Expr::lam(BinderInfo::Default, major.ty.clone(), result.clone());
    let match_head = Expr::const_(matcher.clone(), vec![level.clone()]);
    let equation = |subject: Expr| {
        let rhs = Expr::apps(
            match_head.clone(),
            [result_motive.clone(), subject.clone()]
                .into_iter()
                .chain(alternatives.iter().cloned()),
        );
        eq(level, result, Expr::app(head.clone(), subject), rhs)
    };
    let mut local = context.clone();
    let subject = Binder::push(&mut local, BinderInfo::Default, major.ty.clone());
    let motive = close_lambdas(std::slice::from_ref(&subject), equation(subject.var()));
    let cases = Expr::apps(
        Expr::const_(family.clone().str("casesOn"), vec![Level::zero()]),
        [motive, major.var()].into_iter().chain(case_proofs),
    );
    let statement = equation(major.var());
    let binders = [fixed.clone(), major.clone()];
    equations.push(ElabResult::Theorem {
        name: owner.clone().str("eq_def"),
        universe_params: vec![],
        ty: close_pis(&binders, statement),
        proof: close_lambdas(&binders, cases),
        modifiers: DeclModifiers::default(),
    });
    Some(equations)
}
