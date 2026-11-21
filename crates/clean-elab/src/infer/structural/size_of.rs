// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0

//! Automatic SizeOf declarations for a simple recursive family in Type.

use clean_kernel::tc::LocalContext;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, KernelInstanceInfo, Level, Name};

use super::case_matcher::{close_lambdas, close_pis, open_fields, Binder};

fn nat_literal(value: u64) -> Expr {
    let literal = Expr::nat_lit(value);
    Expr::apps(
        Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
        [
            Expr::const_str("Nat"),
            literal.clone(),
            Expr::app(Expr::const_str("instOfNatNat"), literal),
        ],
    )
}

fn add(left: Expr, right: Expr) -> Expr {
    let nat = Expr::const_str("Nat");
    let instance = Expr::apps(
        Expr::const_(Name::from_string("instHAdd"), vec![Level::zero()]),
        [nat.clone(), Expr::const_str("instAddNat")],
    );
    Expr::apps(
        Expr::const_(Name::from_string("HAdd.hAdd"), vec![Level::zero(); 3]),
        [nat.clone(), nat.clone(), nat, instance, left, right],
    )
}

fn size(carrier: Expr, instance: Expr, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("SizeOf.sizeOf"),
            vec![Level::succ(Level::zero())],
        ),
        [carrier, instance, value],
    )
}

/// Build the fold and its instance, then the exact constructor equations.
/// Parameters, indices, mutual recursion and fields beyond this family and Nat
/// each require their own instance or recursor construction.
pub(crate) fn simple_size_of(
    env: &Environment,
    family: &Name,
) -> Option<(Vec<Declaration>, KernelInstanceInfo)> {
    if env
        .get_option("genSizeOf")
        .is_some_and(|value| value.as_deref() == Some("false"))
    {
        return None;
    }
    let prerequisites = [
        "Nat",
        "SizeOf",
        "SizeOf.mk",
        "SizeOf.sizeOf",
        "instSizeOfNat",
        "HAdd.hAdd",
        "instHAdd",
        "instAddNat",
        "OfNat.ofNat",
        "instOfNatNat",
        "Eq",
        "Eq.refl",
    ];
    if prerequisites
        .iter()
        .any(|name| env.get_const(&Name::from_string(name)).is_none())
    {
        return None;
    }
    let family_info = env.get_inductive(family)?;
    let one = Level::succ(Level::zero());
    if !family_info.is_recursive
        || family_info.num_params != 0
        || family_info.num_indices != 0
        || !family_info.level_params.is_empty()
        || family_info.type_ != Expr::sort(one.clone())
    {
        return None;
    }
    let recursor_name = family.clone().str("rec");
    let recursor = env.get_recursor(&recursor_name)?;
    if recursor.num_params != 0
        || recursor.num_indices != 0
        || recursor.num_motives != 1
        || recursor.level_params.len() != 1
        || recursor.rules.is_empty()
    {
        return None;
    }
    let fold_name = family.clone().str("_sizeOf_1");
    let instance_name = family.clone().str("_sizeOf_inst");
    let family_type = Expr::const_(family.clone(), vec![]);
    let nat = Expr::const_str("Nat");
    let instance = Expr::const_(instance_name.clone(), vec![]);
    let with_equations = !env
        .get_option("genSizeOfSpec")
        .is_some_and(|value| value.as_deref() == Some("false"));
    let mut minors = Vec::with_capacity(recursor.rules.len());
    let mut equations = Vec::with_capacity(recursor.rules.len());
    for rule in &recursor.rules {
        let constructor = env.get_constructor(&rule.constructor_name)?;
        let mut context = LocalContext::new();
        let fields = open_fields(
            &mut context,
            &constructor.type_,
            constructor.num_fields as usize,
        )?;
        if fields.len() != rule.recursive_fields.len() {
            return None;
        }
        let mut fold_sum = nat_literal(1);
        let mut equation_sum = fold_sum.clone();
        let mut hypotheses = Vec::new();
        for (field, recursive) in fields.iter().zip(&rule.recursive_fields) {
            if *recursive && field.ty == family_type {
                let hypothesis = Binder::push(&mut context, BinderInfo::Default, nat.clone());
                fold_sum = add(fold_sum, hypothesis.var());
                equation_sum = add(
                    equation_sum,
                    size(family_type.clone(), instance.clone(), field.var()),
                );
                hypotheses.push(hypothesis);
            } else if !*recursive && field.ty == nat {
                let count = size(nat.clone(), Expr::const_str("instSizeOfNat"), field.var());
                fold_sum = add(fold_sum, count.clone());
                equation_sum = add(equation_sum, count);
            } else {
                return None;
            }
        }
        minors.push(close_lambdas(&fields, close_lambdas(&hypotheses, fold_sum)));
        if with_equations {
            let ctor = Expr::apps(
                Expr::const_(rule.constructor_name.clone(), vec![]),
                fields.iter().map(Binder::var),
            );
            let lhs = size(family_type.clone(), instance.clone(), ctor);
            let eq = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
                [nat.clone(), lhs.clone(), equation_sum],
            );
            let proof = Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]),
                [nat.clone(), lhs],
            );
            equations.push(Declaration::Theorem {
                name: rule.constructor_name.clone().str("sizeOf_spec"),
                level_params: vec![],
                type_: close_pis(&fields, eq),
                value: close_lambdas(&fields, proof),
            });
        }
    }
    let mut context = LocalContext::new();
    let major = Binder::push(&mut context, BinderInfo::Default, family_type.clone());
    let motive = Expr::lam(BinderInfo::Default, family_type.clone(), nat.clone());
    let recursor = Expr::apps(
        Expr::const_(recursor_name, vec![one.clone()]),
        std::iter::once(motive)
            .chain(minors)
            .chain(std::iter::once(major.var())),
    );
    let fold = Declaration::Definition {
        name: fold_name.clone(),
        level_params: vec![],
        type_: Expr::arrow(family_type.clone(), nat),
        value: close_lambdas(std::slice::from_ref(&major), recursor),
        is_reducible: true,
    };
    let method = close_lambdas(
        std::slice::from_ref(&major),
        Expr::app(Expr::const_(fold_name, vec![]), major.var()),
    );
    let class = Name::from_string("SizeOf");
    let instance_type = Expr::app(
        Expr::const_(class.clone(), vec![one.clone()]),
        family_type.clone(),
    );
    let instance_value = Expr::apps(
        Expr::const_(Name::from_string("SizeOf.mk"), vec![one]),
        [family_type, method],
    );
    let instance_def = Declaration::Definition {
        name: instance_name.clone(),
        level_params: vec![],
        type_: instance_type.clone(),
        value: instance_value.clone(),
        is_reducible: true,
    };
    let instance = KernelInstanceInfo {
        name: instance_name,
        class_name: class,
        priority: 1000,
        type_: Some(instance_type),
        value: Some(instance_value),
    };
    let declarations = [fold, instance_def].into_iter().chain(equations).collect();
    Some((declarations, instance))
}
