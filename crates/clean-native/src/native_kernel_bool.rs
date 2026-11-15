// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Delta-reduce two finite logical Bool definitions in kernel-value callers.
//! This does not export noncomputable declarations or replay compiler attributes.

use clean_compiler::CodeMeaning;
use clean_kernel::{
    BinderInfo, ConstantInfo, ConstantKind, DeclarationVerification, Environment, Expr, ExprKind,
    Level, Name, TypeChecker,
};
use std::collections::HashMap;

fn safe_checked(env: &Environment, name: &Name) -> bool {
    env.declaration_verification(name) == Some(DeclarationVerification::FullKernelCheck)
        && !env.is_unsafe(name)
        && !env.is_partial(name)
        && !env.is_staged_header(name)
        && !env.constant_needs_recheck(name)
        && env.axiom_deps(name).is_some_and(|debt| debt.is_empty())
}

fn canonical_bool(env: &Environment) -> bool {
    let name = Name::from_string("Bool");
    let Some(ind) = env.get_inductive(&name) else {
        return false;
    };
    if ind.type_ != Expr::type_()
        || ind.num_params != 0
        || ind.num_indices != 0
        || ind.is_recursive
        || !ind.level_params.is_empty()
        || ind.constructor_names != [name.clone().str("false"), name.clone().str("true")]
    {
        return false;
    }
    ["Bool", "Bool.rec", "Bool.false", "Bool.true"]
        .iter()
        .all(|name| safe_checked(env, &Name::from_string(name)))
        && ["Bool.false", "Bool.true"]
            .iter()
            .enumerate()
            .all(|(index, name)| {
                env.get_constructor(&Name::from_string(name))
                    .is_some_and(|ctor| {
                        ctor.inductive_name == Name::from_string("Bool")
                            && ctor.num_params == 0
                            && ctor.num_fields == 0
                            && ctor.constructor_idx == index as u32
                            && ctor.level_params.is_empty()
                            && ctor.type_ == Expr::const_str("Bool")
                    })
            })
}

fn expected_body(and: bool) -> Expr {
    let bool_ = Expr::const_str("Bool");
    let (false_case, true_case) = if and {
        (Expr::const_str("Bool.false"), Expr::bvar(0))
    } else {
        (Expr::bvar(0), Expr::const_str("Bool.true"))
    };
    let body = Expr::apps(
        Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            Expr::lam(BinderInfo::Default, bool_.clone(), bool_.clone()),
            false_case,
            true_case,
            Expr::bvar(1),
        ],
    );
    Expr::lam(
        BinderInfo::Default,
        bool_.clone(),
        Expr::lam(BinderInfo::Default, bool_, body),
    )
}

fn definitions(env: &Environment) -> Vec<(Name, Expr)> {
    if !canonical_bool(env) {
        return Vec::new();
    }
    let bool_ = Expr::const_str("Bool");
    let ty = Expr::arrow(bool_.clone(), Expr::arrow(bool_.clone(), bool_));
    [("Bool.and", true), ("Bool.or", false)]
        .into_iter()
        .filter_map(|(text, and)| {
            let name = Name::from_string(text);
            let info = env.get_const(&name)?;
            let expected = expected_body(and);
            (safe_checked(env, &name)
                && env.is_noncomputable(&name)
                && info.kind == ConstantKind::Definition
                && info.level_params.is_empty()
                && info.type_ == ty
                && info.value.as_ref() == Some(&expected))
            .then_some((name, expected))
        })
        .collect()
}

fn child(memo: &HashMap<Expr, Expr>, expr: &Expr) -> Result<Expr, String> {
    memo.get(expr)
        .cloned()
        .ok_or_else(|| "missing Bool normalization DAG child".into())
}

/// Keep the operation in a function body even when its caller needs a value.
/// The existing LCNF function-body path lowers Bool.rec to Cases; its generic
/// let-value path deliberately retains unsupported recursors for final refusal.
/// This beta-redex binds the thunk once, then forces it with an irrelevant Bool.
fn branch_value(body: Expr) -> Expr {
    let bool_ = Expr::const_str("Bool");
    let thunk_ty = Expr::arrow(bool_.clone(), bool_.clone());
    let force = Expr::lam(
        BinderInfo::Default,
        thunk_ty,
        Expr::app(Expr::bvar(0), Expr::const_str("Bool.false")),
    );
    let thunk = Expr::lam(BinderInfo::Default, bool_, body.lift(1));
    Expr::app(force, thunk)
}

fn normalize(value: &Expr, definitions: &[(Name, Expr)]) -> Result<Expr, String> {
    let mut pending = vec![(value.clone(), false)];
    let mut memo = HashMap::new();
    while let Some((expr, visited)) = pending.pop() {
        if memo.contains_key(&expr) {
            continue;
        }
        if !visited {
            pending.push((expr.clone(), true));
            match expr.kind() {
                ExprKind::App(f, a) => {
                    pending.push((a.as_ref().clone(), false));
                    pending.push((f.as_ref().clone(), false));
                }
                ExprKind::Lam(_, _, body)
                | ExprKind::MData(_, body)
                | ExprKind::Proj(_, _, body) => pending.push((body.as_ref().clone(), false)),
                ExprKind::Let(_, _, value, body, _) => {
                    pending.push((body.as_ref().clone(), false));
                    pending.push((value.as_ref().clone(), false));
                }
                _ => {}
            }
            continue;
        }
        let rebuilt = match expr.kind() {
            ExprKind::App(f, a) => Expr::app(child(&memo, f)?, child(&memo, a)?),
            ExprKind::Lam(binder, ty, body) => {
                Expr::lam(*binder, ty.as_ref().clone(), child(&memo, body)?)
            }
            ExprKind::Let(name, ty, value, body, non_dep) => Expr::let_named(
                name.clone(),
                ty.as_ref().clone(),
                child(&memo, value)?,
                child(&memo, body)?,
                *non_dep,
            ),
            ExprKind::MData(data, body) => Expr::mdata(data.clone(), child(&memo, body)?),
            ExprKind::Proj(name, index, body) => {
                Expr::proj(name.clone(), *index, child(&memo, body)?)
            }
            _ => expr.clone(),
        };
        let normalized = if let ExprKind::Const(name, levels) = rebuilt.get_app_fn().kind() {
            let args = rebuilt.get_app_args();
            if levels.is_empty() && args.len() == 2 {
                if let Some((_, value)) =
                    definitions.iter().find(|(canonical, _)| canonical == name)
                {
                    let ExprKind::Lam(_, _, body) = value.kind() else {
                        return Err("Bool definition lost first lambda".into());
                    };
                    let partial = body.instantiate(args[0]);
                    let ExprKind::Lam(_, _, body) = partial.kind() else {
                        return Err("Bool definition lost second lambda".into());
                    };
                    branch_value(body.instantiate(args[1]))
                } else {
                    rebuilt.clone()
                }
            } else {
                rebuilt.clone()
            }
        } else {
            rebuilt
        };
        memo.insert(expr, normalized);
    }
    child(&memo, value)
}

pub(crate) fn rewrite(
    env: &Environment,
    info: &ConstantInfo,
    meaning: CodeMeaning,
) -> Result<Option<Expr>, String> {
    if meaning != CodeMeaning::KernelValue {
        return Ok(None);
    }
    let Some(value) = &info.value else {
        return Ok(None);
    };
    let definitions = definitions(env);
    if definitions.is_empty() {
        return Ok(None);
    }
    let normalized = normalize(value, &definitions)?;
    if normalized == *value {
        return Ok(None);
    }
    let tc = TypeChecker::new(env);
    tc.check_type(value, &info.type_)
        .map_err(|error| format!("original caller type refused: {error:?}"))?;
    tc.check_type(&normalized, &info.type_)
        .map_err(|error| format!("rewritten value type refused: {error:?}"))?;
    if !tc.is_def_eq(value, &normalized) {
        return Err(
            "rewritten value is not definitionally equal to the checked source value".into(),
        );
    }
    Ok(Some(normalized))
}

#[cfg(test)]
#[path = "native_kernel_bool_tests.rs"]
mod tests;
