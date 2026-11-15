//! Closed, independent primitive signatures. Binder labels are construction aids;
//! lowering uses positions, and all resulting terms pass normal validation.
use super::*;
use crate::rawexpr::BinderInfo;
use crate::validate::Env;
use crate::{RawExpr, RawLevel};

pub(super) enum Spec {
    Var(&'static str),
    Sort(RawLevel),
    Const(&'static str, Vec<RawLevel>),
    Pi(&'static str, Box<Spec>, Box<Spec>),
    App(Box<Spec>, Box<Spec>),
}
pub(super) fn v(name: &'static str) -> Spec {
    Spec::Var(name)
}
pub(super) fn s(level: RawLevel) -> Spec {
    Spec::Sort(level)
}
pub(super) fn c(name: &'static str, levels: Vec<RawLevel>) -> Spec {
    Spec::Const(name, levels)
}
pub(super) fn pi(name: &'static str, ty: Spec, body: Spec) -> Spec {
    Spec::Pi(name, Box::new(ty), Box::new(body))
}
pub(super) fn arrow(domain: Spec, range: Spec) -> Spec {
    pi("_", domain, range)
}
pub(super) fn app(head: Spec, args: impl IntoIterator<Item = Spec>) -> Spec {
    args.into_iter()
        .fold(head, |f, a| Spec::App(Box::new(f), Box::new(a)))
}
pub(super) fn eq(level: RawLevel, ty: Spec, left: Spec, right: Spec) -> Spec {
    app(c("Eq", vec![level]), [ty, left, right])
}
impl Spec {
    fn lower(self, ctx: &mut Vec<&'static str>) -> Result<RawExpr, Refusal> {
        Ok(match self {
            Self::Var(name) => {
                let position = ctx
                    .iter()
                    .rev()
                    .position(|n| *n == name)
                    .ok_or_else(|| malformed("unbound primitive signature variable"))?;
                RawExpr::BVar(u32::try_from(position).map_err(|_| Refusal::Limit)?)
            }
            Self::Sort(l) => RawExpr::Sort(l),
            Self::Const(name, ls) => RawExpr::Const(Name::from_dotted(name), ls),
            Self::Pi(name, ty, body) => {
                let ty = ty.lower(ctx)?;
                ctx.push(name);
                let body = body.lower(ctx)?;
                ctx.pop();
                RawExpr::Pi(BinderInfo::Default, Box::new(ty), Box::new(body))
            }
            Self::App(f, a) => RawExpr::App(Box::new(f.lower(ctx)?), Box::new(a.lower(ctx)?)),
        })
    }
}
pub(super) fn checked(env: &dyn Env, spec: Spec, levels: u32) -> Result<Term, Refusal> {
    let term = Term::validate(env, &spec.lower(&mut Vec::new())?, 0, levels)?;
    crate::infer_sort(env, &term, &mut Budget::default_budget())?;
    Ok(term)
}

fn family(
    env: &dyn Env,
    name: &str,
    levels: u32,
    np: u32,
    ty: Spec,
    ctors: Vec<(&str, Spec)>,
) -> Result<bool, Refusal> {
    let name = Name::from_dotted(name);
    if env.num_level_params(&name) != Some(levels)
        || env.inductive_num_params(&name) != Some(np)
        || !env
            .recursor_shape(&name)
            .is_some_and(|r| r.num_motives == 1)
    {
        return Ok(false);
    }
    let (Some(actual_ty), Some(actual_ctors)) =
        (env.const_type(&name), env.inductive_constructors(&name))
    else {
        return Ok(false);
    };
    if !terms::same_term(&actual_ty, &checked(env, ty, levels)?)
        || actual_ctors.len() != ctors.len()
    {
        return Ok(false);
    }
    for ((name, ty), (expected_name, expected_ty)) in actual_ctors.iter().zip(ctors) {
        if *name != Name::from_dotted(expected_name)
            || !terms::same_term(ty, &checked(env, expected_ty, levels)?)
        {
            return Ok(false);
        }
    }
    Ok(true)
}
/// Eq's complete type and constructor signature, not merely its printed name.
pub(super) fn canonical_eq(env: &dyn Env) -> Result<bool, Refusal> {
    let u = RawLevel::Param(0);
    let indices = pi("a", v("α"), pi("b", v("α"), s(RawLevel::Zero)));
    let ty = pi("α", s(u.clone()), indices);
    let result = eq(u.clone(), v("α"), v("a"), v("a"));
    let ctor = pi("α", s(u), pi("a", v("α"), result));
    family(env, "Eq", 1, 2, ty, vec![("Eq.refl", ctor)])
}
