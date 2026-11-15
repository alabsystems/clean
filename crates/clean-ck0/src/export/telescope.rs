//! Consume only checked identity annotations. Constructor result syntax stays
//! untouched; only inductive type-former telescopes admit weak-head normalization.
use super::*;
use crate::term::TermKind;
use crate::validate::{Env, Transparency};

pub(super) fn normalize_telescope(env: &MinimalEnv, ty: &Term) -> Result<Term, Refusal> {
    go(
        env,
        ty,
        &mut Vec::new(),
        &mut Budget::default_budget(),
        true,
    )
}
pub(super) fn constructor_annotations(env: &MinimalEnv, ty: &Term) -> Result<Term, Refusal> {
    go(
        env,
        ty,
        &mut Vec::new(),
        &mut Budget::default_budget(),
        false,
    )
}
fn annotation(env: &dyn Env, domain: &Term) -> Result<Term, Refusal> {
    let (head, args) = domain.unfold_apps();
    let TermKind::Const(c) = head.kind() else {
        return Ok(domain.clone());
    };
    let count = if ["outParam", "semiOutParam"]
        .iter()
        .any(|n| c.name() == &Name::from_dotted(n))
    {
        1
    } else if ["optParam", "autoParam"]
        .iter()
        .any(|n| c.name() == &Name::from_dotted(n))
    {
        2
    } else {
        return Ok(domain.clone());
    };
    if args.len() != count {
        return Ok(domain.clone());
    }
    let def = env
        .const_def(c.name())
        .ok_or_else(|| malformed("annotation identity is not defined"))?;
    if def.transparency != Transparency::Transparent {
        return Err(malformed("annotation identity is opaque"));
    }
    let mut value = def.body;
    for _ in 0..count {
        let TermKind::Lam(_, _, body) = value.kind() else {
            return Err(malformed("annotation is not an identity"));
        };
        value = body.clone();
    }
    let expected = u32::try_from(count)
        .map_err(|_| Refusal::Limit)?
        .checked_sub(1)
        .ok_or(Refusal::Limit)?;
    if !matches!(value.kind(),TermKind::BVar(i) if *i==expected) {
        return Err(malformed("annotation is not an identity"));
    }
    args.first()
        .cloned()
        .ok_or_else(|| malformed("annotation argument"))
}
fn go(
    env: &dyn Env,
    ty: &Term,
    ctx: &mut Vec<Term>,
    budget: &mut Budget,
    normalize: bool,
) -> Result<Term, Refusal> {
    let ty = if normalize {
        crate::whnf::whnf_in_context(env, ctx, ty, budget).map_err(|_| Refusal::Limit)?
    } else {
        ty.clone()
    };
    if let TermKind::Pi(bi, domain, body) = ty.kind() {
        let domain = annotation(env, domain)?;
        ctx.push(domain.clone());
        let tail = go(env, body, ctx, budget, normalize)?;
        ctx.pop();
        Ok(Term::pi(*bi, domain, tail))
    } else {
        Ok(ty)
    }
}
