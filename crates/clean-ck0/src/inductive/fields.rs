//! Constructor-field analysis views. Reduce field type heads, including their
//! own Pi spines; keep declared binder types and constructor result syntax.
use crate::budget::{Budget, BudgetError};
use crate::rawexpr::BinderInfo;
use crate::term::{Term, TermKind};
use crate::validate::Env;
use crate::whnf::whnf_in_context;
use crate::Name;

pub(crate) struct ConstructorView {
    pub(crate) type_: Term,
    pub(crate) fields: Vec<Term>,
}
pub(crate) fn constructor_view(
    env: &dyn Env,
    ty: &Term,
    num_params: u32,
    family: &[Name],
) -> Result<ConstructorView, BudgetError> {
    let mut budget = Budget::default_budget();
    let mut ctx = Vec::new();
    let mut binders = Vec::new();
    let mut fields = Vec::new();
    let mut tail = ty.clone();
    while let TermKind::Pi(bi, domain, body) = tail.kind() {
        let normalized =
            if u32::try_from(ctx.len()).map_err(|_| BudgetError::OutOfBudget)? >= num_params {
                // With fresh family names, an absent occurrence cannot be hidden
                // in an earlier definition. Avoid evaluating unrelated field types.
                let view = if family
                    .iter()
                    .any(|n| crate::positivity::term_mentions(domain, n))
                {
                    field_view(env, domain, &mut ctx, &mut budget)?
                } else {
                    domain.clone()
                };
                fields.push(view.clone());
                view
            } else {
                domain.clone()
            };
        binders.push((*bi, normalized));
        ctx.push(domain.clone());
        tail = body.clone();
    }
    // Never WHNF the constructor result (not even for a nullary constructor).
    for (bi, domain) in binders.into_iter().rev() {
        tail = Term::pi(bi, domain, tail);
        if tail.depth > crate::MAX_VALIDATE_DEPTH {
            return Err(BudgetError::OutOfBudget);
        }
    }
    Ok(ConstructorView {
        type_: tail,
        fields,
    })
}
fn field_view(
    env: &dyn Env,
    ty: &Term,
    ctx: &mut Vec<Term>,
    budget: &mut Budget,
) -> Result<Term, BudgetError> {
    let saved = ctx.len();
    let result = (|| {
        let mut tail = whnf_in_context(env, ctx, ty, budget)?;
        let mut binders: Vec<(BinderInfo, Term)> = Vec::new();
        while let TermKind::Pi(bi, domain, body) = tail.kind() {
            if binders.len()
                >= usize::try_from(crate::MAX_VALIDATE_DEPTH)
                    .map_err(|_| BudgetError::OutOfBudget)?
            {
                return Err(BudgetError::OutOfBudget);
            }
            binders.push((*bi, domain.clone()));
            ctx.push(domain.clone());
            tail = whnf_in_context(env, ctx, body, budget)?;
        }
        for (bi, domain) in binders.into_iter().rev() {
            tail = Term::pi(bi, domain, tail);
            if tail.depth > crate::MAX_VALIDATE_DEPTH {
                return Err(BudgetError::OutOfBudget);
            }
        }
        Ok(tail)
    })();
    ctx.truncate(saved);
    result
}
