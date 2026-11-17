//! Prop recognition and the full proof-irrelevance side condition.
use super::*;

/// Proof-irrelevance with the **full side condition** (design §5.1):
/// `a ≡ b` iff `typeof(a) ≡ typeof(b)` *and* `typeof(a) : Prop`. Checks the
/// sort of the bridged subterm through the context-keyed inference entry.
///
/// Returns `Some(true)` if the bridge applies and types match, `Some(false)` if
/// it applies but types differ (so the caller does not accept), `None` if the
/// bridge does not apply (not a Prop).
pub(super) fn is_def_eq_proof_irrel(
    env: &dyn Env,
    ctx: &[Term],
    a: &Term,
    b: &Term,
    budget: &mut Budget,
) -> Result<Option<bool>, BudgetError> {
    // typeof(a) in the current local context.
    let ty_a = match infer_for_conversion(env, ctx, a, budget) {
        Ok(t) => t,
        Err(InferError::OutOfBudget) => return Err(BudgetError::OutOfBudget),
        Err(_) => return Ok(None),
    };
    // typeof(a) : Prop?  i.e. infer(ty_a) whnf's to Sort 0.
    if !type_is_prop(env, ctx, &ty_a, budget)? {
        return Ok(None);
    }
    let ty_b = match infer_for_conversion(env, ctx, b, budget) {
        Ok(t) => t,
        Err(InferError::OutOfBudget) => return Err(BudgetError::OutOfBudget),
        Err(_) => return Ok(None),
    };
    // The common type must itself be def-eq (a and b must be proofs of the
    // *same* proposition).
    let mut ctx_vec = ctx.to_vec();
    Ok(Some(is_def_eq_at(env, &mut ctx_vec, &ty_a, &ty_b, budget)?))
}

/// True iff `ty`'s own type whnf's to `Sort 0` (i.e. `ty : Prop`) in `ctx`.
fn type_is_prop(
    env: &dyn Env,
    ctx: &[Term],
    ty: &Term,
    budget: &mut Budget,
) -> Result<bool, BudgetError> {
    // A Sort is never in Prop (Sort l : Sort (succ l) which is never Sort 0).
    if matches!(ty.kind(), TermKind::Sort(_)) {
        return Ok(false);
    }
    // Lean's is_prop infers the type's sort; it does not normalize the type
    // itself first. A reducible type can have a cheap declared sort and a very
    // expensive body. Only its inferred sort needs weak-head reduction.
    let sort = match infer_for_conversion(env, ctx, ty, budget) {
        Ok(t) => t,
        Err(InferError::OutOfBudget) => return Err(BudgetError::OutOfBudget),
        Err(_) => return Ok(false),
    };
    let sort = whnf_in_context(env, ctx, &sort, budget)?;
    Ok(matches!(sort.kind(), TermKind::Sort(l) if l.is_zero()))
}
