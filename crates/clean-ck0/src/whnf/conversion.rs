//! Delayed head reduction used by pair-directed conversion.
use super::*;
type HeadCache =
    std::collections::HashMap<(bool, Vec<NodeKey>), std::collections::HashMap<NodeKey, Term>>;
thread_local! {
    static CACHE: std::cell::RefCell<HeadCache> = std::cell::RefCell::new(std::collections::HashMap::new());
}
pub(super) fn clear() {
    CACHE.with(|c| c.borrow_mut().clear());
}

/// Head reduction for conversion, postponing delta, literal extensions and
/// expensive projections until the pair's heads have been compared.
pub(crate) fn conversion_whnf(
    env: &dyn Env,
    ctx: &[Term],
    e: &Term,
    budget: &mut Budget,
) -> Result<Term, BudgetError> {
    conversion_head(env, ctx, e, budget, true)
}

/// Retry projections without eagerly unfolding or normalizing the resulting
/// outer application. Lean retries whnf_core here, never full whnf.
pub(crate) fn conversion_project(
    env: &dyn Env,
    ctx: &[Term],
    e: &Term,
    budget: &mut Budget,
) -> Result<Term, BudgetError> {
    conversion_head(env, ctx, e, budget, false)
}

fn conversion_head(
    env: &dyn Env,
    ctx: &[Term],
    e: &Term,
    budget: &mut Budget,
    cheap_proj: bool,
) -> Result<Term, BudgetError> {
    let _scope = DecisionScope::enter();
    let _frame = ReductionFrame::enter()?;
    let key = (cheap_proj, context_key(ctx, e.loose));
    if let Some(hit) = CACHE.with(|c| {
        c.borrow()
            .get(&key)
            .and_then(|m| m.get(&NodeKey(e.clone())))
            .cloned()
    }) {
        return Ok(hit);
    }
    let mut cur = e.clone();
    loop {
        budget.step()?;
        cur = whnf_core_mode(env, ctx, &cur, budget, true, cheap_proj)?;
        if let Some(next) = try_quot(env, ctx, &cur, budget)? {
            cur = next;
            continue;
        }
        if let Some(next) = try_iota(env, ctx, &cur, budget)? {
            cur = next;
            continue;
        }
        CACHE.with(|c| {
            c.borrow_mut()
                .entry(key)
                .or_default()
                .insert(NodeKey(e.clone()), cur.clone())
        });
        return Ok(cur);
    }
}

pub(crate) fn conversion_native(
    env: &dyn Env,
    ctx: &[Term],
    e: &Term,
    budget: &mut Budget,
) -> Result<Option<Term>, BudgetError> {
    // Lean's Nat extension is eager only on closed terms. Open operations
    // can still unfold through their checked definitions.
    if e.loose != 0 {
        return Ok(None);
    }
    let (head, args) = e.unfold_apps();
    try_native_nat(env, ctx, &head, &args, budget)
}
