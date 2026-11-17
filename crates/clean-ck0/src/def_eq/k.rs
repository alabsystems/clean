//! Guarded K-target conversion.
use super::*;

/// Lean's K-like reduction, applied where `ck0` has a context. Since the
/// round-5 merge, `whnf` applies the same rule at a recursor's major
/// (`major_is_k_constructor`), so both sides usually arrive here reduced. The
/// eliminator of an inductive `I` that is a K-target — `I` lives in `Prop` and
/// has exactly one constructor `C`, with no fields — whose saturated major
/// premise `m` is not `C` itself: when `m : I ps is` and `C ps : I ps is'` with
/// the two types definitionally equal, `m` is replaced by `C ps` (proof
/// irrelevance makes them equal; the replacement lets the ι-rule fire). `None`
/// when `e` is not such an application or any step does not hold (the
/// eliminator stays stuck: fail-closed).
pub(crate) fn k_like_major(
    env: &dyn Env,
    ctx: &mut Ctx,
    e: &Term,
    budget: &mut Budget,
) -> Result<Option<Term>, BudgetError> {
    let (head, args) = e.unfold_apps();
    let TermKind::Elim(eref) = head.kind() else {
        return Ok(None);
    };
    let ind = eref.inductive().clone();
    let (Some(shape), Some(rules)) = (env.recursor_shape(&ind), env.recursor_rules(&ind)) else {
        return Ok(None);
    };
    if shape.num_motives != 1 {
        return Ok(None);
    }
    let [rule] = rules.as_slice() else {
        return Ok(None);
    };
    if rule.num_fields != 0 {
        return Ok(None);
    }
    // `I : (params) → (indices) → Prop`.
    let Some(mut ty) = env.const_type(&ind) else {
        return Ok(None);
    };
    while let TermKind::Pi(_, _, body) = ty.kind() {
        let next = body.clone();
        ty = next;
    }
    match ty.kind() {
        TermKind::Sort(l) if l.is_zero() => {}
        _ => return Ok(None),
    }
    let to_usize = |x: u32| usize::try_from(x).unwrap_or(usize::MAX);
    let np = to_usize(shape.num_params);
    let major_pos = np
        .checked_add(to_usize(shape.num_motives))
        .and_then(|x| x.checked_add(to_usize(shape.num_minors)))
        .and_then(|x| x.checked_add(to_usize(shape.num_indices)));
    let Some(major_pos) = major_pos else {
        return Ok(None);
    };
    let Some(major) = args.get(major_pos) else {
        return Ok(None);
    };
    let major_w = whnf_in_context(env, ctx, major, budget)?;
    if let TermKind::Const(c) = major_w.unfold_apps().0.kind() {
        if *c.name() == rule.constructor {
            return Ok(None); // the ι-rule's own case
        }
    }
    let major_ty = match infer_for_conversion(env, ctx, major, budget) {
        Ok(t) => t,
        Err(InferError::OutOfBudget) => return Err(BudgetError::OutOfBudget),
        Err(_) => return Ok(None),
    };
    let major_ty = whnf_in_context(env, ctx, &major_ty, budget)?;
    let (ty_head, ty_args) = major_ty.unfold_apps();
    let TermKind::Const(ty_ref) = ty_head.kind() else {
        return Ok(None);
    };
    if *ty_ref.name() != ind || Some(ty_args.len()) != np.checked_add(to_usize(shape.num_indices)) {
        return Ok(None);
    }
    let Ok(ctor) =
        crate::term::ConstRef::mk(env, rule.constructor.clone(), ty_ref.levels().to_vec())
    else {
        return Ok(None);
    };
    let ctor_app = Term::apply(Term::const_ref(ctor), &ty_args[..np]);
    let ctor_ty = match infer_for_conversion(env, ctx, &ctor_app, budget) {
        Ok(t) => t,
        Err(InferError::OutOfBudget) => return Err(BudgetError::OutOfBudget),
        Err(_) => return Ok(None),
    };
    if !is_def_eq_at(env, ctx, &ctor_ty, &major_ty, budget)? {
        return Ok(None);
    }
    let mut new_args = args.clone();
    new_args[major_pos] = ctor_app;
    Ok(Some(whnf_in_context(
        env,
        ctx,
        &Term::apply(head, &new_args),
        budget,
    )?))
}
