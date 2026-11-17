//! Function/structure η, including field-free unit-like equality.
use super::*;

/// function-η: `λ x. body ≡ other` iff `other` is a function and
/// `λ x. body ≡ λ x. other x`. Symmetric (tries either side as the lambda).
pub(super) fn try_eta(
    env: &dyn Env,
    ctx: &mut Ctx,
    a: &Term,
    b: &Term,
    budget: &mut Budget,
) -> Result<Option<bool>, BudgetError> {
    match (a.kind(), b.kind()) {
        (TermKind::Lam(bi, _, _), _) if !matches!(b.kind(), TermKind::Lam(_, _, _)) => {
            Ok(Some(eta_one(env, ctx, *bi, a, b, budget)?))
        }
        (_, TermKind::Lam(bi, _, _)) if !matches!(a.kind(), TermKind::Lam(_, _, _)) => {
            Ok(Some(eta_one(env, ctx, *bi, b, a, budget)?))
        }
        _ => Ok(None),
    }
}

/// `lam` is a `Lam(bi, dom, _)`; `other` is a non-lambda. Compare
/// `lam ≡ λ (x:dom). other x` (η-expanding `other`).
fn eta_one(
    env: &dyn Env,
    ctx: &mut Ctx,
    bi: BinderInfo,
    lam: &Term,
    other: &Term,
    budget: &mut Budget,
) -> Result<bool, BudgetError> {
    // Preserve typing of the synthetic eta term: use the other function's
    // actual domain, then let binder congruence check the domains agree.
    let other_ty = match infer_for_conversion(env, ctx, other, budget) {
        Ok(ty) => ty,
        Err(InferError::OutOfBudget) => return Err(BudgetError::OutOfBudget),
        Err(_) => return Ok(false),
    };
    let other_ty = whnf_in_context(env, ctx, &other_ty, budget)?;
    let TermKind::Pi(_, domain, _) = other_ty.kind() else {
        return Ok(false);
    };
    let expanded = Term::lam(bi, domain.clone(), Term::app(other.lift(1), Term::bvar(0)));
    is_def_eq_at(env, ctx, lam, &expanded, budget)
}

/// structure-η: if one side's whnf'd *type* is a single-constructor structure
/// and the other side is not already that constructor applied, expand it to
/// `S.mk (proj0) … (projn)` and compare fieldwise. M2: runs UNDER BINDERS too
/// (`infer` is now context-aware), so structure-η fires wherever the corpus
/// needs it, not only at the top level.
pub(super) fn try_struct_eta(
    env: &dyn Env,
    ctx: &mut Ctx,
    a: &Term,
    b: &Term,
    budget: &mut Budget,
) -> Result<Option<bool>, BudgetError> {
    // Try expanding `a` to match `b`'s structure shape, then vice versa.
    if let Some(r) = struct_eta_one(env, ctx, a, b, budget)? {
        return Ok(Some(r));
    }
    struct_eta_one(env, ctx, b, a, budget)
}

/// Expand `e` (the candidate to be η-expanded) into constructor form and compare
/// to `other`. Returns `Some(result)` if `e`'s type is a structure *and* the
/// expansion is licensed (Lean-faithful gating — see below), else `None`.
///
/// ## Lean-faithful gating (totality + soundness-preserving)
///
/// Structure-η exists to decide `s ≡ S.mk f0 … fn`: η-expand the NEUTRAL side
/// `s` to `S.mk (proj0 s) … (projn s)` so it matches the CONSTRUCTOR-headed
/// side. Except for the direct field-free unit-like rule, it fires only when `other`
/// is headed by this structure's constructor `S.mk`. This mirrors Lean's kernel
/// `isDefEqEtaStruct`, which η-expands a term solely to match a constructor.
///
/// For structures with fields, comparing projections of two distinct neutrals
/// would recurse back to the same value comparison. Those cases stay stuck.
/// Field-free structures instead use unit-like equality of the full inferred
/// types, so no projection loop is introduced.
fn struct_eta_one(
    env: &dyn Env,
    ctx: &[Term],
    e: &Term,
    other: &Term,
    budget: &mut Budget,
) -> Result<Option<bool>, BudgetError> {
    // Determine e's structure type (in the current local context).
    let e_ty = match infer_for_conversion(env, ctx, e, budget) {
        Ok(t) => t,
        Err(InferError::OutOfBudget) => return Err(BudgetError::OutOfBudget),
        Err(_) => return Ok(None),
    };
    let e_ty = whnf_in_context(env, ctx, &e_ty, budget)?;
    let (head, ty_args) = e_ty.unfold_apps();
    let TermKind::Const(ty_cref) = head.kind() else {
        return Ok(None);
    };
    let Some(info) = env.structure_info(ty_cref.name()) else {
        return Ok(None);
    };
    // Don't η-expand a term already headed by the same constructor (would loop).
    let (e_head, _) = e.unfold_apps();
    if let TermKind::Const(c) = e_head.kind() {
        if *c.name() == info.ctor {
            return Ok(None);
        }
    }
    // LEAN-FAITHFUL GATING (totality): only η-expand `e` to MATCH a constructor.
    // Fire iff `other` is headed by this structure's constructor `S.mk`; two
    // With fields, two neutrals remain stuck to avoid a projection loop.
    // Without fields, only their full inferred types need comparison.
    let (other_head, _) = other.unfold_apps();
    let other_is_ctor = matches!(
        other_head.kind(),
        TermKind::Const(c) if *c.name() == info.ctor
    );
    if !other_is_ctor {
        if info.num_fields != 0 {
            return Ok(None);
        }
        // A field-free eligible structure is unit-like even when BOTH terms
        // are neutral. Compare their full inferred types (including parameters
        // and universes); no value projections or recursive η-expansion occur.
        let other_ty = match infer_for_conversion(env, ctx, other, budget) {
            Ok(ty) => ty,
            Err(InferError::OutOfBudget) => return Err(BudgetError::OutOfBudget),
            Err(_) => return Ok(None),
        };
        let mut ctx_vec = ctx.to_vec();
        return Ok(Some(is_def_eq_at(
            env,
            &mut ctx_vec,
            &e_ty,
            &other_ty,
            budget,
        )?));
    }
    // Build S.mk params... (proj_0 e) ... (proj_{n-1} e).
    let mut ctor = Term::const_ref(crate::ConstRef::mk(
        env,
        info.ctor.clone(),
        ty_cref.levels().to_vec(),
    )?);
    let num_params = usize::try_from(info.num_params).unwrap_or(usize::MAX);
    for p in ty_args.iter().take(num_params) {
        ctor = Term::app(ctor, p.clone());
    }
    for field in 0..info.num_fields {
        ctor = Term::app(ctor, Term::proj(ty_cref.name().clone(), field, e.clone()));
    }
    let mut ctx_vec = ctx.to_vec();
    Ok(Some(is_def_eq_at(env, &mut ctx_vec, &ctor, other, budget)?))
}
