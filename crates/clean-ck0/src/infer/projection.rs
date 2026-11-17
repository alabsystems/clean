//! Projection typing, retaining all owner/arity/Prop-field checks in both modes.
use super::*;

/// Type a projection. The field type is pulled from `inner`'s inferred
/// *structure* type — it does **not** require `inner` to be a constructor head
/// (design: "Proj typing pulls the field type from e's inferred structure type;
/// does NOT require a constructor head; Proj reduction on a constructor is
/// separate").
///
/// The guards are Lean's `infer_proj` (`type_checker.cpp`; decision R147): the
/// subject's type is headed by the structure the projection NAMES, applied to
/// exactly its parameters (a structure has no indices); and when that type is
/// a proposition (`is_prop`, which since leanprover/lean4#14807 requires the
/// type's type to be a sort), the projected field and every earlier field the
/// rest of the telescope depends on must be proofs, so a proof never yields
/// data.
pub(super) fn infer_proj(
    env: &dyn Env,
    ctx: &mut Ctx,
    struct_name: &Name,
    idx: u32,
    inner: &Term,
    budget: &mut Budget,
    query_only: bool,
) -> Result<Term, InferError> {
    let invalid = || InferError::NotAStructure {
        struct_name: struct_name.clone(),
        idx,
    };
    let inner_ty = type_of(env, ctx, inner, budget, query_only)?;
    let inner_ty = whnf_in_context(env, ctx, &inner_ty, budget)?;
    let (head, ty_args) = inner_ty.unfold_apps();
    let TermKind::Const(ty_cref) = head.kind() else {
        return Err(invalid());
    };
    if ty_cref.name() != struct_name {
        return Err(invalid());
    }
    let info = env.structure_info(struct_name).ok_or_else(invalid)?;
    if idx >= info.num_fields {
        return Err(invalid());
    }
    if u32::try_from(ty_args.len()).ok() != Some(info.num_params) {
        return Err(invalid());
    }
    let is_prop_type = sort_of(env, ctx, &inner_ty, budget, query_only)?.is_zero();
    // The constructor's type, level-instantiated, is a telescope:
    //   (params...) -> (field_0 : F0) -> ... -> StructTy
    // Field `idx`'s type is the domain of the (num_params + idx)-th Pi, with the
    // preceding params instantiated by `ty_args` and the preceding fields by the
    // projections `inner.0 .. inner.(idx-1)`.
    let ctor_ty = env
        .const_type(&info.ctor)
        .ok_or_else(|| InferError::UnknownConst {
            name: info.ctor.clone(),
        })?
        .instantiate_levels(ty_cref.levels())?;
    let mut cur = whnf_in_context(env, ctx, &ctor_ty, budget)?;
    // Instantiate the parameters with the structure type's arguments.
    let num_params = usize::try_from(info.num_params).unwrap_or(usize::MAX);
    for p in ty_args.iter().take(num_params) {
        let TermKind::Pi(_, _, codom) = cur.kind() else {
            return Err(invalid());
        };
        cur = whnf_in_context(env, ctx, &codom.instantiate(p), budget)?;
    }
    // Walk `idx` fields, instantiating each with the projection of `inner`.
    for field in 0..idx {
        let TermKind::Pi(_, dom, codom) = cur.kind() else {
            return Err(invalid());
        };
        // When the rest of the telescope mentions this field, it mentions a
        // projection of `inner`; out of a proof that must itself be a proof.
        if is_prop_type
            && codom.has_loose_bvar(0)
            && !sort_of(env, ctx, dom, budget, query_only)?.is_zero()
        {
            return Err(invalid());
        }
        let proj = Term::proj(struct_name.clone(), field, inner.clone());
        cur = whnf_in_context(env, ctx, &codom.instantiate(&proj), budget)?;
    }
    // The current Pi's domain is field `idx`'s type.
    let TermKind::Pi(_, dom, _) = cur.kind() else {
        return Err(invalid());
    };
    if is_prop_type && !sort_of(env, ctx, dom, budget, query_only)?.is_zero() {
        return Err(invalid());
    }
    Ok(dom.clone())
}

fn type_of(
    env: &dyn Env,
    ctx: &mut Ctx,
    term: &Term,
    budget: &mut Budget,
    query_only: bool,
) -> Result<Term, InferError> {
    if query_only {
        query::known_in(env, ctx, term, budget)
    } else {
        infer_in(env, ctx, term, budget)
    }
}
fn sort_of(
    env: &dyn Env,
    ctx: &mut Ctx,
    term: &Term,
    budget: &mut Budget,
    query_only: bool,
) -> Result<Level, InferError> {
    if query_only {
        query::sort_known(env, ctx, term, budget)
    } else {
        infer_sort_in(env, ctx, term, budget)
    }
}
