// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Recursor **type / minor-premise / ι-rule-RHS** construction and the de Bruijn
//! remap + lift helpers for [`crate::recursor::build_recursor`] (design §5.2).
//! Extracted from `recursor.rs` to keep both files under the 500-line
//! convention. Operates on [`crate::recursor::CtorInfo`] (the per-constructor
//! analysis gathered once by the orchestrator). All functions are `pub(crate)`
//! and called only from within the trusted recursor-derivation path.

use crate::inductive::{count_pi, pi_domains_with_info, return_type, InductiveDecl};
use crate::level::Level;
use crate::name::Name;
use crate::rawexpr::BinderInfo;
use crate::recursor::{ind_app, CtorInfo};
use crate::term::{ConstRef, Term, TermKind};

// ---------------------------------------------------------------------------
// Recursor type.
// ---------------------------------------------------------------------------

/// Build the recursor type:
/// `params → {motive} → minors → indices → (major) → motive indices major`.
pub(crate) fn build_recursor_type(
    decl: &InductiveDecl,
    _rec_name: &Name,
    num_indices: u32,
    motive_univ: &Level,
    ind_level_subst: &[Level],
    ctor_infos: &[CtorInfo],
) -> Result<Term, String> {
    let num_params = decl.num_params;
    let num_minors = u32::try_from(ctor_infos.len()).map_err(|_| "too many ctors".to_string())?;

    // Parameter and index binders, taken from the inductive's own telescope and
    // **level-shifted** by `ind_level_subst`: in a large-eliminating recursor the
    // inductive's own universe params (`Param(i)`) are shifted to `Param(i+1)`
    // (the motive universe occupies index 0), so every binder type pulled from
    // the decl that mentions a universe param must be re-expressed in the
    // recursor's level telescope. For Prop-only / level-monomorphic inductives
    // `ind_level_subst` is the identity, so this is a no-op.
    let param_binders: Vec<(BinderInfo, Term)> = pi_domains_with_info(&decl.type_, num_params)
        .into_iter()
        .map(|(bi, t)| (bi, t.instantiate_levels(ind_level_subst)))
        .collect();
    let mut after_params = decl.type_.clone();
    for _ in 0..num_params {
        if let TermKind::Pi(_, _, codom) = after_params.kind() {
            after_params = codom.clone();
        }
    }
    let index_binders: Vec<(BinderInfo, Term)> = pi_domains_with_info(&after_params, num_indices)
        .into_iter()
        .map(|(bi, t)| (bi, t.instantiate_levels(ind_level_subst)))
        .collect();

    let ind_const = ConstRef::mk_unchecked_levels(decl.name.clone(), ind_level_subst.to_vec());

    // --- innermost: conclusion `motive i_0 .. i_{ni-1} major` ---
    // Layout (from innermost): major=BVar(0), indices=BVar(1..ni),
    // minors=BVar(ni+1 .. ni+nm), motive=BVar(ni+nm+1).
    let motive_bvar = num_indices
        .checked_add(num_minors)
        .and_then(|x| x.checked_add(1))
        .ok_or("bvar overflow")?;
    let mut result = Term::bvar(motive_bvar);
    for i in 0..num_indices {
        // index i (0 = outermost) is at BVar(num_indices - i).
        result = Term::app(result, Term::bvar(num_indices.saturating_sub(i)));
    }
    result = Term::app(result, Term::bvar(0)); // major

    // --- major premise: (t : I params indices) → conclusion ---
    // Under (params, motive, minors, indices) = np? no: at this point the binders
    // ABOVE the major are: indices (ni), minors (nm), motive (1), params (np).
    // Inside the major domain, params are at BVar(ni + nm + 1 + (np-1-p)) and
    // indices at BVar(ni-1-i).
    let major_param_base = num_indices
        .checked_add(num_minors)
        .and_then(|x| x.checked_add(1))
        .ok_or("bvar overflow")?;
    let major_ty = ind_app(
        &decl.name,
        ind_level_subst,
        num_params,
        num_indices,
        |p| major_param_base.saturating_add(num_params.saturating_sub(1).saturating_sub(p)),
        |i| num_indices.saturating_sub(1).saturating_sub(i),
    )?;
    let _ = &ind_const;
    result = Term::pi(BinderInfo::Default, major_ty, result);

    // --- index binders ---
    // Index domain I_i references earlier indices (BVar < i) and params. Between
    // indices and params sit the motive + minors, so param refs shift by
    // (num_minors + 1). Earlier index refs are unchanged.
    let extra = num_minors.checked_add(1).ok_or("bvar overflow")?;
    for (i, (bi, index_ty)) in index_binders.iter().enumerate().rev() {
        let i_u32 = u32::try_from(i).map_err(|_| "index count".to_string())?;
        let lifted = lift_from(index_ty, i_u32, extra);
        result = Term::pi(*bi, lifted, result);
    }

    // --- minor premises ---
    let mut minor_types = Vec::with_capacity(ctor_infos.len());
    for ci in ctor_infos {
        let mty = build_minor_premise_type(decl, num_indices, ind_level_subst, ci)?;
        minor_types.push(mty);
    }
    // Minor i sits under preceding minors (lift by its position) — minor domains
    // reference only the motive + params (above), not indices/major (below).
    for (i, mty) in minor_types.iter().enumerate().rev() {
        let i_u32 = u32::try_from(i).map_err(|_| "minor count".to_string())?;
        let lifted = if i_u32 > 0 {
            lift(mty, i_u32)
        } else {
            mty.clone()
        };
        result = Term::pi(BinderInfo::Default, lifted, result);
    }

    // --- motive: {motive : (indices...) → I params indices → Sort u} ---
    let motive_ty = build_motive_type(decl, num_indices, motive_univ, ind_level_subst)?;
    result = Term::pi(BinderInfo::Implicit, motive_ty, result);

    // --- parameters (outermost) ---
    for (bi, param_ty) in param_binders.iter().rev() {
        result = Term::pi(*bi, param_ty.clone(), result);
    }

    Ok(result)
}

/// The motive type, as a standalone binder domain:
/// `(i_0 : I_0) .. (i_{k-1} : I_{k-1}) → (major : I params indices) → Sort u`.
/// Inside this type, params are bound *outside* (by the recursor's param
/// binders), so a param reference is `BVar(num_indices + 1 + (np-1-p))` from the
/// innermost point (after the major binder). We build inside-out.
fn build_motive_type(
    decl: &InductiveDecl,
    num_indices: u32,
    motive_univ: &Level,
    ind_level_subst: &[Level],
) -> Result<Term, String> {
    let num_params = decl.num_params;
    let mut after_params = decl.type_.clone();
    for _ in 0..num_params {
        if let TermKind::Pi(_, _, codom) = after_params.kind() {
            after_params = codom.clone();
        }
    }
    let index_binders: Vec<(BinderInfo, Term)> = pi_domains_with_info(&after_params, num_indices)
        .into_iter()
        .map(|(bi, t)| (bi, t.instantiate_levels(ind_level_subst)))
        .collect();

    // innermost: Sort u
    let mut mtype = Term::sort(motive_univ.clone());
    // major: (I params indices) → Sort u. Under the index binders (ni of them),
    // index i is at BVar(ni-1-i); params are bound outside the motive entirely,
    // so at BVar(ni + (np-1-p)).
    let major_ty = ind_app(
        &decl.name,
        ind_level_subst,
        num_params,
        num_indices,
        |p| num_indices.saturating_add(num_params.saturating_sub(1).saturating_sub(p)),
        |i| num_indices.saturating_sub(1).saturating_sub(i),
    )?;
    mtype = Term::pi(BinderInfo::Default, major_ty, mtype);
    // index binders, outermost (idx_0) last. Each I_i taken verbatim (params
    // bound directly outside the motive — same relative depth as in the
    // inductive's telescope), so placed unchanged (num_motives = 1).
    for (bi, index_ty) in index_binders.iter().rev() {
        mtype = Term::pi(*bi, index_ty.clone(), mtype);
    }
    Ok(mtype)
}

/// The minor-premise type for one constructor:
/// `(f_0..f_{m-1}) → (IH_j for recursive f_j) → motive ctor_indices (C params fields)`.
fn build_minor_premise_type(
    decl: &InductiveDecl,
    _num_indices: u32,
    ind_level_subst: &[Level],
    ci: &CtorInfo,
) -> Result<Term, String> {
    let num_params = decl.num_params;
    let np = num_params;
    let num_fields = ci.num_fields;
    let num_ihs = u32::try_from(ci.recursive.iter().filter(|&&b| b).count())
        .map_err(|_| "ih count".to_string())?;

    // The minor is a binder domain in the rec type; outside it sit the motive
    // (1) and params (np). Inside the minor, from innermost:
    //   ihs:     BVar(0 .. num_ihs-1)
    //   fields:  BVar(num_ihs .. num_ihs+num_fields-1)
    //   motive:  BVar(num_ihs + num_fields)  ... (then params above)
    //   params:  BVar(num_ihs + num_fields + 1 + (np-1-p))
    let motive_bvar = num_ihs.checked_add(num_fields).ok_or("bvar overflow")?;

    // ctor applied to params + fields (used in the conclusion).
    let ctor_levels: Vec<Level> = ind_level_subst.to_vec();
    let ctor_cref = ConstRef::mk_unchecked_levels(ci.name.clone(), ctor_levels);
    let mut ctor_app = Term::const_ref(ctor_cref);
    for p in 0..np {
        // param p (0 = outermost) is at BVar(num_ihs + num_fields + 1 + (np-1-p)).
        let depth = num_ihs
            .checked_add(num_fields)
            .and_then(|x| x.checked_add(1))
            .and_then(|x| x.checked_add(np.saturating_sub(1).saturating_sub(p)))
            .ok_or("bvar overflow")?;
        ctor_app = Term::app(ctor_app, Term::bvar(depth));
    }
    for f in 0..num_fields {
        // field f (0 = outermost) is at BVar(num_ihs + (num_fields-1-f)).
        let depth = num_ihs
            .checked_add(num_fields.saturating_sub(1).saturating_sub(f))
            .ok_or("bvar overflow")?;
        ctor_app = Term::app(ctor_app, Term::bvar(depth));
    }

    // conclusion: motive ctor_indices (ctor_app).
    // ctor return indices reference fields/params in the *constructor* binder
    // context; remap them into the minor conclusion context (all num_ihs IH
    // binders in scope, no z-binders).
    let mut result = Term::bvar(motive_bvar);
    for idx_expr in &ci.return_indices {
        // return indices: all fields in scope → field_idx = num_fields.
        let remapped = remap_index_for_minor(idx_expr, num_fields, num_fields, num_ihs, 0)?;
        result = Term::app(result, remapped);
    }
    result = Term::app(result, ctor_app);

    // IH binders for recursive fields, innermost-first (reverse order).
    let mut ih_offset: u32 = 0;
    for (i, &is_rec) in ci.recursive.iter().enumerate().rev() {
        if !is_rec {
            continue;
        }
        let i_u32 = u32::try_from(i).map_err(|_| "field idx".to_string())?;
        let ihs_above = num_ihs.saturating_sub(1).saturating_sub(ih_offset);
        // field i is at BVar((num_fields-1-i) + ihs_above) inside the IH binders.
        let field_depth = num_fields
            .saturating_sub(1)
            .saturating_sub(i_u32)
            .checked_add(ihs_above)
            .ok_or("bvar overflow")?;
        // motive is at BVar(num_fields + ihs_above) in this context.
        let ih_motive = num_fields.checked_add(ihs_above).ok_or("bvar overflow")?;

        // IH type. For a *bare* recursive field `I params idxs` the IH is
        // `motive idxs (field i)`. For a *reflexive* field
        // `(z_0:D_0)..(z_{k-1}:D_{k-1}) -> I params idxs` the IH is
        // `(z_0:D_0')..(z_{k-1}:D_{k-1}') -> motive idxs' (field i z_0..z_{k-1})`
        // — i.e. the recursive call under the same higher-order binders (Lean's
        // reflexive minor premise, #1784).
        let field_ty = &ci.field_tys[i];
        let n_pis = count_pi(field_ty);
        let field_ret = return_type(field_ty);
        let (_h, field_ret_args) = field_ret.unfold_apps();
        let np_us = usize::try_from(np).unwrap_or(usize::MAX);
        let field_indices: Vec<Term> = field_ret_args.into_iter().skip(np_us).collect();

        // Under the n_pis z-binders, all outer references shift up by n_pis.
        let ih_motive_r = ih_motive.checked_add(n_pis).ok_or("bvar overflow")?;
        let ih_field_depth = field_depth.checked_add(n_pis).ok_or("bvar overflow")?;

        let mut ih_type = Term::bvar(ih_motive_r);
        for idx_expr in &field_indices {
            // field-i's indices: only the i earlier fields are in scope.
            let remapped = remap_index_for_minor(idx_expr, num_fields, i_u32, ihs_above, n_pis)?;
            ih_type = Term::app(ih_type, remapped);
        }
        // major: (field i) applied to the z-binders z_0..z_{k-1}.
        let mut major = Term::bvar(ih_field_depth);
        for k in (0..n_pis).rev() {
            major = Term::app(major, Term::bvar(k));
        }
        ih_type = Term::app(ih_type, major);

        // Wrap the IH type in the n_pis z-binders, with each domain D_j remapped
        // into the minor context (the j-th domain sits under j z-binders).
        let pi_domains = collect_pi_domains(field_ty);
        for (k, (bi, domain)) in pi_domains.iter().enumerate().rev() {
            let k_u32 = u32::try_from(k).map_err(|_| "pi idx".to_string())?;
            let remapped = remap_index_for_minor(domain, num_fields, i_u32, ihs_above, k_u32)?;
            ih_type = Term::pi(*bi, remapped, ih_type);
        }

        result = Term::pi(BinderInfo::Default, ih_type, result);
        ih_offset = ih_offset.saturating_add(1);
    }

    // field binders (outermost). field_ty[i] references earlier fields (BVar<i)
    // and params; inside the minor, params sit above the motive (1 binder), so
    // param refs in a field domain must shift by 1. We lift_from(i, 1) so refs to
    // earlier fields (< i) are untouched while refs to params (>= i) shift by 1
    // (to step over the motive binder).
    for i in (0..num_fields).rev() {
        let field_ty = &ci.field_tys[usize::try_from(i).unwrap_or(usize::MAX)];
        let lifted = lift_from(field_ty, i, 1);
        result = Term::pi(BinderInfo::Default, lifted, result);
    }

    Ok(result)
}

/// Remap a constructor field-domain / return-index expression — written in the
/// *constructor* binder context `[z-binders(n_pis), earlier-fields, params]`
/// (only the `field_idx` fields *before* this one are in scope) — into the
/// minor-premise context. Mirrors Lean's `remap_residual_index_bvars_for_minor`
/// (single-motive):
///
/// * `k < n_pis` (a reflexive z-binder): identity.
/// * else `ctor_k = k - n_pis`; if `ctor_k < field_idx` it is a field ref →
///   `ih_in_scope + num_fields - field_idx + ctor_k + n_pis`;
/// * else a param ref → `ih_in_scope + num_fields + 1 + (ctor_k - field_idx) +
///   n_pis` (the `+1` is the single motive binder).
///
/// For a constructor's *return indices* (all fields in scope), pass
/// `field_idx = num_fields`.
fn remap_index_for_minor(
    expr: &Term,
    num_fields: u32,
    field_idx: u32,
    ih_in_scope: u32,
    n_pis: u32,
) -> Result<Term, String> {
    match expr.kind() {
        TermKind::BVar(k) => {
            let k = *k;
            let new_k = if k < n_pis {
                k
            } else {
                let ctor_k = k.saturating_sub(n_pis);
                if ctor_k < field_idx {
                    ih_in_scope
                        .checked_add(num_fields)
                        .and_then(|x| x.checked_sub(field_idx))
                        .and_then(|x| x.checked_add(ctor_k))
                        .and_then(|x| x.checked_add(n_pis))
                        .ok_or("bvar overflow")?
                } else {
                    let param_j = ctor_k.saturating_sub(field_idx);
                    ih_in_scope
                        .checked_add(num_fields)
                        .and_then(|x| x.checked_add(1))
                        .and_then(|x| x.checked_add(param_j))
                        .and_then(|x| x.checked_add(n_pis))
                        .ok_or("bvar overflow")?
                }
            };
            Ok(Term::bvar(new_k))
        }
        TermKind::App(f, a) => {
            let f2 = remap_index_for_minor(f, num_fields, field_idx, ih_in_scope, n_pis)?;
            let a2 = remap_index_for_minor(a, num_fields, field_idx, ih_in_scope, n_pis)?;
            Ok(Term::app(f2, a2))
        }
        TermKind::Pi(bi, d, c) => {
            // Inside a reflexive domain's nested arrow the codomain is under one
            // more binder, so its z-offset grows by 1.
            let d2 = remap_index_for_minor(d, num_fields, field_idx, ih_in_scope, n_pis)?;
            let c2 = remap_index_for_minor(
                c,
                num_fields,
                field_idx,
                ih_in_scope,
                n_pis.saturating_add(1),
            )?;
            Ok(Term::pi(*bi, d2, c2))
        }
        _ => Ok(expr.clone()),
    }
}

/// Collect the (binder-info, domain) pairs of the leading Pi binders of `t`.
pub(crate) fn collect_pi_domains(t: &Term) -> Vec<(BinderInfo, Term)> {
    let mut out = Vec::new();
    let mut cur = t.clone();
    while let TermKind::Pi(bi, d, c) = cur.kind() {
        out.push((*bi, d.clone()));
        cur = c.clone();
    }
    out
}

// ---------------------------------------------------------------------------
// de Bruijn lift helpers (local; mirror term_ops but parameterised by cutoff).
// ---------------------------------------------------------------------------

fn lift(t: &Term, amount: u32) -> Term {
    lift_from(t, 0, amount)
}

/// Lift loose bvars `>= cutoff` by `amount`.
fn lift_from(t: &Term, cutoff: u32, amount: u32) -> Term {
    if amount == 0 {
        return t.clone();
    }
    match t.kind() {
        TermKind::BVar(i) => {
            if *i >= cutoff {
                Term::bvar(i.saturating_add(amount))
            } else {
                t.clone()
            }
        }
        TermKind::Sort(_) | TermKind::Const(_) | TermKind::Elim(_) | TermKind::Lit(_) => t.clone(),
        TermKind::App(f, a) => {
            Term::app(lift_from(f, cutoff, amount), lift_from(a, cutoff, amount))
        }
        TermKind::Lam(bi, ty, body) => Term::lam(
            *bi,
            lift_from(ty, cutoff, amount),
            lift_from(body, cutoff.saturating_add(1), amount),
        ),
        TermKind::Pi(bi, ty, body) => Term::pi(
            *bi,
            lift_from(ty, cutoff, amount),
            lift_from(body, cutoff.saturating_add(1), amount),
        ),
        TermKind::Let(ty, val, body) => Term::let_(
            lift_from(ty, cutoff, amount),
            lift_from(val, cutoff, amount),
            lift_from(body, cutoff.saturating_add(1), amount),
        ),
        TermKind::Proj(name, idx, e) => {
            Term::proj(name.clone(), *idx, lift_from(e, cutoff, amount))
        }
    }
}
