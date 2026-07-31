// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Multi-motive **minor-premise type** construction (design §5.2, milestone M3).
//! Extracted from [`crate::recursor_mutual`] to keep both files under the
//! 500-line convention. Mirrors the Lean-faithful reference
//! `crates/clean-kernel/src/env/inductive_recursor_minor.rs` (the
//! `num_motives > 1` path): the conclusion uses the constructor's owner-type
//! motive, and each IH uses the motive of the type the recursive field returns
//! to (`field_motive`).

use crate::inductive::{count_pi, return_type};
use crate::mutual::BlockCtorInfo;
use crate::rawexpr::BinderInfo;
use crate::recursor_mutual::{collect_pi_domains, lift_from, BlockCx};
use crate::term::{ConstRef, Term, TermKind};

/// Minor premise type for one constructor `ci` (multi-motive). The conclusion
/// uses motive `ci.owner_type_idx`; each IH uses motive `ci.field_motive[i]`.
pub(crate) fn build_mutual_minor_type(
    cx: &BlockCx<'_>,
    ci: &BlockCtorInfo,
) -> Result<Term, String> {
    let np = cx.num_params();
    let nt = cx.num_types();
    let num_fields = ci.num_fields;
    let num_ihs = u32::try_from(ci.recursive.iter().filter(|&&b| b).count())
        .map_err(|_| "ih count".to_string())?;

    // Inside the minor, from innermost: ihs(num_ihs), fields(num_fields),
    // motives(N), params. So:
    //   motive_j  : BVar(num_ihs + num_fields + (N-1-j))
    //   params    : BVar(num_ihs + num_fields + N + (np-1-p))
    let conclusion_motive_bvar = num_ihs
        .checked_add(num_fields)
        .and_then(|x| {
            x.checked_add(
                nt.saturating_sub(1)
                    .saturating_sub(u32::try_from(ci.owner_type_idx).ok()?),
            )
        })
        .ok_or("bvar overflow")?;

    // ctor applied to params + fields.
    let ctor_cref = ConstRef::mk_unchecked_levels(ci.name.clone(), cx.ind_level_subst.to_vec());
    let mut ctor_app = Term::const_ref(ctor_cref);
    for p in 0..np {
        let depth = num_ihs
            .checked_add(num_fields)
            .and_then(|x| x.checked_add(nt))
            .and_then(|x| x.checked_add(np.saturating_sub(1).saturating_sub(p)))
            .ok_or("bvar overflow")?;
        ctor_app = Term::app(ctor_app, Term::bvar(depth));
    }
    for f in 0..num_fields {
        let depth = num_ihs
            .checked_add(num_fields.saturating_sub(1).saturating_sub(f))
            .ok_or("bvar overflow")?;
        ctor_app = Term::app(ctor_app, Term::bvar(depth));
    }

    // conclusion: motive_owner ctor_indices (ctor_app).
    let mut result = Term::bvar(conclusion_motive_bvar);
    for idx_expr in &ci.return_indices {
        let remapped = remap_index_for_minor(idx_expr, num_fields, num_fields, num_ihs, nt, 0)?;
        result = Term::app(result, remapped);
    }
    result = Term::app(result, ctor_app);

    // IH binders for recursive fields, innermost-first.
    let mut ih_offset: u32 = 0;
    for (i, &is_rec) in ci.recursive.iter().enumerate().rev() {
        if !is_rec {
            continue;
        }
        let i_u32 = u32::try_from(i).map_err(|_| "field idx".to_string())?;
        let ihs_above = num_ihs.saturating_sub(1).saturating_sub(ih_offset);
        let field_depth = num_fields
            .saturating_sub(1)
            .saturating_sub(i_u32)
            .checked_add(ihs_above)
            .ok_or("bvar overflow")?;
        // IH uses motive of the field's target type.
        let ih_motive_idx =
            u32::try_from(ci.field_motive[i]).map_err(|_| "motive idx".to_string())?;
        let motive_at_ih = num_fields
            .checked_add(ihs_above)
            .and_then(|x| x.checked_add(nt.saturating_sub(1).saturating_sub(ih_motive_idx)))
            .ok_or("bvar overflow")?;

        let field_ty = &ci.field_tys[i];
        let n_pis = count_pi(field_ty);
        let field_ret = return_type(field_ty);
        let (_h, field_ret_args) = field_ret.unfold_apps();
        let np_us = usize::try_from(np).unwrap_or(usize::MAX);
        let field_indices: Vec<Term> = field_ret_args.into_iter().skip(np_us).collect();

        let ih_motive_r = motive_at_ih.checked_add(n_pis).ok_or("bvar overflow")?;
        let ih_field_depth = field_depth.checked_add(n_pis).ok_or("bvar overflow")?;

        let mut ih_type = Term::bvar(ih_motive_r);
        for idx_expr in &field_indices {
            let remapped =
                remap_index_for_minor(idx_expr, num_fields, i_u32, ihs_above, nt, n_pis)?;
            ih_type = Term::app(ih_type, remapped);
        }
        let mut major = Term::bvar(ih_field_depth);
        for k in (0..n_pis).rev() {
            major = Term::app(major, Term::bvar(k));
        }
        ih_type = Term::app(ih_type, major);

        let pi_domains = collect_pi_domains(field_ty);
        for (k, (bi, domain)) in pi_domains.iter().enumerate().rev() {
            let k_u32 = u32::try_from(k).map_err(|_| "pi idx".to_string())?;
            let remapped = remap_index_for_minor(domain, num_fields, i_u32, ihs_above, nt, k_u32)?;
            ih_type = Term::pi(*bi, remapped, ih_type);
        }
        result = Term::pi(BinderInfo::Default, ih_type, result);
        ih_offset = ih_offset.saturating_add(1);
    }

    // field binders (outermost). field_ty[i] references earlier fields (<i) and
    // params; the N motive binders sit between fields and params, so lift_from(i, N).
    for i in (0..num_fields).rev() {
        let field_ty = &ci.field_tys[usize::try_from(i).unwrap_or(usize::MAX)];
        let lifted = lift_from(field_ty, i, nt);
        result = Term::pi(BinderInfo::Default, lifted, result);
    }
    Ok(result)
}

/// Remap a field-domain / return-index expr written in the *constructor* binder
/// context `[z(n_pis), earlier-fields, params]` into the multi-motive minor
/// context `[z(n_pis), ihs, fields, motives(N), params]`:
///
/// * `k < n_pis`: identity (a reflexive z-binder).
/// * else `ctor_k = k - n_pis`; if `ctor_k < field_idx` (field ref) →
///   `ihs_in_scope + (num_fields - field_idx + ctor_k) + n_pis`;
/// * else (param ref, `param_j = ctor_k - field_idx`) →
///   `ihs_in_scope + num_fields + N + param_j + n_pis` (the `+N` steps over the
///   motive binders).
fn remap_index_for_minor(
    expr: &Term,
    num_fields: u32,
    field_idx: u32,
    ih_in_scope: u32,
    num_motives: u32,
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
                        .and_then(|x| x.checked_add(num_motives))
                        .and_then(|x| x.checked_add(param_j))
                        .and_then(|x| x.checked_add(n_pis))
                        .ok_or("bvar overflow")?
                }
            };
            Ok(Term::bvar(new_k))
        }
        TermKind::App(f, a) => Ok(Term::app(
            remap_index_for_minor(f, num_fields, field_idx, ih_in_scope, num_motives, n_pis)?,
            remap_index_for_minor(a, num_fields, field_idx, ih_in_scope, num_motives, n_pis)?,
        )),
        TermKind::Pi(bi, d, c) => Ok(Term::pi(
            *bi,
            remap_index_for_minor(d, num_fields, field_idx, ih_in_scope, num_motives, n_pis)?,
            remap_index_for_minor(
                c,
                num_fields,
                field_idx,
                ih_in_scope,
                num_motives,
                n_pis.saturating_add(1),
            )?,
        )),
        _ => Ok(expr.clone()),
    }
}
