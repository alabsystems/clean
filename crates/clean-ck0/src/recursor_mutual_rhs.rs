// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Multi-motive ι-rule **RHS** construction (design §5.2, milestone M3).
//! Extracted from [`crate::recursor_mutual`] to keep both files under the
//! 500-line convention. The RHS is the closed λ-term that, applied positionally
//! to `params · motives(N) · minors(M) · fields`, yields the owner minor premise
//! invoked on the constructor's fields and each recursive field's IH — where a
//! cross-type recursive field's IH calls the *target type's* recursor (Lean's
//! mutual ι-rule).

use crate::inductive::{count_pi, return_type};
use crate::level::Level;
use crate::mutual::BlockCtorInfo;
use crate::name::Name;
use crate::rawexpr::BinderInfo;
use crate::recursor_mutual::{collect_pi_domains, BlockCx};
use crate::term::{ConstRef, Term, TermKind};

/// Rule RHS: `λ params. λ motives(N). λ minors(M). λ fields.
///   minor_k field_0 .. field_{nf-1} IH_0 .. IH_p`
/// where IH_j = `T_field_target.rec @levels params motives minors field_idxs (field_j ..)`.
pub(crate) fn build_mutual_rule_rhs(
    cx: &BlockCx,
    rec_num_levels: u32,
    ci: &BlockCtorInfo,
) -> Result<Term, String> {
    let np = cx.num_params();
    let nt = cx.num_types();
    let nm = cx.num_minors();
    let nf = ci.num_fields;

    // global ctor index in block order (minor position).
    let ctor_pos = cx
        .ctor_infos
        .iter()
        .position(|c| c.name == ci.name)
        .ok_or("ctor not found")?;
    let ctor_pos_u32 = u32::try_from(ctor_pos).map_err(|_| "ctor idx".to_string())?;

    // Lambda binders (outermost->innermost): params(np), motives(N), minors(M),
    // fields(nf). Inside the body from innermost:
    //   fields:  BVar(0 .. nf-1)
    //   minors:  BVar(nf .. nf+M-1)
    //   motives: BVar(nf+M .. nf+M+N-1)
    //   params:  BVar(nf+M+N ..)
    let total_binders = np
        .checked_add(nt)
        .and_then(|x| x.checked_add(nm))
        .and_then(|x| x.checked_add(nf))
        .ok_or("bvar overflow")?;

    // minor_k: minor_pos (0=outermost in the lambda chain) at BVar(nf+M-1-pos).
    let minor_bvar = nf
        .checked_add(nm)
        .and_then(|x| x.checked_sub(1))
        .and_then(|x| x.checked_sub(ctor_pos_u32))
        .ok_or("bvar overflow")?;
    let mut body = Term::bvar(minor_bvar);
    for f in 0..nf {
        body = Term::app(body, Term::bvar(nf.saturating_sub(1).saturating_sub(f)));
    }

    let rec_levels: Vec<Level> = (0..rec_num_levels).map(Level::param).collect();

    for (i, &is_rec) in ci.recursive.iter().enumerate() {
        if !is_rec {
            continue;
        }
        let i_u32 = u32::try_from(i).map_err(|_| "field idx".to_string())?;
        let field_ty = &ci.field_tys[i];
        let n_pis = count_pi(field_ty);
        // recursor of the field's target type.
        let target_idx = ci.field_motive[i];
        let target_name = &cx.block_names[target_idx];
        let rec_name = Name::from_dotted(&format!("{target_name}.rec"));
        let rec_cref = Term::const_ref(ConstRef::mk_unchecked_levels(rec_name, rec_levels.clone()));
        let mut ih = rec_cref;
        // params: BVar(total_binders-1-p + n_pis).
        for p in 0..np {
            let depth = total_binders
                .checked_sub(1)
                .and_then(|x| x.checked_sub(p))
                .and_then(|x| x.checked_add(n_pis))
                .ok_or("bvar overflow")?;
            ih = Term::app(ih, Term::bvar(depth));
        }
        // motives: motive_j at BVar(nf+M+(N-1-j) + n_pis), in block order 0..N.
        for j in 0..nt {
            let depth = nf
                .checked_add(nm)
                .and_then(|x| x.checked_add(nt.saturating_sub(1).saturating_sub(j)))
                .and_then(|x| x.checked_add(n_pis))
                .ok_or("bvar overflow")?;
            ih = Term::app(ih, Term::bvar(depth));
        }
        // minors: minor j at BVar(nf+M-1-j + n_pis).
        for j in 0..nm {
            let depth = nf
                .checked_add(nm)
                .and_then(|x| x.checked_sub(1))
                .and_then(|x| x.checked_sub(j))
                .and_then(|x| x.checked_add(n_pis))
                .ok_or("bvar overflow")?;
            ih = Term::app(ih, Term::bvar(depth));
        }
        // field indices of the recursive field's return type.
        let field_ret = return_type(field_ty);
        let (_h, args) = field_ret.unfold_apps();
        let np_us = usize::try_from(np).unwrap_or(usize::MAX);
        for idx_expr in args.into_iter().skip(np_us) {
            let remapped = remap_index_for_rhs(&idx_expr, nf, i_u32, nm, nt, n_pis)?;
            ih = Term::app(ih, remapped);
        }
        // major: (field_i z_0..z_{k-1}). field_i at BVar(nf-1-i + n_pis).
        let mut major = Term::bvar(
            nf.saturating_sub(1)
                .saturating_sub(i_u32)
                .checked_add(n_pis)
                .ok_or("bvar overflow")?,
        );
        for k in (0..n_pis).rev() {
            major = Term::app(major, Term::bvar(k));
        }
        ih = Term::app(ih, major);

        let pi_domains = collect_pi_domains(field_ty);
        for (k, (bi, domain)) in pi_domains.iter().enumerate().rev() {
            let k_u32 = u32::try_from(k).map_err(|_| "pi idx".to_string())?;
            let remapped = remap_index_for_rhs(domain, nf, i_u32, nm, nt, k_u32)?;
            ih = Term::lam(*bi, remapped, ih);
        }
        body = Term::app(body, ih);
    }

    // Wrap lambdas with Sort-0 placeholder domains (positional reduction only).
    let dummy = Term::sort(Level::zero());
    for _ in 0..nf {
        body = Term::lam(BinderInfo::Default, dummy.clone(), body);
    }
    for _ in 0..nm {
        body = Term::lam(BinderInfo::Default, dummy.clone(), body);
    }
    for _ in 0..nt {
        body = Term::lam(BinderInfo::Default, dummy.clone(), body);
    }
    for _ in 0..np {
        body = Term::lam(BinderInfo::Default, dummy.clone(), body);
    }
    Ok(body)
}

/// Remap a recursive field's return-index / reflexive-domain from the
/// *constructor* context `[z(n_pis), earlier-fields, params]` into the rule RHS
/// body context `[z(n_pis), fields(nf), minors(M), motives(N), params]`:
///
/// * field `ctor_k < field_idx` → `BVar(nf - field_idx + ctor_k + n_pis)`;
/// * param → `BVar(nf + M + N + (ctor_k - field_idx) + n_pis)`.
fn remap_index_for_rhs(
    expr: &Term,
    nf: u32,
    field_idx: u32,
    num_minors: u32,
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
                    nf.checked_sub(field_idx)
                        .and_then(|x| x.checked_add(ctor_k))
                        .and_then(|x| x.checked_add(n_pis))
                        .ok_or("bvar overflow")?
                } else {
                    let param_j = ctor_k.saturating_sub(field_idx);
                    nf.checked_add(num_minors)
                        .and_then(|x| x.checked_add(num_motives))
                        .and_then(|x| x.checked_add(param_j))
                        .and_then(|x| x.checked_add(n_pis))
                        .ok_or("bvar overflow")?
                }
            };
            Ok(Term::bvar(new_k))
        }
        TermKind::App(f, a) => Ok(Term::app(
            remap_index_for_rhs(f, nf, field_idx, num_minors, num_motives, n_pis)?,
            remap_index_for_rhs(a, nf, field_idx, num_minors, num_motives, n_pis)?,
        )),
        TermKind::Pi(bi, d, c) => Ok(Term::pi(
            *bi,
            remap_index_for_rhs(d, nf, field_idx, num_minors, num_motives, n_pis)?,
            remap_index_for_rhs(
                c,
                nf,
                field_idx,
                num_minors,
                num_motives,
                n_pis.saturating_add(1),
            )?,
        )),
        _ => Ok(expr.clone()),
    }
}
