// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ι-rule **RHS** construction for derived recursors (design §5.2). Extracted
//! from `recursor_build.rs` to keep both files under the 500-line convention.
//! The RHS is the closed λ-term that, applied positionally to
//! `params · motive · minors · fields`, yields the minor premise invoked on the
//! constructor's fields and their recursive IH calls.

use crate::inductive::{count_pi, return_type, InductiveDecl};
use crate::level::Level;
use crate::name::Name;
use crate::rawexpr::BinderInfo;
use crate::recursor::CtorInfo;
use crate::recursor_build::collect_pi_domains;
use crate::term::{ConstRef, Term, TermKind};

// ---------------------------------------------------------------------------
// ι-rule RHS.
// ---------------------------------------------------------------------------

/// The rule RHS: `λ params. λ {motive}. λ minors. λ fields.
///   minor_k field_0 .. field_{m-1} IH_0 .. IH_p`
/// where each IH_j = `I.rec @levels params motive minors field_indices (field_j)`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn build_rule_rhs(
    decl: &InductiveDecl,
    rec_name: &Name,
    rec_num_levels: u32,
    num_indices: u32,
    num_minors: u32,
    ctor_idx: usize,
    ci: &CtorInfo,
    ind_level_subst: &[Level],
) -> Result<Term, String> {
    let np = decl.num_params;
    let nm: u32 = 1; // num_motives, M2
    let nf = ci.num_fields;
    let ctor_idx_u32 = u32::try_from(ctor_idx).map_err(|_| "ctor idx".to_string())?;

    // Lambda binders (outermost→innermost): params (np), motive (1), minors (nm_m),
    // fields (nf). Inside the body, from innermost (BVar(0)):
    //   fields:  BVar(0 .. nf-1)
    //   minors:  BVar(nf .. nf+num_minors-1)
    //   motive:  BVar(nf+num_minors)
    //   params:  BVar(nf+num_minors+1 .. )
    let total_binders = np
        .checked_add(nm)
        .and_then(|x| x.checked_add(num_minors))
        .and_then(|x| x.checked_add(nf))
        .ok_or("bvar overflow")?;

    // minor_k: minors are minor_0 (outermost in the lambda chain) at BVar(nf+num_minors-1).
    let minor_bvar = nf
        .checked_add(num_minors)
        .and_then(|x| x.checked_sub(1))
        .and_then(|x| x.checked_sub(ctor_idx_u32))
        .ok_or("bvar overflow")?;
    let mut body = Term::bvar(minor_bvar);

    // apply fields: field f (0=outermost) at BVar(nf-1-f).
    for f in 0..nf {
        body = Term::app(body, Term::bvar(nf.saturating_sub(1).saturating_sub(f)));
    }

    // recursor levels: the motive level (if large_elim) leads, then ind levels.
    let rec_levels: Vec<Level> = (0..rec_num_levels).map(Level::param).collect();

    // apply IH for each recursive field.
    for (i, &is_rec) in ci.recursive.iter().enumerate() {
        if !is_rec {
            continue;
        }
        let i_u32 = u32::try_from(i).map_err(|_| "field idx".to_string())?;
        let field_ty = &ci.field_tys[i];
        // n_pis = reflexive higher-order binders of the field; the IH recurses
        // under the same binders (Lean #1784). All non-z references shift by
        // n_pis inside those binders.
        let n_pis = count_pi(field_ty);
        // IH = rec @levels params motive minors field_indices' (field_i z..).
        let rec_cref = ElimLikeConst::rec_const(rec_name, &rec_levels);
        let mut ih = rec_cref;
        // params: BVar(total_binders-1 - p + n_pis) for p=0..np-1.
        for p in 0..np {
            let depth = total_binders
                .checked_sub(1)
                .and_then(|x| x.checked_sub(p))
                .and_then(|x| x.checked_add(n_pis))
                .ok_or("bvar overflow")?;
            ih = Term::app(ih, Term::bvar(depth));
        }
        // motive: BVar(nf+num_minors + n_pis).
        let motive_depth = nf
            .checked_add(num_minors)
            .and_then(|x| x.checked_add(n_pis))
            .ok_or("bvar overflow")?;
        ih = Term::app(ih, Term::bvar(motive_depth));
        // minors: minor j at BVar(nf+num_minors-1-j + n_pis).
        for j in 0..num_minors {
            let depth = nf
                .checked_add(num_minors)
                .and_then(|x| x.checked_sub(1))
                .and_then(|x| x.checked_sub(j))
                .and_then(|x| x.checked_add(n_pis))
                .ok_or("bvar overflow")?;
            ih = Term::app(ih, Term::bvar(depth));
        }
        // field indices (from the recursive field's return type), remapped into
        // the rhs body context (no IH binders; fields at BVar(nf-1-f), params at
        // BVar(nf+num_minors+1+(np-1-p)); under the n_pis z-binders shift).
        if num_indices > 0 {
            let field_ret = return_type(field_ty);
            let (_h, args) = field_ret.unfold_apps();
            let np_us = usize::try_from(np).unwrap_or(usize::MAX);
            for idx_expr in args.into_iter().skip(np_us) {
                let remapped = remap_index_for_rhs(&idx_expr, nf, i_u32, num_minors, n_pis)?;
                ih = Term::app(ih, remapped);
            }
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

        // Wrap the IH in the n_pis z-binders (domains remapped into rhs context).
        let pi_domains = collect_pi_domains(field_ty);
        for (k, (bi, domain)) in pi_domains.iter().enumerate().rev() {
            let k_u32 = u32::try_from(k).map_err(|_| "pi idx".to_string())?;
            let remapped = remap_index_for_rhs(domain, nf, i_u32, num_minors, k_u32)?;
            ih = Term::lam(*bi, remapped, ih);
        }

        body = Term::app(body, ih);
    }

    // Wrap lambdas: fields (innermost), minors, motive, params (outermost). The
    // binder *types* are not load-bearing for ι-reduction (reduction is purely
    // positional substitution), so we use the kernel-checked recursor type's own
    // domains where available; for the rhs we use placeholder Sorts since the
    // rule is only ever applied to already-typed arguments. To keep the rhs
    // itself well-typed for the kernel-check, we reconstruct domains from the
    // recursor type in `kernel_check_recursor`. Here we use Sort 0 placeholders.
    let dummy = Term::sort(Level::zero());
    for _ in 0..nf {
        body = Term::lam(BinderInfo::Default, dummy.clone(), body);
    }
    for _ in 0..num_minors {
        body = Term::lam(BinderInfo::Default, dummy.clone(), body);
    }
    for _ in 0..nm {
        body = Term::lam(BinderInfo::Default, dummy.clone(), body);
    }
    for _ in 0..np {
        body = Term::lam(BinderInfo::Default, dummy.clone(), body);
    }
    let _ = ind_level_subst;
    Ok(body)
}

/// Remap a recursive field's return-index / reflexive-domain from the
/// *constructor* context `[z(n_pis), earlier-fields, params]` (only `field_idx`
/// fields in scope) into the rule RHS body context
/// `[z(n_pis), fields(nf), minors(num_minors), motive(1), params]` (no IH
/// binders in the RHS):
///
/// * field `ctor_k < field_idx` → `BVar(nf - field_idx + ctor_k + n_pis)`;
/// * param → `BVar(nf + num_minors + 1 + (ctor_k - field_idx) + n_pis)`.
fn remap_index_for_rhs(
    expr: &Term,
    nf: u32,
    field_idx: u32,
    num_minors: u32,
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
                        .and_then(|x| x.checked_add(1))
                        .and_then(|x| x.checked_add(param_j))
                        .and_then(|x| x.checked_add(n_pis))
                        .ok_or("bvar overflow")?
                }
            };
            Ok(Term::bvar(new_k))
        }
        TermKind::App(f, a) => {
            let f2 = remap_index_for_rhs(f, nf, field_idx, num_minors, n_pis)?;
            let a2 = remap_index_for_rhs(a, nf, field_idx, num_minors, n_pis)?;
            Ok(Term::app(f2, a2))
        }
        TermKind::Pi(bi, d, c) => {
            let d2 = remap_index_for_rhs(d, nf, field_idx, num_minors, n_pis)?;
            let c2 = remap_index_for_rhs(c, nf, field_idx, num_minors, n_pis.saturating_add(1))?;
            Ok(Term::pi(*bi, d2, c2))
        }
        _ => Ok(expr.clone()),
    }
}

/// Helper to build a recursor constant reference in a `Term` for the rule RHS.
/// The recursor is referenced by its name with its own level vector; this is an
/// internal construction used only inside derived rule RHSs (never crosses the
/// untrusted boundary).
struct ElimLikeConst;
impl ElimLikeConst {
    fn rec_const(rec_name: &Name, levels: &[Level]) -> Term {
        Term::const_ref(ConstRef::mk_unchecked_levels(
            rec_name.clone(),
            levels.to_vec(),
        ))
    }
}
