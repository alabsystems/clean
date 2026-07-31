// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Multi-motive** recursor derivation (design §5.2, milestone M3) for a
//! mutual inductive block — the top-tier-TCB generalization of the single-motive
//! M2 builder ([`crate::recursor_build`]). One recursor is derived per type in
//! the block; all share the same `N` motives (one per block type) and the same
//! `M` minor premises (one per constructor across the whole block), differing
//! only in the target type's index/major binders and the conclusion motive.
//!
//! Mirrors the Lean-faithful reference
//! `crates/clean-kernel/src/env/inductive_recursor_types_mutual.rs` and
//! `inductive_recursor_minor.rs` (multi-motive minor premises), restated against
//! `ck0`'s positional-`Param` levels and private `Term`.
//!
//! Every generated recursor type is **kernel-checked** at admission: a wrong
//! motive universe / minor type / index substitution is a false-*accept*, so the
//! derivation re-runs the kernel's `infer_sort` on what it built and rejects on
//! any failure (design §5.2 "not validated as debug-only metadata").
//!
//! ## de Bruijn layout (rec type of block-target type `t`, `N` motives)
//!
//! Counting binders from innermost (after building inside-out):
//! ```text
//!   major     : BVar(0)
//!   indices   : BVar(1) .. BVar(ni_t)
//!   minors    : BVar(ni_t+1) .. BVar(ni_t+M)
//!   motives   : BVar(ni_t+M+1) .. BVar(ni_t+M+N)   (motive_0 outermost = highest)
//!   params    : BVar(ni_t+M+N+1) ..
//! ```

use crate::inductive::{count_pi, pi_domains_with_info, AdmitError};
use crate::level::Level;
use crate::mutual::{gather_block_ctor_infos, BlockCtorInfo, MutualBlock};
use crate::name::Name;
use crate::rawexpr::BinderInfo;
use crate::recursor::{IotaRule, RecursorData};
use crate::term::{ConstRef, Term, TermKind};
use crate::validate::Env;

/// Build + kernel-check one recursor per type in the block.
pub(crate) fn build_block_recursors(
    env: &dyn Env,
    block: &MutualBlock,
    ind_sorts: &[Level],
    large_elim: bool,
) -> Result<Vec<RecursorData>, AdmitError> {
    let nlp = block.num_level_params();
    let (rec_num_levels, motive_univ, ind_level_subst) = if large_elim {
        let ind_subst: Vec<Level> = (0..nlp)
            .map(|i| Level::param(i.saturating_add(1)))
            .collect();
        (nlp.saturating_add(1), Level::param(0), ind_subst)
    } else {
        let ind_subst: Vec<Level> = (0..nlp).map(Level::param).collect();
        (nlp, Level::zero(), ind_subst)
    };
    let _ = ind_sorts;

    let ctor_infos = gather_block_ctor_infos(block, &ind_level_subst)?;
    let block_names = block.type_names();

    let mut recursors = Vec::with_capacity(block.decls.len());
    for (target_idx, decl) in block.decls.iter().enumerate() {
        let derr = |detail: String| AdmitError::Derivation {
            ind: decl.name.clone(),
            detail,
        };
        let rec_name = Name::from_dotted(&format!("{}.rec", decl.name));
        let cx = BlockCx {
            block,
            block_names: &block_names,
            ctor_infos: &ctor_infos,
            ind_level_subst: &ind_level_subst,
            motive_univ: &motive_univ,
        };
        let rec_ty = build_mutual_recursor_type(&cx, target_idx).map_err(&derr)?;

        let num_params = block.num_params();
        let type_arity = count_pi(&decl.type_);
        let num_indices = type_arity.saturating_sub(num_params);

        // ι-rules: one per constructor that BELONGS to this target type. (The
        // recursor `T_target.rec` only fires on constructors of `T_target`; a
        // cross-type recursive IH call uses the *other* type's recursor.)
        let mut rules = Vec::new();
        for ci in ctor_infos.iter().filter(|c| c.owner_type_idx == target_idx) {
            let rhs = crate::recursor_mutual_rhs::build_mutual_rule_rhs(&cx, rec_num_levels, ci)
                .map_err(&derr)?;
            rules.push(IotaRule {
                constructor: ci.name.clone(),
                num_fields: ci.num_fields,
                recursive: ci.recursive.clone(),
                rhs,
                rec_num_levels: usize::try_from(rec_num_levels).unwrap_or(usize::MAX),
            });
        }

        let recursor = RecursorData {
            name: rec_name,
            inductive: decl.name.clone(),
            num_level_params: rec_num_levels,
            large_elim,
            num_params,
            num_indices,
            num_motives: u32::try_from(block.decls.len()).unwrap_or(u32::MAX),
            num_minors_total: u32::try_from(ctor_infos.len()).unwrap_or(u32::MAX),
            type_: rec_ty,
            rules,
        };
        kernel_check(env, decl, &recursor)?;
        recursors.push(recursor);
    }
    Ok(recursors)
}

/// Shared context for building one recursor of the block.
pub(crate) struct BlockCx<'a> {
    pub(crate) block: &'a MutualBlock,
    pub(crate) block_names: &'a [Name],
    pub(crate) ctor_infos: &'a [BlockCtorInfo],
    pub(crate) ind_level_subst: &'a [Level],
    pub(crate) motive_univ: &'a Level,
}

impl BlockCx<'_> {
    pub(crate) fn num_params(&self) -> u32 {
        self.block.num_params()
    }
    pub(crate) fn num_types(&self) -> u32 {
        u32::try_from(self.block.decls.len()).unwrap_or(u32::MAX)
    }
    pub(crate) fn num_minors(&self) -> u32 {
        u32::try_from(self.ctor_infos.len()).unwrap_or(u32::MAX)
    }
    /// Number of indices of block type `idx`.
    pub(crate) fn num_indices_of(&self, idx: usize) -> u32 {
        let d = &self.block.decls[idx];
        count_pi(&d.type_).saturating_sub(self.num_params())
    }
}

// ---------------------------------------------------------------------------
// Recursor type: params -> motives(N) -> minors(M) -> indices_t -> major_t -> C.
// ---------------------------------------------------------------------------

fn build_mutual_recursor_type(cx: &BlockCx<'_>, target_idx: usize) -> Result<Term, String> {
    let np = cx.num_params();
    let nt = cx.num_types();
    let nm = cx.num_minors();
    let target = &cx.block.decls[target_idx];
    let ni = cx.num_indices_of(target_idx);

    // Parameter + (target) index binders, level-shifted into the rec telescope.
    let param_binders: Vec<(BinderInfo, Term)> = pi_domains_with_info(&target.type_, np)
        .into_iter()
        .map(|(bi, t)| (bi, t.instantiate_levels(cx.ind_level_subst)))
        .collect();
    let mut after_params = target.type_.clone();
    for _ in 0..np {
        if let TermKind::Pi(_, _, codom) = after_params.kind() {
            after_params = codom.clone();
        }
    }
    let index_binders: Vec<(BinderInfo, Term)> = pi_domains_with_info(&after_params, ni)
        .into_iter()
        .map(|(bi, t)| (bi, t.instantiate_levels(cx.ind_level_subst)))
        .collect();

    // --- conclusion: motive_target indices major ---
    // target motive bvar (from innermost, after major+indices+minors):
    //   motive_j is at BVar(ni + nm + (N - 1 - j) + 1).
    let target_motive_bvar = ni
        .checked_add(nm)
        .and_then(|x| {
            x.checked_add(
                nt.saturating_sub(1)
                    .saturating_sub(u32::try_from(target_idx).ok()?),
            )
        })
        .and_then(|x| x.checked_add(1))
        .ok_or("bvar overflow")?;
    let mut result = Term::bvar(target_motive_bvar);
    for i in 0..ni {
        // index i (0=outermost) at BVar(ni - i).
        result = Term::app(result, Term::bvar(ni.saturating_sub(i)));
    }
    result = Term::app(result, Term::bvar(0)); // major

    // --- major premise (t : T_target params indices) ---
    // params above the major: ni + nm + N + (np-1-p). indices: ni-1-i.
    let major_param_base = ni
        .checked_add(nm)
        .and_then(|x| x.checked_add(nt))
        .ok_or("bvar overflow")?;
    let major_ty = ind_app(
        &target.name,
        cx.ind_level_subst,
        np,
        ni,
        |p| major_param_base.saturating_add(np.saturating_sub(1).saturating_sub(p)),
        |i| ni.saturating_sub(1).saturating_sub(i),
    )?;
    result = Term::pi(BinderInfo::Default, major_ty, result);

    // --- index binders ---
    // Between indices and params sit motives(N) + minors(M); param refs in an
    // index domain shift by (nm + N). Earlier index refs unchanged.
    let extra = nm.checked_add(nt).ok_or("bvar overflow")?;
    for (i, (bi, index_ty)) in index_binders.iter().enumerate().rev() {
        let i_u32 = u32::try_from(i).map_err(|_| "index count".to_string())?;
        let lifted = lift_from(index_ty, i_u32, extra);
        result = Term::pi(*bi, lifted, result);
    }

    // --- minor premises (M total, block order) ---
    let mut minor_types = Vec::with_capacity(cx.ctor_infos.len());
    for ci in cx.ctor_infos {
        minor_types.push(crate::recursor_mutual_minor::build_mutual_minor_type(
            cx, ci,
        )?);
    }
    for (i, mty) in minor_types.iter().enumerate().rev() {
        let i_u32 = u32::try_from(i).map_err(|_| "minor count".to_string())?;
        let lifted = if i_u32 > 0 {
            lift(mty, i_u32)
        } else {
            mty.clone()
        };
        result = Term::pi(BinderInfo::Default, lifted, result);
    }

    // --- motives (N) ---
    let mut motive_types = Vec::with_capacity(cx.block.decls.len());
    for j in 0..cx.block.decls.len() {
        motive_types.push(build_mutual_motive_type(cx, j)?);
    }
    for (j, mty) in motive_types.iter().enumerate().rev() {
        let j_u32 = u32::try_from(j).map_err(|_| "motive count".to_string())?;
        let lifted = if j_u32 > 0 {
            lift(mty, j_u32)
        } else {
            mty.clone()
        };
        result = Term::pi(BinderInfo::Implicit, lifted, result);
    }

    // --- parameters (outermost) ---
    for (bi, param_ty) in param_binders.iter().rev() {
        result = Term::pi(*bi, param_ty.clone(), result);
    }
    Ok(result)
}

/// Motive type for block type `j`: `(indices_j) -> (T_j params indices) -> Sort u`.
/// Params are bound outside the motive entirely.
fn build_mutual_motive_type(cx: &BlockCx<'_>, j: usize) -> Result<Term, String> {
    let np = cx.num_params();
    let d = &cx.block.decls[j];
    let ni = cx.num_indices_of(j);
    let mut after_params = d.type_.clone();
    for _ in 0..np {
        if let TermKind::Pi(_, _, codom) = after_params.kind() {
            after_params = codom.clone();
        }
    }
    let index_binders: Vec<(BinderInfo, Term)> = pi_domains_with_info(&after_params, ni)
        .into_iter()
        .map(|(bi, t)| (bi, t.instantiate_levels(cx.ind_level_subst)))
        .collect();

    let mut mtype = Term::sort(cx.motive_univ.clone());
    // major: (T_j params indices) -> Sort u. Under the ni index binders, index i
    // at BVar(ni-1-i); params at BVar(ni + (np-1-p)).
    let major_ty = ind_app(
        &d.name,
        cx.ind_level_subst,
        np,
        ni,
        |p| ni.saturating_add(np.saturating_sub(1).saturating_sub(p)),
        |i| ni.saturating_sub(1).saturating_sub(i),
    )?;
    mtype = Term::pi(BinderInfo::Default, major_ty, mtype);
    for (bi, index_ty) in index_binders.iter().rev() {
        mtype = Term::pi(*bi, index_ty.clone(), mtype);
    }
    Ok(mtype)
}

// ---------------------------------------------------------------------------
// Helpers (local clones of recursor_build's; shared with recursor_mutual_rhs).
// ---------------------------------------------------------------------------

pub(crate) fn ind_app(
    ind: &Name,
    levels: &[Level],
    num_params: u32,
    num_indices: u32,
    param_bvar: impl Fn(u32) -> u32,
    index_bvar: impl Fn(u32) -> u32,
) -> Result<Term, String> {
    let cref = ConstRef::mk_unchecked_levels(ind.clone(), levels.to_vec());
    let mut app = Term::const_ref(cref);
    for p in 0..num_params {
        app = Term::app(app, Term::bvar(param_bvar(p)));
    }
    for i in 0..num_indices {
        app = Term::app(app, Term::bvar(index_bvar(i)));
    }
    Ok(app)
}

pub(crate) fn collect_pi_domains(t: &Term) -> Vec<(BinderInfo, Term)> {
    let mut out = Vec::new();
    let mut cur = t.clone();
    while let TermKind::Pi(bi, d, c) = cur.kind() {
        out.push((*bi, d.clone()));
        cur = c.clone();
    }
    out
}

fn lift(t: &Term, amount: u32) -> Term {
    t.lift(amount)
}

pub(crate) fn lift_from(t: &Term, cutoff: u32, amount: u32) -> Term {
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

fn kernel_check(
    env: &dyn Env,
    decl: &crate::inductive::InductiveDecl,
    rec: &RecursorData,
) -> Result<(), AdmitError> {
    let mut budget = crate::mutual::admission_budget();
    crate::infer::infer_sort_in_context(env, &[], &rec.type_, &mut budget).map_err(|e| {
        AdmitError::Derivation {
            ind: decl.name.clone(),
            detail: format!("generated mutual recursor type failed kernel check: {e}"),
        }
    })?;
    Ok(())
}
