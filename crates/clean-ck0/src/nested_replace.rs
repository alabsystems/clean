// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expression-replacement helpers for the nested→mutual auxiliary construction
//! (design §5.2, milestone M3). Extracted from [`crate::nested`] to keep both
//! files under the 500-line convention. Mirrors the Lean-faithful reference
//! `crates/clean-kernel/src/env/inductive_nested_replace.rs`.

use crate::level::Level;
use crate::name::Name;
use crate::nested::Occurrence;
use crate::positivity::term_mentions;
use crate::term::{ConstRef, Term, TermKind};
use crate::validate::Env;

// ---------------------------------------------------------------------------
// Parameter canonicalization for PARAMETERIZED nested inductives (design §5.2).
//
// A nested occurrence `Container <args>` inside a constructor mentions the
// parent's parameters at de Bruijn indices that depend on *where* in the
// constructor telescope the occurrence sits (the parent params are the
// outermost binders, so deeper field/index binders shift their indices). To
// build a SINGLE auxiliary type that is itself parametric over the parent's
// parameters — `Tree._List (A : Type)` for `Tree (A)` — every occurrence's args
// are normalized into one canonical context whose only binders are the `np`
// parent parameters (`below = 0`): canonical param `p` (0 = outermost) sits at
// `BVar(np-1-p)`.
//
// `below` is the number of binders between the term's position and the
// innermost parent-parameter binder; so at the term's position the parent
// params occupy de Bruijn indices `below .. below+np` (a loose `BVar(below)` is
// the innermost param, `BVar(below+np-1)` the outermost). Lowering subtracts
// `below` from those param-range vars and is `None` (REJECT — fail-closed) if a
// loose var lands *below* the param block (i.e. refers to a field/index local):
// such a nesting is not uniform in the parameters and a parametric aux cannot
// represent it.
// ---------------------------------------------------------------------------

/// Lower a term that sits `below` binders inside the parent-parameter block into
/// the canonical `num_params`-parameter context (`below = 0`). Loose vars that
/// reference a parent parameter are remapped; a loose var that references a
/// non-parameter local (a field/index binder) makes the occurrence non-uniform,
/// and lowering returns `None` (a fail-closed reject). Vars bound *inside* `t`
/// are preserved.
pub(crate) fn lower_params(t: &Term, below: u32, num_params: u32) -> Option<Term> {
    lower_params_at(t, below, num_params, 0)
}

fn lower_params_at(t: &Term, below: u32, num_params: u32, local: u32) -> Option<Term> {
    match t.kind() {
        TermKind::BVar(i) => {
            let i = *i;
            if i < local {
                // Bound inside `t` itself — unchanged.
                return Some(Term::bvar(i));
            }
            // Loose relative to `t`: its index into the enclosing context is
            // `i - local`. The parent params occupy enclosing indices
            // `below .. below+num_params`.
            let enclosing = i.checked_sub(local)?;
            let param_lo = below;
            let param_hi = below.checked_add(num_params)?;
            if enclosing < param_lo {
                // A field/index local leaked into a nesting argument: non-uniform.
                return None;
            }
            if enclosing >= param_hi {
                // Escapes the parameter block — impossible for a closed ctor
                // type; reject fail-closed.
                return None;
            }
            // A parameter: drop the `below` field/index binders between it and
            // the canonical context, keeping the local binders.
            let lowered = i.checked_sub(below)?;
            Some(Term::bvar(lowered))
        }
        TermKind::Sort(_) | TermKind::Const(_) | TermKind::Elim(_) | TermKind::Lit(_) => {
            Some(t.clone())
        }
        TermKind::App(f, a) => Some(Term::app(
            lower_params_at(f, below, num_params, local)?,
            lower_params_at(a, below, num_params, local)?,
        )),
        TermKind::Lam(bi, ty, body) => Some(Term::lam(
            *bi,
            lower_params_at(ty, below, num_params, local)?,
            lower_params_at(body, below, num_params, local.checked_add(1)?)?,
        )),
        TermKind::Pi(bi, ty, body) => Some(Term::pi(
            *bi,
            lower_params_at(ty, below, num_params, local)?,
            lower_params_at(body, below, num_params, local.checked_add(1)?)?,
        )),
        TermKind::Let(ty, val, body) => Some(Term::let_(
            lower_params_at(ty, below, num_params, local)?,
            lower_params_at(val, below, num_params, local)?,
            lower_params_at(body, below, num_params, local.checked_add(1)?)?,
        )),
        TermKind::Proj(name, idx, e) => Some(Term::proj(
            name.clone(),
            *idx,
            lower_params_at(e, below, num_params, local)?,
        )),
    }
}

/// Replace `Container <params matching container_args> <indices>` with
/// `Aux <indices>` throughout `expr` (used when building an auxiliary type's own
/// constructors, where the container's self-references must point at the aux
/// type). The aux type carries the block's level params `0..num_level_params`.
pub(crate) fn replace_container_self_ref(
    expr: &Term,
    container: &Name,
    n_container_params: u32,
    container_args: &[Term],
    aux_name: &Name,
    num_level_params: u32,
    num_params: u32,
) -> Term {
    self_ref_at(
        expr,
        container,
        n_container_params,
        container_args,
        aux_name,
        num_level_params,
        num_params,
        0,
    )
}

#[allow(clippy::too_many_arguments)]
fn self_ref_at(
    expr: &Term,
    container: &Name,
    n_container_params: u32,
    container_args: &[Term],
    aux_name: &Name,
    num_level_params: u32,
    num_params: u32,
    below: u32,
) -> Term {
    let (head, args) = expr.unfold_apps();
    if let TermKind::Const(c) = head.kind() {
        if c.name() == container {
            let np = usize::try_from(n_container_params).unwrap_or(usize::MAX);
            // The container's parameter args at THIS site reference the canonical
            // parent params shifted up by `below`; lower them to the canonical
            // frame and compare to the (canonical) occurrence args.
            let params_match = args.len() >= np
                && container_args.len() >= np
                && args
                    .iter()
                    .take(np)
                    .zip(container_args.iter().take(np))
                    .all(|(site_arg, canon_arg)| {
                        lower_params(site_arg, below, num_params)
                            .is_some_and(|lowered| &lowered == canon_arg)
                    });
            if params_match {
                let mut result =
                    aux_applied_to_params(aux_name, num_level_params, num_params, below);
                // Append the container's NON-parameter (index) args, recursively
                // rewritten.
                for arg in args.iter().skip(np) {
                    let new_arg = self_ref_at(
                        arg,
                        container,
                        n_container_params,
                        container_args,
                        aux_name,
                        num_level_params,
                        num_params,
                        below,
                    );
                    result = Term::app(result, new_arg);
                }
                return result;
            }
        }
    }
    map_children_depth(expr, below, &|child, below| {
        self_ref_at(
            child,
            container,
            n_container_params,
            container_args,
            aux_name,
            num_level_params,
            num_params,
            below,
        )
    })
}

/// `Aux` (over the block's level params) applied to the parent's `num_params`
/// parameters as they appear `below` binders inside the parameter block:
/// `Aux p_0 p_1 .. p_{np-1}` where `p_0` is the outermost param. Returns the bare
/// `Aux` const when `num_params == 0` (the parameterless aux).
pub(crate) fn aux_applied_to_params(
    aux_name: &Name,
    num_level_params: u32,
    num_params: u32,
    below: u32,
) -> Term {
    let levels: Vec<Level> = (0..num_level_params).map(Level::param).collect();
    let aux_cref = ConstRef::mk_unchecked_levels(aux_name.clone(), levels);
    let mut result = Term::const_ref(aux_cref);
    // param p (0 = outermost) sits at BVar(below + (np-1-p)).
    for p in 0..num_params {
        let idx = below.saturating_add(num_params.saturating_sub(1).saturating_sub(p));
        result = Term::app(result, Term::bvar(idx));
    }
    result
}

/// Replace nested container occurrences in `expr` (an original constructor type)
/// with references to the matching auxiliary type.
pub(crate) fn replace_nested(
    env: &dyn Env,
    expr: &Term,
    self_name: &Name,
    occurrences: &[Occurrence],
    num_level_params: u32,
    num_params: u32,
) -> Term {
    replace_nested_at(
        env,
        expr,
        self_name,
        occurrences,
        num_level_params,
        num_params,
        0,
    )
}

#[allow(clippy::too_many_arguments)]
fn replace_nested_at(
    env: &dyn Env,
    expr: &Term,
    self_name: &Name,
    occurrences: &[Occurrence],
    num_level_params: u32,
    num_params: u32,
    depth: u32,
) -> Term {
    // The parent's parameters are the OUTERMOST binders of the constructor type;
    // having descended `depth` binders, they occupy enclosing de Bruijn indices
    // `(depth - np) .. depth`, so the canonical `below` offset is `depth - np`.
    // Occurrences only ever sit in field domains (`depth >= np`), so this never
    // underflows there; guard anyway (fail-closed: skip matching above the params).
    let below = depth.checked_sub(num_params);
    let (head, args) = expr.unfold_apps();
    if let (Some(below), TermKind::Const(c)) = (below, head.kind()) {
        let cname = c.name();
        if cname != self_name {
            if let Some(cont_np) = env.inductive_num_params(cname) {
                let mentions = args.iter().any(|a| term_mentions(a, self_name));
                if mentions {
                    // Canonicalize the site's container args (parameter refs
                    // lowered into the canonical frame) and match an occurrence.
                    let canon: Option<Vec<Term>> = args
                        .iter()
                        .map(|a| lower_params(a, below, num_params))
                        .collect();
                    if let Some(canon) = canon {
                        if let Some(occ) = occurrences
                            .iter()
                            .find(|o| o.container == *cname && o.args == canon)
                        {
                            let mut result = aux_applied_to_params(
                                &occ.aux_name,
                                num_level_params,
                                num_params,
                                below,
                            );
                            // Append the container's NON-parameter (index) args,
                            // recursively rewritten (kept at the current depth).
                            let npu = usize::try_from(cont_np).unwrap_or(usize::MAX);
                            for arg in args.iter().skip(npu) {
                                result = Term::app(
                                    result,
                                    replace_nested_at(
                                        env,
                                        arg,
                                        self_name,
                                        occurrences,
                                        num_level_params,
                                        num_params,
                                        depth,
                                    ),
                                );
                            }
                            return result;
                        }
                    }
                }
            }
        }
    }
    map_children_depth(expr, depth, &|child, depth| {
        replace_nested_at(
            env,
            child,
            self_name,
            occurrences,
            num_level_params,
            num_params,
            depth,
        )
    })
}

/// Apply `f` to each immediate child of `expr`, rebuilding the node and
/// threading the binder depth (incremented under each binder's body).
fn map_children_depth(expr: &Term, depth: u32, f: &dyn Fn(&Term, u32) -> Term) -> Term {
    let under = depth.saturating_add(1);
    match expr.kind() {
        TermKind::App(g, a) => Term::app(f(g, depth), f(a, depth)),
        TermKind::Pi(bi, d, c) => Term::pi(*bi, f(d, depth), f(c, under)),
        TermKind::Lam(bi, t, b) => Term::lam(*bi, f(t, depth), f(b, under)),
        TermKind::Let(t, v, b) => Term::let_(f(t, depth), f(v, depth), f(b, under)),
        TermKind::Proj(n, i, e) => Term::proj(n.clone(), *i, f(e, depth)),
        _ => expr.clone(),
    }
}

/// The last string component of a name (for building aux names); falls back to
/// the full display form for numeric tails.
pub(crate) fn last_component(name: &Name) -> String {
    name.last_str()
        .map(str::to_string)
        .unwrap_or_else(|| name.to_string())
}
