// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expression-replacement helpers for the nested→mutual auxiliary construction
//! (design §5.2, milestone M3). Extracted from [`crate::nested`] to keep both
//! files under the 500-line convention. Mirrors the Lean-faithful reference
//! `crates/clean-kernel/src/env/inductive_nested_replace.rs`.
//!
//! Each rewrite looks at a node of its term a bounded number of times
//! (R176). A first walk marks the nodes that mention the constant a site
//! needs: the parent in phase 3, the container in a self-reference rewrite.
//! A node that does not mention it holds no site that could match (every
//! occurrence has an argument that mentions the parent, and lowering adds no
//! constant), so its rewrite is the node itself, returned as it is. An
//! application spine is taken apart once, its applications are tried longest
//! first, and each of its arguments is lowered at most once. Matching is
//! charged what it does, before it does it: one node for each node lowering
//! builds, and one for each pair of nodes a comparison looks at.

use std::sync::Arc;

use crate::level::Level;
use crate::name::Name;
use crate::nested::{NestedError, Occurrence};
use crate::term::{ConstRef, Term, TermKind};
use crate::validate::Env;

mod index;
mod rewrite;
mod self_ref;
mod walk;

pub(crate) use index::{args_key, OccIndex};
use rewrite::{Lowered, Rewrite};
pub(crate) use self_ref::replace_container_self_ref;
#[cfg(test)]
pub(crate) use walk::narrow_hashes;
use walk::{Mentions, Spine};

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

/// What matching a site pays (R176): called, before the work, with the nodes
/// lowering is about to build or the pairs of nodes a comparison is about to
/// look at (one at a time), it charges them to the nested inductive's budget,
/// or refuses.
pub(crate) type Charge<'a> = dyn FnMut(u64) -> Result<(), NestedError> + 'a;

/// Lower a term that sits `below` binders inside the parent-parameter block into
/// the canonical `num_params`-parameter context (`below = 0`). Loose vars that
/// reference a parent parameter are remapped; a loose var that references a
/// non-parameter local (a field/index binder) makes the occurrence non-uniform,
/// and lowering returns `None` (a fail-closed reject). Vars bound *inside* `t`
/// are preserved. Uncharged: phase 1 runs before the budget exists.
pub(crate) fn lower_params(t: &Term, below: u32, num_params: u32) -> Option<Term> {
    let mut free = |_: u64| Ok::<(), NestedError>(());
    // The free charge never refuses, so `ok()` drops nothing.
    lower_params_at(t, below, num_params, 0, &mut free)
        .ok()
        .flatten()
}

/// [`lower_params`], charging each node it builds before it builds it
/// (R176): on success the charge is exactly the nodes built; on failure it is
/// the nodes looked at past the closed-subterm shortcut up to the variable
/// that fails, which is at least the nodes built.
pub(crate) fn lower_params_charged(
    t: &Term,
    below: u32,
    num_params: u32,
    charge: &mut Charge<'_>,
) -> Result<Option<Term>, NestedError> {
    lower_params_at(t, below, num_params, 0, charge)
}

fn lower_params_at(
    t: &Term,
    below: u32,
    num_params: u32,
    local: u32,
    charge: &mut Charge<'_>,
) -> Result<Option<Term>, NestedError> {
    #[cfg(test)]
    crate::term::walk_step();
    if t.loose <= local {
        // No variable of `t` reaches past its own binders, so lowering is the
        // identity: return the subterm itself rather than a copy (R174).
        return Ok(Some(t.clone()));
    }
    if let TermKind::Sort(_) | TermKind::Const(_) | TermKind::Elim(_) | TermKind::Lit(_) = t.kind()
    {
        // Closed, so the shortcut above returned it: kept for totality, and
        // it builds nothing.
        return Ok(Some(t.clone()));
    }
    // Every other node is rebuilt here, or is the variable that fails: one
    // node, charged before it is built (R176).
    charge(1)?;
    let lowered = match t.kind() {
        TermKind::BVar(i) => lower_var(*i, below, num_params, local),
        TermKind::App(f, a) => {
            let Some(f) = lower_params_at(f, below, num_params, local, charge)? else {
                return Ok(None);
            };
            let Some(a) = lower_params_at(a, below, num_params, local, charge)? else {
                return Ok(None);
            };
            Some(Term::app(f, a))
        }
        TermKind::Lam(bi, ty, body) => {
            let Some(ty) = lower_params_at(ty, below, num_params, local, charge)? else {
                return Ok(None);
            };
            let Some(under) = local.checked_add(1) else {
                return Ok(None);
            };
            let Some(body) = lower_params_at(body, below, num_params, under, charge)? else {
                return Ok(None);
            };
            Some(Term::lam(*bi, ty, body))
        }
        TermKind::Pi(bi, ty, body) => {
            let Some(ty) = lower_params_at(ty, below, num_params, local, charge)? else {
                return Ok(None);
            };
            let Some(under) = local.checked_add(1) else {
                return Ok(None);
            };
            let Some(body) = lower_params_at(body, below, num_params, under, charge)? else {
                return Ok(None);
            };
            Some(Term::pi(*bi, ty, body))
        }
        TermKind::Let(ty, val, body) => {
            let Some(ty) = lower_params_at(ty, below, num_params, local, charge)? else {
                return Ok(None);
            };
            let Some(val) = lower_params_at(val, below, num_params, local, charge)? else {
                return Ok(None);
            };
            let Some(under) = local.checked_add(1) else {
                return Ok(None);
            };
            let Some(body) = lower_params_at(body, below, num_params, under, charge)? else {
                return Ok(None);
            };
            Some(Term::let_(ty, val, body))
        }
        TermKind::Proj(name, idx, e) => {
            let Some(e) = lower_params_at(e, below, num_params, local, charge)? else {
                return Ok(None);
            };
            Some(Term::proj(name.clone(), *idx, e))
        }
        TermKind::Sort(_) | TermKind::Const(_) | TermKind::Elim(_) | TermKind::Lit(_) => {
            Some(t.clone())
        }
    };
    Ok(lowered)
}

/// `BVar(i)`, `local` binders inside the term being lowered, in the canonical
/// frame; `None` when it names a field or index binder, or escapes the
/// parameter block.
fn lower_var(i: u32, below: u32, num_params: u32, local: u32) -> Option<Term> {
    if i < local {
        // Bound inside the term itself — unchanged.
        return Some(Term::bvar(i));
    }
    // Loose relative to the term: its index into the enclosing context is
    // `i - local`. The parent params occupy enclosing indices
    // `below .. below+num_params`.
    let enclosing = i.checked_sub(local)?;
    let param_hi = below.checked_add(num_params)?;
    if enclosing < below {
        // A field/index local leaked into a nesting argument: non-uniform.
        return None;
    }
    if enclosing >= param_hi {
        // Escapes the parameter block — impossible for a closed ctor type;
        // reject fail-closed.
        return None;
    }
    // A parameter: drop the `below` field/index binders between it and the
    // canonical context, keeping the local binders.
    Some(Term::bvar(i.checked_sub(below)?))
}

/// `Aux` (over the block's level params) applied to the parent's `num_params`
/// parameters as they appear `below` binders inside the parameter block:
/// `Aux p_0 p_1 .. p_{np-1}` where `p_0` is the outermost param. Returns the bare
/// `Aux` const when `num_params == 0` (the parameterless aux).
///
/// `aux_levels` is the block's level-param vector `Param 0 .. Param (nlp-1)`,
/// built once (and bounded) by `nested::add_inductive_nested` and shared here.
pub(crate) fn aux_applied_to_params(
    aux_name: &Name,
    aux_levels: &Arc<[Level]>,
    num_params: u32,
    below: u32,
) -> Term {
    let aux_cref = ConstRef::mk_unchecked_shared_levels(aux_name.clone(), Arc::clone(aux_levels));
    let mut result = Term::const_ref(aux_cref);
    // param p (0 = outermost) sits at BVar(below + (np-1-p)).
    for p in 0..num_params {
        let idx = below.saturating_add(num_params.saturating_sub(1).saturating_sub(p));
        result = Term::app(result, Term::bvar(idx));
    }
    result
}

/// Replace nested container occurrences in `expr` (an original constructor
/// type) with references to the matching auxiliary type; `index` is
/// `occurrences`' [`OccIndex`], in their order. A site is tried only where an
/// argument mentions the parent and an occurrence is of its container with as
/// many arguments (R174). A node that does not mention the parent is returned
/// as it is (R176).
#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn replace_nested(
    env: &dyn Env,
    expr: &Term,
    self_name: &Name,
    occurrences: &[Occurrence],
    index: &OccIndex,
    aux_levels: &Arc<[Level]>,
    num_params: u32,
    charge: &mut Charge<'_>,
) -> Result<Term, NestedError> {
    replace_nested_block(
        env,
        expr,
        std::slice::from_ref(self_name),
        occurrences,
        index,
        aux_levels,
        num_params,
        charge,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn replace_nested_block(
    env: &dyn Env,
    expr: &Term,
    self_names: &[Name],
    occurrences: &[Occurrence],
    index: &OccIndex,
    aux_levels: &Arc<[Level]>,
    num_params: u32,
    charge: &mut Charge<'_>,
) -> Result<Term, NestedError> {
    let pass = Nesting {
        env,
        marks: Mentions::of_many(expr, self_names),
        self_names: self_names.iter().cloned().collect(),
        occurrences,
        index,
        aux_levels,
        num_params,
    };
    pass.rewrite(expr, 0, charge)
}

/// Phase 3's rewrite of one parent constructor type.
struct Nesting<'a> {
    env: &'a dyn Env,
    marks: Mentions<'a>,
    self_names: std::collections::HashSet<Name>,
    occurrences: &'a [Occurrence],
    index: &'a OccIndex,
    aux_levels: &'a Arc<[Level]>,
    num_params: u32,
}

impl Rewrite for Nesting<'_> {
    fn marks(&self) -> &Mentions<'_> {
        &self.marks
    }

    fn rewrite(&self, t: &Term, depth: u32, charge: &mut Charge<'_>) -> Result<Term, NestedError> {
        #[cfg(test)]
        crate::term::walk_step();
        if !self.marks.contains(t) {
            return Ok(t.clone());
        }
        match t.kind() {
            TermKind::App(..) | TermKind::Const(_) => {
                let spine = Spine::of(t);
                let matched = self.match_spine(&spine, depth, charge)?;
                self.rebuild(&spine, matched, depth, charge)
            }
            _ => map_children_depth(t, depth, &mut |child, depth| {
                self.rewrite(child, depth, charge)
            }),
        }
    }
}

impl Nesting<'_> {
    /// The rewrite of the longest application of `spine` that matches an
    /// occurrence, with its argument count: R174's rewrite tried them from
    /// the top of the spine down.
    fn match_spine(
        &self,
        spine: &Spine<'_>,
        depth: u32,
        charge: &mut Charge<'_>,
    ) -> Result<Option<(Term, usize)>, NestedError> {
        // The parent's parameters are the OUTERMOST binders of the
        // constructor type, so `depth - num_params` binders sit between the
        // spine and them; above them nothing matches (fail-closed).
        let Some(below) = depth.checked_sub(self.num_params) else {
            return Ok(None);
        };
        let TermKind::Const(c) = spine.head.kind() else {
            return Ok(None);
        };
        let container = c.name();
        if self.self_names.contains(container) {
            return Ok(None);
        }
        let Some(cont_np) = self.env.inductive_num_params(container) else {
            return Ok(None);
        };
        // An application mentions the parent exactly when it has more
        // arguments than the spine's longest application that does not (the
        // head is a container, not the parent): R174's mention test.
        let low = spine
            .apps
            .iter()
            .rposition(|app| !self.marks.contains(app))
            .map_or(0, |i| i.saturating_add(1));
        let arities = self.index.arities(container);
        let longest = arities.partition_point(|&n| n > spine.args.len());
        let tried = arities.get(longest..).unwrap_or_default();
        let mut lowered = Lowered::new(below, self.num_params);
        for &n in tried.iter().take_while(|&&n| n > low) {
            if !lowered.reach(&spine.args, n, charge)? {
                continue;
            }
            let Some((canon, key)) = lowered.prefix(n) else {
                continue;
            };
            let found = self
                .index
                .find(self.occurrences, container, canon, key, charge)?;
            let Some(occ) = found else {
                continue;
            };
            let mut result =
                aux_applied_to_params(&occ.aux_name, self.aux_levels, self.num_params, below);
            // Append the container's NON-parameter (index) args, rewritten
            // (kept at the current depth).
            let npu = usize::try_from(cont_np).unwrap_or(usize::MAX);
            let site = spine.args.get(..n).unwrap_or_default();
            for arg in site.iter().skip(npu) {
                result = Term::app(result, self.rewrite(arg, depth, charge)?);
            }
            return Ok(Some((result, n)));
        }
        Ok(None)
    }
}

/// Apply `f` to each immediate child of `expr`, rebuilding the node and
/// threading the binder depth (incremented under each binder's body); the
/// first refusal stops it.
fn map_children_depth(
    expr: &Term,
    depth: u32,
    f: &mut dyn FnMut(&Term, u32) -> Result<Term, NestedError>,
) -> Result<Term, NestedError> {
    let under = depth.saturating_add(1);
    Ok(match expr.kind() {
        TermKind::App(g, a) => Term::app(f(g, depth)?, f(a, depth)?),
        TermKind::Pi(bi, d, c) => Term::pi(*bi, f(d, depth)?, f(c, under)?),
        TermKind::Lam(bi, t, b) => Term::lam(*bi, f(t, depth)?, f(b, under)?),
        TermKind::Let(t, v, b) => Term::let_(f(t, depth)?, f(v, depth)?, f(b, under)?),
        TermKind::Proj(n, i, e) => Term::proj(n.clone(), *i, f(e, depth)?),
        _ => expr.clone(),
    })
}

/// The last string component of a name (for building aux names); falls back to
/// the full display form for numeric tails.
pub(crate) fn last_component(name: &Name) -> String {
    name.last_str()
        .map(str::to_string)
        .unwrap_or_else(|| name.to_string())
}

#[cfg(test)]
mod cost_tests;
#[cfg(test)]
mod equivalence_tests;
#[cfg(test)]
mod tests;
