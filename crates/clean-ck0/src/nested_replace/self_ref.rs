// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The auxiliary's self-reference rewrite (design §5.2): the container's
//! self-references in its constructors, once the occurrence's arguments are
//! substituted for its parameters, become the auxiliary.

use std::sync::Arc;

use super::rewrite::Rewrite;
use super::walk::{same_term, Mentions, Spine};
use super::{aux_applied_to_params, lower_params_charged, map_children_depth, Charge};
use crate::level::Level;
use crate::name::Name;
use crate::nested::NestedError;
use crate::term::{Term, TermKind};

/// Replace `Container <params matching container_args> <indices>` with
/// `Aux <indices>` throughout `expr` (used when building an auxiliary type's own
/// constructors, where the container's self-references must point at the aux
/// type). The aux type carries the block's level params (`aux_levels`).
///
/// Only what mentions the container is rewritten (R176), and a spine headed
/// by it is compared once, on its first `n_container_params` arguments,
/// which each of its applications with as many arguments shares: one that
/// does not match is not compared again at its shorter applications.
#[allow(clippy::too_many_arguments)]
pub(crate) fn replace_container_self_ref(
    expr: &Term,
    container: &Name,
    n_container_params: u32,
    container_args: &[Term],
    aux_name: &Name,
    aux_levels: &Arc<[Level]>,
    num_params: u32,
    charge: &mut Charge<'_>,
) -> Result<Term, NestedError> {
    let np = usize::try_from(n_container_params).unwrap_or(usize::MAX);
    let pass = SelfRef {
        marks: Mentions::of(expr, container),
        container,
        params: container_args.get(..np),
        aux_name,
        aux_levels,
        num_params,
    };
    pass.rewrite(expr, 0, charge)
}

/// The self-reference rewrite of one auxiliary constructor type. It is in
/// the canonical frame, so a node's binder depth is its `below`.
struct SelfRef<'a> {
    marks: Mentions<'a>,
    container: &'a Name,
    /// The occurrence's arguments in the container's parameter places, or
    /// `None` when it has fewer, and then nothing matches.
    params: Option<&'a [Term]>,
    aux_name: &'a Name,
    aux_levels: &'a Arc<[Level]>,
    num_params: u32,
}

impl Rewrite for SelfRef<'_> {
    fn marks(&self) -> &Mentions<'_> {
        &self.marks
    }

    fn rewrite(&self, t: &Term, below: u32, charge: &mut Charge<'_>) -> Result<Term, NestedError> {
        #[cfg(test)]
        crate::term::walk_step();
        if !self.marks.contains(t) {
            return Ok(t.clone());
        }
        match t.kind() {
            // A bare constant is a spine of no arguments: with no
            // parameters, the container itself is a self-reference.
            TermKind::App(..) | TermKind::Const(_) => {
                let spine = Spine::of(t);
                let matched = self.match_spine(&spine, below, charge)?;
                self.rebuild(&spine, matched, below, charge)
            }
            _ => map_children_depth(t, below, &mut |child, below| {
                self.rewrite(child, below, charge)
            }),
        }
    }
}

impl SelfRef<'_> {
    /// `spine` as the auxiliary applied to its rewritten index arguments,
    /// with its argument count, when it is the container applied to the
    /// occurrence's parameter arguments.
    fn match_spine(
        &self,
        spine: &Spine<'_>,
        below: u32,
        charge: &mut Charge<'_>,
    ) -> Result<Option<(Term, usize)>, NestedError> {
        let TermKind::Const(c) = spine.head.kind() else {
            return Ok(None);
        };
        if c.name() != self.container {
            return Ok(None);
        }
        let Some(params) = self.params else {
            return Ok(None);
        };
        let Some(site) = spine.args.get(..params.len()) else {
            return Ok(None);
        };
        // The container's parameter arguments here reference the canonical
        // parameters shifted up by `below`: lower each in turn and compare it
        // with the occurrence's, stopping at the first that differs, as R174
        // did.
        for (site_arg, param) in site.iter().zip(params) {
            let Some(lowered) = lower_params_charged(site_arg, below, self.num_params, charge)?
            else {
                return Ok(None);
            };
            if !same_term(&lowered, param, charge)? {
                return Ok(None);
            }
        }
        let mut result =
            aux_applied_to_params(self.aux_name, self.aux_levels, self.num_params, below);
        // Append the container's NON-parameter (index) args, rewritten.
        for arg in spine.args.get(params.len()..).unwrap_or_default() {
            result = Term::app(result, self.rewrite(arg, below, charge)?);
        }
        Ok(Some((result, spine.args.len())))
    }
}
