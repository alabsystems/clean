// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The search for one lowering of a recursive component (design §5.3 steps
//! 2–4): the fixed prefix, the recursor families its parameters belong to,
//! and the combinations of major premises, each assembled and kernel-checked
//! until one succeeds.

use clean_kernel::{Expr, ExprKind, FVarId, Name};

use super::{
    assemble, scc, specialize, trace_on, LiftError, LiftedMember, PreDef, MAX_MAJOR_COMBINATIONS,
};
use crate::infer::ElabCtx;
use crate::ElabError;

impl ElabCtx<'_> {
    pub(super) fn lift_recursive_scc(
        &mut self,
        members: &[&PreDef],
        all_forward: &[FVarId],
    ) -> Result<Vec<LiftedMember>, ElabError> {
        let depth = self.locals.len();
        let result = self.lift_scc_inner(members, all_forward);
        let result = result.map_err(|err| self.render_lift_error(members, err));
        self.locals.truncate(depth);
        result
    }

    fn lift_scc_inner(
        &mut self,
        members: &[&PreDef],
        all_forward: &[FVarId],
    ) -> Result<Vec<LiftedMember>, LiftError> {
        let first = members[0];
        if members.iter().any(|m| m.is_theorem != first.is_theorem) {
            return Err(LiftError::block(
                "it mixes theorems and definitions".to_string(),
            ));
        }
        let forward: Vec<FVarId> = members.iter().map(|m| m.fvar).collect();
        for member in members {
            if !scc::mentioned_members(&forward, &[&member.ty]).is_empty() {
                return Err(LiftError::member(
                    &member.name,
                    "its type mentions a member of its own recursive block".to_string(),
                ));
            }
        }
        let fixed = self.fixed_prefix(members);
        let opened = self.open_members(members, fixed);
        // Parameter order per member: the ones its outermost case split
        // examines first (Lean's structural search tries the parameters the
        // source matches on), then the rest; the fixed prefix never recurses.
        let orders: Vec<Vec<usize>> = (0..members.len())
            .map(|i| {
                if let Some(major) = members[i].structural_major {
                    return if major >= fixed && major < opened.params[i].len() {
                        vec![major]
                    } else {
                        Vec::new()
                    };
                }
                let mut order: Vec<usize> =
                    top_match_params(self.env, &opened.bodies[i], &opened.params[i])
                        .into_iter()
                        .filter(|p| *p >= fixed)
                        .collect();
                let rest: Vec<usize> = (fixed..opened.params[i].len())
                    .filter(|p| !order.contains(p))
                    .collect();
                order.extend(rest);
                order
            })
            .collect();
        // Families in the same preference: a member's preferred parameter's
        // family is tried before a family it reaches only by a later one.
        let mut families = Vec::new();
        for rank in 0..orders.iter().map(Vec::len).max().unwrap_or(0) {
            for (i, order) in orders.iter().enumerate() {
                let Some(pos) = order.get(rank) else {
                    continue;
                };
                for key in self.family_candidates(&opened.params[i][*pos].ty) {
                    if !families.contains(&key) {
                        families.push(key);
                    }
                }
            }
        }
        let mut first_error: Option<LiftError> = None;
        for key in families {
            let fam = match self.family_info(&key) {
                Ok(fam) => fam,
                Err(err) => {
                    first_error.get_or_insert(LiftError::block(format!("{err}")));
                    continue;
                }
            };
            // Per member: (parameter, slot) candidates, preferred first.
            let mut candidates: Vec<Vec<(usize, usize)>> = Vec::with_capacity(members.len());
            for (i, member) in members.iter().enumerate() {
                let mut list = Vec::new();
                for &pos in &orders[i] {
                    let ty = &opened.params[i][pos].ty;
                    if let Some(slot) = fam
                        .slot_domains
                        .iter()
                        .position(|dom| dom == ty || self.is_def_eq(dom, ty))
                    {
                        list.push((pos, slot));
                    }
                }
                if list.is_empty() {
                    first_error.get_or_insert(LiftError::member(
                        &member.name,
                        format!(
                            "none of its parameters has a type `{}` recurses through",
                            fam.key.name
                        ),
                    ));
                }
                candidates.push(list);
            }
            if candidates.iter().any(Vec::is_empty) {
                continue;
            }
            let mut odometer = vec![0usize; members.len()];
            for _ in 0..MAX_MAJOR_COMBINATIONS {
                let choice: Vec<(usize, usize)> = odometer
                    .iter()
                    .enumerate()
                    .map(|(i, c)| candidates[i][*c])
                    .collect();
                let majors: Vec<usize> = choice.iter().map(|c| c.0).collect();
                let slots: Vec<usize> = choice.iter().map(|c| c.1).collect();
                let attempt = self
                    .assemble(members, &opened, &fam, &majors, &slots)
                    .and_then(|assembled| {
                        let owners = assembled.owners;
                        self.precheck(members, &forward, all_forward, assembled.values)
                            .map(|values| (values, owners))
                    });
                match attempt {
                    Ok((values, owners)) => {
                        let rec =
                            |i: usize| fam.rec_by_slot[slots[i]].clone().unwrap_or_else(Name::anon);
                        let mut equations: Vec<Vec<Expr>> = (0..members.len())
                            .map(|i| self.constructor_equations(members[i], &opened, i, majors[i]))
                            .collect();
                        return Ok(values
                            .into_iter()
                            .enumerate()
                            .map(|(i, value)| LiftedMember {
                                equations: std::mem::take(&mut equations[i]),
                                value,
                                recursor: rec(i),
                                slot: slots[i],
                                major: majors[i],
                                rest: (fixed..opened.params[i].len())
                                    .filter(|p| *p != majors[i])
                                    .collect(),
                                fixed,
                                owner_index: owners[i].0,
                                owner_count: owners[i].1,
                            })
                            .collect());
                    }
                    Err(err) => {
                        if trace_on() {
                            eprintln!("mutual-lift: majors {majors:?} refused: {err:?}");
                        }
                        first_error.get_or_insert(err);
                    }
                }
                if !advance(&mut odometer, &candidates) {
                    break;
                }
            }
        }
        Err(first_error.unwrap_or_else(|| {
            LiftError::block(
                "no parameter of any member has an inductive type the block could recurse on"
                    .to_string(),
            )
        }))
    }

    /// Every lifted value is closed (up to forward locals of OTHER components,
    /// which become constants registered before it) and has its member's type.
    fn precheck(
        &mut self,
        members: &[&PreDef],
        forward: &[FVarId],
        all_forward: &[FVarId],
        values: Vec<Expr>,
    ) -> Result<Vec<Expr>, LiftError> {
        for (member, value) in members.iter().zip(&values) {
            let free = scc::free_fvars(value);
            if free.iter().any(|id| forward.contains(id)) {
                return Err(LiftError::member(
                    &member.name,
                    "a call to a member survived the lowering".to_string(),
                ));
            }
            if free.iter().any(|id| !all_forward.contains(id)) {
                return Err(LiftError::member(
                    &member.name,
                    "the lowered value is not closed".to_string(),
                ));
            }
            let inferred = self.infer_type_full(value).map_err(|e| {
                LiftError::member(
                    &member.name,
                    format!("the lowered value does not type-check: {e}"),
                )
            })?;
            if !self.is_def_eq(&inferred, &member.ty) {
                return Err(LiftError::member(
                    &member.name,
                    format!("the lowered value has type `{inferred}`, not its declared type"),
                ));
            }
        }
        Ok(values)
    }
}

/// The parameters the body's outermost case split examines, in order: the
/// major premise of a recursor/`casesOn` at the head (through `let`s), or the
/// components of a tuple scrutinee there.
fn top_match_params(
    env: &clean_kernel::Environment,
    body: &Expr,
    params: &[assemble::Param],
) -> Vec<usize> {
    let position = |e: &Expr| match specialize::strip_mdata(e).kind() {
        ExprKind::FVar(id) => params.iter().position(|p| p.fvar == *id),
        _ => None,
    };
    let mut cur = specialize::strip_mdata(body);
    while let ExprKind::Let(_, _, _, inner, _) = cur.kind() {
        cur = specialize::strip_mdata(inner);
    }
    let ExprKind::Const(name, _) = cur.get_app_fn().kind() else {
        return Vec::new();
    };
    let Some(rec) = env.get_recursor(name) else {
        return Vec::new();
    };
    let major_idx = match rec.arg_order {
        clean_kernel::RecursorArgOrder::MajorAfterMinors => {
            rec.num_params + rec.num_motives + rec.num_minors + rec.num_indices
        }
        clean_kernel::RecursorArgOrder::MajorAfterMotive => {
            rec.num_params + rec.num_motives + rec.num_indices
        }
    } as usize;
    let args = cur.get_app_args();
    let Some(major) = args.get(major_idx) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    if let Some(pos) = position(major) {
        out.push(pos);
    }
    for inner in specialize::strip_mdata(major).get_app_args() {
        if let Some(pos) = position(inner) {
            if !out.contains(&pos) {
                out.push(pos);
            }
        }
    }
    out
}

/// Next index vector in lexicographic order; `false` when exhausted.
fn advance(odometer: &mut [usize], candidates: &[Vec<(usize, usize)>]) -> bool {
    for i in (0..odometer.len()).rev() {
        if odometer[i] + 1 < candidates[i].len() {
            odometer[i] += 1;
            for later in odometer.iter_mut().skip(i + 1) {
                *later = 0;
            }
            return true;
        }
    }
    false
}
