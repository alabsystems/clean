// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A candidate's binder metavariables, determined through the TYPES of the
//! ones unification assigned — the half of Lean's `checkTypesAndAssign`
//! (`Lean/Meta/ExprDefEq.lean`: every `?m := v` first unifies `inferType ?m`
//! with `inferType v`) that instance search needs.
//!
//! # The measured gap
//!
//! Clean's unifier assigns a metavariable without unifying its type with the
//! value's. Usually the goal pins every binder directly, but an instance-goal
//! argument that `elab_app` has normalised at instance transparency no longer
//! mentions the implicit TYPE argument of a projection:
//! `needsDec (a < b)` under `[MyLO α]` asks for
//! `Decidable (inst.toLT.1 a b)`, where `@LT.lt α (@MyLO.toLT α inst) a b`
//! used to carry `α`. The candidate `MyLO.decLT : {α} → [self : MyLO α] →
//! MyDecLT α` (Mathlib's `LinearOrder.toDecidableLT` shape) then unifies
//! `?self := inst` through the projection and leaves `?α` open, and the
//! hygiene check rejected it as undetermined — `min_def_lt`, `max_def_lt`,
//! `LinearOrder.lift` on `Mathlib/Order/Basic.lean`. In Lean the assignment
//! `?self := inst` unifies `MyLO ?α =?= MyLO α` first, which fixes `?α`.
//!
//! # Why it cannot admit a wrong candidate
//!
//! It only ever ADDS the unifications Lean performs before an assignment is
//! accepted; each is scoped and rolled back when it fails; the hygiene check
//! that follows still refuses any binder left undetermined; and the emitted
//! term is re-checked by the kernel.

use super::super::ElabCtx;
use crate::unify::MetaState;
use clean_kernel::{Expr, ExprKind, FVarId};
use std::collections::HashSet;

impl<'a> ElabCtx<'a> {
    /// For each ASSIGNED binder metavariable of a candidate whose declared
    /// type still mentions an UNASSIGNED binder metavariable of the same
    /// candidate, unify the declared type with the type of the assigned
    /// value (Lean's `checkTypesAndAssign`). A no-op when every binder is
    /// already determined, which is the common case.
    pub(super) fn determine_binders_from_assignment_types(&mut self, binder_metas: &[Expr]) {
        let meta_id_of = |e: &Expr| match e.kind() {
            ExprKind::FVar(fv) => MetaState::from_fvar(*fv).map(|id| (*fv, id)),
            _ => None,
        };
        let open: HashSet<FVarId> = binder_metas
            .iter()
            .filter_map(|m| {
                let solved = self.metas.instantiate(m);
                meta_id_of(&solved)
                    .filter(|(_, id)| !self.metas.is_assigned(*id))
                    .map(|(fv, _)| fv)
            })
            .collect();
        if open.is_empty() {
            return;
        }
        for meta_arg in binder_metas {
            let Some((_, id)) = meta_id_of(meta_arg) else {
                continue;
            };
            if !self.metas.is_assigned(id) {
                continue;
            }
            let Some(declared) = self.metas.get(id).map(|mv| mv.ty.clone()) else {
                continue;
            };
            let declared = self.metas.instantiate(&declared);
            if !self
                .collect_meta_fvars(&declared)
                .iter()
                .any(|fv| open.contains(fv))
            {
                continue;
            }
            let value = self.metas.instantiate(meta_arg);
            let Ok(value_ty) = self.infer_type(&value) else {
                continue;
            };
            self.metas.push_scope();
            if self.try_unify(&declared, &value_ty) {
                self.metas.commit();
            } else {
                self.metas.pop_scope();
            }
        }
    }
}
