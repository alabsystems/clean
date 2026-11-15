// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! One motive per recursor slot (design §5.3 step 5 and §5.4).
//!
//! * An OWNED slot's motive is the tuple of its owners' types with the major
//!   premise abstracted (`fun t => Π rest, R`); one owner is the B1 case.
//! * A TRANSPARENT INTERMEDIATE is an unowned slot with exactly one
//!   constructor whose fields include family types — `String × T` in
//!   `List (String × T)`. Its motive is the tuple of the motives of the slots
//!   its fields live in, which is only meaningful when those motives are
//!   CONSTANT (they do not mention the value): the induction hypothesis of a
//!   pair `hd` then serves a call on `hd.2` whatever `hd` is. A dependent
//!   field motive leaves the slot `PUnit` with the reason recorded, and a
//!   call through it is refused with that reason.
//! * Every other slot gets `PUnit`.

use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Name};

use super::assemble::{Opened, Param};
use super::slots::FamilyInfo;
use super::tuple::TupleKind;
use super::{LiftError, PreDef};
use crate::infer::ElabCtx;

/// What one recursor slot carries.
#[derive(Debug, Clone)]
pub(super) enum SlotPlan {
    /// The members owning it, in source order.
    Owned { owners: Vec<usize> },
    /// A single-constructor structure carrying its fields' hypotheses:
    /// `(field index, field slot)` per induction-hypothesis binder.
    Intermediate {
        struct_name: Name,
        components: Vec<(usize, usize)>,
    },
    /// `PUnit`; `reason` is set when it is an intermediate the lift could
    /// not make transparent.
    Unit { reason: Option<String> },
}

/// The motives of one lowering and how each slot is laid out.
pub(super) struct Motives {
    pub(super) motives: Vec<Expr>,
    pub(super) plans: Vec<SlotPlan>,
    pub(super) kind: TupleKind,
}

/// Inputs shared by the motive and minor builders.
pub(super) struct Layout<'a> {
    pub(super) defs: &'a [&'a PreDef],
    pub(super) opened: &'a Opened,
    pub(super) majors: &'a [usize],
    pub(super) slots: &'a [usize],
    /// Each member's non-fixed, non-major parameters.
    pub(super) rest: &'a [Vec<Param>],
    /// Each member's `Π rest, R` with its major premise free.
    pub(super) body_tys: &'a [Expr],
}

impl Layout<'_> {
    pub(super) fn major(&self, member: usize) -> &Param {
        &self.opened.params[member][self.majors[member]]
    }
}

impl ElabCtx<'_> {
    /// Choose the tuple former for the block's motive universe and build
    /// every slot's motive.
    pub(super) fn build_motives(
        &mut self,
        layout: &Layout<'_>,
        fam: &FamilyInfo,
        level: &Level,
        punit: Option<&Expr>,
    ) -> Result<Motives, LiftError> {
        let (kind, tuples) = self.tuple_kind(level);
        let count = fam.slot_domains.len();
        let mut plans: Vec<Option<SlotPlan>> = vec![None; count];
        let mut motives: Vec<Option<Expr>> = vec![None; count];
        let unit_motive = |slot: usize| -> Result<Expr, LiftError> {
            let ty = punit.ok_or_else(|| {
                LiftError::block(
                    "an unused slot needs `PUnit`, which this environment lacks".to_string(),
                )
            })?;
            Ok(Expr::lam(
                BinderInfo::Default,
                fam.slot_domains[slot].clone(),
                ty.clone(),
            ))
        };
        for slot in 0..count {
            let owners: Vec<usize> = (0..layout.defs.len())
                .filter(|i| layout.slots[*i] == slot)
                .collect();
            if let Some(&first) = owners.first() {
                if owners.len() > 1 {
                    if let Err(why) = &tuples {
                        let names: Vec<String> = owners
                            .iter()
                            .map(|i| format!("`{}`", layout.defs[*i].name))
                            .collect();
                        return Err(LiftError::block(format!(
                            "{} share the recursor slot `{}`, but {why}",
                            names.join(" and "),
                            fam.slot_domains[slot]
                        )));
                    }
                }
                let t = self.fresh_fvar();
                let comps: Vec<Expr> = owners
                    .iter()
                    .map(|i| layout.body_tys[*i].subst_fvar(layout.major(*i).fvar, &Expr::fvar(t)))
                    .collect();
                motives[slot] = Some(Expr::lam(
                    BinderInfo::Default,
                    layout.major(first).ty.clone(),
                    kind.ty(&comps).abstract_fvar(t),
                ));
                plans[slot] = Some(SlotPlan::Owned { owners });
            } else if self.intermediate_shape(fam, slot).is_none() {
                motives[slot] = Some(unit_motive(slot)?);
                plans[slot] = Some(SlotPlan::Unit { reason: None });
            }
        }
        // Intermediates, innermost first: each needs its fields' motives.
        loop {
            let mut progressed = false;
            for slot in 0..count {
                if plans[slot].is_some() {
                    continue;
                }
                let Some((struct_name, components)) = self.intermediate_shape(fam, slot) else {
                    continue;
                };
                let field_motives: Option<Vec<Expr>> = components
                    .iter()
                    .map(|(_, s)| motives[*s].clone())
                    .collect();
                let Some(field_motives) = field_motives else {
                    continue;
                };
                progressed = true;
                let bodies: Option<Vec<Expr>> =
                    field_motives.iter().map(constant_motive_body).collect();
                let reason = match (&bodies, &tuples) {
                    (None, _) => Some(format!(
                        "the recursion goes through `{}`, and the motive of one of its fields \
                         depends on the value (a dependent motive through an intermediate \
                         type is not supported)",
                        fam.slot_domains[slot]
                    )),
                    (Some(b), Err(why)) if b.len() > 1 => Some(format!(
                        "the recursion goes through `{}`, but {why}",
                        fam.slot_domains[slot]
                    )),
                    _ => None,
                };
                match (reason, bodies) {
                    (None, Some(bodies)) => {
                        motives[slot] = Some(Expr::lam(
                            BinderInfo::Default,
                            fam.slot_domains[slot].clone(),
                            kind.ty(&bodies),
                        ));
                        plans[slot] = Some(SlotPlan::Intermediate {
                            struct_name,
                            components,
                        });
                    }
                    (reason, _) => {
                        motives[slot] = Some(unit_motive(slot)?);
                        plans[slot] = Some(SlotPlan::Unit { reason });
                    }
                }
            }
            if !progressed {
                break;
            }
        }
        let mut out_motives = Vec::with_capacity(count);
        let mut out_plans = Vec::with_capacity(count);
        for slot in 0..count {
            match (motives[slot].take(), plans[slot].take()) {
                (Some(motive), Some(plan)) => {
                    out_motives.push(motive);
                    out_plans.push(plan);
                }
                _ => {
                    out_motives.push(unit_motive(slot)?);
                    out_plans.push(SlotPlan::Unit {
                        reason: Some(format!(
                            "the recursion goes through `{}`, an intermediate type whose \
                             fields reach back into it",
                            fam.slot_domains[slot]
                        )),
                    });
                }
            }
        }
        Ok(Motives {
            motives: out_motives,
            plans: out_plans,
            kind,
        })
    }

    /// `And` for a `Prop` block, `PProd` otherwise; the second component is
    /// why tuples cannot be formed here, if they cannot.
    fn tuple_kind(&mut self, level: &Level) -> (TupleKind, Result<(), String>) {
        if self.is_def_eq(&Expr::sort(level.clone()), &Expr::prop()) {
            let ok = if self.env.get_inductive(&Name::from_string("And")).is_some() {
                Ok(())
            } else {
                Err("this environment lacks `And`".to_string())
            };
            return (TupleKind::And, ok);
        }
        let ok = if self
            .env
            .get_inductive(&Name::from_string("PProd"))
            .is_none()
        {
            Err("this environment lacks `PProd`".to_string())
        } else if self.is_def_eq(
            &Expr::sort(Level::max(Level::succ(Level::zero()), level.clone())),
            &Expr::sort(level.clone()),
        ) {
            Ok(())
        } else {
            Err(format!(
                "the members' results live in `Sort {level}`, which may be `Prop`, so they \
                 cannot be paired"
            ))
        };
        (TupleKind::PProd(level.clone()), ok)
    }

    /// An unowned slot whose single constructor is a structure with
    /// induction hypotheses on fields of OTHER slots: its structure name and
    /// `(field, slot)` per hypothesis.
    pub(super) fn intermediate_shape(
        &self,
        fam: &FamilyInfo,
        slot: usize,
    ) -> Option<(Name, Vec<(usize, usize)>)> {
        let mut minors = fam.minors.iter().filter(|m| m.slot == slot);
        let shape = minors.next()?;
        if minors.next().is_some()
            || shape.ihs.is_empty()
            || shape.ihs.iter().any(|(_, s)| *s == slot)
        {
            return None;
        }
        let ExprKind::Const(ctor_name, _) = shape.ctor_head.get_app_fn().kind() else {
            return None;
        };
        let ctor = self.env.get_constructor(ctor_name)?;
        let ind = self.env.get_inductive(&ctor.inductive_name)?;
        if ind.num_indices != 0 || ind.constructor_names.len() != 1 {
            return None;
        }
        Some((ctor.inductive_name.clone(), shape.ihs.clone()))
    }
}

/// The body of `fun t => B` when `B` does not mention `t`.
fn constant_motive_body(motive: &Expr) -> Option<Expr> {
    match motive.kind() {
        ExprKind::Lam(_, _, body) if !body.has_loose_bvar(0) => {
            Some(body.instantiate(&Expr::prop()))
        }
        _ => None,
    }
}
