// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The recursor family a lifted block eliminates (design §5.3 steps 3–4).
//!
//! A family is an inductive `T` whose `T.rec` the kernel generated — for a
//! nested `T` one motive per member of the nested block, auxiliary containers
//! (`List T`, `String × T`) included, with `T.rec_N` eliminating the N-th
//! auxiliary. Every recursor of the family shares the motives and the minors;
//! they differ only in which slot's major premise they take. This module reads
//! all of that off the recursor TYPES (the authoritative source after restore,
//! see `motive_domains_from_rec_type`), never from names it reconstructs.

use clean_kernel::{Expr, ExprKind, FVarId, Level, Name};

use super::super::ElabCtx;
use crate::ElabError;

/// One family instance: `T.{levels} indparams`.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct FamilyKey {
    pub(super) name: Name,
    pub(super) levels: Vec<Level>,
    pub(super) indparams: Vec<Expr>,
}

/// The shape of one minor premise of the family recursor.
#[derive(Debug, Clone)]
pub(super) struct MinorShape {
    /// The slot whose constructor this minor handles.
    pub(super) slot: usize,
    /// The constructor applied to its parameters (fields are appended).
    pub(super) ctor_head: Expr,
    pub(super) num_fields: usize,
    /// For each induction-hypothesis binder, in order: (field index, slot).
    pub(super) ihs: Vec<(usize, usize)>,
}

#[derive(Debug, Clone)]
pub(super) struct FamilyInfo {
    pub(super) key: FamilyKey,
    /// Applied domain of every motive, in motive order.
    pub(super) slot_domains: Vec<Expr>,
    /// The recursor eliminating each slot (`None` if the kernel made none).
    pub(super) rec_by_slot: Vec<Option<Name>>,
    pub(super) minors: Vec<MinorShape>,
    /// Whether the recursors take a motive-universe parameter first.
    pub(super) has_motive_level: bool,
}

/// Open the leading `Π` binders of `ty` with the given values.
fn peel(mut ty: Expr, vals: &[Expr]) -> Option<Expr> {
    for val in vals {
        let ExprKind::Pi(_, _, body) = ty.kind() else {
            return None;
        };
        ty = body.instantiate(val);
    }
    Some(ty)
}

impl ElabCtx<'_> {
    /// Family instances a parameter type can belong to: its own head and the
    /// heads of its arguments (`List T` names `T`), when that head is an
    /// inductive with a kernel recursor and no indices.
    pub(super) fn family_candidates(&self, ty: &Expr) -> Vec<FamilyKey> {
        let mut out = Vec::new();
        let ty = self.whnf(ty);
        let mut consider = vec![ty.clone()];
        consider.extend(ty.get_app_args().into_iter().cloned());
        for candidate in consider {
            let ExprKind::Const(name, levels) = candidate.get_app_fn().kind() else {
                continue;
            };
            let Some(ind) = self.env.get_inductive(name) else {
                continue;
            };
            if ind.num_indices != 0 || self.env.get_recursor(&name.clone().str("rec")).is_none() {
                continue;
            }
            let args: Vec<Expr> = candidate.get_app_args().into_iter().cloned().collect();
            if args.len() != ind.num_params as usize {
                continue;
            }
            let key = FamilyKey {
                name: name.clone(),
                levels: levels.to_vec(),
                indparams: args,
            };
            if !out.contains(&key) {
                out.push(key);
            }
        }
        out
    }

    /// Read the family's slots, per-slot recursors and minor shapes.
    pub(super) fn family_info(&mut self, key: &FamilyKey) -> Result<FamilyInfo, ElabError> {
        let unsupported = |why: String| ElabError::Unsupported {
            feature: format!("mutual structural recursion over `{}`: {why}", key.name),
        };
        let rec_name = key.name.clone().str("rec");
        let rec = self
            .env
            .get_recursor(&rec_name)
            .cloned()
            .ok_or_else(|| unsupported("it has no recursor".to_string()))?;
        if rec.num_indices != 0 {
            return Err(unsupported(
                "indexed families are not supported".to_string(),
            ));
        }
        let has_motive_level = rec.level_params.len() == key.levels.len() + 1;
        if !has_motive_level && rec.level_params.len() != key.levels.len() {
            return Err(unsupported(
                "its recursor's universe parameters are unexpected".to_string(),
            ));
        }
        let num_motives = rec.num_motives as usize;
        let rec_ty = self.instantiate_rec_levels(&rec.type_, &rec.level_params, key, Level::zero());
        let rec_ty = peel(rec_ty, &key.indparams)
            .ok_or_else(|| unsupported("its recursor type is malformed".to_string()))?;
        let slot_domains =
            super::super::elab_match::motive_domains_from_rec_type(&rec_ty, num_motives);
        if slot_domains.len() != num_motives {
            return Err(unsupported(
                "its recursor's motives are malformed".to_string(),
            ));
        }
        let motive_fvars: Vec<FVarId> = (0..num_motives).map(|_| self.fresh_fvar()).collect();
        let motive_vals: Vec<Expr> = motive_fvars.iter().map(|id| Expr::fvar(*id)).collect();
        let mut cursor = peel(rec_ty, &motive_vals)
            .ok_or_else(|| unsupported("its recursor's motives are malformed".to_string()))?;
        let mut minors = Vec::with_capacity(rec.num_minors as usize);
        for _ in 0..rec.num_minors {
            let ExprKind::Pi(_, minor_ty, body) = cursor.kind() else {
                return Err(unsupported(
                    "its recursor's minors are malformed".to_string(),
                ));
            };
            let shape = self
                .minor_shape(minor_ty, &motive_fvars)
                .ok_or_else(|| unsupported(format!("a minor premise has an unsupported shape (`{minor_ty}`): reflexive or indexed constructors are not supported")))?;
            minors.push(shape);
            let dummy = Expr::fvar(self.fresh_fvar());
            cursor = body.instantiate(&dummy);
        }
        let rec_by_slot = self.recursors_by_slot(key, num_motives, rec.num_minors as usize);
        Ok(FamilyInfo {
            key: key.clone(),
            slot_domains,
            rec_by_slot,
            minors,
            has_motive_level,
        })
    }

    /// `ty` with the recursor's universe parameters set to `motive_level`
    /// (when it has one) followed by the family's levels.
    pub(super) fn instantiate_rec_levels(
        &self,
        ty: &Expr,
        params: &[Name],
        key: &FamilyKey,
        motive_level: Level,
    ) -> Expr {
        let levels = self.rec_levels(params.len(), key, motive_level);
        ty.instantiate_level_params_direct(params, &levels)
    }

    pub(super) fn rec_levels(
        &self,
        count: usize,
        key: &FamilyKey,
        motive_level: Level,
    ) -> Vec<Level> {
        if count == key.levels.len() + 1 {
            std::iter::once(motive_level)
                .chain(key.levels.iter().cloned())
                .collect()
        } else {
            key.levels.clone()
        }
    }

    fn minor_shape(&mut self, minor_ty: &Expr, motives: &[FVarId]) -> Option<MinorShape> {
        let motive_index = |expr: &Expr| match expr.get_app_fn().kind() {
            ExprKind::FVar(id) => motives.iter().position(|m| m == id),
            _ => None,
        };
        let mut fields: Vec<FVarId> = Vec::new();
        let mut ihs = Vec::new();
        let mut cursor = minor_ty.clone();
        while let ExprKind::Pi(_, dom, body) = cursor.kind() {
            let mut target: &Expr = dom;
            while let ExprKind::Pi(_, _, inner) = target.kind() {
                target = inner;
            }
            if dom.is_pi() && motive_index(target).is_some() {
                return None; // reflexive induction hypothesis
            }
            let id = self.fresh_fvar();
            if let Some(slot) = motive_index(dom) {
                let args = dom.get_app_args();
                let [arg] = args.as_slice() else {
                    return None;
                };
                let ExprKind::FVar(field) = arg.kind() else {
                    return None;
                };
                let field_idx = fields.iter().position(|f| f == field)?;
                ihs.push((field_idx, slot));
            } else {
                if !ihs.is_empty() {
                    return None; // fields after induction hypotheses
                }
                fields.push(id);
            }
            cursor = body.instantiate(&Expr::fvar(id));
        }
        let slot = motive_index(&cursor)?;
        let args = cursor.get_app_args();
        let [ctor_app] = args.as_slice() else {
            return None;
        };
        let ExprKind::Const(ctor_name, _) = ctor_app.get_app_fn().kind() else {
            return None;
        };
        self.env.get_constructor(ctor_name)?;
        let ctor_args = ctor_app.get_app_args();
        let n = ctor_args.len().checked_sub(fields.len())?;
        for (arg, field) in ctor_args[n..].iter().zip(&fields) {
            if !matches!(arg.kind(), ExprKind::FVar(id) if id == field) {
                return None;
            }
        }
        let ctor_head = Expr::apps(
            ctor_app.get_app_fn().clone(),
            ctor_args[..n].iter().map(|arg| (*arg).clone()),
        );
        if super::scc::mentioned_members(&fields, &[&ctor_head]).is_empty() {
            Some(MinorShape {
                slot,
                ctor_head,
                num_fields: fields.len(),
                ihs,
            })
        } else {
            None
        }
    }

    /// For each slot, the family recursor whose conclusion is that slot's
    /// motive: `T.rec`, each mutual sibling's `.rec`, and `T.rec_N`.
    fn recursors_by_slot(
        &mut self,
        key: &FamilyKey,
        num_motives: usize,
        num_minors: usize,
    ) -> Vec<Option<Name>> {
        let mut out = vec![None; num_motives];
        let mut names: Vec<Name> = self
            .env
            .get_inductive(&key.name)
            .map(|ind| ind.all_names.iter().map(|n| n.clone().str("rec")).collect())
            .unwrap_or_default();
        names.extend((1..=num_motives).map(|i| key.name.clone().str(format!("rec_{i}"))));
        for name in names {
            let Some(rec) = self.env.get_recursor(&name).cloned() else {
                continue;
            };
            if rec.num_motives as usize != num_motives
                || rec.num_minors as usize != num_minors
                || rec.num_indices != 0
                || rec.arg_order != clean_kernel::RecursorArgOrder::MajorAfterMinors
            {
                continue;
            }
            let ty = self.instantiate_rec_levels(&rec.type_, &rec.level_params, key, Level::zero());
            let Some(ty) = peel(ty, &key.indparams) else {
                continue;
            };
            let motives: Vec<FVarId> = (0..num_motives).map(|_| self.fresh_fvar()).collect();
            let motive_vals: Vec<Expr> = motives.iter().map(|id| Expr::fvar(*id)).collect();
            let rest: Vec<Expr> = (0..=num_minors)
                .map(|_| Expr::fvar(self.fresh_fvar()))
                .collect();
            let Some(conclusion) = peel(ty, &motive_vals).and_then(|ty| peel(ty, &rest)) else {
                continue;
            };
            if let ExprKind::FVar(head) = conclusion.get_app_fn().kind() {
                if let Some(slot) = motives.iter().position(|m| m == head) {
                    if out[slot].is_none() {
                        out[slot] = Some(name);
                    }
                }
            }
        }
        out
    }
}
