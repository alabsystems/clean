// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mutual inductive recursor type construction (#3237).
//!
//! Builds rec and recOn type expressions for mutual inductives, which need
//! multiple motives (one per type in the mutual block) and minors for all
//! constructors across the block.
//!
//! Extracted from `inductive_recursor_types.rs` for file-size compliance.
//! Reference: Lean 4 `inductive.cpp:752-776`.

use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::inductive::{count_pi_args, InductiveDecl};
use crate::level::Level;
use crate::name::Name;

use super::inductive_fixed_indices::{ind_const_with_levels, CtorInfo};
use super::Environment;

impl Environment {
    /// Build motive types for all types in a mutual inductive block.
    ///
    /// Each motive has type: `Pi indices_i, T_i params indices_i -> Sort u`
    fn build_mutual_motive_types(&self, decl: &InductiveDecl, motive_univ: &Level) -> Vec<Expr> {
        let num_params = decl.num_params;
        let mut motive_types = Vec::with_capacity(decl.types.len());
        for t in &decl.types {
            let t_arity = count_pi_args(&t.type_);
            let t_indices = t_arity.saturating_sub(num_params);
            let t_const = ind_const_with_levels(&t.name, &decl.level_params);

            let mut t_current = t.type_.clone();
            for _ in 0..num_params {
                if let ExprKind::Pi(_, _, body) = &t_current.kind {
                    t_current = (**body).clone();
                }
            }
            let t_index_binders = self.collect_pi_binders(&t_current, t_indices);

            let mut mt = Expr::from_kind(ExprKind::Sort(motive_univ.clone()));
            let mut t_app = t_const;
            for i in 0..num_params {
                let idx = t_indices + (num_params - 1 - i);
                t_app = Expr::app(t_app, Expr::bvar(idx));
            }
            for i in 0..t_indices {
                let idx = t_indices - 1 - i;
                t_app = Expr::app(t_app, Expr::bvar(idx));
            }
            mt = Expr::pi(BinderInfo::Default, t_app, mt);

            for (i, (binder_info, idx_ty)) in t_index_binders.iter().enumerate().rev() {
                let inner = t_index_binders.len() - 1 - i;
                let lift_by = inner as u32;
                let lifted = if lift_by > 0 {
                    idx_ty.lift(lift_by)
                } else {
                    idx_ty.clone()
                };
                mt = Expr::pi(*binder_info, lifted, mt);
            }
            motive_types.push(mt);
        }
        motive_types
    }

    /// Build minor premise types for all constructors in a mutual block.
    ///
    /// For mutual inductives, each minor's conclusion uses the motive of the
    /// type that constructor belongs to. IH types use the motive of the type
    /// the recursive field returns to (Lean 4 inductive.cpp:644,658).
    fn build_mutual_minor_types(
        &self,
        ind_name: &Name,
        decl: &InductiveDecl,
        all_ctor_infos: &[CtorInfo],
    ) -> Vec<Expr> {
        let num_motives = decl.types.len();

        // Build a map from constructor index to its parent type's motive index.
        let mut ctor_motive_indices = Vec::with_capacity(all_ctor_infos.len());
        for (type_idx, t) in decl.types.iter().enumerate() {
            for _ in &t.constructors {
                ctor_motive_indices.push(type_idx);
            }
        }

        let mut minor_types = Vec::new();
        for (i, (ctor_name, num_fields, recursive_flags, field_types, return_indices)) in
            all_ctor_infos.iter().enumerate()
        {
            let conclusion_motive_idx = ctor_motive_indices.get(i).copied().unwrap_or(0);
            let minor_ty = self.build_minor_premise_type(
                ind_name,
                ctor_name,
                *num_fields,
                recursive_flags,
                field_types,
                decl.num_params,
                &decl.level_params,
                return_indices,
                num_motives,
                conclusion_motive_idx,
                &decl.types,
            );
            minor_types.push(minor_ty);
        }
        minor_types
    }

    /// Wrap motives, parameters, and apply infer_implicit to a result type.
    fn wrap_mutual_outer_binders(
        &self,
        mut result_ty: Expr,
        motive_types: &[Expr],
        param_binders: &[(crate::expr::BinderData, Expr)],
    ) -> Expr {
        // Add motives (in reverse order)
        for (i, motive_ty) in motive_types.iter().enumerate().rev() {
            let lifted = if i > 0 {
                motive_ty.lift(Self::usize_to_u32(i))
            } else {
                motive_ty.clone()
            };
            result_ty = Expr::pi(BinderInfo::Implicit, lifted, result_ty);
        }

        // Add parameters (outermost)
        for (_i, (binder_info, param_ty)) in param_binders.iter().enumerate().rev() {
            result_ty = Expr::pi(*binder_info, param_ty.clone(), result_ty);
        }

        // Apply infer_implicit
        result_ty.infer_implicit(true)
    }

    /// Build the recursor type for a mutual inductive (#3237).
    ///
    /// For Even/Odd mutual inductive, Even.rec has type:
    /// ```text
    /// {motive_even : Even → Sort u} →
    /// {motive_odd : Odd → Sort u} →
    /// motive_even Even.zero →
    /// ((o : Odd) → motive_odd o → motive_even (Even.succ_odd o)) →
    /// ((e : Even) → motive_even e → motive_odd (Odd.succ_even e)) →
    /// (t : Even) → motive_even t
    /// ```
    ///
    /// Key difference from simple: num_motives = num_types, num_minors = total_ctors.
    /// Reference: Lean 4 `inductive.cpp:752-776`.
    pub(crate) fn build_mutual_recursor_type(
        &self,
        ind_name: &Name,
        decl: &InductiveDecl,
        motive_univ_name: Option<&Name>,
        all_ctor_infos: &[CtorInfo],
    ) -> Expr {
        let motive_univ = match motive_univ_name {
            Some(name) => Level::param(name.clone()),
            None => Level::zero(),
        };

        let num_params = decl.num_params;
        let num_types = decl.types.len();
        let num_minors = all_ctor_infos.len();

        let ind_type = decl
            .types
            .iter()
            .find(|t| &t.name == ind_name)
            .expect("ind_name must be in decl.types");
        let target_type_idx = decl
            .types
            .iter()
            .position(|t| &t.name == ind_name)
            .expect("ind_name must be in decl.types");

        let type_arity = count_pi_args(&ind_type.type_);
        let num_indices = type_arity.saturating_sub(num_params);

        let param_binders = self.collect_pi_binders(&ind_type.type_, num_params);
        let mut current = ind_type.type_.clone();
        for _ in 0..num_params {
            if let ExprKind::Pi(_, _, body) = &current.kind {
                current = (**body).clone();
            }
        }
        let index_binders = self.collect_pi_binders(&current, num_indices);

        let motive_types = self.build_mutual_motive_types(decl, &motive_univ);
        let minor_types = self.build_mutual_minor_types(ind_name, decl, all_ctor_infos);

        // Build the full rec type from inside out:
        // params -> motives -> minors -> indices -> major -> motive_target indices major
        let target_ind_const = ind_const_with_levels(ind_name, &decl.level_params);
        let target_motive_idx =
            Self::usize_to_u32(num_minors + num_indices as usize + num_types - 1 - target_type_idx)
                + 1;

        let mut result_ty = Expr::bvar(target_motive_idx);
        for i in 0..num_indices {
            let idx = Self::usize_to_u32(num_indices as usize - i as usize);
            result_ty = Expr::app(result_ty, Expr::bvar(idx));
        }
        result_ty = Expr::app(result_ty, Expr::bvar(0)); // major

        // Add major premise: (t : Ind params indices) -> result
        let build_target_ind_app = |param_offset: u32, index_offset: u32| -> Expr {
            let mut ind_app = target_ind_const.clone();
            for i in 0..num_params {
                let idx = param_offset + (num_params - 1 - i);
                ind_app = Expr::app(ind_app, Expr::bvar(idx));
            }
            for i in 0..num_indices {
                let idx = index_offset + (num_indices - 1 - i);
                ind_app = Expr::app(ind_app, Expr::bvar(idx));
            }
            ind_app
        };

        let major_ty = build_target_ind_app(num_indices + num_minors as u32 + num_types as u32, 0);
        result_ty = Expr::pi(BinderInfo::Default, major_ty, result_ty);

        // Add index binders
        let extra = Self::usize_to_u32(num_minors + num_types);
        for (i, (binder_info, index_ty)) in index_binders.iter().enumerate().rev() {
            let lifted_index_ty = if extra > 0 {
                index_ty.lift_from(i as u32, extra)
            } else {
                index_ty.clone()
            };
            result_ty = Expr::pi(*binder_info, lifted_index_ty, result_ty);
        }

        // Add minor premises (in reverse order since we're building inside-out)
        for (i, minor_ty) in minor_types.iter().enumerate().rev() {
            let extra_motives = Self::usize_to_u32(num_types - 1);
            let shifted = if extra_motives > 0 {
                minor_ty.lift(extra_motives)
            } else {
                minor_ty.clone()
            };
            let lifted_minor_ty = if i > 0 {
                shifted.lift(Self::usize_to_u32(i))
            } else {
                shifted
            };
            result_ty = Expr::pi(BinderInfo::Default, lifted_minor_ty, result_ty);
        }

        self.wrap_mutual_outer_binders(result_ty, &motive_types, &param_binders)
    }

    /// Build the recOn type for a mutual inductive (#3237).
    ///
    /// Like `build_mutual_recursor_type` but with recOn argument ordering:
    /// params -> motives -> indices -> major -> minors -> result
    ///
    /// For Even/Odd mutual inductive, Even.recOn has type:
    /// ```text
    /// {motive_even : Even -> Sort u} ->
    /// {motive_odd : Odd -> Sort u} ->
    /// (t : Even) ->
    /// motive_even Even.zero ->
    /// ((o : Odd) -> motive_odd o -> motive_even (Even.succ_odd o)) ->
    /// ((e : Even) -> motive_even e -> motive_odd (Odd.succ_even e)) ->
    /// motive_even t
    /// ```
    pub(crate) fn build_mutual_rec_on_type(
        &self,
        ind_name: &Name,
        decl: &InductiveDecl,
        motive_univ_name: Option<&Name>,
        all_ctor_infos: &[CtorInfo],
    ) -> Expr {
        let motive_univ = match motive_univ_name {
            Some(name) => Level::param(name.clone()),
            None => Level::zero(),
        };

        let num_params = decl.num_params;
        let num_types = decl.types.len();
        let num_minors = all_ctor_infos.len();

        let ind_type = decl
            .types
            .iter()
            .find(|t| &t.name == ind_name)
            .expect("ind_name must be in decl.types");
        let target_type_idx = decl
            .types
            .iter()
            .position(|t| &t.name == ind_name)
            .expect("ind_name must be in decl.types");

        let type_arity = count_pi_args(&ind_type.type_);
        let num_indices = type_arity.saturating_sub(num_params);

        let param_binders = self.collect_pi_binders(&ind_type.type_, num_params);
        let mut current = ind_type.type_.clone();
        for _ in 0..num_params {
            if let ExprKind::Pi(_, _, body) = &current.kind {
                current = (**body).clone();
            }
        }
        let index_binders = self.collect_pi_binders(&current, num_indices);

        let motive_types = self.build_mutual_motive_types(decl, &motive_univ);
        let minor_types = self.build_mutual_minor_types(ind_name, decl, all_ctor_infos);

        // Build the full recOn type from inside out:
        // params -> motives -> indices -> major -> minors -> motive_target indices major
        let target_ind_const = ind_const_with_levels(ind_name, &decl.level_params);

        let target_motive_idx =
            Self::usize_to_u32(num_minors + num_indices as usize + num_types - 1 - target_type_idx)
                + 1;
        let major_idx = Self::usize_to_u32(num_minors);

        let mut result_ty = Expr::bvar(target_motive_idx);
        for i in 0..num_indices {
            let idx = Self::usize_to_u32(num_minors + num_indices as usize - 1 - i as usize) + 1;
            result_ty = Expr::app(result_ty, Expr::bvar(idx));
        }
        result_ty = Expr::app(result_ty, Expr::bvar(major_idx));

        // Add minor premises (in reverse order since we're building inside-out)
        for (i, minor_ty) in minor_types.iter().enumerate().rev() {
            let extra_motives = Self::usize_to_u32(num_types - 1);
            let shifted = if extra_motives > 0 {
                minor_ty.lift(extra_motives)
            } else {
                minor_ty.clone()
            };
            let lift_by = num_indices as usize + 1 + i;
            let lifted_minor_ty = if lift_by > 0 {
                shifted.lift(Self::usize_to_u32(lift_by))
            } else {
                shifted
            };
            result_ty = Expr::pi(BinderInfo::Default, lifted_minor_ty, result_ty);
        }

        // Add major premise: (t : Ind params indices) -> result
        let build_target_ind_app = |param_offset: u32, index_offset: u32| -> Expr {
            let mut ind_app = target_ind_const.clone();
            for i in 0..num_params {
                let idx = param_offset + (num_params - 1 - i);
                ind_app = Expr::app(ind_app, Expr::bvar(idx));
            }
            for i in 0..num_indices {
                let idx = index_offset + (num_indices - 1 - i);
                ind_app = Expr::app(ind_app, Expr::bvar(idx));
            }
            ind_app
        };

        let major_ty = build_target_ind_app(num_indices + num_types as u32, 0);
        result_ty = Expr::pi(BinderInfo::Default, major_ty, result_ty);

        // Add index binders
        for (i, (binder_info, index_ty)) in index_binders.iter().enumerate().rev() {
            let lifted_index_ty = index_ty.lift_from(i as u32, num_types as u32);
            result_ty = Expr::pi(*binder_info, lifted_index_ty, result_ty);
        }

        self.wrap_mutual_outer_binders(result_ty, &motive_types, &param_binders)
    }
}
