// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Recursor type construction for inductive types.
//!
//! Builds the type expressions for `.rec`, `.casesOn`, `.recOn`, and their
//! minor premises. Extracted from `inductive_recursor.rs` for maintainability.
//!
//! For mutual inductives (Lean 4 inductive.cpp:752-776), each recursor includes
//! motives for ALL types in the mutual block and minor premises for ALL
//! constructors across ALL types.

use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::inductive::{count_pi_args, get_return_type, InductiveType};
use crate::level::Level;
use crate::name::Name;

use super::inductive_fixed_indices::{ind_const_with_levels, CtorInfo};
use super::Environment;

impl Environment {
    /// Determine which type in the mutual block a constructor belongs to,
    /// returning the motive index (0-based position in `all_types`).
    ///
    /// For a constructor named `Even.zero` with `all_types = [Even, Odd]`,
    /// returns 0. For `Odd.succ_even`, returns 1.
    fn ctor_motive_index(ctor_name: &Name, all_types: &[InductiveType]) -> usize {
        for (idx, ind_type) in all_types.iter().enumerate() {
            for ctor in &ind_type.constructors {
                if &ctor.name == ctor_name {
                    return idx;
                }
            }
        }
        // Fallback: shouldn't happen with well-formed declarations
        0
    }

    /// Determine the motive index for a recursive field type by examining
    /// the head constant of the field type's return type.
    ///
    /// For a field of type `Odd` in an `[Even, Odd]` mutual block, returns 1.
    /// For a field of type `(Unit -> Even)`, returns 0 (the return type is Even).
    pub(crate) fn field_motive_index(field_ty: &Expr, all_types: &[InductiveType]) -> usize {
        // Navigate past all Pi binders to get the return type
        let ret_ty = get_return_type(field_ty);
        // Get the head constant from the return type application
        let head = ret_ty.get_app_fn();
        if let ExprKind::Const(name, _) = &head.kind {
            for (idx, ind_type) in all_types.iter().enumerate() {
                if &ind_type.name == name {
                    return idx;
                }
            }
        }
        // Fallback for non-mutual or unrecognized field types
        0
    }

    /// Build the recursor type for an inductive.
    ///
    /// For mutual inductives, generates motives for ALL types and minors for
    /// ALL constructors. Example for Even/Odd:
    /// ```text
    /// Even.rec : {motive₁ : Even → Sort u} → {motive₂ : Odd → Sort u} →
    ///            motive₁ Even.zero →
    ///            ((o : Odd) → motive₂ o → motive₁ (Even.succ_odd o)) →
    ///            ((e : Even) → motive₁ e → motive₂ (Odd.succ_even e)) →
    ///            (t : Even) → motive₁ t
    /// ```
    ///
    /// Ordering: params → motives → minors → indices → major → result
    ///
    /// # Contract
    ///
    /// REQUIRES: `ind_name` is a valid inductive name in the environment
    /// REQUIRES: `ind_type` is the well-formed type of the inductive
    /// REQUIRES: `num_params` + `num_indices` <= Pi binders in `ind_type`
    /// REQUIRES: `motive_univ_name` is `Some(name)` for large elimination, `None` for Prop-only
    /// REQUIRES: Each entry in `ctor_infos` is (name, num_fields, recursive_flags, field_types, return_indices)
    ///           where recursive_flags.len() == field_types.len() == num_fields
    /// REQUIRES: `all_types` contains ALL types in the mutual block (or just [current_type] for non-mutual)
    ///
    /// ENSURES: Returns a well-formed recursor type expression
    /// ENSURES: Result has shape: params → motives → minors → indices → major → result
    /// ENSURES: De Bruijn indices are correctly computed for all bound variables
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn build_recursor_type(
        &self,
        ind_name: &Name,
        ind_type: &Expr,
        num_params: u32,
        num_indices: u32,
        motive_univ_name: Option<&Name>,
        ind_level_params: &[Name],
        ctor_infos: &[CtorInfo],
        all_types: &[InductiveType],
    ) -> Expr {
        // Prop-only elimination: motive targets Sort 0 (Prop).
        // Large elimination: motive targets Sort u (parameterized universe).
        let motive_univ = match motive_univ_name {
            Some(name) => Level::param(name.clone()),
            None => Level::zero(),
        };
        let ind_const = ind_const_with_levels(ind_name, ind_level_params);

        let num_motives = all_types.len();

        // Collect parameter and index binders from the inductive type
        let param_binders = self.collect_pi_binders(ind_type, num_params);
        let mut current = ind_type.clone();
        for _ in 0..num_params {
            if let ExprKind::Pi(_, _, body) = &current.kind {
                current = (**body).clone();
            }
        }
        let index_binders = self.collect_pi_binders(&current, num_indices);
        let num_minors = ctor_infos.len();

        // Helper to build Ind applied to params and indices at given depths
        let build_ind_app = |param_offset: u32, index_offset: u32| -> Expr {
            let mut ind_app = ind_const.clone();
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

        // Build motive types for ALL types in the mutual block.
        // Each motive has type: Π indices_i, Π (major : Type_i indices_i), Sort u
        // For non-mutual, this is a single motive.
        let mut motive_types = Vec::with_capacity(num_motives);
        for t in all_types {
            let t_const = ind_const_with_levels(&t.name, ind_level_params);
            let t_type_arity = count_pi_args(&t.type_);
            let t_num_indices = t_type_arity.saturating_sub(num_params);
            let t_index_binders =
                self.collect_pi_binders_after_skip(&t.type_, num_params, t_num_indices);

            let mut mtype = Expr::from_kind(ExprKind::Sort(motive_univ.clone()));
            // major type: Type_i params indices
            let mut major_ty_for_motive = t_const.clone();
            for i in 0..num_params {
                let idx = t_num_indices + (num_params - 1 - i);
                major_ty_for_motive = Expr::app(major_ty_for_motive, Expr::bvar(idx));
            }
            for i in 0..t_num_indices {
                let idx = t_num_indices - 1 - i;
                major_ty_for_motive = Expr::app(major_ty_for_motive, Expr::bvar(idx));
            }
            mtype = Expr::pi(BinderInfo::Default, major_ty_for_motive, mtype);
            // Add the index binders, outermost (idx_0) last.
            //
            // De Bruijn: each index domain `I_i` is taken verbatim from the
            // inductive's own Pi telescope (parameters skipped). There `I_i`
            // sits under `i` preceding index binders (idx_0..idx_{i-1}) with the
            // parameters immediately beyond them, so a reference to an earlier
            // index `idx_j` is `BVar(i-1-j)` and a reference to param `p_m` is
            // `BVar(i + (num_params-1-m))`.
            //
            // In the standalone motive `Π idx_0 .. idx_{k-1} → (major) → Sort`
            // each `I_i` again sits under exactly `i` preceding index binders,
            // and the parameters are bound directly outside the motive (the
            // inter-motive lift applied later, when the motive is wrapped as a
            // binder, shifts those param references uniformly). The two contexts
            // are therefore identical, so `I_i` is placed UNCHANGED. A previous
            // version lifted `I_i` by `len-1-i`, which over-shifted every
            // non-final index domain mentioning a param or earlier index and
            // left a loose `BVar` past the parameter — the multi-index recursor
            // mis-typing fixed here.
            for (binder_info, index_ty) in t_index_binders.iter().rev() {
                mtype = Expr::pi(*binder_info, index_ty.clone(), mtype);
            }
            motive_types.push(mtype);
        }

        // Determine which motive index corresponds to ind_name
        let this_motive_idx = all_types
            .iter()
            .position(|t| &t.name == ind_name)
            .unwrap_or(0);

        // Build minor premise types. Each entry is `(type, is_path)`: a HIT path
        // constructor's minor premise (`is_path == true`) is built directly in
        // its final telescope position, so it is NOT subjected to the per-minor
        // lift applied below.
        let mut minor_types: Vec<(Expr, bool)> = Vec::new();
        for (
            minor_self_idx,
            (ctor_name, num_fields, recursive_flags, field_types, return_indices),
        ) in ctor_infos.iter().enumerate()
        {
            let ctor_motive_idx = Self::ctor_motive_index(ctor_name, all_types);
            if let Some((left, right)) = Self::ctor_path_data(ctor_name, all_types) {
                // rec layout: params → motives → minors → indices → major. At
                // this minor's domain the motive `C_k` sits at
                // `minor_self_idx + (num_motives - 1 - k)` (k = conclusion motive).
                let motive_bvar_base = minor_self_idx + (num_motives - 1 - ctor_motive_idx);
                let minor_ty = Self::build_path_minor_premise_type(
                    ctor_name,
                    &left,
                    &right,
                    motive_bvar_base,
                    minor_self_idx,
                    ind_level_params,
                    all_types,
                );
                minor_types.push((minor_ty, true));
            } else {
                let minor_ty = self.build_minor_premise_type(
                    ind_name,
                    ctor_name,
                    *num_fields,
                    recursive_flags,
                    field_types,
                    num_params,
                    ind_level_params,
                    return_indices,
                    num_motives,
                    ctor_motive_idx,
                    all_types,
                );
                minor_types.push((minor_ty, false));
            }
        }

        // Build the full rec type from inside out:
        // Structure: params → motives → minors → indices → major → motive_i indices major
        // At result level (innermost):
        //   - major is BVar(0)
        //   - indices are BVar(1) to BVar(num_indices)
        //   - motives are at BVar(num_indices + 1 + num_minors + (num_motives - 1 - motive_idx))
        //     where motive_0 (outermost) is at the highest BVar
        let this_motive_bvar = Self::usize_to_u32(
            num_minors + num_indices as usize + 1 + (num_motives - 1 - this_motive_idx),
        );
        let mut result_ty = Expr::bvar(this_motive_bvar);
        for i in 0..num_indices {
            let idx = Self::usize_to_u32(num_indices as usize - i as usize);
            result_ty = Expr::app(result_ty, Expr::bvar(idx));
        }
        result_ty = Expr::app(result_ty, Expr::bvar(0)); // major

        // Add major premise: (t : Ind params indices) → result
        let major_ty = build_ind_app(num_indices + num_minors as u32 + num_motives as u32, 0);
        result_ty = Expr::pi(BinderInfo::Default, major_ty, result_ty);

        // Add index binders
        // Index domains' BVars reference both other indices (BVar < i) and params
        // (BVar >= i). Motive + minor binders sit between indices and params in the
        // recursor type, so param-referencing BVars must be shifted by (num_minors + num_motives).
        let extra = Self::usize_to_u32(num_minors + num_motives);
        for (i, (binder_info, index_ty)) in index_binders.iter().enumerate().rev() {
            let lifted_index_ty = if extra > 0 {
                index_ty.lift_from(i as u32, extra)
            } else {
                index_ty.clone()
            };
            result_ty = Expr::pi(*binder_info, lifted_index_ty, result_ty);
        }

        // Add minor premises (in reverse order since we're building inside-out)
        // Each minor type's BVars reference the motives. Minor domains are NOT under the
        // inner binders (indices/major), only under preceding minor binders and motives.
        // Path-constructor minors are already in final context (built that way to
        // express their endpoints as earlier minor binders) — they skip the lift.
        for (i, (minor_ty, is_path)) in minor_types.iter().enumerate().rev() {
            let lifted_minor_ty = if *is_path || i == 0 {
                minor_ty.clone()
            } else {
                minor_ty.lift(Self::usize_to_u32(i))
            };
            result_ty = Expr::pi(BinderInfo::Default, lifted_minor_ty, result_ty);
        }

        // Add motives (innermost motive last = all_types[n-1], outermost = all_types[0])
        // Each motive domain sits inside the preceding motive binders. Motive_i needs
        // to be lifted by i to account for the i motives already wrapped inside.
        for (i, mtype) in motive_types.iter().enumerate().rev() {
            let lifted_mtype = if i > 0 {
                mtype.lift(Self::usize_to_u32(i))
            } else {
                mtype.clone()
            };
            result_ty = Expr::pi(BinderInfo::Implicit, lifted_mtype, result_ty);
        }

        // Add parameters (outermost)
        for (_i, (binder_info, param_ty)) in param_binders.iter().enumerate().rev() {
            result_ty = Expr::pi(*binder_info, param_ty.clone(), result_ty);
        }

        // Apply infer_implicit: mark explicit binders as Implicit when their
        // bound variable appears in a subsequent Pi domain (strict mode).
        // Reference: lean4-ref/src/kernel/inductive.cpp:767
        result_ty = result_ty.infer_implicit(true);

        result_ty
    }

    /// Build the recOn type for an inductive.
    ///
    /// For mutual inductives, includes all motives and all minors.
    /// Ordering: params → motives → indices → major → minors → result
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn build_rec_on_type(
        &self,
        ind_name: &Name,
        ind_type: &Expr,
        num_params: u32,
        num_indices: u32,
        motive_univ_name: Option<&Name>,
        ind_level_params: &[Name],
        ctor_infos: &[CtorInfo],
        all_types: &[InductiveType],
    ) -> Expr {
        let motive_univ = match motive_univ_name {
            Some(name) => Level::param(name.clone()),
            None => Level::zero(),
        };
        let ind_const = ind_const_with_levels(ind_name, ind_level_params);

        let num_motives = all_types.len();

        let param_binders = self.collect_pi_binders(ind_type, num_params);
        let mut current = ind_type.clone();
        for _ in 0..num_params {
            if let ExprKind::Pi(_, _, body) = &current.kind {
                current = (**body).clone();
            }
        }
        let index_binders = self.collect_pi_binders(&current, num_indices);
        let num_minors = ctor_infos.len();

        let build_ind_app = |param_offset: u32, index_offset: u32| -> Expr {
            let mut ind_app = ind_const.clone();
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

        // Build motive types for ALL types (same as build_recursor_type)
        let mut motive_types = Vec::with_capacity(num_motives);
        for t in all_types {
            let t_const = ind_const_with_levels(&t.name, ind_level_params);
            let t_type_arity = count_pi_args(&t.type_);
            let t_num_indices = t_type_arity.saturating_sub(num_params);
            let t_index_binders =
                self.collect_pi_binders_after_skip(&t.type_, num_params, t_num_indices);

            let mut mtype = Expr::from_kind(ExprKind::Sort(motive_univ.clone()));
            let mut major_ty_for_motive = t_const.clone();
            for i in 0..num_params {
                let idx = t_num_indices + (num_params - 1 - i);
                major_ty_for_motive = Expr::app(major_ty_for_motive, Expr::bvar(idx));
            }
            for i in 0..t_num_indices {
                let idx = t_num_indices - 1 - i;
                major_ty_for_motive = Expr::app(major_ty_for_motive, Expr::bvar(idx));
            }
            mtype = Expr::pi(BinderInfo::Default, major_ty_for_motive, mtype);
            // Add the index binders, outermost (idx_0) last.
            //
            // De Bruijn: each index domain `I_i` is taken verbatim from the
            // inductive's own Pi telescope (parameters skipped). There `I_i`
            // sits under `i` preceding index binders (idx_0..idx_{i-1}) with the
            // parameters immediately beyond them, so a reference to an earlier
            // index `idx_j` is `BVar(i-1-j)` and a reference to param `p_m` is
            // `BVar(i + (num_params-1-m))`.
            //
            // In the standalone motive `Π idx_0 .. idx_{k-1} → (major) → Sort`
            // each `I_i` again sits under exactly `i` preceding index binders,
            // and the parameters are bound directly outside the motive (the
            // inter-motive lift applied later, when the motive is wrapped as a
            // binder, shifts those param references uniformly). The two contexts
            // are therefore identical, so `I_i` is placed UNCHANGED. A previous
            // version lifted `I_i` by `len-1-i`, which over-shifted every
            // non-final index domain mentioning a param or earlier index and
            // left a loose `BVar` past the parameter — the multi-index recursor
            // mis-typing fixed here.
            for (binder_info, index_ty) in t_index_binders.iter().rev() {
                mtype = Expr::pi(*binder_info, index_ty.clone(), mtype);
            }
            motive_types.push(mtype);
        }

        let this_motive_idx = all_types
            .iter()
            .position(|t| &t.name == ind_name)
            .unwrap_or(0);

        // Build minor premise types (see `build_recursor_type` for the
        // `(type, is_path)` convention). recOn layout puts minors INNERMOST, so a
        // path minor's conclusion motive sits past the major + indices.
        let mut minor_types: Vec<(Expr, bool)> = Vec::new();
        for (
            minor_self_idx,
            (ctor_name, num_fields, recursive_flags, field_types, return_indices),
        ) in ctor_infos.iter().enumerate()
        {
            let ctor_motive_idx = Self::ctor_motive_index(ctor_name, all_types);
            if let Some((left, right)) = Self::ctor_path_data(ctor_name, all_types) {
                // recOn layout: params → motives → indices → major → minors. At
                // this minor's domain the motive `C_k` sits at
                // `minor_self_idx + 1 (major) + num_indices + (num_motives-1-k)`.
                let motive_bvar_base =
                    minor_self_idx + 1 + num_indices as usize + (num_motives - 1 - ctor_motive_idx);
                let minor_ty = Self::build_path_minor_premise_type(
                    ctor_name,
                    &left,
                    &right,
                    motive_bvar_base,
                    minor_self_idx,
                    ind_level_params,
                    all_types,
                );
                minor_types.push((minor_ty, true));
            } else {
                let minor_ty = self.build_minor_premise_type(
                    ind_name,
                    ctor_name,
                    *num_fields,
                    recursive_flags,
                    field_types,
                    num_params,
                    ind_level_params,
                    return_indices,
                    num_motives,
                    ctor_motive_idx,
                    all_types,
                );
                minor_types.push((minor_ty, false));
            }
        }

        // Build the full recOn type from inside out:
        // Structure: params → motives → indices → major → minor₁ → ... → minorₙ → motive indices major
        // At result level:
        //   - major is BVar(num_minors)
        //   - indices start at BVar(num_minors + 1)
        //   - motives at BVar(num_minors + num_indices + 1 + (num_motives - 1 - motive_idx))
        let this_motive_bvar = Self::usize_to_u32(
            num_minors + num_indices as usize + 1 + (num_motives - 1 - this_motive_idx),
        );
        let major_idx = Self::usize_to_u32(num_minors);
        let mut result_ty = Expr::bvar(this_motive_bvar);
        for i in 0..num_indices {
            let idx = Self::usize_to_u32(num_minors + num_indices as usize - 1 - i as usize) + 1;
            result_ty = Expr::app(result_ty, Expr::bvar(idx));
        }
        result_ty = Expr::app(result_ty, Expr::bvar(major_idx));

        // Add minor premises (in reverse order since we're building inside-out)
        // Each minor type's BVars need to be lifted to account for indices and major.
        // Path-constructor minors are already in final context — they skip the lift.
        for (i, (minor_ty, is_path)) in minor_types.iter().enumerate().rev() {
            let lifted_minor_ty = if *is_path {
                minor_ty.clone()
            } else {
                let lift_by = num_indices as usize + 1 + i;
                minor_ty.lift(Self::usize_to_u32(lift_by))
            };
            result_ty = Expr::pi(BinderInfo::Default, lifted_minor_ty, result_ty);
        }

        // Add major premise: (t : Ind params indices) → result
        let major_ty = build_ind_app(num_indices + num_motives as u32, 0);
        result_ty = Expr::pi(BinderInfo::Default, major_ty, result_ty);

        // Add index binders
        // In recOn, only the motive binders sit between indices and params, so extra = num_motives.
        for (i, (binder_info, index_ty)) in index_binders.iter().enumerate().rev() {
            let lifted_index_ty = index_ty.lift_from(i as u32, num_motives as u32);
            result_ty = Expr::pi(*binder_info, lifted_index_ty, result_ty);
        }

        // Add motives
        for (i, mtype) in motive_types.iter().enumerate().rev() {
            let lifted_mtype = if i > 0 {
                mtype.lift(Self::usize_to_u32(i))
            } else {
                mtype.clone()
            };
            result_ty = Expr::pi(BinderInfo::Implicit, lifted_mtype, result_ty);
        }

        // Add parameters (outermost)
        for (_i, (binder_info, param_ty)) in param_binders.iter().enumerate().rev() {
            result_ty = Expr::pi(*binder_info, param_ty.clone(), result_ty);
        }

        result_ty = result_ty.infer_implicit(true);

        result_ty
    }

    /// Collect Pi binders after skipping `skip` binders, collecting up to `count`.
    fn collect_pi_binders_after_skip(
        &self,
        ty: &Expr,
        skip: u32,
        count: u32,
    ) -> Vec<(crate::expr::BinderData, Expr)> {
        let mut current = ty.clone();
        for _ in 0..skip {
            if let ExprKind::Pi(_, _, body) = &current.kind {
                current = (**body).clone();
            }
        }
        self.collect_pi_binders(&current, count)
    }
}
