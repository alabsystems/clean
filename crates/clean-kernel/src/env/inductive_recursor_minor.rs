// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Minor premise type construction for inductive recursors.
//!
//! Builds the types of minor premises (one per constructor) for `.rec`,
//! `.casesOn`, and `.recOn`. Extracted from `inductive_recursor_types.rs`
//! for maintainability.
//!
//! For mutual inductives (#3237), each minor's conclusion uses the motive
//! of the type the constructor belongs to, and each IH uses the motive
//! of the type the recursive field returns to (Lean 4 inductive.cpp:644,658).

use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::inductive::{get_return_type, InductiveType};
use crate::level::Level;
use crate::name::Name;
use std::sync::Arc;

use super::inductive_fixed_indices::ind_const_with_levels;
use super::Environment;

impl Environment {
    /// Build the minor premise type for a constructor.
    ///
    /// For `succ (n : Nat)`, generates: `(n : Nat) -> motive n -> motive (Nat.succ n)`
    ///
    /// For mutual inductives, `num_motives > 1` and the conclusion uses
    /// `conclusion_motive_idx` to select the correct motive. IH types use
    /// the motive corresponding to the recursive field's target type.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn build_minor_premise_type(
        &self,
        ind_name: &Name,
        ctor_name: &Name,
        num_fields: u32,
        recursive_flags: &[bool],
        field_types: &[Expr],
        num_params: u32,
        ind_level_params: &[Name],
        ctor_indices: &[Expr],
        num_motives: usize,
        conclusion_motive_idx: usize,
        all_types: &[InductiveType],
    ) -> Expr {
        // Count how many IH parameters we need
        let num_ihs: usize = recursive_flags.iter().filter(|&&b| b).count();
        let num_fields = num_fields as usize;

        // With num_motives motives, the motive binders occupy positions
        // [num_fields + num_ihs .. num_fields + num_ihs + num_motives - 1].
        // Motive_0 (outermost) is at the highest BVar, motive_{n-1} (innermost) at lowest.
        // conclusion_motive_idx selects which motive to use for the conclusion.
        let conclusion_motive_bvar =
            num_fields + num_ihs + (num_motives - 1 - conclusion_motive_idx);

        let adjust_index_expr = |expr: Expr, ih_offset: usize| -> Expr {
            let mut adjusted = expr.lift(Self::usize_to_u32(ih_offset));
            adjusted = adjusted.lift_from(
                Self::usize_to_u32(ih_offset + num_fields),
                num_motives as u32,
            );
            adjusted
        };

        // Build ctor applied to all field arguments
        let ctor_levels: Vec<Level> = ind_level_params
            .iter()
            .map(|p| Level::param(p.clone()))
            .collect();
        let mut ctor_app = Expr::const_(ctor_name.clone(), ctor_levels);
        for i in 0..num_params {
            let param_depth =
                num_fields + num_ihs + num_motives + (num_params as usize - 1 - i as usize);
            ctor_app = Expr::app(ctor_app, Expr::bvar(Self::usize_to_u32(param_depth)));
        }
        for i in 0..num_fields {
            let field_depth = (num_fields - 1 - i) + num_ihs;
            ctor_app = Expr::app(ctor_app, Expr::bvar(Self::usize_to_u32(field_depth)));
        }

        // Build conclusion: motive_c indices (ctor fields)
        let mut result = Expr::bvar(Self::usize_to_u32(conclusion_motive_bvar));
        for idx_expr in ctor_indices {
            let adjusted = adjust_index_expr(idx_expr.clone(), num_ihs);
            result = Expr::app(result, adjusted);
        }
        result = Expr::app(result, ctor_app);

        // Add IH binders for recursive arguments (in reverse order).
        let mut ih_offset = 0usize;
        for (i, &is_recursive) in recursive_flags.iter().enumerate().rev() {
            if is_recursive {
                let ihs_above = num_ihs - 1 - ih_offset;
                let field_depth = (num_fields - 1 - i) + ihs_above;

                // Determine which motive to use for this IH based on the field type's
                // return type (Lean 4 inductive.cpp:658 -- get_I_indices on u_i_ty).
                let ih_motive_idx = field_types
                    .get(i)
                    .map(|ft| Self::field_motive_index(ft, all_types))
                    .unwrap_or(conclusion_motive_idx);
                let motive_at_ih = num_fields + ihs_above + (num_motives - 1 - ih_motive_idx);

                // Count Pi binders for reflexive fields (#1784).
                let n_pis = field_types.get(i).map(Self::count_pi_binders).unwrap_or(0);

                // Under n_pis Pi binders, all outer BVars shift by n_pis.
                let ih_motive = motive_at_ih + n_pis;
                let ih_field_depth = field_depth + n_pis;

                let mut ih_type = Expr::bvar(Self::usize_to_u32(ih_motive));

                // Apply index arguments (remapped for the Pi-wrapped context).
                let field_ty = field_types
                    .get(i)
                    .cloned()
                    .unwrap_or_else(|| ind_const_with_levels(ind_name, ind_level_params));
                let field_indices = self.get_constructor_return_indices(&field_ty, num_params);
                for idx_expr in &field_indices {
                    let remapped = Self::remap_residual_index_bvars_for_minor(
                        idx_expr,
                        i,
                        num_fields,
                        ihs_above,
                        num_motives,
                        n_pis,
                    );
                    ih_type = Expr::app(ih_type, remapped);
                }

                // Apply major premise: (field xs) for reflexive, bare field otherwise.
                let mut major = Expr::bvar(Self::usize_to_u32(ih_field_depth));
                for k in (0..n_pis).rev() {
                    major = Expr::app(major, Expr::bvar(Self::usize_to_u32(k)));
                }
                ih_type = Expr::app(ih_type, major);

                // Wrap in Pi binders for reflexive fields (#1784 audit fix).
                let pi_domains = field_types
                    .get(i)
                    .map(Self::collect_pi_domains)
                    .unwrap_or_default();
                for (k, (bi, domain)) in pi_domains.iter().enumerate().rev() {
                    let remapped = Self::remap_residual_index_bvars_for_minor(
                        domain,
                        i,
                        num_fields,
                        ihs_above,
                        num_motives,
                        k,
                    );
                    ih_type = Expr::pi(*bi, remapped, ih_type);
                }

                result = Expr::pi(BinderInfo::Default, ih_type, result);
                ih_offset += 1;
            }
        }

        // Add field binders (outermost), using constructor field types.
        for i in (0..num_fields).rev() {
            let field_ty = field_types
                .get(i)
                .cloned()
                .unwrap_or_else(|| ind_const_with_levels(ind_name, ind_level_params));
            // Insert num_motives slots at depth `i` for the motive binders.
            let lifted_field_ty = field_ty.lift_from(Self::usize_to_u32(i), num_motives as u32);
            result = Expr::pi(BinderInfo::Default, lifted_field_ty, result);
        }

        result
    }

    /// If `ctor_name` names a HIT *path* constructor in `all_types`, return its
    /// `(left, right)` path endpoints; otherwise `None`.
    ///
    /// A path constructor is one whose return type is a `CubicalPath` (e.g.
    /// S¹'s `loop : Path (λ_:I. S¹) base base`). Validation
    /// (`inductive::validate_path_ctor_return_type`) guarantees that when this
    /// returns `Some`, the inductive has no parameters/indices, the constructor
    /// has no fields, and both endpoints are bare point constructors declared
    /// earlier — exactly the shape `build_path_minor_premise_type` assumes.
    pub(crate) fn ctor_path_data(
        ctor_name: &Name,
        all_types: &[InductiveType],
    ) -> Option<(Expr, Expr)> {
        for t in all_types {
            for c in &t.constructors {
                if &c.name == ctor_name {
                    if let ExprKind::CubicalPath { left, right, .. } =
                        &get_return_type(&c.type_).kind
                    {
                        return Some((left.as_ref().clone(), right.as_ref().clone()));
                    }
                    return None;
                }
            }
        }
        None
    }

    /// Build the recursor minor premise for a HIT *path* constructor, directly in
    /// its **final** position within the recursor telescope (so the caller must
    /// NOT apply the usual per-minor lift to the result).
    ///
    /// For S¹'s `loop`, the minor premise is the PathP
    /// `cl : Path (λ i:I. C (loop @ i)) cb cb` where `cb` is the earlier `base`
    /// minor premise. Concretely the produced expression is
    /// `CubicalPath { ty = λ i. (motive) (ctor @ i), left = cb_bvar, right = cb_bvar }`.
    ///
    /// De Bruijn discipline (at this minor's *domain* position):
    /// - `motive_bvar_base` is the index of the conclusion motive `C` *outside*
    ///   the line's interval `λ`. Under that `λ` it becomes `motive_bvar_base + 1`.
    /// - sibling point-constructor endpoints become the corresponding earlier
    ///   minor binder: a point ctor at minor index `j < minor_self_idx` is
    ///   `BVar(minor_self_idx - 1 - j)` (minors are adjacent, so this offset is
    ///   identical in the `rec` and `recOn` telescopes — only `motive_bvar_base`
    ///   differs, which the caller computes).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn build_path_minor_premise_type(
        ctor_name: &Name,
        left: &Expr,
        right: &Expr,
        motive_bvar_base: usize,
        minor_self_idx: usize,
        ind_level_params: &[Name],
        all_types: &[InductiveType],
    ) -> Expr {
        // `ctor @ i` under the interval binder (i = BVar(0)).
        let ctor_levels: Vec<Level> = ind_level_params
            .iter()
            .map(|p| Level::param(p.clone()))
            .collect();
        let ctor_const = Expr::const_(ctor_name.clone(), ctor_levels);
        let path_at_i = Expr::from_kind(ExprKind::CubicalPathApp {
            path: Arc::new(ctor_const),
            arg: Arc::new(Expr::bvar(0)),
        });

        // Motive `C` applied to `(ctor @ i)`, under the interval `λ` (so `+1`).
        let motive = Expr::bvar(Self::usize_to_u32(motive_bvar_base + 1));
        let motive_app = Expr::app(motive, path_at_i);
        let interval = Expr::from_kind(ExprKind::CubicalInterval);
        let line = Expr::lam(BinderInfo::Default, interval, motive_app);

        // Endpoints: rewrite each point-constructor endpoint to its minor binder.
        let left_m = Self::path_endpoint_minor_bvar(left, minor_self_idx, all_types);
        let right_m = Self::path_endpoint_minor_bvar(right, minor_self_idx, all_types);

        Expr::from_kind(ExprKind::CubicalPath {
            ty: Arc::new(line),
            left: Arc::new(left_m),
            right: Arc::new(right_m),
        })
    }

    /// Rewrite a path-constructor endpoint (a bare point constructor) to the
    /// `BVar` that names its minor premise binder at this path minor's domain.
    ///
    /// Validation guarantees the endpoint is a bare `Const(c)` for an earlier
    /// point constructor, so this always finds `j < minor_self_idx` and returns
    /// `BVar(minor_self_idx - 1 - j)`. The unchanged-endpoint fallback is
    /// defensive only (never reached for validated declarations).
    fn path_endpoint_minor_bvar(
        endpoint: &Expr,
        minor_self_idx: usize,
        all_types: &[InductiveType],
    ) -> Expr {
        if endpoint.get_app_args().is_empty() {
            if let ExprKind::Const(c, _) = &endpoint.kind {
                let mut idx = 0usize;
                for t in all_types {
                    for cc in &t.constructors {
                        if &cc.name == c && idx < minor_self_idx {
                            return Expr::bvar(Self::usize_to_u32(minor_self_idx - 1 - idx));
                        }
                        idx += 1;
                    }
                }
            }
        }
        endpoint.clone()
    }
}
