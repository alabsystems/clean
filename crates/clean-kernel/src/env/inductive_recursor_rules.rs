// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Recursor rule RHS construction and BVar remapping for inductive types.
//!
//! Builds the RHS lambda terms for `.rec` / `.casesOn` / `.recOn` rules
//! and provides BVar remapping helpers for index expressions.
//! Extracted from `inductive_recursor.rs` for maintainability.

use crate::expr::{BinderData, BinderInfo, Expr, ExprKind};
use crate::inductive::{get_return_type, InductiveType};
use crate::level::Level;
use crate::name::Name;
use smallvec::SmallVec;

use super::Environment;

impl Environment {
    /// Count the number of leading Pi binders in an expression.
    ///
    /// For `Pi(_, _, Pi(_, _, T))` returns 2. For a non-Pi expression returns 0.
    /// Used to determine how many lambda wrappers are needed for reflexive IH (#1784).
    pub(crate) fn count_pi_binders(expr: &Expr) -> usize {
        let mut count = 0;
        let mut current = expr;
        while let ExprKind::Pi(_, _, body) = &current.kind {
            count += 1;
            current = body;
        }
        count
    }

    /// Collect Pi domain types and binder info from the leading Pi binders
    /// of an expression.
    ///
    /// For `Pi(bi₀, D₀, Pi(bi₁, D₁, body))` returns `[(bi₀, D₀), (bi₁, D₁)]`.
    /// Used to extract actual domain types for reflexive IH wrapping (#1784).
    pub(crate) fn collect_pi_domains(expr: &Expr) -> Vec<(BinderData, Expr)> {
        let mut domains = Vec::new();
        let mut current = expr;
        while let ExprKind::Pi(bi, domain, body) = &current.kind {
            domains.push((*bi, (**domain).clone()));
            current = body;
        }
        domains
    }

    /// Remap BVars in an index expression extracted from a (possibly reflexive)
    /// recursive field's return type (#1782, #1784).
    pub(crate) fn remap_residual_index_bvars(
        expr: &Expr,
        field_idx: usize,
        np: usize,
        nf: usize,
        n_minors: usize,
        nm: usize,
        n_pis: usize,
    ) -> Expr {
        Self::remap_residual_bvars_impl(expr, n_pis, &|ctor_k| {
            if ctor_k < field_idx {
                // Field reference
                let field_j = field_idx - 1 - ctor_k;
                nf - 1 - field_j
            } else {
                // Param reference
                let param_j = np - 1 - (ctor_k - field_idx);
                nf + n_minors + nm + np - 1 - param_j
            }
        })
    }

    /// Remap BVars in an index expression for the minor premise type context
    /// (#1782, #1784).
    pub(crate) fn remap_residual_index_bvars_for_minor(
        expr: &Expr,
        field_idx: usize,
        nf: usize,
        ih_offset: usize,
        num_motives: usize,
        n_pis: usize,
    ) -> Expr {
        Self::remap_residual_bvars_impl(expr, n_pis, &|ctor_k| {
            if ctor_k < field_idx {
                // Field reference
                let field_j = field_idx - 1 - ctor_k;
                ih_offset + nf - 1 - field_j
            } else {
                // Param reference: ctor_k - field_idx gives the 0-based
                // param offset (0 = closest to fields). Unlike
                // remap_residual_index_bvars where the double reversal
                // (np-1-offset then np-1-param_j) cancels out, here we
                // use the offset directly since the target formula adds
                // param_j without reversing. ALL motive binders sit between
                // the params and the minor's field telescope — the shift is
                // `num_motives`, not a hardcoded 1 (mutual-block fix
                // 2026-08-04; the old constant was correct only for
                // single-type blocks and pointed a param reference at a
                // motive whenever num_motives > 1).
                let param_j = ctor_k - field_idx;
                ih_offset + nf + num_motives + param_j
            }
        })
    }

    /// Binder-aware BVar remap walker shared by the two residual-index
    /// remappers above.
    ///
    /// `depth` counts locally bound variables: the wrapper Pis of a reflexive
    /// field (`n_pis` at the top call) PLUS any binder crossed inside the
    /// index expression itself. Historically this walker recursed only into
    /// `App`, so an index argument containing a binder — e.g. the const-map
    /// index `fun _ => β` in `Std.DHashMap.Raw.WF` / `Std.DTreeMap.Internal.
    /// Impl.WF` — kept its ctor-context BVars verbatim under the lambda,
    /// producing IH premises (and iota rule RHS) with wrong de Bruijn indices.
    /// A variable below `depth` is locally bound (identity); anything at or
    /// above it lives in the ctor field context and is remapped by `remap`,
    /// then re-shifted by `depth`.
    fn remap_residual_bvars_impl(
        expr: &Expr,
        depth: usize,
        remap: &dyn Fn(usize) -> usize,
    ) -> Expr {
        match &expr.kind {
            ExprKind::BVar(k) => {
                let k = *k as usize;
                if k < depth {
                    // Locally bound (wrapper Pi or a binder inside the index
                    // expression) → identity.
                    expr.clone()
                } else {
                    Expr::bvar(Self::usize_to_u32(remap(k - depth) + depth))
                }
            }
            ExprKind::App(f, a) => Expr::app(
                Self::remap_residual_bvars_impl(f, depth, remap),
                Self::remap_residual_bvars_impl(a, depth, remap),
            ),
            ExprKind::Lam(bd, ty, body) => Expr::lam(
                *bd,
                Self::remap_residual_bvars_impl(ty, depth, remap),
                Self::remap_residual_bvars_impl(body, depth + 1, remap),
            ),
            ExprKind::Pi(bd, ty, body) => Expr::pi(
                *bd,
                Self::remap_residual_bvars_impl(ty, depth, remap),
                Self::remap_residual_bvars_impl(body, depth + 1, remap),
            ),
            ExprKind::Let(name, ty, val, body, non_dep) => Expr::let_named(
                name.clone(),
                Self::remap_residual_bvars_impl(ty, depth, remap),
                Self::remap_residual_bvars_impl(val, depth, remap),
                Self::remap_residual_bvars_impl(body, depth + 1, remap),
                *non_dep,
            ),
            ExprKind::Proj(struct_name, idx, e) => Expr::proj(
                struct_name.clone(),
                *idx,
                Self::remap_residual_bvars_impl(e, depth, remap),
            ),
            ExprKind::MData(md, e) => {
                Expr::mdata(md.clone(), Self::remap_residual_bvars_impl(e, depth, remap))
            }
            // FVar, Sort, Const, Lit, and mode-specific leaves have no BVars —
            // return as-is.
            _ => expr.clone(),
        }
    }

    /// Build the RHS lambda for a recursor rule (#1406, #1782, #1784, #3237).
    ///
    /// Produces a lambda term matching Lean 4's `comp_rhs` structure:
    /// ```text
    /// λ params. λ motives. λ minors. λ fields.
    ///   minor_k field₀ ... fieldₙ IH₀ ... IHₘ
    /// ```
    ///
    /// For mutual inductives, each recursive field's IH uses the recursor of
    /// the type that field belongs to (Lean 4 inductive.cpp:738).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn build_recursor_rule_rhs(
        &self,
        rec_name: &Name,
        rec_level_params: &[Name],
        num_params: u32,
        num_motives: u32,
        num_fields: u32,
        recursive_flags: &[bool],
        field_types: &[Expr],
        num_ctors: usize,
        ctor_idx: usize,
        eliminator_type: &Expr,
        all_types: &[InductiveType],
    ) -> Expr {
        let nf = num_fields as usize;
        let np = num_params as usize;
        let nm = num_motives as usize;
        let n_minors = num_ctors; // num_minors == num_ctors for standard rec
                                  // Total lambda binders: params + motives + minors + fields
        let total_binders = np + nm + n_minors + nf;

        // Inside the body, de Bruijn indices (innermost = BVar(0)):
        // fields:  BVar(0) .. BVar(nf-1)      field_last=BVar(0), field_first=BVar(nf-1)
        // minors:  BVar(nf) .. BVar(nf+n_minors-1)
        // motives: BVar(nf+n_minors) .. BVar(nf+n_minors+nm-1)
        // params:  BVar(nf+n_minors+nm) .. BVar(total_binders-1)

        // The minor for ctor_idx: minors go minor_0 (outermost) to minor_{n-1} (innermost)
        // minor_0 = BVar(nf + n_minors - 1), minor_{ctor_idx} = BVar(nf + n_minors - 1 - ctor_idx)
        let minor_bvar = Self::usize_to_u32(nf + n_minors - 1 - ctor_idx);
        let mut body = Expr::bvar(minor_bvar);

        // Apply all fields to minor: minor field₀ ... fieldₙ₋₁
        for i in 0..nf {
            // field_i: outermost field = BVar(nf-1), innermost = BVar(0)
            let field_bvar = Self::usize_to_u32(nf - 1 - i);
            body = Expr::app(body, Expr::bvar(field_bvar));
        }

        // Apply IH for each recursive field.
        // IH_j = rec@{level_params} params motives minors field_rec_j
        let rec_levels: SmallVec<[Level; 2]> = rec_level_params
            .iter()
            .map(|n| Level::param(n.clone()))
            .collect();

        for (i, &is_recursive) in recursive_flags.iter().enumerate() {
            if is_recursive {
                // Count Pi binders in the field type (#1784).
                let n_pis = field_types.get(i).map(Self::count_pi_binders).unwrap_or(0);

                // When n_pis > 0, the IH body is under n_pis additional lambda
                // binders. All BVar references to params/motives/minors/fields
                // must be shifted up by n_pis to account for these.
                let shift = n_pis;

                // For mutual inductives, each recursive field's IH uses the recursor
                // of the type that field returns to (Lean 4 inductive.cpp:738).
                // Determine the target recursor name from the field type's return type.
                let ih_rec_name = if all_types.len() > 1 {
                    if let Some(field_ty) = field_types.get(i) {
                        let ret_ty = get_return_type(field_ty);
                        let head = ret_ty.get_app_fn();
                        if let ExprKind::Const(name, _) = &head.kind {
                            Name::from_string(&format!("{name}.rec"))
                        } else {
                            rec_name.clone()
                        }
                    } else {
                        rec_name.clone()
                    }
                } else {
                    rec_name.clone()
                };

                // Build: ih_rec@{levels} params motives minors [indices] (field xs)
                let mut ih = Expr::const_(ih_rec_name, rec_levels.clone());

                // Apply params (outermost group)
                for j in 0..np {
                    let param_bvar = Self::usize_to_u32(total_binders - 1 - j + shift);
                    ih = Expr::app(ih, Expr::bvar(param_bvar));
                }

                // Apply motives
                for j in 0..nm {
                    let motive_bvar = Self::usize_to_u32(nf + n_minors + nm - 1 - j + shift);
                    ih = Expr::app(ih, Expr::bvar(motive_bvar));
                }

                // Apply minors
                for j in 0..n_minors {
                    let minor_bvar_idx = Self::usize_to_u32(nf + n_minors - 1 - j + shift);
                    ih = Expr::app(ih, Expr::bvar(minor_bvar_idx));
                }

                // Apply index arguments for indexed inductives (#1782, #1784).
                // The index count is intrinsic to the FIELD's target type: its
                // return-type args after the shared params are exactly that
                // target's residual indices (empty for a 0-index target). It
                // must NOT be gated on the num_indices of the type whose rule
                // is being built — a mutual SIBLING field can carry residual
                // indices even when the current type has none, and the old
                // gate dropped them, minting an IH the subject-reduction
                // validator rejects (found via the nested-local lift's
                // indexed-container fixture, 2026-08-04).
                if let Some(field_ty) = field_types.get(i) {
                    let indices = self.get_constructor_return_indices(field_ty, num_params);
                    for idx_expr in indices {
                        let remapped = Self::remap_residual_index_bvars(
                            &idx_expr, i, np, nf, n_minors, nm, n_pis,
                        );
                        ih = Expr::app(ih, remapped);
                    }
                }

                // Apply the recursive field as major premise.
                let mut major = Expr::bvar(Self::usize_to_u32(nf - 1 - i + shift));
                for k in (0..n_pis).rev() {
                    major = Expr::app(major, Expr::bvar(Self::usize_to_u32(k)));
                }
                ih = Expr::app(ih, major);

                // Wrap IH in lambda binders for Pi-bound variables (#1784).
                let pi_domains = field_types
                    .get(i)
                    .map(Self::collect_pi_domains)
                    .unwrap_or_default();
                for (k, (bi, domain)) in pi_domains.iter().enumerate().rev() {
                    let remapped =
                        Self::remap_residual_index_bvars(domain, i, np, nf, n_minors, nm, k);
                    ih = Expr::lam(*bi, remapped, ih);
                }

                body = Expr::app(body, ih);
            }
        }

        // Extract actual domain types from the eliminator type's Pi binders.
        // The eliminator type has structure: Π params. Π motive. Π minors. Π rest...
        // Reference: Lean 4 comp_rhs (inductive.cpp:744) uses actual types from
        // local declarations, not dummy Sort(0).
        let dummy_ty = Expr::sort(Level::zero());
        let mut elim_cursor = eliminator_type.clone();
        let mut param_domain_types: Vec<Expr> = Vec::with_capacity(np);
        for _ in 0..np {
            if let ExprKind::Pi(_, domain, body) = &elim_cursor.kind {
                param_domain_types.push((**domain).clone());
                elim_cursor = (**body).clone();
            } else {
                param_domain_types.push(dummy_ty.clone());
            }
        }
        let mut motive_domain_types: Vec<Expr> = Vec::with_capacity(nm);
        for _ in 0..nm {
            if let ExprKind::Pi(_, domain, body) = &elim_cursor.kind {
                motive_domain_types.push((**domain).clone());
                elim_cursor = (**body).clone();
            } else {
                motive_domain_types.push(dummy_ty.clone());
            }
        }
        let mut minor_domain_types: Vec<Expr> = Vec::with_capacity(n_minors);
        for _ in 0..n_minors {
            if let ExprKind::Pi(_, domain, body) = &elim_cursor.kind {
                minor_domain_types.push((**domain).clone());
                elim_cursor = (**body).clone();
            } else {
                minor_domain_types.push(dummy_ty.clone());
            }
        }

        // Wrap body in lambda binders with actual types:
        // λ params. λ motives. λ minors. λ fields. body
        let mut result = body;

        // Fields (innermost) — lift constructor field types to account for
        // motive+minor binders inserted between params and fields.
        // field_types[i] has BVars: 0..i-1 = prior fields, i.. = params.
        // In the RHS lambda, params are shifted by (nm + n_minors), so
        // lift_from(i, nm + n_minors) shifts param refs while keeping field refs.
        let lift_amount = Self::usize_to_u32(nm + n_minors);
        for i in (0..nf).rev() {
            let field_ty = if let Some(ft) = field_types.get(i) {
                if lift_amount > 0 {
                    ft.lift_from(i as u32, lift_amount)
                } else {
                    ft.clone()
                }
            } else {
                dummy_ty.clone()
            };
            result = Expr::lam(BinderInfo::Default, field_ty, result);
        }
        // Minors (innermost minor first wrapping outward)
        for minor_ty in minor_domain_types.iter().rev() {
            result = Expr::lam(BinderInfo::Default, minor_ty.clone(), result);
        }
        // Motives
        for motive_ty in motive_domain_types.iter().rev() {
            result = Expr::lam(BinderInfo::Default, motive_ty.clone(), result);
        }
        // Params (innermost param first wrapping outward)
        for param_ty in param_domain_types.iter().rev() {
            result = Expr::lam(BinderInfo::Default, param_ty.clone(), result);
        }

        result
    }
}
