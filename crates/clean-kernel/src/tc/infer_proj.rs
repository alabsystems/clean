// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Projection type inference and batch caching.
//!
//! Extracted from `infer.rs` (#2594) — no logic changes.
//! Contains:
//! - `infer_proj_type` — release-only fast path for `Proj(name, idx, e)`
//! - `infer_proj_type_from` / `_quick` / `_impl` — core projection typing
//! - `cache_projection_field_types_non_prop` — O(n) batch cache fill (non-Prop)
//! - `cache_projection_field_types_prop` — O(n) batch cache fill with Prop validation (#1420)
//! - `instantiate_params` — Pi telescope instantiation
//! - `is_prop` — check if a type is in Prop (its type must be a sort, #14807)

use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::{TypeChecker, TypeError};

impl<'env> TypeChecker<'env> {
    /// Infer the type of a projection expression.
    ///
    /// For a projection `struct_name.idx e`, we need to:
    /// 1. Infer the type of `e`
    /// 2. Verify the type is an application of the struct's inductive type
    /// 3. Look up the constructor to find the field type at index `idx`
    /// 4. Instantiate the field type with the expression's type arguments
    ///
    /// Note: Only used by infer_type_fast_impl (release builds).
    /// Debug builds use infer_type_with_cert_impl which calls infer_proj_type_from directly.
    #[cfg(not(debug_assertions))]
    pub(super) fn infer_proj_type(
        &self,
        struct_name: &Name,
        idx: u32,
        expr: &Expr,
    ) -> Result<Expr, TypeError> {
        // Infer the type of the projected expression
        let expr_type = self.infer_type_fast_impl(expr)?;
        self.infer_proj_type_from(struct_name, idx, expr, &expr_type)
    }

    /// Infer the type of a projection expression with a pre-computed expression type.
    ///
    /// This variant avoids duplicate type inference when the caller has already
    /// computed the type of `expr`.
    pub(super) fn infer_proj_type_from(
        &self,
        struct_name: &Name,
        idx: u32,
        expr: &Expr,
        expr_type: &Expr,
    ) -> Result<Expr, TypeError> {
        self.infer_proj_type_from_impl(struct_name, idx, expr, expr_type, true)
    }

    /// Quick projection typing for def-eq paths.
    ///
    /// Uses the same batch projection cache as the strict path
    /// (`infer_proj_type_from`) but skips Prop-only projection validation
    /// to keep `try_infer_type_quick` fast.
    pub(super) fn infer_proj_type_from_quick(
        &self,
        struct_name: &Name,
        idx: u32,
        expr: &Expr,
        expr_type: &Expr,
    ) -> Option<Expr> {
        self.infer_proj_type_from_impl(struct_name, idx, expr, expr_type, false)
            .ok()
    }

    fn infer_proj_type_from_impl(
        &self,
        struct_name: &Name,
        idx: u32,
        expr: &Expr,
        expr_type: &Expr,
        validate_prop_projection: bool,
    ) -> Result<Expr, TypeError> {
        let proj_expr = Expr::proj(struct_name.clone(), idx, expr.clone());
        if let Some(cached) = self.proj_type_cache.borrow_mut().get(&proj_expr) {
            return Ok(cached);
        }

        // Use whnf_impl since we're called from _impl functions (avoid redundant stack_safe re-entry)
        let expr_type_whnf = self.whnf_impl(expr_type);

        // NOTE: `is_prop(expr_type_whnf)` is computed below, AFTER the structure
        // head, name, single-constructor and argument-count checks, matching
        // Lean 4's `infer_proj` order (type_checker.cpp: `is_prop(type)` runs
        // only once `type` is a fully-applied structure). Since #14807 made
        // `is_prop` require a sort, computing it here — before those checks —
        // would raise `ExpectedSort` on a not-a-structure / under-applied type
        // and mask its structural `InvalidProj*` diagnostic.

        // Extract the inductive type name and universe levels
        // Per Lean 4 (type_checker.cpp:241): const_levels(I) are used to
        // instantiate the constructor's universe level parameters.
        let (type_name, type_levels) = match &expr_type_whnf.get_app_fn().kind {
            ExprKind::Const(name, levels) => (name.clone(), levels.clone()),
            _ => return Err(TypeError::InvalidProjNotStruct(Box::new(expr_type_whnf))),
        };

        // Verify the type matches the struct name in the projection
        if &type_name != struct_name {
            return Err(TypeError::InvalidProjNotStruct(Box::new(expr_type_whnf)));
        }

        let type_args = expr_type_whnf.get_app_args();

        // 3. Look up the inductive type
        let ind_val = self
            .env
            .get_inductive(struct_name)
            .ok_or_else(|| TypeError::UnknownInductive(struct_name.clone()))?;

        // Structures must have exactly one constructor
        if ind_val.constructor_names.len() != 1 {
            return Err(TypeError::InvalidProjNotUniqueConstructor(
                struct_name.clone(),
            ));
        }

        // 4. Look up the constructor
        let ctor_name = &ind_val.constructor_names[0];
        let ctor_val = self
            .env
            .get_constructor(ctor_name)
            .ok_or_else(|| TypeError::UnknownConst(ctor_name.clone()))?;

        // Check index is in bounds
        if idx >= ctor_val.num_fields {
            return Err(TypeError::InvalidProjIndexOutOfBounds(
                idx,
                ctor_val.num_fields,
            ));
        }

        // 5. Get the field type from the constructor
        // The constructor type is: (params...) → (fields...) → Ind params...
        // We need to skip num_params pis and then get the idx-th pi domain
        //
        // Per Lean 4 (type_checker.cpp:241): instantiate universe level params
        // on the constructor type BEFORE walking the Pi telescope. Without this,
        // field types containing Level::Param(...) remain unsubstituted (#2172).
        // Per Lean 4 (instantiate.cpp:249): level count mismatch is a hard error.
        // Previously a debug_assert_eq! — but release builds must also reject
        // mismatched levels (e.g. from malformed .olean imports via add_decl_unchecked).
        if ind_val.level_params.len() != type_levels.len() {
            return Err(TypeError::LevelCountMismatch {
                name: struct_name.clone(),
                expected: ind_val.level_params.len(),
                got: type_levels.len(),
            });
        }
        // In the checker's theory (`tc/level_profile.rs`, DECISIONS R150): Lean's
        // `instantiate_type_lparams` under the Lean theories, so a stored
        // `max`/`imax` is rebuilt by `mk_max`/`mk_imax`, never collapsed.
        let ctor_type = self.instantiate_levels_checked(
            ctor_name,
            &ctor_val.type_,
            &ind_val.level_params,
            &type_levels,
        )?;

        // Instantiate parameters with the type arguments
        // Per Lean 4 (type_checker.cpp:237-238), require exactly num_params + num_indices arguments
        let num_params = ctor_val.num_params as usize;
        let num_indices = ind_val.num_indices as usize;
        let expected_args = num_params + num_indices;
        if type_args.len() != expected_args {
            return Err(TypeError::InvalidProjWrongArgCount {
                got: type_args.len(),
                expected: expected_args,
                num_params,
                num_indices,
            });
        }
        // Performance: Pass iterator directly to avoid intermediate Vec allocation.
        // type_args is SmallVec<&Expr>, we pass the first num_params elements.
        let instantiated_ctor_type =
            self.instantiate_params(&ctor_type, type_args[..num_params].iter().copied());

        // Per Lean 4 (type_checker.cpp:248 / #14807), check if the struct type
        // is in Prop — AFTER the structure/arg-count validation above, exactly
        // where Lean's `infer_proj` computes `is_prop(type)`. Strict projection
        // typing validates Prop-only field constraints; quick paths may skip
        // those checks but must still know whether the type is in Prop to avoid
        // populating the non-Prop batch cache. Propagate inference errors — if
        // we can't determine Prop status, we can't safely type-check the
        // projection (#2208), and since #14807 a type whose type is not a sort
        // is refused here rather than silently treated as non-Prop.
        let is_prop_type = self.is_prop(&expr_type_whnf)?;

        // Precompute and cache all projection field types in one telescope walk
        // when the type is not in Prop. This converts the O(n^2) cost of querying
        // proj 0..n (common in structure eta expansion) into O(n).
        // Both strict and quick paths benefit from this batch cache (#1516).
        if !is_prop_type {
            return self.cache_projection_field_types_non_prop(
                struct_name,
                expr,
                &instantiated_ctor_type,
                ctor_val.num_fields,
                idx,
            );
        }

        // Prop-typed structure: batch-fill the projection cache for all fields,
        // validating Prop constraints along the way. This mirrors the non-Prop batch
        // approach in `cache_projection_field_types_non_prop` but additionally checks
        // that dependency-driving fields and the target field are in Prop.
        //
        // Optimization (#1420): walking the telescope once for ALL fields and caching
        // each intermediate result converts sequential projection queries (proj 0,
        // proj 1, ..., proj N) from O(N^2) to O(N) — subsequent calls hit the cache
        // at the top of this function.
        // Quick path (validate_prop_projection=false): skip Prop validation and
        // caching to avoid poisoning the cache for the strict path. Walk to the
        // target field directly and return. This is O(idx) per call but avoids
        // the correctness issue of caching non-Prop fields as valid.
        if !validate_prop_projection {
            return self.walk_prop_telescope_to_idx(
                struct_name,
                expr,
                &instantiated_ctor_type,
                idx,
                ctor_val.num_fields,
            );
        }

        // Strict path: batch-fill the projection cache for all fields with
        // Prop validation. Converts sequential queries from O(N^2) to O(N) (#1420).
        self.cache_projection_field_types_prop(
            struct_name,
            expr,
            &instantiated_ctor_type,
            ctor_val.num_fields,
            idx,
        )
    }

    fn cache_projection_field_types_non_prop(
        &self,
        struct_name: &Name,
        expr: &Expr,
        instantiated_ctor_type: &Expr,
        num_fields: u32,
        target_idx: u32,
    ) -> Result<Expr, TypeError> {
        let mut current_type = instantiated_ctor_type.clone();
        let mut requested = None;
        for field_idx in 0..num_fields {
            let (domain, body) = self.pi_domain_body_quick(&current_type).ok_or(
                TypeError::InvalidProjIndexOutOfBounds(num_fields.saturating_sub(1), field_idx),
            )?;
            // Build the projection node once: borrow it to instantiate the
            // dependent body, then move the same node into the cache as its key
            // (cache.insert consumes the key). Avoids a second identical
            // Expr::proj (Arc alloc + meta hash) per dependent field.
            let proj_expr = Expr::proj(struct_name.clone(), field_idx, expr.clone());
            if field_idx == target_idx {
                // Cache capacity is a performance setting, not a typing
                // premise. Later inserts in this same walk may evict the
                // requested field before the caller could look it up again.
                requested = Some(domain.clone());
            }
            if field_idx + 1 < num_fields {
                if body.has_loose_bvars() {
                    current_type = body.instantiate(&proj_expr);
                } else {
                    current_type = body;
                }
            }
            {
                let mut cache = self.proj_type_cache.borrow_mut();
                cache.trim_if_needed(self.max_cache_entries);
                cache.insert(proj_expr, domain);
            }
        }
        requested.ok_or(TypeError::InvalidProjIndexOutOfBounds(
            target_idx, num_fields,
        ))
    }

    /// Walk a Prop-typed structure telescope to a specific field index without
    /// caching. Used by the quick path (`validate_prop_projection=false`) to
    /// return the field type without poisoning the cache for the strict path.
    fn walk_prop_telescope_to_idx(
        &self,
        struct_name: &Name,
        expr: &Expr,
        instantiated_ctor_type: &Expr,
        target_idx: u32,
        num_fields: u32,
    ) -> Result<Expr, TypeError> {
        let mut current_type = instantiated_ctor_type.clone();
        for field_idx in 0..=target_idx {
            let (domain, body) = self.pi_domain_body_quick(&current_type).ok_or(
                TypeError::InvalidProjIndexOutOfBounds(num_fields.saturating_sub(1), field_idx),
            )?;
            if field_idx == target_idx {
                return Ok(domain);
            }
            if body.has_loose_bvars() {
                let proj_field = Expr::proj(struct_name.clone(), field_idx, expr.clone());
                current_type = body.instantiate(&proj_field);
            } else {
                current_type = body;
            }
        }
        Err(TypeError::InvalidProjIndexOutOfBounds(
            target_idx, num_fields,
        ))
    }

    /// Batch-fill the projection cache for all fields of a Prop-typed structure.
    ///
    /// Cache only valid proof projections. A non-Prop field is skippable when
    /// the remaining telescope does not depend on it; otherwise it prevents
    /// later projections. Unrelated later fields cannot invalidate an already
    /// derived target (Lean 4 `infer_proj` checks only through the target).
    ///
    /// Walking the full telescope once and caching all field types converts
    /// sequential projection queries from O(N^2) to O(N) (#1420).
    fn cache_projection_field_types_prop(
        &self,
        struct_name: &Name,
        expr: &Expr,
        instantiated_ctor_type: &Expr,
        num_fields: u32,
        target_idx: u32,
    ) -> Result<Expr, TypeError> {
        let mut current_type = instantiated_ctor_type.clone();
        let mut requested = None;
        for field_idx in 0..num_fields {
            let Some((domain, body)) = self.pi_domain_body_quick(&current_type) else {
                return requested.ok_or(TypeError::InvalidProjIndexOutOfBounds(
                    target_idx, field_idx,
                ));
            };
            let dependent = body.has_loose_bvar(0);
            let valid_field = self.is_prop(&domain).and_then(|is_prop| {
                if is_prop {
                    Ok(())
                } else {
                    Err(TypeError::InvalidProjFromProp { field_idx })
                }
            });

            // Build the projection node once: borrow it to instantiate the
            // dependent body, then move the same node into the cache as its key.
            let proj_expr = Expr::proj(struct_name.clone(), field_idx, expr.clone());
            match valid_field {
                Ok(()) => {
                    if field_idx == target_idx {
                        requested = Some(domain.clone());
                    }
                    let mut cache = self.proj_type_cache.borrow_mut();
                    cache.trim_if_needed(self.max_cache_entries);
                    cache.insert(proj_expr.clone(), domain);
                }
                Err(error) if field_idx == target_idx || dependent => {
                    // A later invalid field must not turn a cached successful
                    // target into an error on its first (but not second) call.
                    return requested.ok_or(error);
                }
                Err(_) => {} // Unused data/unknown field: never cache it.
            }
            if field_idx + 1 < num_fields {
                if dependent {
                    current_type = body.instantiate(&proj_expr);
                } else {
                    let Some(lowered) = body.lower_loose_bvars(1) else {
                        return requested.ok_or(TypeError::InvalidProjFromProp { field_idx });
                    };
                    current_type = lowered;
                }
            }
        }
        requested.ok_or(TypeError::InvalidProjIndexOutOfBounds(
            target_idx, num_fields,
        ))
    }

    /// Instantiate the parameters of a type with given arguments.
    ///
    /// Performance: Accepts iterator over &Expr to avoid intermediate Vec allocations
    /// when caller has slice of references (e.g., `&[&Expr]`).
    pub(super) fn instantiate_params<'a>(
        &self,
        ty: &Expr,
        args: impl Iterator<Item = &'a Expr>,
    ) -> Expr {
        let mut result = ty.clone();
        for arg in args {
            // Use whnf_impl since we're called from _impl functions (avoid redundant stack_safe re-entry)
            let result_whnf = self.whnf_impl(&result);
            if let ExprKind::Pi(_, _, body) = &result_whnf.kind {
                result = body.instantiate(arg);
            } else {
                break;
            }
        }
        result
    }

    /// Check if a type is in Prop, using full type inference.
    /// Matches Lean 4's `is_prop` (type_checker.cpp, v4.33.1):
    /// `normalizes_to_zero(sort_level(ensure_sort(infer_type(e))))`.
    ///
    /// Returns `Ok(true)` if the type is in Prop, `Ok(false)` if it is a type
    /// of a higher sort, and `Err(TypeError)` if type inference fails (#2208)
    /// or the type of `ty` does not whnf to a sort. Callers must handle the
    /// error case explicitly rather than treating it as "not Prop".
    pub(super) fn is_prop(&self, ty: &Expr) -> Result<bool, TypeError> {
        let ty_whnf = self.whnf_impl(ty);
        // Try quick path first (avoids full inference overhead)
        if let Some(ty_of_ty) = self.try_infer_type_quick(&ty_whnf) {
            return self.ensure_sort_is_prop(ty_of_ty);
        }
        // Fall back to full type inference (handles Pi, Let, etc.)
        // Per Lean 4 (type_checker.cpp:327): is_prop calls infer_type_core(e, true).
        // Always use infer_only=true to avoid cascading arg type checks from
        // check_type context. Part of #3134.
        let ty_of_ty = self.infer_type_infer_only(&ty_whnf)?;
        self.ensure_sort_is_prop(ty_of_ty)
    }

    /// Lean 4's `ensure_sort` on the type of a type, then whether its level is
    /// zero (`Level::is_zero` is up to normalization: `imax 1 0` is zero).
    ///
    /// SOUNDNESS (leanprover/lean4#14807): a type whose own type does not whnf
    /// to a sort is ill-formed. Answering `Ok(false)` ("not a proposition") for
    /// it let projection typing skip its Prop-only field guard, so a data field
    /// could be projected out of a proof. Lean's fix replaces `whnf` with
    /// `ensure_sort`, raising `(kernel) type expected`; this is that fix.
    fn ensure_sort_is_prop(&self, ty_of_ty: Expr) -> Result<bool, TypeError> {
        let ty_of_ty_whnf = self.whnf_impl(&ty_of_ty);
        match &ty_of_ty_whnf.kind {
            ExprKind::Sort(l) => Ok(l.is_zero()),
            // Clean's other sort: the type-of-type invariant (`tc/infer.rs`)
            // admits `Sort | SProp`, so `SProp` passes `ensure_sort`, and its
            // verdict is the one it had before this guard.
            ExprKind::SProp => Ok(false),
            _ => Err(TypeError::ExpectedSort {
                ty: Box::new(ty_of_ty),
                location: self.expr_loc_snapshot(),
            }),
        }
    }
}
