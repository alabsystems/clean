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
//! - `is_prop` — check if a type is in Prop

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

        // Per Lean 4 (type_checker.cpp:248), check if struct type is in Prop.
        // Strict projection typing validates Prop-only field constraints; quick
        // paths may skip those checks but must still know whether the type is
        // in Prop to avoid populating the non-Prop batch cache.
        // Propagate inference errors — if we can't determine Prop status,
        // we can't safely type-check the projection (#2208).
        let is_prop_type = self.is_prop(&expr_type_whnf)?;

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
        let ctor_type = if ind_val.level_params.is_empty() {
            ctor_val.type_.clone()
        } else {
            ctor_val
                .type_
                .instantiate_level_params_direct(&ind_val.level_params, &type_levels)
        };

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

        // Precompute and cache all projection field types in one telescope walk
        // when the type is not in Prop. This converts the O(n^2) cost of querying
        // proj 0..n (common in structure eta expansion) into O(n).
        // Both strict and quick paths benefit from this batch cache (#1516).
        if !is_prop_type {
            self.cache_projection_field_types_non_prop(
                struct_name,
                expr,
                &instantiated_ctor_type,
                ctor_val.num_fields,
            )?;
            if let Some(cached) = self.proj_type_cache.borrow_mut().get(&proj_expr) {
                return Ok(cached);
            }
            return Err(TypeError::InvalidProjIndexOutOfBounds(
                idx,
                ctor_val.num_fields,
            ));
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
        )?;
        if let Some(cached) = self.proj_type_cache.borrow_mut().get(&proj_expr) {
            return Ok(cached);
        }
        Err(TypeError::InvalidProjIndexOutOfBounds(
            idx,
            ctor_val.num_fields,
        ))
    }

    fn cache_projection_field_types_non_prop(
        &self,
        struct_name: &Name,
        expr: &Expr,
        instantiated_ctor_type: &Expr,
        num_fields: u32,
    ) -> Result<(), TypeError> {
        let mut current_type = instantiated_ctor_type.clone();
        for field_idx in 0..num_fields {
            let (domain, body) = self.pi_domain_body_quick(&current_type).ok_or(
                TypeError::InvalidProjIndexOutOfBounds(num_fields.saturating_sub(1), field_idx),
            )?;
            // Build the projection node once: borrow it to instantiate the
            // dependent body, then move the same node into the cache as its key
            // (cache.insert consumes the key). Avoids a second identical
            // Expr::proj (Arc alloc + meta hash) per dependent field.
            let proj_expr = Expr::proj(struct_name.clone(), field_idx, expr.clone());
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
        Ok(())
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
    /// Mirrors `cache_projection_field_types_non_prop` but additionally validates
    /// that each field type is in Prop (Lean 4 type_checker.cpp:252-263). For
    /// dependent bodies, the dependency-driving field's domain must be in Prop.
    ///
    /// Walking the full telescope once and caching all field types converts
    /// sequential projection queries from O(N^2) to O(N) (#1420).
    fn cache_projection_field_types_prop(
        &self,
        struct_name: &Name,
        expr: &Expr,
        instantiated_ctor_type: &Expr,
        num_fields: u32,
    ) -> Result<(), TypeError> {
        let mut current_type = instantiated_ctor_type.clone();
        for field_idx in 0..num_fields {
            let (domain, body) = self.pi_domain_body_quick(&current_type).ok_or(
                TypeError::InvalidProjIndexOutOfBounds(num_fields.saturating_sub(1), field_idx),
            )?;

            // Per Lean 4 (type_checker.cpp:263): projected field type must be in Prop.
            if !self.is_prop(&domain)? {
                return Err(TypeError::InvalidProjFromProp { field_idx });
            }

            // Build the projection node once: borrow it to instantiate the
            // dependent body, then move the same node into the cache as its key.
            // Avoids a second identical Expr::proj per dependent field.
            let proj_expr = Expr::proj(struct_name.clone(), field_idx, expr.clone());
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
        Ok(())
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
    /// Matches Lean 4's `is_prop` (type_checker.cpp:327): `whnf(infer_type(e)) == mk_Prop()`.
    ///
    /// Returns `Ok(true)` if the type is in Prop, `Ok(false)` if not, and
    /// `Err(TypeError)` if type inference fails. Callers must handle the error
    /// case explicitly rather than treating inference failure as "not Prop".
    /// Fixes #2208.
    pub(super) fn is_prop(&self, ty: &Expr) -> Result<bool, TypeError> {
        let ty_whnf = self.whnf_impl(ty);
        // Try quick path first (avoids full inference overhead)
        if let Some(ty_of_ty) = self.try_infer_type_quick(&ty_whnf) {
            let ty_of_ty_whnf = self.whnf_impl(&ty_of_ty);
            return Ok(matches!(&ty_of_ty_whnf.kind, ExprKind::Sort(l) if l.is_zero()));
        }
        // Fall back to full type inference (handles Pi, Let, etc.)
        // Per Lean 4 (type_checker.cpp:327): is_prop calls infer_type_core(e, true).
        // Always use infer_only=true to avoid cascading arg type checks from
        // check_type context. Part of #3134.
        let ty_of_ty = self.infer_type_infer_only(&ty_whnf)?;
        let ty_of_ty_whnf = self.whnf_impl(&ty_of_ty);
        Ok(matches!(&ty_of_ty_whnf.kind, ExprKind::Sort(l) if l.is_zero()))
    }
}
