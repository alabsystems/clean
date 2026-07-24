// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Derive handlers for automatic typeclass instance generation
//!
//! This module implements the `deriving` clause functionality for structures
//! and inductive types. It generates typeclass instances for:
//! - BEq (equality comparison)
//! - Repr (string representation)
//! - Hashable (hash function)
//! - Inhabited (default value)
//! - DecidableEq (decidable equality)
//! - Ord (ordering comparison)
//! - Nonempty (type is nonempty)
//! - ToString (string conversion)
//! - Functor (functorial mapping)
//! - Foldable (folding operations)
//! - Traversable (traversable container)
//!
//! ## Architecture
//!
//! The derive handlers are implemented as methods on `ElabCtx` via a separate
//! `impl` block. This keeps the derive logic cleanly separated while still
//! having full access to the elaboration context.
//!
//! Each derive handler follows a similar pattern:
//! 1. Build the instance type (e.g., `BEq Point`)
//! 2. Build the instance value (constructor + method implementations)
//! 3. For parametric types, wrap with type parameter and constraint bindings
//!
//! ## Parametric Structures
//!
//! For parametric structures like `structure Pair (α : Type) (β : Type)`,
//! derived instances include constraints for each type parameter:
//! ```text
//! instance [BEq α] [BEq β] : BEq (Pair α β) where ...
//! ```

mod beq_inductive;
mod beq_parametric;
mod beq_parametric_recursive;
mod beq_recursive;
mod decidable_eq_enum;
mod decidable_eq_fielded;
mod decidable_eq_list_recursive;
mod decidable_eq_parametric;
mod decidable_eq_parametric_multi;
mod decidable_eq_parametric_recursive;
mod decidable_eq_recursive;
mod hashable;
mod inductive;
mod inductive_ext;
mod nested_detect;
mod ord_parametric;
mod ord_parametric_recursive;
mod structure;
mod structure_ext;

use super::{DerivedInstance, ElabCtx};
use crate::derive::instance_name;
use crate::derive_handlers::user_derive_handler_shape;
use crate::ElabError;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};
use clean_parser::{SurfaceBinder, SurfaceCtor, SurfaceField};

/// Extract the universe level from a type expression.
///
/// For `Sort(l)`, returns `Some(l)`.
/// For `Pi(_, _, body)`, recurses into the body (strips binders).
/// Returns `None` for other expression kinds.
fn extract_sort_level(ty: &Expr) -> Option<Level> {
    match ty.kind() {
        ExprKind::Sort(l) => Some(l.clone()),
        ExprKind::Pi(_, _, body) => extract_sort_level(body),
        _ => None,
    }
}

/// For a monomorphic type (no type parameters), replace all `Level::Param`
/// in the instance expressions with the concrete universe level of the target type.
///
/// This fixes #3393/#3396: `mk_const` generates fresh universe params (e.g., `u_0`)
/// for universe-polymorphic helper constants like `DecidableEq`, `Eq`, etc.
/// For monomorphic types these should be concrete levels (e.g., `Succ(Zero)` for Type),
/// not free parameters.
fn concretize_monomorphic_instance(instance: &mut DerivedInstance, target_level: &Level) {
    if instance.level_params.is_empty() {
        return;
    }
    let subst: Vec<(Name, Level)> = instance
        .level_params
        .iter()
        .map(|name| (name.clone(), target_level.clone()))
        .collect();
    instance.ty = instance.ty.instantiate_level_params(&subst);
    instance.val = instance.val.instantiate_level_params(&subst);
    instance.level_params = vec![];
}

/// Given a class's first-parameter sort *template* (the `Sort(level)` domain of
/// the class constant, where `level` mentions the class's single universe param)
/// and the concrete sort level `L` of the target type, solve for the level the
/// class constant must be instantiated at.
///
/// Clean's two relevant param kinds:
///   - `Inhabited (α : Sort u)` → template level `Param(u)` ⇒ class level = `L`.
///   - `BEq (α : Type u)` i.e. `Sort(Succ u)` → class level = `pred(L)`.
///
/// This is the per-class adjustment the spurious `mk_const`-generated universe
/// params (`BEq.{u_i}`, `BEq.beq.{u_j}`, …) must collapse to. Without it,
/// concretizing every class's params to the *result sort* over-shoots for
/// `Type u` classes (BEq/Hashable/Repr/Ord/DecidableEq), yielding e.g.
/// `BEq.{Succ Zero}` (= `BEq : Type 1 → …`) applied to a `Type 0` target.
///
/// Returns `None` when the template/target shape is unsupported, leaving the
/// caller to fall back to the raw result sort.
fn solve_class_level(param_sort_template: &Level, target_sort: &Level) -> Option<Level> {
    // Count the `Succ` offset of the template `Param(u) + off`
    // (e.g. `u` for Inhabited ⇒ off 0, `Succ u` for BEq ⇒ off 1).
    let mut base = param_sort_template;
    let mut off = 0u32;
    while let Level::Succ(inner) = base {
        off += 1;
        base = inner;
    }
    if !matches!(base, Level::Param(_)) {
        return None;
    }
    // Solve `Param(u) + off = target_sort` ⇒ `u = target_sort - off` by peeling
    // `off` `Succ` constructors off the target sort.
    let mut level = target_sort;
    for _ in 0..off {
        match level {
            Level::Succ(pred) => level = pred,
            _ => return None,
        }
    }
    Some(level.clone())
}

#[derive(Debug, Clone)]
struct OpenHandlerBinder {
    binder_info: BinderInfo,
    domain: Expr,
    fvar: FVarId,
}

/// Derive handlers for structures and inductives
impl<'a> ElabCtx<'a> {
    // =========================================================================
    // Structure derive handlers
    // =========================================================================

    /// Generate derived instances for the given structure and deriving clauses
    pub(super) fn generate_derived_instances(
        &mut self,
        struct_name: &Name,
        _universe_params: &[String],
        binders: &[SurfaceBinder],
        fields: &[SurfaceField],
        struct_ty: &Expr,
        deriving: &[String],
    ) -> Result<Vec<DerivedInstance>, ElabError> {
        use super::elab_types::collect_level_params;

        let mut instances = Vec::new();

        // Collect field names for deriving handlers
        let field_names: Vec<Name> = fields.iter().map(|f| Name::from_string(&f.name)).collect();

        // For monomorphic types (no type parameters), extract the concrete
        // universe level so we can replace spurious Level::Param values.
        // Fixes #3396.
        //
        // Track E gap (2): parametric structures whose type parameters are at a
        // *concrete* universe (e.g. `structure Pair (α β : Type)` — α, β at
        // `Sort 1`/Type 0, so the structure's result sort is `Sort 1` with NO
        // declared universe params) also need this concretization. Without it,
        // `mk_const(Inhabited)` / `mk_const(BEq)` invent a fresh `u_i` for the
        // class constant applied to `Pair α β`, and that free `u_i` is never
        // constrained to `Succ Zero`, so the kernel rejects the instance with
        // "expected Sort(Param u_i), got Sort(Succ Zero)". The fix concretizes
        // the spurious params to the structure's (param-free) result sort.
        //
        // Genuinely universe-polymorphic structures (`structure Pair.{u v}
        // (α : Type u) (β : Type v)`) have a result sort that *contains*
        // `Level::Param`; those params are legitimate and must be threaded, not
        // collapsed — so we only concretize when the result sort is param-free.
        let concrete_level = extract_sort_level(struct_ty).filter(|l| !l.has_params());

        for class_name in deriving {
            if let Some(mut instance) =
                self.derive_instance(struct_name, binders, fields, &field_names, class_name)?
            {
                // Compute the universe level params actually used by this instance's
                // type and value expressions. Fixes #3393: without this, instances
                // for concrete types would reference u_0 etc. without declaring them.
                instance.level_params = collect_level_params(&[&instance.ty, &instance.val]);

                // Fixes #3396: For monomorphic types, mk_const generates fresh
                // Level::Param values (e.g., u_0) for universe-polymorphic helpers
                // like DecidableEq, Eq, etc. These must be resolved to concrete
                // levels — declaring them as free parameters causes kernel type
                // check failures ("expected Sort(Param(u_0)), got Sort(Succ(Zero))").
                //
                // Track E: the spurious params belong to the derived class's own
                // universe family (`BEq.{u}`, `BEq.beq.{u}`, …), so they collapse
                // to the level the class wants for a target at this sort — NOT the
                // raw result sort. For `Type u` classes (BEq/Hashable/Repr/Ord/
                // DecidableEq) that is the *predecessor* of the result sort.
                if let Some(ref result_sort) = concrete_level {
                    let level = self
                        .class_concretize_level(class_name, result_sort)
                        .unwrap_or_else(|| result_sort.clone());
                    concretize_monomorphic_instance(&mut instance, &level);
                }

                crate::derive::admit_generated_instance(
                    self.env,
                    class_name,
                    &struct_name.to_string(),
                    &instance.name,
                    &instance.ty,
                    &instance.val,
                )
                .map_err(|error| ElabError::Unsupported {
                    feature: error.to_string(),
                })?;

                instances.push(instance);
            }
        }

        Ok(instances)
    }

    /// Compute the universe level the derived class's spurious params should
    /// collapse to, given the (param-free) result sort of the target type.
    ///
    /// Looks up the class's first-parameter sort template (`Sort u` for
    /// `Inhabited`, `Sort (Succ u)` i.e. `Type u` for `BEq`/`Hashable`/…) and
    /// solves it against `result_sort`. Returns `None` when the class isn't a
    /// recognizable single-param class, leaving the caller to fall back to the
    /// raw result sort (the historical monomorphic behavior).
    fn class_concretize_level(&self, class_name: &str, result_sort: &Level) -> Option<Level> {
        let name = Name::from_string(class_name);
        let class_ty = if let Some(ind) = self.env.get_inductive(&name) {
            ind.type_.clone()
        } else {
            self.env.get_const(&name)?.type_.clone()
        };
        // First Pi domain = the class parameter; its sort level is the template.
        let ExprKind::Pi(_, domain, _) = class_ty.kind() else {
            return None;
        };
        let ExprKind::Sort(template) = domain.kind() else {
            return None;
        };
        solve_class_level(template, result_sort)
    }

    /// Check if a class constant exists in the environment.
    ///
    /// Used to guard derive handlers for classes that may not be in the
    /// prelude (e.g. Repr, Hashable). Without this guard, derive would
    /// produce broken instances referencing non-existent constants.
    /// Part of #3396.
    fn class_exists_in_env(&self, class_name: &str) -> bool {
        let name = Name::from_string(class_name);
        self.env.get_const(&name).is_some() || self.env.get_inductive(&name).is_some()
    }

    /// Derive a single type class instance for a structure
    ///
    /// Returns None if the class is not supported for deriving
    fn derive_instance(
        &mut self,
        struct_name: &Name,
        binders: &[SurfaceBinder],
        fields: &[SurfaceField],
        field_names: &[Name],
        class_name: &str,
    ) -> Result<Option<DerivedInstance>, ElabError> {
        if let Some(instance) = self.try_user_defined_handler(struct_name, binders, class_name)? {
            return Ok(Some(instance));
        }

        let builtin = match class_name {
            "BEq" => Some(self.derive_beq(struct_name, binders, fields, field_names)?),
            "Repr" if self.class_exists_in_env("Repr") => {
                Some(self.derive_repr(struct_name, binders, fields)?)
            }
            "Hashable" if self.class_exists_in_env("Hashable") => {
                Some(self.derive_hashable(struct_name, binders, fields)?)
            }
            "Inhabited" => Some(self.derive_inhabited(struct_name, binders, fields)?),
            "DecidableEq" => {
                Some(self.derive_decidable_eq(struct_name, binders, fields, field_names)?)
            }
            "Ord" => Some(self.derive_ord(struct_name, binders, fields, field_names)),
            "Nonempty" if binders.is_empty() && fields.is_empty() => {
                Some(self.derive_nonempty(struct_name, binders, fields))
            }
            "Nonempty" => {
                return Err(ElabError::Unsupported {
                    feature: format!(
                        "deriving Nonempty for `{struct_name}` requires a closed nullary constructor"
                    ),
                });
            }
            "ToString" | "Functor" | "Foldable" | "Traversable" => {
                return Err(ElabError::Unsupported {
                    feature: format!(
                        "deriving {class_name} for `{struct_name}` has no authenticated structural implementation"
                    ),
                });
            }
            _ => None,
        };
        if builtin.is_some() {
            return Ok(builtin);
        }

        Err(ElabError::Unsupported {
            feature: format!(
                "no available derive handler for class `{class_name}` on `{struct_name}`; \
                 explicit deriving clauses are never silently skipped"
            ),
        })
    }

    // =========================================================================
    // Inductive derive handlers
    // =========================================================================

    /// Generate derived instances for an inductive type
    ///
    /// For inductives, deriving requires pattern matching on constructors.
    /// E.g., for `inductive Bool | false | true deriving BEq`:
    /// ```text
    /// instance : BEq Bool where
    ///   beq a b := match a, b with
    ///     | Bool.false, Bool.false => true
    ///     | Bool.true, Bool.true => true
    ///     | _, _ => false
    /// ```
    pub(super) fn generate_derived_instances_inductive(
        &mut self,
        registered_candidate: &clean_kernel::Environment,
        ind_name: &Name,
        _universe_params: &[String],
        binders: &[SurfaceBinder],
        ctors: &[SurfaceCtor],
        ind_ty: &Expr,
        deriving: &[String],
    ) -> Result<Vec<DerivedInstance>, ElabError> {
        use super::elab_types::collect_level_params;

        let mut instances = Vec::new();

        // Collect constructor names
        let ctor_names: Vec<Name> = ctors
            .iter()
            .map(|c| Name::from_string(&format!("{}.{}", ind_name, c.name)))
            .collect();

        // For monomorphic inductives, extract concrete universe level.
        // Same fix as for structures — see #3396. Track E gap (2) extends this
        // to parametric inductives whose result sort is param-free (concrete
        // `Type 0` parameters); genuinely universe-polymorphic inductives keep
        // their params (result sort contains `Level::Param`).
        let concrete_level = extract_sort_level(ind_ty).filter(|l| !l.has_params());

        for class_name in deriving {
            if let Some(mut instance) = self.derive_instance_inductive(
                registered_candidate,
                ind_name,
                binders,
                ctors,
                &ctor_names,
                class_name,
            )? {
                // Compute the universe level params actually used by this instance.
                // Same fix as for structures — see #3393.
                instance.level_params = collect_level_params(&[&instance.ty, &instance.val]);

                // Fixes #3396: resolve spurious Level::Param for monomorphic
                // types, class-aware (Track E — see structure path above).
                if let Some(ref result_sort) = concrete_level {
                    let level = self
                        .class_concretize_level(class_name, result_sort)
                        .unwrap_or_else(|| result_sort.clone());
                    concretize_monomorphic_instance(&mut instance, &level);
                }

                crate::derive::admit_generated_instance(
                    self.env,
                    class_name,
                    &ind_name.to_string(),
                    &instance.name,
                    &instance.ty,
                    &instance.val,
                )
                .map_err(|error| ElabError::Unsupported {
                    feature: error.to_string(),
                })?;

                instances.push(instance);
            }
        }

        Ok(instances)
    }

    /// Derive a single instance for an inductive type
    fn derive_instance_inductive(
        &mut self,
        registered_candidate: &clean_kernel::Environment,
        ind_name: &Name,
        binders: &[SurfaceBinder],
        ctors: &[SurfaceCtor],
        ctor_names: &[Name],
        class_name: &str,
    ) -> Result<Option<DerivedInstance>, ElabError> {
        if let Some(instance) = self.try_user_defined_handler(ind_name, binders, class_name)? {
            return Ok(Some(instance));
        }

        let builtin = match class_name {
            "BEq" => Some(self.derive_beq_inductive(ind_name, binders, ctors, ctor_names)?),
            "Repr" if self.class_exists_in_env("Repr") => {
                let bootstrap = self.derive_repr_inductive(ind_name, binders, ctors, ctor_names)?;
                Some(crate::derive::materialize_inductive_repr(
                    registered_candidate,
                    ind_name,
                    &bootstrap,
                )?)
            }
            "Hashable" if self.class_exists_in_env("Hashable") => {
                Some(self.derive_hashable_inductive(ind_name, binders, ctors, ctor_names)?)
            }
            "Inhabited" => {
                Some(self.derive_inhabited_inductive(ind_name, binders, ctors, ctor_names)?)
            }
            "DecidableEq" => {
                Some(self.derive_decidable_eq_inductive(ind_name, binders, ctors, ctor_names)?)
            }
            "Ord" => Some(self.derive_ord_inductive(ind_name, binders, ctors, ctor_names)?),
            "Nonempty"
                if binders.is_empty()
                    && !ctor_names.is_empty()
                    && decidable_eq_enum::all_ctors_nullary(ctors) =>
            {
                self.derive_nonempty_inductive(ind_name, binders, ctors, ctor_names)
            }
            "Nonempty" => {
                return Err(ElabError::Unsupported {
                    feature: format!(
                        "deriving Nonempty for `{ind_name}` requires a monomorphic inductive with a closed nullary constructor"
                    ),
                });
            }
            "ToString" | "Functor" | "Foldable" | "Traversable" => {
                return Err(ElabError::Unsupported {
                    feature: format!(
                        "deriving {class_name} for `{ind_name}` has no authenticated structural implementation"
                    ),
                });
            }
            _ => None,
        };
        if builtin.is_some() {
            return Ok(builtin);
        }

        Err(ElabError::Unsupported {
            feature: format!(
                "no available derive handler for class `{class_name}` on `{ind_name}`; \
                 explicit deriving clauses are never silently skipped"
            ),
        })
    }

    // =========================================================================
    // Helper methods for parametric instances
    // =========================================================================

    /// Build the parametric struct type applied to bound type variables
    ///
    /// For a structure like `structure Pair (α : Type) (β : Type)`,
    /// this builds `Pair α β` where α and β are bound variables at the given offset.
    ///
    /// `offset` is the de Bruijn offset for accessing the type parameters:
    /// - For instance type: offset = number of instance params (for [BEq α] etc.)
    /// - For function body: offset = number of lambdas before accessing params
    fn build_parametric_target_type(
        &mut self,
        type_name: &Name,
        num_params: usize,
        offset: usize,
    ) -> Expr {
        let mut result = self.mk_const(type_name);

        // Apply type parameter variables in order (from outermost to innermost)
        // With de Bruijn indices: if we have (α : Type) (β : Type), then
        // inside a body with `offset` additional binders:
        // - α is at index (offset + num_params - 1 - 0) = offset + num_params - 1
        // - β is at index (offset + num_params - 1 - 1) = offset + num_params - 2
        for i in 0..num_params {
            let var_idx = offset + num_params - 1 - i;
            // SAFETY: de Bruijn index bounded by context depth
            let var_idx_u32 = u32::try_from(var_idx).unwrap_or(u32::MAX);
            result = Expr::app(result, Expr::bvar(var_idx_u32));
        }

        result
    }

    fn build_parametric_struct_type(
        &mut self,
        type_name: &Name,
        num_params: usize,
        offset: usize,
    ) -> Expr {
        self.build_parametric_target_type(type_name, num_params, offset)
    }

    /// Build the instance type with type parameter bindings and constraints
    ///
    /// For `BEq (Pair α β)` with params `(α : Type) (β : Type)`, this builds:
    /// `∀ (α : Type) (β : Type) [BEq α] [BEq β], BEq (Pair α β)`
    ///
    /// Returns: (instance_type, number_of_constraint_params)
    fn build_parametric_instance_type(
        &mut self,
        type_name: &Name,
        binders: &[SurfaceBinder],
        class_name: &Name,
    ) -> (Expr, usize) {
        let num_params = binders.len();

        if num_params == 0 {
            // Non-parametric: just `Class StructName`
            let struct_type = self.mk_const(type_name);
            let instance_ty = Expr::app(self.mk_const(class_name), struct_type);
            return (instance_ty, 0);
        }

        // For parametric structures, we need instance constraints for each type parameter
        // The number of constraint params depends on the class requirements.
        // For BEq/DecidableEq/Hashable: need constraint for each param
        // For Repr/Inhabited: also need constraint for each param
        let num_constraints = num_params;

        // Build the core type: Class (Struct α β ...)
        // At this point, we're inside num_params type binders + num_constraints constraint binders
        let struct_applied =
            self.build_parametric_target_type(type_name, num_params, num_constraints);
        let core_instance_ty = Expr::app(self.mk_const(class_name), struct_applied);

        // Wrap with instance constraints: [Class α] → [Class β] → ...
        // These are applied in reverse order (innermost first), i.e. the loop
        // first creates the constraint for the LAST param (c_β) as the innermost
        // Pi, then c_α as the next one out.
        //
        // de Bruijn for `Class (bvar k)` in constraint c_i's domain: at c_i's
        // domain context, ALL type-param binders are outer, AND every *outer*
        // constraint binder (c_0 … c_{i-1}, which wrap c_i) is also in scope.
        // - position of param i among type params, innermost-first: num_params-1-i
        // - constraints c_0..c_{i-1} wrapping c_i add another `i` binders
        // ⇒ index = (num_params - 1 - i) + i = num_params - 1 (constant!).
        //
        // The previous formula used just `num_params - 1 - i`, which forgot the
        // `i` wrapping constraint binders and made c_β reference c_α instead of
        // β — surfacing as a Track-E parametric-deriving kernel mismatch.
        let mut result = core_instance_ty;
        for i in (0..num_params).rev() {
            let param_idx = (num_params - 1 - i) + i;
            // SAFETY: de Bruijn index bounded by number of parameters
            let param_idx_u32 = u32::try_from(param_idx).unwrap_or(u32::MAX);
            let constraint_ty = Expr::app(self.mk_const(class_name), Expr::bvar(param_idx_u32));

            result = Expr::pi(BinderInfo::InstImplicit, constraint_ty, result);
        }

        // Wrap with type parameter bindings: (α : Type) → (β : Type) → ...
        // These are applied in reverse order (innermost first)
        for _i in (0..num_params).rev() {
            // Each type param has type `Type` (Sort 1)
            let type_sort = Expr::sort(Level::succ(Level::zero()));
            result = Expr::pi(BinderInfo::Implicit, type_sort, result);
        }

        (result, num_constraints)
    }

    /// Wrap an instance value with lambdas for type parameters and constraints
    ///
    /// For a parametric instance, the value needs to be a function taking
    /// the type parameters and their class instances as arguments.
    fn wrap_parametric_instance_value(
        &mut self,
        inner_val: Expr,
        num_params: usize,
        class_name: &Name,
    ) -> Expr {
        if num_params == 0 {
            return inner_val;
        }

        let mut result = inner_val;

        // Wrap with lambdas for instance constraints (innermost first = last
        // param). The binder-type de Bruijn indices MUST mirror
        // `build_parametric_instance_type` exactly: param i is at
        // `(num_params - 1 - i) + i = num_params - 1` in constraint c_i's
        // domain (the `+ i` accounts for the wrapping outer constraint
        // binders). Using only `num_params - 1 - i` here made the value's
        // constraint annotations disagree with the instance type.
        for i in (0..num_params).rev() {
            let param_idx = (num_params - 1 - i) + i;
            // SAFETY: de Bruijn index bounded by number of parameters
            let param_idx_u32 = u32::try_from(param_idx).unwrap_or(u32::MAX);
            let constraint_ty = Expr::app(self.mk_const(class_name), Expr::bvar(param_idx_u32));
            result = Expr::lam(BinderInfo::InstImplicit, constraint_ty, result);
        }

        // Wrap with lambdas for type parameters (innermost first = last param)
        for _i in (0..num_params).rev() {
            let type_sort = Expr::sort(Level::succ(Level::zero()));
            result = Expr::lam(BinderInfo::Implicit, type_sort, result);
        }

        result
    }

    fn build_open_target_type(&mut self, type_name: &Name, param_fvars: &[FVarId]) -> Expr {
        let mut result = self.mk_const(type_name);
        for fvar in param_fvars {
            result = Expr::app(result, Expr::fvar(*fvar));
        }
        result
    }

    fn open_user_handler_type(
        &mut self,
        handler_ty: &Expr,
        binder_count: usize,
    ) -> (Vec<OpenHandlerBinder>, Expr) {
        let mut curr = handler_ty.clone();
        let mut binders: Vec<OpenHandlerBinder> = Vec::with_capacity(binder_count);

        for _ in 0..binder_count {
            let ExprKind::Pi(binder_info, domain, body) = curr.kind() else {
                break;
            };
            let opened_args: Vec<Expr> = binders
                .iter()
                .rev()
                .map(|b: &OpenHandlerBinder| Expr::fvar(b.fvar))
                .collect();
            let domain = if opened_args.is_empty() {
                domain.as_ref().clone()
            } else {
                domain.instantiate_rev(&opened_args)
            };
            let fvar = self.fresh_fvar();
            binders.push(OpenHandlerBinder {
                binder_info: binder_info.info,
                domain,
                fvar,
            });
            curr = body.as_ref().clone();
        }

        let opened_args: Vec<Expr> = binders
            .iter()
            .rev()
            .map(|b: &OpenHandlerBinder| Expr::fvar(b.fvar))
            .collect();
        let codomain = if opened_args.is_empty() {
            curr
        } else {
            curr.instantiate_rev(&opened_args)
        };
        (binders, codomain)
    }

    fn try_user_defined_handler(
        &mut self,
        type_name: &Name,
        binders: &[SurfaceBinder],
        class_name: &str,
    ) -> Result<Option<DerivedInstance>, ElabError> {
        let class = Name::from_string(class_name);
        let Some(handler_names) = self.env.get_derive_handlers(&class) else {
            return Ok(None);
        };

        for handler_name in handler_names.iter().rev() {
            let handler_const = self.mk_const(handler_name);
            let handler_ty = self.infer_type(&handler_const)?;
            let Some(shape) = user_derive_handler_shape(&handler_ty) else {
                continue;
            };
            if shape.class_name != class {
                continue;
            }

            let (opened_binders, opened_codomain) =
                self.open_user_handler_type(&handler_ty, shape.binder_count);
            let app_args = opened_codomain.get_app_args();
            if app_args.len() != 1 {
                continue;
            }

            let target_binder_pos = shape.binder_count
                - 1
                - usize::try_from(shape.target_bvar_idx).unwrap_or(usize::MAX);
            let Some(target_binder) = opened_binders.get(target_binder_pos) else {
                continue;
            };
            let ExprKind::FVar(target_fvar) = app_args[0].kind() else {
                continue;
            };
            if *target_fvar != target_binder.fvar {
                continue;
            }

            let decl_param_fvars: Vec<FVarId> =
                (0..binders.len()).map(|_| self.fresh_fvar()).collect();
            let target_type = self.build_open_target_type(type_name, &decl_param_fvars);
            let mut kept_binders = Vec::with_capacity(opened_binders.len().saturating_sub(1));
            let mut handler_args = Vec::with_capacity(opened_binders.len());

            for (idx, binder) in opened_binders.iter().enumerate() {
                if idx == target_binder_pos {
                    handler_args.push(target_type.clone());
                } else {
                    handler_args.push(Expr::fvar(binder.fvar));
                    kept_binders.push(OpenHandlerBinder {
                        binder_info: binder.binder_info,
                        domain: binder.domain.subst_fvar(target_binder.fvar, &target_type),
                        fvar: binder.fvar,
                    });
                }
            }

            let mut instance_ty = opened_codomain.subst_fvar(target_binder.fvar, &target_type);
            let mut instance_val = Expr::apps(handler_const, handler_args);

            for binder in kept_binders.iter().rev() {
                instance_ty = instance_ty.abstract_fvar(binder.fvar);
                instance_ty = Expr::pi(binder.binder_info, binder.domain.clone(), instance_ty);
                instance_val = instance_val.abstract_fvar(binder.fvar);
                instance_val = Expr::lam(binder.binder_info, binder.domain.clone(), instance_val);
            }

            let type_sort = Expr::sort(Level::succ(Level::zero()));
            for fvar in decl_param_fvars.iter().rev() {
                instance_ty = instance_ty.abstract_fvar(*fvar);
                instance_ty = Expr::pi(BinderInfo::Implicit, type_sort.clone(), instance_ty);
                instance_val = instance_val.abstract_fvar(*fvar);
                instance_val = Expr::lam(BinderInfo::Implicit, type_sort.clone(), instance_val);
            }

            return Ok(Some(DerivedInstance {
                name: instance_name(class_name, type_name),
                class_name: class,
                ty: instance_ty,
                val: instance_val,
                priority: 100,
                level_params: vec![],
            }));
        }

        Ok(None)
    }
}
