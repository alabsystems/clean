// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Instance declaration elaboration.

use crate::instances::{extract_class_app, DEFAULT_PRIORITY};
use crate::ElabError;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};
use clean_parser::{DeclModifiers, SurfaceBinder, SurfaceExpr, SurfaceFieldAssign};

use super::{convert_binder_info, ElabCtx, ElabResult};

impl<'a> ElabCtx<'a> {
    /// Elaborate an instance declaration.
    ///
    /// An instance provides an implementation of a type class for specific types.
    ///
    /// ```text
    /// instance : Add Nat where
    ///   add := Nat.add
    /// ```
    ///
    /// This elaborates to a definition whose value is the class constructor
    /// applied to the field values, and registers the instance in the instance table.
    pub(super) fn elab_instance(
        &mut self,
        name: Option<&str>,
        _universe_params: &[String],
        binders: &[SurfaceBinder],
        class_type: &SurfaceExpr,
        fields: &[SurfaceFieldAssign],
        priority: Option<u32>,
        modifiers: &DeclModifiers,
    ) -> Result<ElabResult, ElabError> {
        // `scoped instance` requires an enclosing namespace to scope TO —
        // Lean rejects it at the root ("scoped attributes must be used inside
        // namespaces"). Loud here so it can never silently register as a
        // global instance (B99).
        if modifiers.scope == clean_parser::DeclScope::Scoped && self.namespace_prefix.is_empty() {
            return Err(ElabError::Unsupported {
                feature: "`scoped instance` outside of a namespace (scoped attributes must be \
                          used inside namespaces)"
                    .to_string(),
            });
        }

        // Collect fvars for binders so we can abstract over them
        let mut binder_fvars = Vec::new();
        let mut binder_types = Vec::new();
        let mut binder_infos = Vec::new();

        // Elaborate binders (e.g., `[Add α]` for dependent instances)
        // Track which binders are instance-implicit for local instance resolution
        let mut inst_implicit_indices = Vec::new();
        for (idx, binder) in binders.iter().enumerate() {
            let binder_ty = if let Some(t) = &binder.ty {
                self.elaborate(t)?
            } else {
                let binder_sort = Expr::sort(self.fresh_universe_param());
                self.fresh_meta(binder_sort)
            };
            let bi = convert_binder_info(binder.info);
            let fvar = self.push_local(binder.name.clone(), binder_ty.clone());

            // Register instance-implicit binders for nested resolution
            if bi == BinderInfo::InstImplicit {
                self.push_local_instance(fvar, binder_ty.clone());
                inst_implicit_indices.push(idx);
            }

            binder_fvars.push(fvar);
            binder_types.push(binder_ty);
            binder_infos.push(bi);
        }

        // Elaborate the class type (e.g., `Add Nat`)
        let class_ty_expr = self.elaborate(class_type)?;
        let class_ty = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&class_ty_expr));
        let class_ty_whnf = self.whnf(&class_ty);

        // Extract the class name and arguments from the type
        let (class_name, class_args) = extract_class_app(&class_ty_whnf).ok_or_else(|| {
            ElabError::NotImplemented(format!(
                "instance class type must be a class application, got: {class_ty:?}"
            ))
        })?;

        // Detect the short-form instance syntax: `instance : Class := expr`.
        // The parser represents this as a single pseudo-field named `_value`
        // (see clean-parser/src/grammar/decl/class_instance.rs:225). In this
        // case, the user is providing the entire instance value (typically an
        // anonymous constructor like `⟨0⟩`), which we elaborate against the
        // class type as expected type. This path does NOT require the class
        // to have been registered via `register_structure_fields`, so it works
        // for built-in classes like `Inhabited` that are registered only via
        // `add_inductive` during kernel prelude initialization (#3534).
        let is_short_form = fields.len() == 1 && fields[0].name == "_value";
        if is_short_form {
            return self.elab_instance_short_form(
                name,
                &binder_fvars,
                &binder_types,
                &binder_infos,
                &inst_implicit_indices,
                &class_ty,
                &class_name,
                &class_args,
                &fields[0].val,
                priority,
                modifiers,
            );
        }

        // Look up the class (which is a structure/inductive) to get field info.
        // Long-form instances (`where` syntax) iterate the class fields in
        // constructor order. Natively-declared classes carry a clean-side
        // field-name table; an *imported* class (loaded from a real `.olean`)
        // ships only its projection functions and a single-constructor
        // inductive, so it has NO field-name table. In that case we cannot
        // iterate field names here, but the structure-literal path already
        // resolves fields positionally (via the projection functions) and fills
        // omitted defaulted methods from `<Class>.<field>._default`. So for an
        // imported class we desugar `instance : C T where f := v` to the
        // structure literal `({ f := v } : C T)` and reuse that machinery,
        // keeping imported and native long-form instances on one code path.
        let field_names = match self.env.get_structure_field_names(&class_name) {
            Some(names) => names.to_vec(),
            None => {
                return self.elab_instance_via_struct_lit(
                    name,
                    &binder_fvars,
                    &binder_types,
                    &binder_infos,
                    &inst_implicit_indices,
                    &class_ty,
                    &class_name,
                    &class_args,
                    class_type,
                    fields,
                    priority,
                    modifiers,
                );
            }
        };
        let ind_info = self.env.get_inductive(&class_name).ok_or_else(|| {
            ElabError::NotImplemented(format!(
                "class {class_name} not found in environment (must be declared as a class/structure first)"
            ))
        })?;

        // The constructor name is ClassName.mk
        let ctor_name = Name::from_string(&format!("{class_name}.mk"));
        let ctor_info = self
            .env
            .get_const(&ctor_name)
            .ok_or_else(|| ElabError::UnknownIdent(ctor_name.to_string()))?;

        // If any declared field is OMITTED, hand off to the structure-literal
        // path. It materializes defaulted methods from `<Class>.<field>._default`
        // and assembles `extends`-parent subobjects from the flattened field
        // spellings (an omitted `toParent` field) — neither of which the
        // field-by-field native path below can do — while still reporting a
        // genuinely default-less missing field precisely
        // (`MissingStructureFields`). The all-fields-provided common case falls
        // through to the native path unchanged. B12 (`p04` default methods,
        // `p09` `extends` instances).
        let provided_fields: std::collections::HashSet<_> =
            fields.iter().map(|f| &f.name).collect();
        if field_names
            .iter()
            .any(|f| !provided_fields.contains(&f.to_string()))
        {
            return self.elab_instance_via_struct_lit(
                name,
                &binder_fvars,
                &binder_types,
                &binder_infos,
                &inst_implicit_indices,
                &class_ty,
                &class_name,
                &class_args,
                class_type,
                fields,
                priority,
                modifiers,
            );
        }

        // Build the instance value by applying the constructor to field values
        // Order fields according to the class definition
        // Extract universe levels from class_ty_expr to use for the constructor.
        // If class_ty_expr is `MyRing.{0} Nat`, we want the constructor `MyRing.mk.{0}`.
        let ctor_levels: Vec<Level> = {
            // Get levels from the class constant in class_ty_expr
            let class_const = class_ty_whnf.get_app_fn();
            if let ExprKind::Const(_, levels) = class_const.kind() {
                levels.to_vec()
            } else {
                // Fallback: use fresh params like elab_ident does
                ctor_info
                    .level_params
                    .iter()
                    .map(|_| self.fresh_universe_param())
                    .collect()
            }
        };
        if ctor_info.level_params.len() != ctor_levels.len() {
            return Err(ElabError::TypeMismatch {
                expected: format!(
                    "{} universe levels for {}.mk",
                    ctor_info.level_params.len(),
                    class_name
                ),
                actual: format!("{} universe levels supplied", ctor_levels.len()),
            });
        }
        let level_subst: Vec<(Name, Level)> = ctor_info
            .level_params
            .iter()
            .cloned()
            .zip(ctor_levels.iter().cloned())
            .collect();
        let ctor_type = ctor_info.type_.instantiate_level_params(&level_subst);

        let mut instance_val = Expr::const_(ctor_name.clone(), ctor_levels);
        let mut result_ty = ctor_type;

        // Class constructor parameters are part of the telescope. Seed them from the
        // target class application so later field elaboration sees the correct field types.
        if class_args.len() < ind_info.num_params as usize {
            return Err(ElabError::TypeMismatch {
                expected: format!(
                    "{} class parameters for {}",
                    ind_info.num_params, class_name
                ),
                actual: format!("{} parameters supplied", class_args.len()),
            });
        }
        for arg in class_args.iter().take(ind_info.num_params as usize) {
            result_ty = self.whnf(&result_ty);
            let body_ty = match result_ty.kind() {
                ExprKind::Pi(_, _, body_ty) => body_ty.instantiate(arg),
                _ => {
                    return Err(ElabError::TypeMismatch {
                        expected: format!(
                            "constructor telescope for {} with {} parameters",
                            class_name, ind_info.num_params
                        ),
                        actual: format!("{result_ty:?}"),
                    })
                }
            };
            instance_val = Expr::app(instance_val, arg.clone());
            result_ty = self.metas.instantiate(&body_ty);
        }

        let (mut instance_val, mut result_ty) = self.insert_implicit_args(instance_val, &result_ty);

        // Then apply the field values in order
        for field_name in &field_names {
            result_ty = self.whnf(&result_ty);
            let expected_field_ty = match result_ty.kind() {
                ExprKind::Pi(_, arg_ty, _) => Some(self.metas.instantiate(arg_ty)),
                _ => None,
            };
            let field_name_str = field_name.to_string();
            let field_assign = fields
                .iter()
                .find(|f| f.name == field_name_str)
                .ok_or_else(|| {
                    ElabError::NotImplemented(format!(
                        "missing field {field_name_str} in instance for {class_name}"
                    ))
                })?;

            // Instance field values are TERM positions: unknown idents are loud,
            // never auto-bound (B03; Lean auto-binds only in decl headers).
            let field_val = self.with_term_body_scope(|this| {
                this.elaborate_with_expected_type(&field_assign.val, expected_field_ty.clone())
            })?;

            if let Some(exp_ty) = expected_field_ty.as_ref() {
                self.enforce_expr_type(&field_val, exp_ty)?;
            }

            instance_val = Expr::app(instance_val, field_val.clone());
            if let ExprKind::Pi(_, _, body_ty) = result_ty.kind() {
                result_ty = body_ty.instantiate(&field_val);
            }
        }

        // Generate instance name if not provided (freshened; see
        // `instance_decl_name`).
        let instance_name = self.instance_decl_name(name, &class_name, &class_args);

        let priority = priority.unwrap_or(DEFAULT_PRIORITY);

        let result_ty = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&result_ty));
        if !self.try_unify(&result_ty, &class_ty) {
            return Err(ElabError::TypeMismatch {
                expected: format!("{class_ty:?}"),
                actual: format!("{result_ty:?}"),
            });
        }

        // Close the instance over its binder telescope: the explicit
        // `{a}`/`[C a]` binders AND the auto-bound implicits (`a` in `[C a]`).
        // See `close_instance_telescope`.
        let (final_ty, final_val) = self.close_instance_telescope(
            &class_ty,
            &instance_val,
            &binder_fvars,
            &binder_types,
            &binder_infos,
            &inst_implicit_indices,
        );

        self.ensure_no_residual_fvars(
            "instance",
            &instance_name.to_string(),
            &final_ty,
            Some(&final_val),
        )?;

        // Register the instance
        self.instances.add_instance(
            instance_name.clone(),
            class_name.clone(),
            final_val.clone(),
            final_ty.clone(),
            priority,
        );

        // Use self.universe_params which includes auto-bound params (#1324)
        Ok(ElabResult::Instance {
            name: instance_name,
            universe_params: self
                .universe_params
                .iter()
                .map(|s| Name::from_string(s))
                .collect(),
            class_name,
            ty: final_ty,
            val: final_val,
            priority,
            modifiers: *modifiers,
        })
    }

    /// Elaborate a long-form `instance : Class T where …` declaration for a
    /// class that has NO clean-side field-name table — i.e. an **imported**
    /// class loaded from a real `.olean`, which ships only its projection
    /// functions and a single-constructor inductive.
    ///
    /// The native long-form path iterates the field-name table to drive
    /// constructor application; an import has no such table, so historically
    /// the long-form path rejected imported classes outright. The
    /// structure-literal path (`elab_struct_lit`), by contrast, already handles
    /// imports correctly: it resolves field assignments positionally through
    /// the projection functions and fills omitted defaulted methods from the
    /// shipped `<Class>.<field>._default` definition. We therefore desugar the
    /// `where` block into the structure literal `({ field := val, … } : Class T)`
    /// — using the *same* surface class-type expression as the annotation so
    /// the still-pushed instance binders remain in scope — and reuse that
    /// machinery. The kernel re-checks the produced constructor application via
    /// the final `enforce_expr_type`, so a wrong field or default is rejected
    /// rather than passed silently.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn elab_instance_via_struct_lit(
        &mut self,
        name: Option<&str>,
        binder_fvars: &[FVarId],
        binder_types: &[Expr],
        binder_infos: &[BinderInfo],
        inst_implicit_indices: &[usize],
        class_ty: &Expr,
        class_name: &Name,
        class_args: &[Expr],
        class_type: &SurfaceExpr,
        fields: &[SurfaceFieldAssign],
        priority: Option<u32>,
        modifiers: &DeclModifiers,
    ) -> Result<ElabResult, ElabError> {
        // Desugar the `where` fields into a structure literal annotated with the
        // class type, then elaborate it through `elab_struct_lit`. Cloning the
        // already-parsed `class_type` keeps the binders (pushed as locals before
        // this point) in scope when the annotation is re-elaborated.
        let struct_type = Some(Box::new(class_type.clone()));
        let instance_val = self.elab_struct_lit(&struct_type, &None, fields)?;

        // Re-check the produced value against the class type. `elab_struct_lit`
        // already kernel-checks each field against the constructor telescope;
        // this guards the overall shape (and unifies any remaining metavariables
        // / universe levels against the expected class type).
        self.enforce_expr_type(&instance_val, class_ty)?;

        // Generate instance name if not provided (freshened; see
        // `instance_decl_name`).
        let instance_name = self.instance_decl_name(name, class_name, class_args);

        let priority = priority.unwrap_or(DEFAULT_PRIORITY);

        // Close over the binder telescope + auto-bound implicits (mirrors the
        // native long-form and short-form paths). See `close_instance_telescope`.
        let (final_ty, final_val) = self.close_instance_telescope(
            class_ty,
            &instance_val,
            binder_fvars,
            binder_types,
            binder_infos,
            inst_implicit_indices,
        );

        self.ensure_no_residual_fvars(
            "instance",
            &instance_name.to_string(),
            &final_ty,
            Some(&final_val),
        )?;

        self.instances.add_instance(
            instance_name.clone(),
            class_name.clone(),
            final_val.clone(),
            final_ty.clone(),
            priority,
        );

        Ok(ElabResult::Instance {
            name: instance_name,
            universe_params: self
                .universe_params
                .iter()
                .map(|s| Name::from_string(s))
                .collect(),
            class_name: class_name.clone(),
            ty: final_ty,
            val: final_val,
            priority,
            modifiers: *modifiers,
        })
    }

    /// Elaborate the short-form instance syntax: `instance : Class := expr`.
    ///
    /// Unlike the long-form `where`-syntax path, this does NOT require the
    /// class to be registered in `structure_fields`. The user supplies the
    /// entire instance value (typically an anonymous constructor `⟨...⟩`),
    /// which we elaborate with the class type as the expected type. This
    /// dispatches through the same general term-elaboration path that `def`
    /// uses (e.g., `elab_anonymous_ctor`), so it works uniformly for
    /// user-defined classes AND kernel-builtin classes like `Inhabited` that
    /// are registered only via `add_inductive` during prelude initialization.
    ///
    /// Fix for #3534.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn elab_instance_short_form(
        &mut self,
        name: Option<&str>,
        binder_fvars: &[FVarId],
        binder_types: &[Expr],
        binder_infos: &[BinderInfo],
        inst_implicit_indices: &[usize],
        class_ty: &Expr,
        class_name: &Name,
        class_args: &[Expr],
        value: &SurfaceExpr,
        priority: Option<u32>,
        modifiers: &DeclModifiers,
    ) -> Result<ElabResult, ElabError> {
        // Elaborate the value expression against the class type as the expected
        // type. For `⟨0⟩`-style bodies this dispatches through
        // `elab_anonymous_ctor`, which looks up the inductive via
        // `get_inductive` (not `get_structure_field_names`) and therefore
        // works for classes registered only via `add_inductive`.
        // The value is a TERM position: unknown idents are loud, never
        // auto-bound (B03; Lean auto-binds only in decl headers).
        let instance_val = self.with_term_body_scope(|this| {
            this.elaborate_with_expected_type(value, Some(class_ty.clone()))
        })?;

        // Verify the elaborated value has the expected class type.
        self.enforce_expr_type(&instance_val, class_ty)?;

        // Generate instance name if not provided (freshened; see
        // `instance_decl_name`).
        let instance_name = self.instance_decl_name(name, class_name, class_args);

        let priority = priority.unwrap_or(DEFAULT_PRIORITY);

        // Close over the binder telescope + auto-bound implicits. See
        // `close_instance_telescope`.
        let (final_ty, final_val) = self.close_instance_telescope(
            class_ty,
            &instance_val,
            binder_fvars,
            binder_types,
            binder_infos,
            inst_implicit_indices,
        );

        self.ensure_no_residual_fvars(
            "instance",
            &instance_name.to_string(),
            &final_ty,
            Some(&final_val),
        )?;

        // Register the instance.
        self.instances.add_instance(
            instance_name.clone(),
            class_name.clone(),
            final_val.clone(),
            final_ty.clone(),
            priority,
        );

        Ok(ElabResult::Instance {
            name: instance_name,
            universe_params: self
                .universe_params
                .iter()
                .map(|s| Name::from_string(s))
                .collect(),
            class_name: class_name.clone(),
            ty: final_ty,
            val: final_val,
            priority,
            modifiers: *modifiers,
        })
    }

    /// Close an instance's elaborated type and value over its full binder
    /// telescope before `add_decl`, so the registered declaration has no free
    /// variables.
    ///
    /// Two layers, innermost-out:
    /// 1. **Explicit binders** — the surface `{a}` / `[C a]` binders the user
    ///    wrote, abstracted into a Pi/Lam telescope (innermost binder last).
    /// 2. **Auto-bound implicits** — the type variables Lean auto-binds because
    ///    an instance-implicit premise mentions them (`a` in
    ///    `instance [C a] : C (List a)`). These are closed OUTSIDE the explicit
    ///    binders, because an explicit binder's *type* (`C a`) references them.
    ///
    /// This mirrors the `def`/`theorem` discipline in `elab_definition_inner`:
    /// `elab_def_body` builds the explicit-binder Pi/Lam telescope and then
    /// `wrap_with_auto_implicits` closes the auto-bounds around it. The instance
    /// paths previously abstracted only the explicit binders and never took the
    /// auto-implicits, so a parametric instance registered with the auto-bound
    /// `a` still free → "Declaration contains free variables" (gap sweep B26).
    ///
    /// Also pops the pushed local instances and binder locals, and instantiates
    /// level constraints collected during unification.
    fn close_instance_telescope(
        &mut self,
        class_ty: &Expr,
        instance_val: &Expr,
        binder_fvars: &[FVarId],
        binder_types: &[Expr],
        binder_infos: &[BinderInfo],
        inst_implicit_indices: &[usize],
    ) -> (Expr, Expr) {
        let mut final_ty = self.metas.instantiate(class_ty);
        let mut final_val = self.metas.instantiate(instance_val);

        // Layer 1: explicit binders (innermost last). `abstract_fvar` recurses
        // into already-built inner Pi binder types, so a dependent binder whose
        // type mentions an earlier binder is abstracted correctly.
        for i in (0..binder_fvars.len()).rev() {
            final_ty = final_ty.abstract_fvar(binder_fvars[i]);
            final_val = final_val.abstract_fvar(binder_fvars[i]);
            final_ty = Expr::pi(binder_infos[i], binder_types[i].clone(), final_ty);
            final_val = Expr::lam(binder_infos[i], binder_types[i].clone(), final_val);
        }

        // Pop local instances (reverse of push order) and the explicit binder
        // locals. Auto-implicit locals are removed by `take_auto_implicits`.
        for _ in inst_implicit_indices {
            self.pop_local_instance();
        }
        for _ in 0..binder_fvars.len() {
            self.pop_local();
        }

        // Layer 2: auto-bound implicits, closed OUTSIDE the explicit binders.
        // `wrap_with_auto_implicits` abstracts each auto-implicit fvar over the
        // whole telescope (including the embedded explicit-binder types that
        // reference it), then wraps the outermost implicit `{a}` Pi/Lam.
        let auto_implicits = self.take_auto_implicits();
        let (final_ty, final_val) =
            Self::wrap_with_auto_implicits(final_ty, final_val, &auto_implicits);

        // Substitute level constraints collected during unification.
        let final_ty = self.metas.instantiate_levels(&final_ty);
        let final_val = self.metas.instantiate_levels(&final_val);
        (final_ty, final_val)
    }

    /// The declaration name for an `instance`: a user-supplied name verbatim,
    /// or the auto-generated `inst<Class><Arg1>…` **freshened** against the
    /// environment so a second anonymous instance for the same class becomes
    /// `inst…_1`, `inst…_2`, … rather than colliding (`Duplicate declaration`).
    ///
    /// Lean: `mkInstanceName` builds `inst<Class><args>` and `mkUnusedBaseName`
    /// appends the numeric suffix (`src/Lean/Elab/DeclNameGen.lean`). Freshening
    /// against `env.get_const` is exactly the kernel's duplicate-name test, and
    /// every declaration is elaborated with a fresh `ElabCtx` rebuilt from the
    /// env, so earlier same-file instances are already visible here. B12
    /// (`classes_instances/p05,p06,p16`).
    fn instance_decl_name(
        &self,
        name: Option<&str>,
        class_name: &Name,
        class_args: &[Expr],
    ) -> Name {
        if let Some(n) = name {
            return Name::from_string(n);
        }
        let mut base = format!("inst{class_name}");
        for arg in class_args {
            if let ExprKind::Const(n, _) = arg.kind() {
                base.push_str(&n.to_string());
            }
        }
        self.fresh_global_name(&base)
    }

    /// `base` if free in the environment, else the first `base_1`, `base_2`, …
    /// no constant already claims (Lean `mkUnusedBaseName`).
    fn fresh_global_name(&self, base: &str) -> Name {
        let base_name = Name::from_string(base);
        if self.env.get_const(&base_name).is_none() {
            return base_name;
        }
        let mut i = 1u32;
        loop {
            let candidate = Name::from_string(&format!("{base}_{i}"));
            if self.env.get_const(&candidate).is_none() {
                return candidate;
            }
            i = i.saturating_add(1);
        }
    }
}
