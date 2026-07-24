// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structure-specific derive implementations.

use crate::infer::{DerivedInstance, ElabCtx};
use crate::ElabError;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, Level};
use clean_parser::{SurfaceBinder, SurfaceField};

/// Structure-specific derive implementations
impl<'a> ElabCtx<'a> {
    /// Derive BEq instance for a structure
    ///
    /// Generates: instance : BEq StructName where
    ///   beq := fun a b => a.field1 == b.field1 && a.field2 == b.field2 && ...
    ///
    /// For parametric structures like `structure Pair (α : Type) (β : Type)`:
    ///   instance [BEq α] [BEq β] : BEq (Pair α β) where ...
    ///
    /// The generated beq function compares each field pairwise and combines
    /// the results with Bool.and. For a structure with no fields, returns true.
    /// Universe handling (#3429): BEq.{u} : Type u -> Type u. For a
    /// monomorphic type T : Type 0, we need BEq.{0}. The generic
    /// concretize_monomorphic_instance substitutes the sort level
    /// (Succ(Zero) for Type 0), giving BEq.{1} which is wrong. Fix: for
    /// monomorphic types, use explicit Level::zero() for BEq's param and
    /// explicit BEq.beq.{0} for field comparisons.
    pub(super) fn derive_beq(
        &mut self,
        struct_name: &Name,
        binders: &[SurfaceBinder],
        fields: &[SurfaceField],
        field_names: &[Name],
    ) -> Result<DerivedInstance, ElabError> {
        let instance_name = Name::from_string(&format!("inst{struct_name}BEq"));
        let class_name = Name::from_string("BEq");
        let num_params = binders.len();
        let is_monomorphic = num_params == 0;

        // BEq.{u} takes Type u, so for monomorphic T : Type 0, u = 0.
        let beq_u = Level::zero();

        // Build instance type: BEq.{0} StructName for monomorphic types
        let instance_ty = if is_monomorphic {
            let struct_const = Expr::const_(struct_name.clone(), vec![]);
            let beq_const = Expr::const_(Name::from_string("BEq"), vec![beq_u.clone()]);
            Expr::app(beq_const, struct_const)
        } else {
            let (ty, _) = self.build_parametric_instance_type(struct_name, binders, &class_name);
            ty
        };

        // Parametric structures need their field `[BEq αᵢ]` instances resolved
        // against the (opened) constraint binders; the simple
        // `wrap_parametric_instance_value` path leaves those instances as
        // unsolved metas → "contains free variables". Build the full value with
        // an fvar telescope (mirroring the Inhabited parametric path) instead.
        if !is_monomorphic {
            let instance_val =
                self.build_beq_value_parametric(struct_name, binders, &class_name, fields)?;
            return Ok(DerivedInstance {
                name: instance_name,
                class_name,
                ty: instance_ty,
                val: instance_val,
                priority: 100,
                level_params: vec![],
            });
        }

        // Build the struct type for lambda annotations (monomorphic path).
        let struct_type = Expr::const_(struct_name.clone(), vec![]);

        // Build the beq function: fun a b => <comparisons>
        // Create bound variable references for lambda parameters
        // In de Bruijn indexing: a = BVar(1), b = BVar(0) inside the body
        let a_ref = Expr::bvar(1);
        let b_ref = Expr::bvar(0);

        // Build the comparison body
        let body = if field_names.is_empty() {
            // No fields - return Bool.true (genuinely 0-universe)
            Expr::const_(Name::from_string("Bool.true"), vec![])
        } else {
            // Build field comparisons: (a.field0 == b.field0) && (a.field1 == b.field1) && ...
            // Bool.and is genuinely 0-universe (Bool → Bool → Bool)
            let bool_and = Name::from_string("Bool.and");

            // Start with comparison of first field
            let mut comparison = self.build_field_beq(
                struct_name,
                fields,
                0,
                &a_ref,
                &b_ref,
                is_monomorphic,
                &beq_u,
            )?;

            // AND with remaining field comparisons
            for (idx, _field_name) in field_names.iter().enumerate().skip(1) {
                // SAFETY: Field index bounded by number of fields in structure
                let idx_u32 = u32::try_from(idx).unwrap_or(u32::MAX);
                let field_cmp = self.build_field_beq(
                    struct_name,
                    fields,
                    idx_u32,
                    &a_ref,
                    &b_ref,
                    is_monomorphic,
                    &beq_u,
                )?;

                // Bool.and comparison field_cmp (genuinely 0-universe)
                comparison = Expr::app(
                    Expr::app(Expr::const_(bool_and.clone(), vec![]), comparison),
                    field_cmp,
                );
            }

            comparison
        };

        // Build: λ (a : StructName) => λ (b : StructName) => body
        let inner_lam = Expr::lam(BinderInfo::Default, struct_type.clone(), body);
        let beq_func = Expr::lam(BinderInfo::Default, struct_type.clone(), inner_lam);

        // BEq.mk.{0} StructType beq_func for monomorphic types.
        // BEq.mk.{u} : {α : Type u} → (α → α → Bool) → BEq α
        // The α parameter is implicit but must be supplied at kernel level.
        let beq_mk = Expr::const_(Name::from_string("BEq.mk"), vec![beq_u]);
        let struct_const = Expr::const_(struct_name.clone(), vec![]);
        let instance_val = Expr::app(Expr::app(beq_mk, struct_const), beq_func);

        Ok(DerivedInstance {
            name: instance_name,
            class_name,
            ty: instance_ty,
            val: instance_val,
            priority: 100,
            level_params: vec![],
        })
    }

    /// Build the full `BEq (S α₁ … αₙ)` instance value for a *parametric*
    /// structure using an fvar telescope, exactly mirroring the parametric
    /// Inhabited path so the de Bruijn indices line up with the instance type
    /// from `build_parametric_instance_type`:
    /// ```text
    /// fun {α₁ … αₙ} [inst₁ : BEq α₁] … [instₙ : BEq αₙ] =>
    ///   BEq.mk (S α₁ … αₙ)
    ///     (fun (a b : S α₁ … αₙ) =>
    ///        @BEq.beq f₀ inst_{f₀} a.0 b.0 && … && @BEq.beq f_{k-1} inst_{f_{k-1}} a.k b.k)
    /// ```
    /// Each field's `[BEq fieldTy]` instance is resolved against the opened
    /// constraint binders (pushed as local instances), so e.g. a field of type
    /// `α` is compared with the `[BEq α]` binder rather than an unsolved meta.
    fn build_beq_value_parametric(
        &mut self,
        struct_name: &Name,
        binders: &[SurfaceBinder],
        class_name: &Name,
        fields: &[SurfaceField],
    ) -> Result<Expr, ElabError> {
        let num_params = binders.len();
        let type_sort = Expr::sort(Level::succ(Level::zero()));

        // Fresh fvars for type params and `[BEq αᵢ]` constraints (binder order).
        let param_fvars: Vec<clean_kernel::FVarId> =
            (0..num_params).map(|_| self.fresh_fvar()).collect();
        let constraint_fvars: Vec<clean_kernel::FVarId> =
            (0..num_params).map(|_| self.fresh_fvar()).collect();

        let constraint_tys: Vec<Expr> = (0..num_params)
            .map(|i| Expr::app(self.mk_const(class_name), Expr::fvar(param_fvars[i])))
            .collect();
        for (i, cty) in constraint_tys.iter().enumerate() {
            self.push_local_instance(constraint_fvars[i], cty.clone());
        }

        // Open the type-parameter binders as locals so field types elaborate.
        let saved_locals_len = self.locals.len();
        for (i, binder) in binders.iter().enumerate() {
            self.push_local_with_fvar(binder.name.clone(), param_fvars[i], type_sort.clone());
        }

        // Target type `S α₁ … αₙ`.
        let mut struct_type = self.mk_const(struct_name);
        for fv in &param_fvars {
            struct_type = Expr::app(struct_type, Expr::fvar(*fv));
        }

        // `a` and `b` as fvars of type `S α₁ … αₙ`.
        let a_fvar = self.fresh_fvar();
        let b_fvar = self.fresh_fvar();
        let a_ref = Expr::fvar(a_fvar);
        let b_ref = Expr::fvar(b_fvar);

        // Comparison body over the fvar `a`/`b`.
        let body_result = (|| -> Result<Expr, ElabError> {
            if fields.is_empty() {
                return Ok(Expr::const_(Name::from_string("Bool.true"), vec![]));
            }
            let bool_and = Name::from_string("Bool.and");
            let mut comparison =
                self.build_field_beq_resolved(struct_name, fields, 0, &a_ref, &b_ref)?;
            for idx in 1..fields.len() {
                // SAFETY: bounded by field count.
                let idx_u32 = u32::try_from(idx).unwrap_or(u32::MAX);
                let field_cmp =
                    self.build_field_beq_resolved(struct_name, fields, idx_u32, &a_ref, &b_ref)?;
                comparison = Expr::app(
                    Expr::app(Expr::const_(bool_and.clone(), vec![]), comparison),
                    field_cmp,
                );
            }
            Ok(comparison)
        })();

        // Restore temporary elaboration state even when a field cannot be
        // elaborated or its BEq instance cannot be resolved.
        self.locals.truncate(saved_locals_len);
        for _ in 0..num_params {
            self.pop_local_instance();
        }
        let body = body_result?;

        // λ (a b : S …) => body  (abstract b first → BVar 0, then a → BVar 1).
        let mut beq_func = body.abstract_fvar(b_fvar);
        beq_func = Expr::lam(BinderInfo::Default, struct_type.clone(), beq_func);
        beq_func = beq_func.abstract_fvar(a_fvar);
        beq_func = Expr::lam(BinderInfo::Default, struct_type.clone(), beq_func);

        // BEq.mk (S α₁ … αₙ) beq_func — supply the implicit `α := S …`
        // explicitly (the value is committed to the kernel verbatim).
        let mut value = Expr::app(
            Expr::app(self.mk_const_str("BEq.mk"), struct_type),
            beq_func,
        );

        // Wrap the param/constraint telescope. Same idiom as the parametric
        // Inhabited path: abstract-this-fvar-then-wrap, with binder types still
        // referencing the fvars so outer abstractions shift them consistently.
        let mut outer_fvars: Vec<clean_kernel::FVarId> = param_fvars.clone();
        outer_fvars.extend_from_slice(&constraint_fvars);
        let binder_infos: Vec<BinderInfo> = std::iter::repeat_n(BinderInfo::Implicit, num_params)
            .chain(std::iter::repeat_n(BinderInfo::InstImplicit, num_params))
            .collect();
        let mut binder_tys: Vec<Expr> = std::iter::repeat_n(type_sort, num_params).collect();
        binder_tys.extend(constraint_tys);

        for idx in (0..outer_fvars.len()).rev() {
            value = value.abstract_fvar(outer_fvars[idx]);
            value = Expr::lam(binder_infos[idx], binder_tys[idx].clone(), value);
        }

        Ok(value)
    }

    /// Build the per-field equality `@BEq.beq fieldTy fieldInst a.idx b.idx`.
    ///
    /// `BEq.beq : {α : Sort u} → [inst : BEq α] → α → α → Bool` — the implicit
    /// type argument and the `[BEq fieldTy]` instance argument MUST be supplied
    /// explicitly, because the derived value is committed to the kernel verbatim
    /// (no implicit-arg insertion runs at registration). Previously the field
    /// values were passed straight into the `{α : Sort u}` slot, producing
    /// "expected Sort _, got <fieldTy>" kernel errors. The field instance is
    /// resolved to a closed term; failure is reported as `Unsupported` rather
    /// than leaking an elaborator metavariable into the generated declaration.
    #[allow(clippy::too_many_arguments)]
    fn build_field_beq(
        &mut self,
        struct_name: &Name,
        fields: &[SurfaceField],
        idx: u32,
        a_ref: &Expr,
        b_ref: &Expr,
        is_monomorphic: bool,
        beq_u: &Level,
    ) -> Result<Expr, ElabError> {
        let a_field = Expr::proj(struct_name.clone(), idx, a_ref.clone());
        let b_field = Expr::proj(struct_name.clone(), idx, b_ref.clone());

        // Field type for the `{α}` argument.
        let field = &fields[idx as usize];
        let field_ty = self.elaborate(&field.ty)?;

        // `[BEq fieldTy]` instance argument.
        let beq_class = Name::from_string("BEq");
        let beq_field_ty = Expr::app(self.mk_const(&beq_class), field_ty.clone());
        let field_inst =
            self.resolve_instance(&beq_field_ty)
                .ok_or_else(|| ElabError::Unsupported {
                    feature: format!(
                        "deriving BEq for `{struct_name}` cannot synthesize BEq for field `{}`",
                        field.name
                    ),
                })?;

        let beq_beq = if is_monomorphic {
            Expr::const_(Name::from_string("BEq.beq"), vec![beq_u.clone()])
        } else {
            self.mk_const_str("BEq.beq")
        };

        // @BEq.beq fieldTy fieldInst a.idx b.idx
        Ok(Expr::app(
            Expr::app(Expr::app(Expr::app(beq_beq, field_ty), field_inst), a_field),
            b_field,
        ))
    }

    /// Like `build_field_beq` but for the *parametric* path: `BEq.beq` is left
    /// universe-polymorphic (`mk_const_str`) and the field's `[BEq fieldTy]`
    /// instance is resolved against the currently-pushed local instances (the
    /// opened `[BEq αᵢ]` constraint binders). `a_ref`/`b_ref` are the opened
    /// `a`/`b` fvars, so the projections are closed once those are abstracted.
    fn build_field_beq_resolved(
        &mut self,
        struct_name: &Name,
        fields: &[SurfaceField],
        idx: u32,
        a_ref: &Expr,
        b_ref: &Expr,
    ) -> Result<Expr, ElabError> {
        let a_field = Expr::proj(struct_name.clone(), idx, a_ref.clone());
        let b_field = Expr::proj(struct_name.clone(), idx, b_ref.clone());

        let field = &fields[idx as usize];
        let field_ty = self.elaborate(&field.ty)?;

        let beq_class = Name::from_string("BEq");
        let beq_field_ty = Expr::app(self.mk_const(&beq_class), field_ty.clone());
        let field_inst =
            self.resolve_instance(&beq_field_ty)
                .ok_or_else(|| ElabError::Unsupported {
                    feature: format!(
                        "deriving BEq for `{struct_name}` cannot synthesize BEq for field `{}`",
                        field.name
                    ),
                })?;

        let beq_beq = self.mk_const_str("BEq.beq");
        // @BEq.beq fieldTy fieldInst a.idx b.idx
        Ok(Expr::app(
            Expr::app(Expr::app(Expr::app(beq_beq, field_ty), field_inst), a_field),
            b_field,
        ))
    }

    /// Derive a `Repr` instance for a structure.
    ///
    /// Emits the equivalent of:
    /// ```lean
    /// instance : Repr StructName where
    ///   reprPrec _ _ := "StructName"
    /// ```
    /// against Clean's String-valued `Repr` class (`reprPrec : α → Nat →
    /// String`; see clean-kernel `data_typeclasses_repr`). The body is
    /// minimal-but-type-correct — it mirrors the shipped inductive-Repr
    /// bootstrap (`derive_repr_inductive`), and the everyday `structure …
    /// deriving Repr` pattern only needs the instance to *synthesize and
    /// kernel-check*, not to render a particular string.
    ///
    /// Fidelity: every field's `Repr fieldTy` instance is still resolved (and
    /// then discarded — the minimal body does not consume it) so deriving fails
    /// LOUD, exactly like Lean, when a field type has no `Repr` (e.g. a bare
    /// `Nat → Nat`) rather than silently minting a bogus instance.
    ///
    /// Parametric structures gain `[Repr αᵢ]` constraints via
    /// `build_parametric_instance_type`, mirroring `derive_inhabited`/
    /// `derive_beq`; the monomorphic path relies on the caller's
    /// `concretize_monomorphic_instance` to collapse the fresh `Repr.{u}` /
    /// `Repr.mk.{u}` universe params to the target sort.
    pub(super) fn derive_repr(
        &mut self,
        struct_name: &Name,
        binders: &[SurfaceBinder],
        fields: &[SurfaceField],
    ) -> Result<DerivedInstance, ElabError> {
        let instance_name = Name::from_string(&format!("inst{struct_name}Repr"));
        let class_name = Name::from_string("Repr");
        let num_params = binders.len();

        // Instance type: `Repr S` (mono) or
        // `∀ {αᵢ} [Repr αᵢ], Repr (S α…)` (parametric).
        let (instance_ty, _num_constraints) =
            self.build_parametric_instance_type(struct_name, binders, &class_name);

        let instance_val = if num_params == 0 {
            self.build_repr_value_monomorphic(struct_name, &class_name, fields)?
        } else {
            self.build_repr_value_parametric(struct_name, binders, &class_name, fields)?
        };

        Ok(DerivedInstance {
            name: instance_name,
            class_name,
            ty: instance_ty,
            val: instance_val,
            priority: 100,
            level_params: vec![],
        })
    }

    /// Resolve a field's `Repr fieldTy` instance, failing LOUD (never silently
    /// minting a bogus instance) when the field type has no `Repr`. The
    /// resolved instance is intentionally discarded — the minimal `reprPrec`
    /// body does not consume it; this is the Lean-faithful requirement that
    /// every field of a `deriving Repr` type be representable.
    fn ensure_field_repr(
        &mut self,
        struct_name: &Name,
        field_name: &str,
        class_name: &Name,
        field_ty: &Expr,
    ) -> Result<(), ElabError> {
        let repr_field_ty = Expr::app(self.mk_const(class_name), field_ty.clone());
        // The resolved instance is intentionally discarded (the minimal body
        // does not consume it); resolution runs purely as the fail-loud gate.
        let _resolved =
            self.resolve_instance(&repr_field_ty)
                .ok_or_else(|| ElabError::Unsupported {
                    feature: format!(
                        "deriving Repr for `{struct_name}` cannot synthesize Repr for field `{field_name}`"
                    ),
                })?;
        Ok(())
    }

    /// Build `Repr.mk S (fun (_ : S) (_ : Nat) => "S")` for a monomorphic
    /// struct, resolving every field's `Repr` instance first so a
    /// non-representable field fails loud (see `ensure_field_repr`).
    fn build_repr_value_monomorphic(
        &mut self,
        struct_name: &Name,
        class_name: &Name,
        fields: &[SurfaceField],
    ) -> Result<Expr, ElabError> {
        for field in fields {
            let field_ty = self.elaborate(&field.ty)?;
            self.ensure_field_repr(struct_name, &field.name, class_name, &field_ty)?;
        }

        let struct_type = self.mk_const(struct_name);
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        // reprPrec := fun (_ : S) (_ : Nat) => "S"
        let repr_fn = Expr::lam(
            BinderInfo::Default,
            struct_type.clone(),
            Expr::lam(
                BinderInfo::Default,
                nat_ty,
                Expr::str_lit(struct_name.to_string()),
            ),
        );
        // `Repr.mk : {α : Type u} → (α → Nat → String) → Repr α` — supply the
        // implicit `α := S` explicitly (the value is committed to the kernel
        // verbatim; no implicit-arg insertion runs at registration).
        Ok(Expr::app(
            Expr::app(self.mk_const_str("Repr.mk"), struct_type),
            repr_fn,
        ))
    }

    /// Build the full `Repr (S α₁ … αₙ)` instance value for a *parametric*
    /// structure using an fvar telescope, mirroring the parametric BEq/Inhabited
    /// paths so the de Bruijn indices line up with the instance type from
    /// `build_parametric_instance_type`:
    /// ```text
    /// fun {α₁ … αₙ} [inst₁ : Repr α₁] … [instₙ : Repr αₙ] =>
    ///   Repr.mk (S α₁ … αₙ) (fun (_ : S α₁ … αₙ) (_ : Nat) => "S")
    /// ```
    /// Each field's `[Repr fieldTy]` instance is resolved against the opened
    /// `[Repr αᵢ]` constraint binders (fail-loud) before the body is built.
    fn build_repr_value_parametric(
        &mut self,
        struct_name: &Name,
        binders: &[SurfaceBinder],
        class_name: &Name,
        fields: &[SurfaceField],
    ) -> Result<Expr, ElabError> {
        let num_params = binders.len();
        let type_sort = Expr::sort(Level::succ(Level::zero()));

        // Fresh fvars for type params and `[Repr αᵢ]` constraints (binder order).
        let param_fvars: Vec<clean_kernel::FVarId> =
            (0..num_params).map(|_| self.fresh_fvar()).collect();
        let constraint_fvars: Vec<clean_kernel::FVarId> =
            (0..num_params).map(|_| self.fresh_fvar()).collect();

        let constraint_tys: Vec<Expr> = (0..num_params)
            .map(|i| Expr::app(self.mk_const(class_name), Expr::fvar(param_fvars[i])))
            .collect();
        for (i, cty) in constraint_tys.iter().enumerate() {
            self.push_local_instance(constraint_fvars[i], cty.clone());
        }

        // Open the type-parameter binders as locals so field types elaborate.
        let saved_locals_len = self.locals.len();
        for (i, binder) in binders.iter().enumerate() {
            self.push_local_with_fvar(binder.name.clone(), param_fvars[i], type_sort.clone());
        }

        // Target type `S α₁ … αₙ` (built while the params are open).
        let mut struct_type = self.mk_const(struct_name);
        for fv in &param_fvars {
            struct_type = Expr::app(struct_type, Expr::fvar(*fv));
        }

        // Resolve each field's `Repr` against the opened `[Repr αᵢ]` constraints.
        let resolve_result = (|| -> Result<(), ElabError> {
            for field in fields {
                let field_ty = self.elaborate(&field.ty)?;
                self.ensure_field_repr(struct_name, &field.name, class_name, &field_ty)?;
            }
            Ok(())
        })();

        // Restore temporary elaboration state even when a field cannot be
        // elaborated or its Repr instance cannot be resolved.
        self.locals.truncate(saved_locals_len);
        for _ in 0..num_params {
            self.pop_local_instance();
        }
        resolve_result?;

        // reprPrec := fun (_ : S α…) (_ : Nat) => "S" — minimal, closed body.
        let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
        let repr_fn = Expr::lam(
            BinderInfo::Default,
            struct_type.clone(),
            Expr::lam(
                BinderInfo::Default,
                nat_ty,
                Expr::str_lit(struct_name.to_string()),
            ),
        );

        // Repr.mk (S α₁ … αₙ) reprPrec — supply the implicit `α := S …`.
        let mut value = Expr::app(
            Expr::app(self.mk_const_str("Repr.mk"), struct_type),
            repr_fn,
        );

        // Wrap the param/constraint telescope. Same idiom as the parametric
        // BEq/Inhabited paths: abstract-this-fvar-then-wrap, with binder types
        // still referencing the fvars so outer abstractions shift them
        // consistently.
        let mut outer_fvars: Vec<clean_kernel::FVarId> = param_fvars.clone();
        outer_fvars.extend_from_slice(&constraint_fvars);
        let binder_infos: Vec<BinderInfo> = std::iter::repeat_n(BinderInfo::Implicit, num_params)
            .chain(std::iter::repeat_n(BinderInfo::InstImplicit, num_params))
            .collect();
        let mut binder_tys: Vec<Expr> = std::iter::repeat_n(type_sort, num_params).collect();
        binder_tys.extend(constraint_tys);

        for idx in (0..outer_fvars.len()).rev() {
            value = value.abstract_fvar(outer_fvars[idx]);
            value = Expr::lam(binder_infos[idx], binder_tys[idx].clone(), value);
        }

        Ok(value)
    }

    /// Derive Inhabited instance for a structure
    ///
    /// Generates: instance : Inhabited StructName where
    ///   default := StructName.mk (Inhabited.default field1) (Inhabited.default field2) ...
    ///
    /// For parametric structures: instance [Inhabited α] [Inhabited β] : Inhabited (Pair α β) where ...
    pub(super) fn derive_inhabited(
        &mut self,
        struct_name: &Name,
        binders: &[SurfaceBinder],
        fields: &[SurfaceField],
    ) -> Result<DerivedInstance, ElabError> {
        let instance_name = Name::from_string(&format!("inst{struct_name}Inhabited"));
        let class_name = Name::from_string("Inhabited");
        let num_params = binders.len();

        // Build instance type with constraints
        let (instance_ty, _num_constraints) =
            self.build_parametric_instance_type(struct_name, binders, &class_name);

        let core_instance_val = if num_params == 0 {
            // Monomorphic structure: field types are ground, so each field's
            // `Inhabited fieldTy` instance can be resolved to a *closed* term at
            // derive time. The previous implementation left a `fresh_meta`
            // (encoded as an fvar) as the instance argument; an unsolved meta is
            // a free variable, and the kernel rejected the declaration with
            // "contains free variables". Resolving the instance here closes the
            // term. (Track A blocker #1.)
            self.build_inhabited_default_monomorphic(struct_name, &class_name, fields)?
        } else {
            // Parametric structure: open the type parameters and their
            // `[Inhabited αᵢ]` constraints as fresh fvars, resolve each field's
            // instance against those local instances, then abstract the fvars
            // back into lambdas. This produces a closed instance value with the
            // constraint binders supplying the per-field defaults.
            self.build_inhabited_value_parametric(struct_name, binders, &class_name, fields)?
        };

        Ok(DerivedInstance {
            name: instance_name,
            class_name,
            ty: instance_ty,
            val: core_instance_val,
            priority: 100,
            level_params: vec![],
        })
    }

    /// Build `Inhabited.mk (S.mk (default f1) (default f2) …)` for a
    /// monomorphic structure, resolving each field's `Inhabited` instance to a
    /// closed term (no metavariables / free variables).
    fn build_inhabited_default_monomorphic(
        &mut self,
        struct_name: &Name,
        class_name: &Name,
        fields: &[SurfaceField],
    ) -> Result<Expr, ElabError> {
        let ctor_name_str = format!("{struct_name}.mk");
        let mut ctor_app = self.mk_const_str(&ctor_name_str);

        for field in fields {
            let field_ty = self.elaborate(&field.ty)?;
            let default_val =
                self.field_inhabited_default(struct_name, &field.name, class_name, field_ty)?;
            ctor_app = Expr::app(ctor_app, default_val);
        }

        // `Inhabited.mk : {α : Sort u} → α → Inhabited α` — the implicit type
        // argument `α := <struct>` must be supplied explicitly because the
        // derived value is committed to the kernel verbatim (no implicit-arg
        // insertion happens at registration).
        let struct_type = self.mk_const(struct_name);
        Ok(Expr::app(
            Expr::app(self.mk_const_str("Inhabited.mk"), struct_type),
            ctor_app,
        ))
    }

    /// Build the full instance value for a parametric structure using an
    /// fvar telescope: `fun {α₁ …} [inst₁ : Inhabited α₁] … =>
    /// Inhabited.mk (S.mk … (default fieldTy fieldInst) …)`.
    fn build_inhabited_value_parametric(
        &mut self,
        struct_name: &Name,
        binders: &[SurfaceBinder],
        class_name: &Name,
        fields: &[SurfaceField],
    ) -> Result<Expr, ElabError> {
        let num_params = binders.len();
        let type_sort = Expr::sort(Level::succ(Level::zero()));

        // Fresh fvars for each type parameter and each `[Inhabited αᵢ]`
        // constraint, in binder order (outermost first).
        let param_fvars: Vec<clean_kernel::FVarId> =
            (0..num_params).map(|_| self.fresh_fvar()).collect();
        let constraint_fvars: Vec<clean_kernel::FVarId> =
            (0..num_params).map(|_| self.fresh_fvar()).collect();

        // Push the constraints as local instances so field-instance resolution
        // can see them (e.g. `Inhabited α` is solved by the `instᵢ` fvar).
        let constraint_tys: Vec<Expr> = (0..num_params)
            .map(|i| Expr::app(self.mk_const(class_name), Expr::fvar(param_fvars[i])))
            .collect();
        for (i, cty) in constraint_tys.iter().enumerate() {
            self.push_local_instance(constraint_fvars[i], cty.clone());
        }

        // Map each surface binder name to its parameter fvar so field types
        // elaborate against the opened parameters.
        let saved_locals_len = self.locals.len();
        for (i, binder) in binders.iter().enumerate() {
            self.push_local_with_fvar(binder.name.clone(), param_fvars[i], type_sort.clone());
        }

        // The target type `S α₁ … αₙ` (applied to the parameter fvars).
        let mut struct_type = self.mk_const(struct_name);
        for fv in &param_fvars {
            struct_type = Expr::app(struct_type, Expr::fvar(*fv));
        }

        // S.mk applied to the type-parameter fvars.
        let ctor_name_str = format!("{struct_name}.mk");
        let mut ctor_app = self.mk_const_str(&ctor_name_str);
        for fv in &param_fvars {
            ctor_app = Expr::app(ctor_app, Expr::fvar(*fv));
        }

        let fields_result = (|| -> Result<(), ElabError> {
            for field in fields {
                let field_ty = self.elaborate(&field.ty)?;
                let default_val =
                    self.field_inhabited_default(struct_name, &field.name, class_name, field_ty)?;
                ctor_app = Expr::app(ctor_app.clone(), default_val);
            }
            Ok(())
        })();

        // Restore locals; the field-type binders were only needed for elaboration.
        self.locals.truncate(saved_locals_len);
        // Drop the local instances we pushed.
        for _ in 0..num_params {
            self.pop_local_instance();
        }
        fields_result?;

        // `Inhabited.mk : {α : Sort u} → α → Inhabited α` — supply the implicit
        // type argument `α := S α₁ … αₙ` explicitly (see monomorphic path).
        let mut value = Expr::app(
            Expr::app(self.mk_const_str("Inhabited.mk"), struct_type),
            ctor_app,
        );

        // Wrap the value in the lambda telescope that matches the instance type
        // built by `build_parametric_instance_type`:
        //   fun {α₁ … αₙ} [inst₁ : Inhabited α₁] … [instₙ : Inhabited αₙ] => …
        // The outer fvars (in binder order) are the type params followed by the
        // constraints. We fold from the innermost binder (last constraint)
        // outward; at each step we abstract the new binder's fvar in the body
        // AND re-abstract every still-open *outer* fvar in the binder's own type
        // annotation, mirroring the `auto_implicit` wrapping idiom so de Bruijn
        // indices stay consistent.
        //
        // `outer_fvars` lists the binders that remain to be wrapped, outermost
        // first. As we wrap the innermost remaining binder we pop it off the
        // tail and abstract the rest from its type.
        let mut outer_fvars: Vec<clean_kernel::FVarId> = param_fvars.clone();
        outer_fvars.extend_from_slice(&constraint_fvars);

        let binder_infos: Vec<BinderInfo> = std::iter::repeat_n(BinderInfo::Implicit, num_params)
            .chain(std::iter::repeat_n(BinderInfo::InstImplicit, num_params))
            .collect();
        // Binder type templates (still referencing the param fvars where needed).
        let mut binder_tys: Vec<Expr> =
            std::iter::repeat_n(type_sort.clone(), num_params).collect();
        binder_tys.extend(constraint_tys.iter().cloned());

        // Build the lambda telescope innermost-first. The binder type
        // annotations still reference the parameter fvars DIRECTLY (not
        // pre-abstracted). At each step we
        //   (1) `abstract_fvar` this binder's fvar in the accumulated body so
        //       it becomes `BVar(0)` of the lambda we are about to add, then
        //   (2) wrap the lambda with the fvar-bearing domain.
        // The *outer* iterations' `abstract_fvar` calls later descend into this
        // lambda's domain and shift its surviving fvars/bvars consistently, so
        // a constraint domain like `Inhabited α` ends up at the same de Bruijn
        // index the instance type assigns it (`build_parametric_instance_type`
        // ⇒ `BVar(num_params-1)`).
        //
        // Two earlier bugs both lived here: pre-abstracting the domain with the
        // outer fvars double-counted (out-of-range `BVar 3`), and abstracting
        // the body AFTER wrapping put this binder at `BVar 1` instead of
        // `BVar 0`.
        for idx in (0..outer_fvars.len()).rev() {
            let fvar = outer_fvars[idx];
            value = value.abstract_fvar(fvar);
            value = Expr::lam(binder_infos[idx], binder_tys[idx].clone(), value);
        }

        Ok(value)
    }

    /// Build `Inhabited.default fieldTy fieldInst` where `fieldInst` is a
    /// resolved (closed) instance term. Missing field instances are reported as
    /// typed unsupported-shape errors; automatic deriving never leaves a meta.
    fn field_inhabited_default(
        &mut self,
        struct_name: &Name,
        field_name: &str,
        class_name: &Name,
        field_ty: Expr,
    ) -> Result<Expr, ElabError> {
        let inhabited_field_ty = Expr::app(self.mk_const(class_name), field_ty.clone());
        let inst = self
            .resolve_instance(&inhabited_field_ty)
            .ok_or_else(|| ElabError::Unsupported {
                feature: format!(
                    "deriving Inhabited for `{struct_name}` cannot synthesize Inhabited for field `{field_name}`"
                ),
            })?;
        let inhabited_default = self.mk_const_str("Inhabited.default");
        Ok(Expr::app(Expr::app(inhabited_default, field_ty), inst))
    }

    /// Derive DecidableEq instance for a structure
    ///
    /// Generates: `instance : DecidableEq StructName where`
    ///   `decEq := fun a b => ...` (field-aware decision procedure)
    ///
    /// For parametric structures: instance [DecidableEq α] [DecidableEq β] : DecidableEq (Pair α β) where ...
    ///
    /// Only proof-producing monomorphic paths are admitted: nullary structures
    /// use the shared nullary-constructor recursor builder, while structures
    /// with fields compose their fields' resolved `DecidableEq` instances.
    /// Unsupported parameter/field-instance shapes return a typed elaboration
    /// error rather than manufacturing a `sorryAx` decision procedure.
    pub(super) fn derive_decidable_eq(
        &mut self,
        struct_name: &Name,
        binders: &[SurfaceBinder],
        fields: &[SurfaceField],
        _field_names: &[Name],
    ) -> Result<DerivedInstance, ElabError> {
        let instance_name = Name::from_string(&format!("inst{struct_name}DecidableEq"));
        let class_name = Name::from_string("DecidableEq");
        let num_params = binders.len();

        // Build instance type with constraints
        let (instance_ty, _num_constraints) =
            self.build_parametric_instance_type(struct_name, binders, &class_name);

        // Build parametric struct type for lambda annotations
        let struct_type = if num_params == 0 {
            self.mk_const(struct_name)
        } else {
            self.build_parametric_struct_type(struct_name, num_params, num_params)
        };

        // First try the SOUND, sorry-free instance value for the monomorphic
        // (non-parametric) struct shape. An empty structure is decided by the
        // shared nullary-constructor recursor builder. A fielded structure
        // decides each field via its own `DecidableEq` instance and composes by
        // congruence over the constructor (`decidable_eq_struct_value`). These
        // produce the full `λ (a b : S) => <recursor dispatch>` term — no
        // `sorry`. The fielded path only succeeds when every field type resolves
        // a monomorphic in-tree `DecidableEq` instance (e.g. `index : Nat` →
        // `instDecidableEqNat`); otherwise deriving fails closed with
        // `Unsupported`. This is what lets
        // `decide (a = b)` / `a == b` on `deriving DecidableEq` wrapper structs
        // such as trust-ir's `ValueId`/`AllocId` resolve without a `sorry`.
        if num_params == 0 {
            if let Some(sound) = self.try_sound_struct_decidable_eq(struct_name, fields) {
                let instance_val =
                    self.wrap_parametric_instance_value(sound, num_params, &class_name);
                return Ok(DerivedInstance {
                    name: instance_name,
                    class_name,
                    ty: instance_ty,
                    val: instance_val,
                    priority: 100,
                    level_params: vec![],
                });
            }
        }

        let _ = struct_type;
        Err(ElabError::Unsupported {
            feature: format!(
                "deriving DecidableEq for `{struct_name}` has no closed proof-producing \
                 construction for this parameter/field shape; automatic deriving refuses \
                 `sorryAx`"
            ),
        })
    }

    /// Try to build the SOUND (sorry-free) `DecidableEq` instance *value* for a
    /// monomorphic struct, reusing the shared nullary-constructor or
    /// single-ctor-field builder as appropriate. Returns the full binary lambda
    /// `λ (a b : S) => <Decidable.rec field dispatch>` on success, or `None`
    /// when any field type lacks a resolvable monomorphic `DecidableEq` instance
    /// (the caller then reports `Unsupported`).
    ///
    /// The struct is `Type 0` for the wrapper-style structs this targets
    /// (`structure ValueId where index : Nat`), so the `Eq`/`DecidableEq` level
    /// is `Sort 1 = succ 0`. The resulting term mentions only the struct's own
    /// projections, each field's `DecidableEq` instance, `congrArg`, `Eq.trans`,
    /// `Eq.refl`, and the `Decidable` constructors — no `sorryAx`/axioms.
    fn try_sound_struct_decidable_eq(
        &mut self,
        struct_name: &Name,
        fields: &[SurfaceField],
    ) -> Option<Expr> {
        use crate::derive_ext_handlers2::{
            decidable_eq_nullary_enum_value, decidable_eq_struct_value, CtorInfo2,
        };

        // Elaborate each field's type; bail if any fails to elaborate.
        let mut ctor_fields: Vec<(Name, Expr)> = Vec::with_capacity(fields.len());
        for field in fields {
            let field_ty = self.elaborate(&field.ty).ok()?;
            ctor_fields.push((Name::from_string(&field.name), field_ty));
        }

        let ctor = CtorInfo2 {
            name: Name::from_string(&format!("{struct_name}.mk")),
            fields: ctor_fields,
            is_recursive: false,
        };

        // `Type 0` wrapper structs ⇒ `Eq.{1}`/`DecidableEq.{1}` (Sort 1 = succ 0).
        let u_level = Level::succ(Level::zero());
        let ctors = std::slice::from_ref(&ctor);
        if fields.is_empty() {
            decidable_eq_nullary_enum_value(struct_name, ctors, 0, &u_level)
        } else {
            decidable_eq_struct_value(self.env, struct_name, ctors, 0, &u_level)
        }
    }
}
