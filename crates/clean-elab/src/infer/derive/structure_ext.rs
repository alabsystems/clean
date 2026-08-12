// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended structure derive implementations for additional typeclasses:
//! Ord, Nonempty, ToString, Functor, Foldable, Traversable.

use crate::infer::{DerivedInstance, ElabCtx};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, Level};
use clean_parser::{SurfaceBinder, SurfaceField};

/// Extended structure derive implementations
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
impl<'a> ElabCtx<'a> {
    /// Derive Ord instance for a structure
    ///
    /// Generates lexicographic comparison over fields using `Ord.compare`.
    /// For a structure with fields f1, f2, ...:
    /// ```text
    /// instance : Ord StructName where
    ///   compare a b := match compare a.f1 b.f1 with
    ///     | Ordering.eq => match compare a.f2 b.f2 with ... | r => r
    ///     | r => r
    /// ```
    pub(super) fn derive_ord(
        &mut self,
        struct_name: &Name,
        binders: &[SurfaceBinder],
        fields: &[SurfaceField],
        field_names: &[Name],
    ) -> DerivedInstance {
        let instance_name = Name::from_string(&format!("inst{struct_name}Ord"));
        let class_name = Name::from_string("Ord");
        let num_params = binders.len();

        let (instance_ty, _num_constraints) =
            self.build_parametric_instance_type(struct_name, binders, &class_name);

        // Monomorphic path: a real lexicographic `compare` over the fields, each
        // via its own `Ord` instance resolved by the elaborator (mirrors
        // `derive_beq`). The previous code emitted bare `Ord.compare a.f b.f`
        // (missing the implicit `{α}`/`[Ord α]` args, so the kernel read the
        // projection value as the type argument — "expected Sort, got Nat") and
        // sequenced with `Ordering.then`, which is absent from the prelude. Both
        // are fixed here: `@Ord.compare.{0} fieldTy fieldInst a.f b.f` per field,
        // sequenced lexicographically with `Ordering.casesOn` (`.eq` ⇒ compare the
        // next field, else return the ordering), and `Ord.mk.{0} StructT` with the
        // explicit level/type the kernel requires.
        if num_params == 0 {
            let ord_u = Level::zero();
            let struct_type = Expr::const_(struct_name.clone(), vec![]);
            let a_ref = Expr::bvar(1);
            let b_ref = Expr::bvar(0);

            let body = if field_names.is_empty() {
                Expr::const_(Name::from_string("Ordering.eq"), vec![])
            } else {
                // Base: the last field's raw comparison (result when all earlier
                // fields tie). A single field collapses to exactly this.
                let last_idx = field_names.len() - 1;
                let last_idx_u32 = u32::try_from(last_idx).unwrap_or(u32::MAX);
                let mut result =
                    self.build_field_ord(struct_name, fields, last_idx_u32, &a_ref, &b_ref, &ord_u);

                let ordering_ty = Expr::const_str("Ordering");
                let caseson_u = Level::succ(Level::zero());
                for idx in (0..last_idx).rev() {
                    let idx_u32 = u32::try_from(idx).unwrap_or(u32::MAX);
                    let field_cmp =
                        self.build_field_ord(struct_name, fields, idx_u32, &a_ref, &b_ref, &ord_u);
                    // `Ordering.casesOn (fun _ => Ordering) field_cmp .lt <rest> .gt`
                    // ≡ `field_cmp.then rest` — `.eq` falls through to `rest`.
                    let motive = Expr::lam(
                        BinderInfo::Default,
                        ordering_ty.clone(),
                        ordering_ty.clone(),
                    );
                    let cases_on = Expr::const_(
                        Name::from_string("Ordering.casesOn"),
                        vec![caseson_u.clone()],
                    );
                    result = Expr::apps(
                        cases_on,
                        [
                            motive,
                            field_cmp,
                            Expr::const_str("Ordering.lt"),
                            result,
                            Expr::const_str("Ordering.gt"),
                        ],
                    );
                }
                result
            };

            let inner_lam = Expr::lam(BinderInfo::Default, struct_type.clone(), body);
            let compare_func = Expr::lam(BinderInfo::Default, struct_type.clone(), inner_lam);

            // Ord.mk.{0} StructT compare_func — explicit level + type (as derive_beq
            // supplies for BEq.mk) to satisfy the kernel's level-arity check.
            let ord_mk = Expr::const_(Name::from_string("Ord.mk"), vec![ord_u]);
            let struct_const = Expr::const_(struct_name.clone(), vec![]);
            let instance_val = Expr::app(Expr::app(ord_mk, struct_const), compare_func);

            return DerivedInstance {
                name: instance_name,
                class_name,
                ty: instance_ty,
                val: instance_val,
                priority: 100,
                level_params: vec![],
            };
        }

        // Parametric path: build the full value with an fvar telescope so each
        // field's `[Ord αᵢ]` instance resolves against the opened `[Ord αᵢ]`
        // constraint binders (mirrors `build_beq_value_parametric`).
        let instance_val =
            self.build_ord_value_parametric(struct_name, binders, &class_name, fields);
        DerivedInstance {
            name: instance_name,
            class_name,
            ty: instance_ty,
            val: instance_val,
            priority: 100,
            level_params: vec![],
        }
    }

    /// Build the full `Ord (S α₁ … αₙ)` instance value for a *parametric*
    /// structure, exactly mirroring [`build_beq_value_parametric`] but with the
    /// lexicographic `Ordering.casesOn` fold from the monomorphic `derive_ord`:
    /// ```text
    /// fun {α₁ … αₙ} [inst₁ : Ord α₁] … [instₙ : Ord αₙ] =>
    ///   Ord.mk (S α₁ … αₙ)
    ///     (fun (a b : S α₁ … αₙ) => <lex compare of fields via @Ord.compare>)
    /// ```
    /// Each field's `[Ord fieldTy]` instance resolves against the opened
    /// constraint binders (pushed as local instances), so a field of type `α` is
    /// compared with the `[Ord α]` binder rather than an unsolved meta.
    fn build_ord_value_parametric(
        &mut self,
        struct_name: &Name,
        binders: &[SurfaceBinder],
        class_name: &Name,
        fields: &[SurfaceField],
    ) -> Expr {
        let num_params = binders.len();
        let type_sort = Expr::sort(Level::succ(Level::zero()));

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

        let saved_locals_len = self.locals.len();
        for (i, binder) in binders.iter().enumerate() {
            self.push_local_with_fvar(binder.name.clone(), param_fvars[i], type_sort.clone());
        }

        let mut struct_type = self.mk_const(struct_name);
        for fv in &param_fvars {
            struct_type = Expr::app(struct_type, Expr::fvar(*fv));
        }

        let a_fvar = self.fresh_fvar();
        let b_fvar = self.fresh_fvar();
        let a_ref = Expr::fvar(a_fvar);
        let b_ref = Expr::fvar(b_fvar);

        let body = if fields.is_empty() {
            Expr::const_(Name::from_string("Ordering.eq"), vec![])
        } else {
            let last_idx = fields.len() - 1;
            let last_idx_u32 = u32::try_from(last_idx).unwrap_or(u32::MAX);
            let mut result =
                self.build_field_ord_resolved(struct_name, fields, last_idx_u32, &a_ref, &b_ref);
            let ordering_ty = Expr::const_str("Ordering");
            let caseson_u = Level::succ(Level::zero());
            for idx in (0..last_idx).rev() {
                let idx_u32 = u32::try_from(idx).unwrap_or(u32::MAX);
                let field_cmp =
                    self.build_field_ord_resolved(struct_name, fields, idx_u32, &a_ref, &b_ref);
                let motive = Expr::lam(
                    BinderInfo::Default,
                    ordering_ty.clone(),
                    ordering_ty.clone(),
                );
                let cases_on = Expr::const_(
                    Name::from_string("Ordering.casesOn"),
                    vec![caseson_u.clone()],
                );
                result = Expr::apps(
                    cases_on,
                    [
                        motive,
                        field_cmp,
                        Expr::const_str("Ordering.lt"),
                        result,
                        Expr::const_str("Ordering.gt"),
                    ],
                );
            }
            result
        };

        // λ (a b : S …) => body  (abstract b first → BVar 0, then a → BVar 1).
        let mut compare_func = body.abstract_fvar(b_fvar);
        compare_func = Expr::lam(BinderInfo::Default, struct_type.clone(), compare_func);
        compare_func = compare_func.abstract_fvar(a_fvar);
        compare_func = Expr::lam(BinderInfo::Default, struct_type.clone(), compare_func);

        // Ord.mk (S α₁ … αₙ) compare_func — universe-polymorphic (the struct's
        // level depends on the params, unlike the monomorphic `.{0}` path).
        let mut value = Expr::app(
            Expr::app(self.mk_const_str("Ord.mk"), struct_type),
            compare_func,
        );

        self.locals.truncate(saved_locals_len);
        for _ in 0..num_params {
            self.local_instances.pop();
        }

        // Wrap the param/constraint telescope (implicit params, then `[Ord αᵢ]`).
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

        value
    }

    /// Per-field `@Ord.compare fieldTy fieldInst a.idx b.idx` for the parametric
    /// path: `Ord.compare` is left universe-polymorphic (`mk_const_str`) and the
    /// field's `[Ord fieldTy]` instance is resolved against the currently-pushed
    /// local instances (the opened `[Ord αᵢ]` constraint binders). Mirrors
    /// `build_field_beq_resolved`.
    fn build_field_ord_resolved(
        &mut self,
        struct_name: &Name,
        fields: &[SurfaceField],
        idx: u32,
        a_ref: &Expr,
        b_ref: &Expr,
    ) -> Expr {
        let a_field = Expr::proj(struct_name.clone(), idx, a_ref.clone());
        let b_field = Expr::proj(struct_name.clone(), idx, b_ref.clone());

        let field = &fields[idx as usize];
        let field_ty = match self.elaborate(&field.ty) {
            Ok(ty) => ty,
            Err(_) => self.fresh_meta(Expr::type_()),
        };

        let ord_class = Name::from_string("Ord");
        let ord_field_ty = Expr::app(self.mk_const(&ord_class), field_ty.clone());
        let field_inst = self
            .resolve_instance(&ord_field_ty)
            .unwrap_or_else(|| self.fresh_meta(ord_field_ty));

        let ord_compare = self.mk_const_str("Ord.compare");
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ord_compare, field_ty), field_inst),
                a_field,
            ),
            b_field,
        )
    }

    /// Build one field's `Ord` comparison `@Ord.compare.{u} fieldTy fieldInst
    /// a.idx b.idx` for the monomorphic struct path, resolving the field type's
    /// own `Ord` instance from the environment (mirrors `build_field_beq`). If the
    /// instance is unresolvable a fresh metavariable is used, matching the BEq
    /// path's behavior.
    fn build_field_ord(
        &mut self,
        struct_name: &Name,
        fields: &[SurfaceField],
        idx: u32,
        a_ref: &Expr,
        b_ref: &Expr,
        ord_u: &Level,
    ) -> Expr {
        let a_field = Expr::proj(struct_name.clone(), idx, a_ref.clone());
        let b_field = Expr::proj(struct_name.clone(), idx, b_ref.clone());

        let field = &fields[idx as usize];
        let field_ty = match self.elaborate(&field.ty) {
            Ok(ty) => ty,
            Err(_) => self.fresh_meta(Expr::type_()),
        };

        let ord_class = Name::from_string("Ord");
        let ord_field_ty = Expr::app(self.mk_const(&ord_class), field_ty.clone());
        let field_inst = self
            .resolve_instance(&ord_field_ty)
            .unwrap_or_else(|| self.fresh_meta(ord_field_ty));

        let ord_compare = Expr::const_(Name::from_string("Ord.compare"), vec![ord_u.clone()]);
        // @Ord.compare fieldTy fieldInst a.idx b.idx
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ord_compare, field_ty), field_inst),
                a_field,
            ),
            b_field,
        )
    }

    /// Derive Nonempty instance for a structure
    ///
    /// Generates: `instance : Nonempty StructName := ⟨StructName.mk default ... default⟩`
    pub(super) fn derive_nonempty(
        &mut self,
        struct_name: &Name,
        binders: &[SurfaceBinder],
        fields: &[SurfaceField],
    ) -> DerivedInstance {
        let instance_name = Name::from_string(&format!("inst{struct_name}Nonempty"));
        let class_name = Name::from_string("Nonempty");
        let num_params = binders.len();

        let (instance_ty, _num_constraints) =
            self.build_parametric_instance_type(struct_name, binders, &class_name);

        // Build a witness: StructName.mk default ... default
        let ctor_name_str = format!("{struct_name}.mk");
        let mut ctor_app = self.mk_const_str(&ctor_name_str);

        // Apply type parameters for parametric structures
        for i in 0..num_params {
            let var_idx = num_params * 2 - 1 - i;
            let var_idx_u32 = u32::try_from(var_idx).unwrap_or(u32::MAX);
            ctor_app = Expr::app(ctor_app, Expr::bvar(var_idx_u32));
        }

        // Apply default values for each field
        for field in fields {
            let field_ty = match self.elaborate(&field.ty) {
                Ok(ty) => ty,
                Err(_) => self.fresh_meta(Expr::type_()),
            };
            let inhabited_default = self.mk_const_str("Inhabited.default");
            let default_val = Expr::app(inhabited_default, field_ty);
            ctor_app = Expr::app(ctor_app, default_val);
        }

        // Nonempty.intro witness
        let core_instance_val = Expr::app(self.mk_const_str("Nonempty.intro"), ctor_app);

        let instance_val =
            self.wrap_parametric_instance_value(core_instance_val, num_params, &class_name);

        DerivedInstance {
            name: instance_name,
            class_name,
            ty: instance_ty,
            val: instance_val,
            priority: 100,
            level_params: vec![],
        }
    }

    /// Derive ToString instance for a structure
    ///
    /// Generates: `instance : ToString StructName where`
    ///   `toString s := reprStr s`
    ///
    /// Delegates to Repr for the actual string representation.
    pub(super) fn derive_to_string(
        &mut self,
        struct_name: &Name,
        binders: &[SurfaceBinder],
        _field_names: &[Name],
    ) -> DerivedInstance {
        let instance_name = Name::from_string(&format!("inst{struct_name}ToString"));
        let class_name = Name::from_string("ToString");
        let num_params = binders.len();

        let (instance_ty, _num_constraints) =
            self.build_parametric_instance_type(struct_name, binders, &class_name);

        let struct_type = if num_params == 0 {
            self.mk_const(struct_name)
        } else {
            self.build_parametric_struct_type(struct_name, num_params, num_params)
        };

        // Build: fun s => reprStr s
        // reprStr delegates to Repr.reprPrec with precedence 0
        let s_ref = Expr::bvar(0);
        let body = Expr::app(self.mk_const_str("reprStr"), s_ref);
        let to_string_func = Expr::lam(BinderInfo::Default, struct_type, body);

        let core_instance_val = Expr::app(self.mk_const_str("ToString.mk"), to_string_func);

        let instance_val =
            self.wrap_parametric_instance_value(core_instance_val, num_params, &class_name);

        DerivedInstance {
            name: instance_name,
            class_name,
            ty: instance_ty,
            val: instance_val,
            priority: 100,
            level_params: vec![],
        }
    }

    /// Derive Functor instance for a structure (stub)
    ///
    /// Registers the Functor class for the type but uses a default
    /// identity-like mapping. Full functorial map requires analyzing
    /// which fields depend on the type parameter.
    pub(super) fn derive_functor(
        &mut self,
        struct_name: &Name,
        binders: &[SurfaceBinder],
    ) -> DerivedInstance {
        let instance_name = Name::from_string(&format!("inst{struct_name}Functor"));
        let class_name = Name::from_string("Functor");
        let num_params = binders.len();

        let (instance_ty, _num_constraints) =
            self.build_parametric_instance_type(struct_name, binders, &class_name);

        // Build a stub Functor.mk with a default map function
        // map : (α → β) → F α → F β
        // Default: use sorry (placeholder) since full analysis of covariant
        // positions requires field type inspection
        let core_instance_val = Expr::app(
            self.mk_const_str("Functor.mk"),
            self.mk_const_str("Functor.map"),
        );

        let instance_val =
            self.wrap_parametric_instance_value(core_instance_val, num_params, &class_name);

        DerivedInstance {
            name: instance_name,
            class_name,
            ty: instance_ty,
            val: instance_val,
            priority: 100,
            level_params: vec![],
        }
    }

    /// Derive Foldable instance for a structure (stub)
    ///
    /// Registers the Foldable class for the type. Full implementation
    /// requires analyzing which fields contain the type parameter.
    pub(super) fn derive_foldable(
        &mut self,
        struct_name: &Name,
        binders: &[SurfaceBinder],
    ) -> DerivedInstance {
        let instance_name = Name::from_string(&format!("inst{struct_name}Foldable"));
        let class_name = Name::from_string("Foldable");
        let num_params = binders.len();

        let (instance_ty, _num_constraints) =
            self.build_parametric_instance_type(struct_name, binders, &class_name);

        // Build a stub Foldable.mk with default fold function
        let core_instance_val = Expr::app(
            self.mk_const_str("Foldable.mk"),
            self.mk_const_str("Foldable.foldl"),
        );

        let instance_val =
            self.wrap_parametric_instance_value(core_instance_val, num_params, &class_name);

        DerivedInstance {
            name: instance_name,
            class_name,
            ty: instance_ty,
            val: instance_val,
            priority: 100,
            level_params: vec![],
        }
    }

    /// Derive Traversable instance for a structure (stub)
    ///
    /// Registers the Traversable class for the type. Full implementation
    /// requires analyzing which fields contain the type parameter and
    /// sequencing effects through an applicative functor.
    pub(super) fn derive_traversable(
        &mut self,
        struct_name: &Name,
        binders: &[SurfaceBinder],
    ) -> DerivedInstance {
        let instance_name = Name::from_string(&format!("inst{struct_name}Traversable"));
        let class_name = Name::from_string("Traversable");
        let num_params = binders.len();

        let (instance_ty, _num_constraints) =
            self.build_parametric_instance_type(struct_name, binders, &class_name);

        // Build a stub Traversable.mk with default traverse function
        let core_instance_val = Expr::app(
            self.mk_const_str("Traversable.mk"),
            self.mk_const_str("Traversable.traverse"),
        );

        let instance_val =
            self.wrap_parametric_instance_value(core_instance_val, num_params, &class_name);

        DerivedInstance {
            name: instance_name,
            class_name,
            ty: instance_ty,
            val: instance_val,
            priority: 100,
            level_params: vec![],
        }
    }
}
