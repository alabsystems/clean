// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended inductive derive implementations for additional typeclasses:
//! Ord, Nonempty, ToString, Functor, Foldable, Traversable.

use crate::infer::{DerivedInstance, ElabCtx};
use crate::ElabError;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, FVarId, Level};
use clean_parser::{SurfaceBinder, SurfaceCtor};

/// Extended inductive derive implementations
impl<'a> ElabCtx<'a> {
    /// Derive Ord for an inductive type
    ///
    /// For enumeration-like inductives, generates ordering based on
    /// constructor index (first constructor < second < ...).
    pub(super) fn derive_ord_inductive(
        &mut self,
        ind_name: &Name,
        binders: &[SurfaceBinder],
        ctors: &[SurfaceCtor],
        ctor_names: &[Name],
    ) -> Result<DerivedInstance, ElabError> {
        let instance_name = Name::from_string(&format!("inst{ind_name}Ord"));
        let class_name = Name::from_string("Ord");
        let num_params = binders.len();

        let (instance_ty, _num_constraints) =
            self.build_parametric_instance_type(ind_name, binders, &class_name);

        // Parametric shape whose every field is a type parameter (`Box a`,
        // `MyOpt a`, `Sum a b`): a real fvar-based comparison threading `[Ord a]`,
        // replacing the weak `Ordering.eq` fallback (a reachable silent-wrong now
        // that `Ord` is wired into the prelude). See `ord_parametric.rs`.
        if num_params > 0 {
            if let Some(per_ctor) = super::inductive::multi_ctor_param_fields(binders, ctors) {
                if let Some(val) =
                    self.build_ord_parametric(ind_name, num_params, &per_ctor, ctor_names)
                {
                    return Ok(DerivedInstance {
                        name: instance_name,
                        class_name,
                        ty: instance_ty,
                        val,
                        priority: 100,
                        level_params: vec![],
                    });
                }
            }
            // Single-parameter directly self-recursive shape (`Tree a`): drive the
            // parametric recursor with a per-field IH (`Ordering.then` chain of
            // per-field `Ord.compare`; recursive fields via the IH). See
            // `ord_parametric_recursive.rs`.
            if let Some(per_ctor) = super::beq_parametric_recursive::classify_single_param_recursive(
                ind_name, binders, ctors,
            ) {
                if let Some(val) =
                    self.build_ord_parametric_recursive(ind_name, &per_ctor, ctor_names)
                {
                    return Ok(DerivedInstance {
                        name: instance_name,
                        class_name,
                        ty: instance_ty,
                        val,
                        priority: 100,
                        level_params: vec![],
                    });
                }
            }
        }

        let ind_type = if num_params == 0 {
            self.mk_const(ind_name)
        } else {
            self.build_parametric_struct_type(ind_name, num_params, num_params)
        };

        // Build the `compare` function. `a = bvar(1)`, `b = bvar(0)` inside the
        // `λ (a b : Ind) => body` context built below.
        //
        // Monomorphic types get a REAL nested-`casesOn` decision that compares
        // FIELDS on the same-ctor diagonal (via `Ord.compare` chained with
        // `Ordering.then`) and the constructor ordinal (`Nat.compare`) off the
        // diagonal — retiring the field-ignoring silent-wrong where distinct
        // same-ctor values (`Val.mkA 1` vs `Val.mkA 2`) compared `Ordering.eq`.
        // `build_ord_inductive_body` also covers nullary enums and a single
        // fielded ctor. The old ordinal-only body additionally mis-built
        // `casesOn` without a motive (`Level count mismatch`), so it never
        // kernel-checked once `Ord` was wired into the prelude.
        let body = if ctor_names.is_empty() {
            Expr::const_(Name::from_string("Ordering.eq"), vec![])
        } else if num_params == 0 {
            // Per-ctor field types, only when every field is non-recursive.
            let per_ctor: Option<Vec<Vec<Expr>>> = self
                .collect_ctor_fields(ind_name, ctors)
                .filter(|cf| cf.iter().all(|c| !c.has_recursive_field))
                .map(|cf| cf.iter().map(|c| c.field_types.clone()).collect());
            match per_ctor {
                Some(ref pc) if self.all_field_ord_instances_closed(pc) => {
                    let a_ref = Expr::bvar(1);
                    let b_ref = Expr::bvar(0);
                    self.build_ord_inductive_body(
                        ind_name, &ind_type, ctor_names, pc, &a_ref, &b_ref,
                    )
                }
                _ => {
                    return Err(ElabError::Unsupported {
                        feature: format!(
                            "deriving Ord for `{ind_name}` requires a closed structural comparator for every constructor field"
                        ),
                    });
                }
            }
        } else {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "deriving Ord for `{ind_name}` has no authenticated comparator for this parameter/recursion shape"
                ),
            });
        };

        let inner_lam = Expr::lam(BinderInfo::Default, ind_type.clone(), body);
        let compare_func = Expr::lam(BinderInfo::Default, ind_type.clone(), inner_lam);

        // `Ord.mk.{u} : {α : Type u} → (α → α → Ordering) → Ord α`. The `α` is
        // implicit but must be supplied at the kernel level — for monomorphic
        // `T : Type 0`, `@Ord.mk.{0} T compare_func` (mirrors the BEq derive).
        let core_instance_val = if num_params == 0 {
            let ord_mk = Expr::const_(Name::from_string("Ord.mk"), vec![Level::zero()]);
            let ind_const = Expr::const_(ind_name.clone(), vec![]);
            Expr::app(Expr::app(ord_mk, ind_const), compare_func)
        } else {
            Expr::app(self.mk_const_str("Ord.mk"), compare_func)
        };

        let instance_val =
            self.wrap_parametric_instance_value(core_instance_val, num_params, &class_name);

        Ok(DerivedInstance {
            name: instance_name,
            class_name,
            ty: instance_ty,
            val: instance_val,
            priority: 100,
            level_params: vec![],
        })
    }

    /// Real monomorphic `Ord.compare` body: nested `casesOn` on both scrutinees
    /// (`a = a_ref`, `b = b_ref`). Same-ctor diagonal chains per-field
    /// `Ord.compare` with `Ordering.then`; distinct ctors compare their ordinals
    /// via `Nat.compare`. Mirrors `build_beq_inductive_body`.
    fn build_ord_inductive_body(
        &mut self,
        ind_name: &Name,
        ind_type: &Expr,
        ctor_names: &[Name],
        per_ctor_field_types: &[Vec<Expr>],
        a_ref: &Expr,
        b_ref: &Expr,
    ) -> Expr {
        let motive_u = Level::succ(Level::zero());
        let cases_on_name = Name::from_string(&format!("{ind_name}.casesOn"));
        let ordering = || Expr::const_(Name::from_string("Ordering"), vec![]);
        // Motive `λ _ : Ind => Ordering` (shared by outer and inner casesOn).
        let motive = Expr::lam(BinderInfo::Default, ind_type.clone(), ordering());

        let mut outer_minors = Vec::with_capacity(ctor_names.len());
        for (i, fields_i) in per_ctor_field_types.iter().enumerate() {
            let a_fvars: Vec<FVarId> = fields_i.iter().map(|_| self.fresh_fvar()).collect();

            let mut inner_minors = Vec::with_capacity(ctor_names.len());
            for (j, fields_j) in per_ctor_field_types.iter().enumerate() {
                let b_fvars: Vec<FVarId> = fields_j.iter().map(|_| self.fresh_fvar()).collect();
                let mut minor_body = if i == j {
                    self.build_field_ord_chain(fields_i, &a_fvars, &b_fvars)
                } else {
                    // Distinct ctors ⇒ compare ordinals via `Nat.compare i j`.
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Nat.compare"), vec![]),
                            Expr::nat_lit(i as u64),
                        ),
                        Expr::nat_lit(j as u64),
                    )
                };
                // λ (b_f : T) … => minor_body  (abstract innermost-first).
                for k in (0..b_fvars.len()).rev() {
                    minor_body = minor_body.abstract_fvar(b_fvars[k]);
                    minor_body = Expr::lam(BinderInfo::Default, fields_j[k].clone(), minor_body);
                }
                inner_minors.push(minor_body);
            }

            // Ind.casesOn.{1} motive b inner_minor…
            let mut inner = Expr::app(
                Expr::const_(cases_on_name.clone(), vec![motive_u.clone()]),
                motive.clone(),
            );
            inner = Expr::app(inner, b_ref.clone());
            for m in inner_minors {
                inner = Expr::app(inner, m);
            }

            // λ (a_f : T) … => inner  (abstract innermost-first).
            let mut outer_minor = inner;
            for k in (0..a_fvars.len()).rev() {
                outer_minor = outer_minor.abstract_fvar(a_fvars[k]);
                outer_minor = Expr::lam(BinderInfo::Default, fields_i[k].clone(), outer_minor);
            }
            outer_minors.push(outer_minor);
        }

        // Ind.casesOn.{1} motive a outer_minor…
        let mut outer = Expr::app(Expr::const_(cases_on_name, vec![motive_u]), motive);
        outer = Expr::app(outer, a_ref.clone());
        for m in outer_minors {
            outer = Expr::app(outer, m);
        }
        outer
    }

    /// `(Ord.compare T₀ i₀ a₀ b₀).then (… .then (Ord.compare T_{k-1} …))`, or
    /// `Ordering.eq` when there are no fields. Folded so the FIRST field is the
    /// most significant (lexicographic).
    fn build_field_ord_chain(
        &mut self,
        field_types: &[Expr],
        a_fvars: &[FVarId],
        b_fvars: &[FVarId],
    ) -> Expr {
        let mut acc: Option<Expr> = None;
        for k in (0..field_types.len()).rev() {
            let cmp = self.build_field_ord_compare(
                &field_types[k],
                Expr::fvar(a_fvars[k]),
                Expr::fvar(b_fvars[k]),
            );
            acc = Some(match acc {
                None => cmp,
                Some(rest) => self.build_ordering_then(cmp, rest),
            });
        }
        acc.unwrap_or_else(|| Expr::const_(Name::from_string("Ordering.eq"), vec![]))
    }

    /// `@Ord.compare fieldTy fieldInst a b`, resolving `[Ord fieldTy]` to a
    /// closed term (the caller restricts this path to ground field types).
    fn build_field_ord_compare(&mut self, field_ty: &Expr, a: Expr, b: Expr) -> Expr {
        let ord_class = Name::from_string("Ord");
        let ord_field_ty = Expr::app(self.mk_const(&ord_class), field_ty.clone());
        let field_inst = self
            .resolve_instance(&ord_field_ty)
            .unwrap_or_else(|| self.fresh_meta(ord_field_ty));
        let ord_compare = self.mk_const_str("Ord.compare");
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ord_compare, field_ty.clone()), field_inst),
                a,
            ),
            b,
        )
    }

    /// `Ordering.then x y` inlined via `Ordering.casesOn` (no dependency on a
    /// prelude `Ordering.then`): `x = lt ⇒ lt`, `x = eq ⇒ y`, `x = gt ⇒ gt`.
    fn build_ordering_then(&mut self, x: Expr, y: Expr) -> Expr {
        let motive_u = Level::succ(Level::zero());
        let ordering = Expr::const_(Name::from_string("Ordering"), vec![]);
        // motive: λ _ : Ordering => Ordering
        let motive = Expr::lam(BinderInfo::Default, ordering.clone(), ordering);
        // @Ordering.casesOn.{1} motive x Ordering.lt y Ordering.gt
        let mut e = Expr::app(
            Expr::const_(Name::from_string("Ordering.casesOn"), vec![motive_u]),
            motive,
        );
        e = Expr::app(e, x);
        e = Expr::app(e, Expr::const_(Name::from_string("Ordering.lt"), vec![]));
        e = Expr::app(e, y);
        e = Expr::app(e, Expr::const_(Name::from_string("Ordering.gt"), vec![]));
        e
    }

    /// Every field's `[Ord fieldTy]` instance resolves to a closed term.
    fn all_field_ord_instances_closed(&mut self, per_ctor_field_types: &[Vec<Expr>]) -> bool {
        let ord_class = Name::from_string("Ord");
        for fields in per_ctor_field_types {
            for fty in fields {
                let goal = Expr::app(self.mk_const(&ord_class), fty.clone());
                match self.resolve_instance(&goal) {
                    Some(inst) if !inst.has_fvar_quick() && !self.has_metavars(&inst) => {}
                    _ => return false,
                }
            }
        }
        true
    }

    /// Derive Nonempty for an inductive type
    ///
    /// Uses the first constructor as a witness. Returns None if there
    /// are no constructors (the type would be empty).
    pub(super) fn derive_nonempty_inductive(
        &mut self,
        ind_name: &Name,
        binders: &[SurfaceBinder],
        _ctors: &[SurfaceCtor],
        ctor_names: &[Name],
    ) -> Option<DerivedInstance> {
        if ctor_names.is_empty() {
            return None;
        }

        let instance_name = Name::from_string(&format!("inst{ind_name}Nonempty"));
        let class_name = Name::from_string("Nonempty");
        let num_params = binders.len();

        let (instance_ty, _num_constraints) =
            self.build_parametric_instance_type(ind_name, binders, &class_name);

        // Use the first constructor as a witness (works for nullary constructors)
        let first_ctor_name = &ctor_names[0];
        let witness = self.mk_const(first_ctor_name);

        // Nonempty.intro witness
        let core_instance_val = Expr::app(self.mk_const_str("Nonempty.intro"), witness);

        let instance_val =
            self.wrap_parametric_instance_value(core_instance_val, num_params, &class_name);

        Some(DerivedInstance {
            name: instance_name,
            class_name,
            ty: instance_ty,
            val: instance_val,
            priority: 100,
            level_params: vec![],
        })
    }

    /// Derive ToString for an inductive type
    ///
    /// Delegates to Repr via reprStr, same pattern as the structure version.
    pub(super) fn derive_to_string_inductive(
        &mut self,
        ind_name: &Name,
        binders: &[SurfaceBinder],
        _ctors: &[SurfaceCtor],
        _ctor_names: &[Name],
    ) -> DerivedInstance {
        let instance_name = Name::from_string(&format!("inst{ind_name}ToString"));
        let class_name = Name::from_string("ToString");
        let num_params = binders.len();

        let (instance_ty, _num_constraints) =
            self.build_parametric_instance_type(ind_name, binders, &class_name);

        let ind_type = if num_params == 0 {
            self.mk_const(ind_name)
        } else {
            self.build_parametric_struct_type(ind_name, num_params, num_params)
        };

        // Build: fun x => reprStr x
        let x_ref = Expr::bvar(0);
        let body = Expr::app(self.mk_const_str("reprStr"), x_ref);
        let to_string_func = Expr::lam(BinderInfo::Default, ind_type, body);

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

    /// Derive Functor for an inductive type (stub)
    ///
    /// Registers the Functor class. Full implementation requires recursive
    /// analysis of constructor argument types.
    pub(super) fn derive_functor_inductive(
        &mut self,
        ind_name: &Name,
        binders: &[SurfaceBinder],
    ) -> DerivedInstance {
        let instance_name = Name::from_string(&format!("inst{ind_name}Functor"));
        let class_name = Name::from_string("Functor");
        let num_params = binders.len();

        let (instance_ty, _num_constraints) =
            self.build_parametric_instance_type(ind_name, binders, &class_name);

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

    /// Derive Foldable for an inductive type (stub)
    ///
    /// Registers the Foldable class. Full implementation requires recursive
    /// analysis of constructor argument types.
    pub(super) fn derive_foldable_inductive(
        &mut self,
        ind_name: &Name,
        binders: &[SurfaceBinder],
    ) -> DerivedInstance {
        let instance_name = Name::from_string(&format!("inst{ind_name}Foldable"));
        let class_name = Name::from_string("Foldable");
        let num_params = binders.len();

        let (instance_ty, _num_constraints) =
            self.build_parametric_instance_type(ind_name, binders, &class_name);

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

    /// Derive Traversable for an inductive type (stub)
    ///
    /// Registers the Traversable class. Full implementation requires
    /// recursive analysis and effect sequencing.
    pub(super) fn derive_traversable_inductive(
        &mut self,
        ind_name: &Name,
        binders: &[SurfaceBinder],
    ) -> DerivedInstance {
        let instance_name = Name::from_string(&format!("inst{ind_name}Traversable"));
        let class_name = Name::from_string("Traversable");
        let num_params = binders.len();

        let (instance_ty, _num_constraints) =
            self.build_parametric_instance_type(ind_name, binders, &class_name);

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
