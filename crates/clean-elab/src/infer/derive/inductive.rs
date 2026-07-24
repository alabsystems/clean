// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Inductive-specific derive implementations.

use super::decidable_eq_enum::{all_ctors_nullary, build_body as build_enum_decidable_eq_body};
use super::nested_detect::any_ctor_has_nested_container;
use crate::infer::{DerivedInstance, ElabCtx};
use crate::ElabError;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, Level};
use clean_parser::{SurfaceBinder, SurfaceCtor, SurfaceExpr};

/// Inductive-specific derive implementations
impl<'a> ElabCtx<'a> {
    /// Derive BEq for an inductive type
    ///
    /// For enumeration-like inductives (constructors with no arguments),
    /// generates a simple comparison based on constructor equality.
    ///
    /// Universe handling (#3429): BEq.{u} : Type u -> Type u. For a
    /// monomorphic type T : Type 0, we need BEq.{0}. The generic
    /// concretize_monomorphic_instance substitutes the sort level
    /// (Succ(Zero) for Type 0), giving BEq.{1} which is wrong. Fix: for
    /// monomorphic types, use explicit Level::zero() for BEq's param and
    /// Level::succ(Level::zero()) for casesOn's motive param (motive
    /// returns Bool : Sort 1).
    ///
    /// Unsupported field/parameter/recursion shapes fail closed. In particular,
    /// reflexivity alone does not make a constant-`true` comparator a derived
    /// equality: distinct values must compare false.
    pub(super) fn derive_beq_inductive(
        &mut self,
        ind_name: &Name,
        binders: &[SurfaceBinder],
        ctors: &[SurfaceCtor],
        ctor_names: &[Name],
    ) -> Result<DerivedInstance, ElabError> {
        let instance_name = Name::from_string(&format!("inst{ind_name}BEq"));
        let class_name = Name::from_string("BEq");
        let num_params = binders.len();
        let is_monomorphic = num_params == 0;

        // BEq.{u} takes Type u, so for monomorphic T : Type 0, u = 0.
        let beq_u = Level::zero();

        // Build instance type: BEq.{0} IndName for monomorphic types
        let instance_ty = if is_monomorphic {
            let ind_const = Expr::const_(ind_name.clone(), vec![]);
            let beq_const = Expr::const_(Name::from_string("BEq"), vec![beq_u.clone()]);
            Expr::app(beq_const, ind_const)
        } else {
            let (ty, _) = self.build_parametric_instance_type(ind_name, binders, &class_name);
            ty
        };

        // Parametric single-ctor shape whose every field is a type parameter
        // (`Box a`, `Pair a b`): a real fvar-based `BEq`
        // (`mk x… == mk y… ≡ (x₀ == y₀) && …`), replacing the weak `Bool.true`
        // fallback. Other parametric shapes still fall through below.
        if !is_monomorphic && ctor_names.len() == 1 {
            if let Some(field_params) = all_param_fields(binders, ctors) {
                if let Some(val) = self.build_beq_parametric(ind_name, num_params, &field_params) {
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

        // Parametric MULTI-ctor shape whose every field is a type parameter
        // (`MyOpt a`, `Sum a b`): a real fvar-based `BEq` nesting `casesOn` on
        // both scrutinees (diagonal folds fields, off-diagonal ⇒ `Bool.false`),
        // retiring the weak `Bool.true` total fallback (silent-wrong S2).
        if !is_monomorphic && ctor_names.len() >= 2 {
            if let Some(per_ctor) = multi_ctor_param_fields(binders, ctors) {
                if let Some(val) =
                    self.build_beq_parametric_multi(ind_name, num_params, &per_ctor, ctor_names)
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

        // Parametric single-parameter DIRECTLY self-recursive shape (`Tree a`):
        // drive the parametric recursor `@Ind.rec.{1} p motive minors… a b` so
        // recursive `Ind p` sub-fields compare via the per-field induction
        // hypothesis and the `a` field via `[BEq a]`. See
        // `beq_parametric_recursive.rs`.
        if !is_monomorphic {
            if let Some(per_ctor) = super::beq_parametric_recursive::classify_single_param_recursive(
                ind_name, binders, ctors,
            ) {
                if let Some(val) =
                    self.build_beq_parametric_recursive(ind_name, &per_ctor, ctor_names)
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

        // Build type for lambda annotations
        let ind_type = if is_monomorphic {
            Expr::const_(ind_name.clone(), vec![])
        } else {
            self.build_parametric_struct_type(ind_name, num_params, num_params)
        };

        // Detect nested inductive containers in any ctor field (#3434). When
        // detected, `ind_name.casesOn` gets a mutual-block signature that our
        // single-motive casesOn application can't match.
        let ind_name_str = ind_name.to_string();
        let has_nested_container = any_ctor_has_nested_container(self.env, &ind_name_str, ctors);

        // Generate BEq comparison using casesOn for multi-constructor inductives.
        //
        // casesOn.{u} : {motive : T -> Sort u} -> (t : T) -> ... -> motive t
        // For BEq, motive is (lambda (_ : T) => Bool). The motive is implicit
        // but must be supplied explicitly at the kernel level.
        // Field-binding path (monomorphic, one-or-more constructors): bind each constructor's
        // fields in the `casesOn` minors and compare them pairwise. Only valid
        // when (a) the inductive is monomorphic, (b) it has no nested container
        // (whose mutual-block `casesOn` we can't drive with a single motive),
        // and (c) no constructor has a *recursive* field (a self-referential
        // `@BEq.beq Ind self …` would need brecOn, not casesOn). When any of
        // these fail, deriving rejects instead of installing a bogus equality.
        let ctor_fields = if is_monomorphic && !ctor_names.is_empty() && !has_nested_container {
            self.collect_ctor_fields(ind_name, ctors)
        } else {
            None
        };
        // Use field-binding only when every constructor field is non-recursive
        // AND its `BEq fieldTy` instance resolves to a closed term (so the
        // committed instance never "contains free variables").
        let use_field_binding = match ctor_fields.as_ref() {
            Some(cf) if cf.iter().all(|c| !c.has_recursive_field) => {
                self.all_field_beq_instances_closed(cf)
            }
            _ => false,
        };

        // Recursive path (Track L / Track P): when the inductive is monomorphic,
        // multi-ctor, and has a recursive field — either a DIRECT self-reference
        // (`vector : Nat -> Ty`, num_motives=1) or a nested `List Self` field
        // (`tuple : List Ty`, num_motives=2, mutual block) — drive the kernel's
        // own recursor `Ind.rec` so recursive sub-terms compare with the type's
        // OWN BEq (via the per-field induction hypothesis) and `List Self` fields
        // compare element-wise. The SAME enum may mix both shapes. The builder
        // returns `None` (fall through) for shapes it doesn't support.
        //
        // We attempt it whenever there's a nested container (which always implies
        // a recursive field) OR the non-nested field analysis found a recursive
        // field. The builder itself re-analyzes and bails to `None` if there is
        // no recursive field after all.
        let has_direct_recursive_field = ctor_fields
            .as_ref()
            .map(|cf| cf.iter().any(|c| c.has_recursive_field))
            .unwrap_or(false);
        let recursive_body = if is_monomorphic
            && !ctor_names.is_empty()
            && (has_nested_container || has_direct_recursive_field)
        {
            let a_ref = Expr::bvar(1);
            let b_ref = Expr::bvar(0);
            self.build_beq_recursive(ind_name, &ind_type, ctors, &a_ref, &b_ref)
        } else {
            None
        };

        let body = if ctor_names.is_empty() || (ctor_names.len() == 1 && all_ctors_nullary(ctors)) {
            // Empty or single-nullary types are subsingleton, so true is exact.
            Expr::const_(Name::from_string("Bool.true"), vec![])
        } else if let Some(rec_body) = recursive_body {
            // Real recursive comparison via `Ind.rec` (see `beq_recursive`).
            rec_body
        } else if use_field_binding {
            // Real field-binding comparison (see `beq_inductive`).
            let a_ref = Expr::bvar(1);
            let b_ref = Expr::bvar(0);
            self.build_beq_inductive_body(
                ind_name,
                &ind_type,
                ctor_names,
                ctor_fields.as_ref().expect("checked Some"),
                &a_ref,
                &b_ref,
            )?
        } else {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "deriving BEq for `{ind_name}` requires a structural comparator for every \
                     constructor field; this shape is unsupported and no constant-true \
                     fallback is admitted"
                ),
            });
        };

        // lambda (a : Ind) (b : Ind) => body
        let inner_lam = Expr::lam(BinderInfo::Default, ind_type.clone(), body);
        let beq_func = Expr::lam(BinderInfo::Default, ind_type.clone(), inner_lam);

        // BEq.mk.{0} IndType beq_func for monomorphic types.
        // BEq.mk.{u} : {α : Type u} → (α → α → Bool) → BEq α
        // The α parameter is implicit but must be supplied at kernel level.
        let core_instance_val = if is_monomorphic {
            let beq_mk = Expr::const_(Name::from_string("BEq.mk"), vec![beq_u]);
            let ind_const = Expr::const_(ind_name.clone(), vec![]);
            Expr::app(Expr::app(beq_mk, ind_const), beq_func)
        } else {
            Expr::app(self.mk_const_str("BEq.mk"), beq_func)
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

    /// Prepare the internal bootstrap value for a built-in inductive `Repr`.
    ///
    /// The final constructor-aware body is materialized by the registration
    /// transaction *after* the kernel has installed the inductive.  That timing
    /// is required for recursive/nested inductives: only then do the genuine
    /// recursor packet, auxiliary motives, and constructor metadata exist.  The
    /// closed body built here is an internal handoff only: the derive dispatcher
    /// replaces it immediately using a kernel-registered candidate environment,
    /// before admission or construction of the public elaboration result.
    pub(super) fn derive_repr_inductive(
        &mut self,
        ind_name: &Name,
        binders: &[SurfaceBinder],
        ctors: &[SurfaceCtor],
        ctor_names: &[Name],
    ) -> Result<DerivedInstance, ElabError> {
        if !binders.is_empty() {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "deriving Repr for `{ind_name}` does not yet synthesize parameter constraints"
                ),
            });
        }
        let _ = (ctors, ctor_names);

        let ind_ty = Expr::const_(ind_name.clone(), vec![]);
        let instance_ty = Expr::app(
            Expr::const_(Name::from_string("Repr"), vec![Level::zero()]),
            ind_ty.clone(),
        );
        let provisional_repr = Expr::lam(
            BinderInfo::Default,
            ind_ty.clone(),
            Expr::lam(
                BinderInfo::Default,
                Expr::const_(Name::from_string("Nat"), vec![]),
                Expr::str_lit(ind_name.to_string()),
            ),
        );
        let provisional_val = Expr::apps(
            Expr::const_(Name::from_string("Repr.mk"), vec![Level::zero()]),
            [ind_ty, provisional_repr],
        );

        Ok(DerivedInstance {
            name: Name::from_string(&format!("inst{ind_name}Repr")),
            class_name: Name::from_string("Repr"),
            ty: instance_ty,
            val: provisional_val,
            priority: 100,
            level_params: vec![],
        })
    }

    /// Derive Inhabited for an inductive type
    ///
    /// Uses the first constructor as the default value.
    pub(super) fn derive_inhabited_inductive(
        &mut self,
        ind_name: &Name,
        binders: &[SurfaceBinder],
        ctors: &[SurfaceCtor],
        ctor_names: &[Name],
    ) -> Result<DerivedInstance, ElabError> {
        if !binders.is_empty() || ctor_names.is_empty() || !all_ctors_nullary(ctors) {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "deriving Inhabited for `{ind_name}` requires a monomorphic inductive with a closed nullary constructor"
                ),
            });
        }

        let instance_name = Name::from_string(&format!("inst{ind_name}Inhabited"));
        let class_name = Name::from_string("Inhabited");
        let u = Level::succ(Level::zero());
        let ind_type = Expr::const_(ind_name.clone(), vec![]);
        let instance_ty = Expr::app(
            Expr::const_(class_name.clone(), vec![u.clone()]),
            ind_type.clone(),
        );
        let default_val = Expr::const_(ctor_names[0].clone(), vec![]);
        let instance_val = Expr::apps(
            Expr::const_(Name::from_string("Inhabited.mk"), vec![u]),
            [ind_type, default_val],
        );

        Ok(DerivedInstance {
            name: instance_name,
            class_name,
            ty: instance_ty,
            val: instance_val,
            priority: 100,
            level_params: vec![],
        })
    }

    /// Derive DecidableEq for an inductive type
    ///
    /// Universe handling (#3431, #3432): `IndName.casesOn` and
    /// `IndName.noConfusion` are generated by the kernel AFTER the inductive
    /// (and its derived instances) are elaborated, so `mk_const_str` would
    /// fall back to empty levels and trigger a strict-check error
    ///   "Level count mismatch for IndName.casesOn: declared 1 level params,
    ///    got 0".
    ///
    /// For **monomorphic enums with only nullary constructors** — the common
    /// case for `inductive Color | red | green | blue deriving DecidableEq` —
    /// we sidestep the kernel lookup by supplying the universe levels
    /// directly at derive time:
    ///   - `X.casesOn.{1}` (motive returns `Decidable _ : Sort 1`)
    ///   - `X.noConfusion.{0}` (result universe for `P = False : Prop`)
    ///     This produces a real, reducing `Decidable` value: `decide (x = y)`
    ///     evaluates to `Bool.true` / `Bool.false` via iota reduction on `casesOn`
    ///     and the native `decide` reducer (#3432).
    ///
    /// Shapes outside the proof-producing builders fail closed; automatic
    /// deriving never inserts `sorryAx` as a decision procedure.
    pub(super) fn derive_decidable_eq_inductive(
        &mut self,
        ind_name: &Name,
        binders: &[SurfaceBinder],
        ctors: &[SurfaceCtor],
        ctor_names: &[Name],
    ) -> Result<DerivedInstance, ElabError> {
        let instance_name = Name::from_string(&format!("inst{ind_name}DecidableEq"));
        let class_name = Name::from_string("DecidableEq");
        let num_params = binders.len();
        let is_monomorphic = num_params == 0;

        let (instance_ty, _num_constraints) =
            self.build_parametric_instance_type(ind_name, binders, &class_name);

        // Parametric single-ctor shape whose every field is a type parameter
        // (`Box a`, `Pair a b`): a real fvar-based decision procedure (see
        // `decidable_eq_parametric`), no `sorry`, no parametric `noConfusion`.
        // Other parametric shapes still fall through below.
        if !is_monomorphic && ctor_names.len() == 1 {
            if let Some(field_params) = all_param_fields(binders, ctors) {
                if let Some(val) = self.build_decidable_eq_parametric(
                    ind_name,
                    &ctor_names[0],
                    num_params,
                    &field_params,
                ) {
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

        // Parametric MULTI-ctor shape whose every field is a type parameter
        // (`MyOpt a`, `Sum a b`): a real fvar-based decision procedure — nested
        // `casesOn`, diagonal decides fields (isTrue congruence / isFalse
        // projection injectivity), off-diagonal `isFalse` via a `casesOn`
        // discriminator (noConfusion-free — parametric noConfusion is
        // heterogeneous). Retires the `sorry` fallback for Option/Sum shapes.
        if !is_monomorphic && ctor_names.len() >= 2 {
            if let Some(per_ctor) = multi_ctor_param_fields(binders, ctors) {
                if let Some(val) = self.build_decidable_eq_parametric_multi(
                    ind_name, ctor_names, num_params, &per_ctor,
                ) {
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

        // Parametric single-parameter DIRECTLY self-recursive shape (`Tree a`):
        // recursor-driven decision — recursive `Ind p` fields decide via the IH
        // `(t' : Ind p) → Decidable (l = t')`, the `a` field via `[DecidableEq a]`.
        // See `decidable_eq_parametric_recursive.rs`.
        if !is_monomorphic {
            if let Some(per_ctor) = super::beq_parametric_recursive::classify_single_param_recursive(
                ind_name, binders, ctors,
            ) {
                if let Some(val) =
                    self.build_decidable_eq_parametric_recursive(ind_name, &per_ctor, ctor_names)
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

        let ind_type = if is_monomorphic {
            self.mk_const(ind_name)
        } else {
            self.build_parametric_struct_type(ind_name, num_params, num_params)
        };

        let body = if all_ctors_nullary(ctors) {
            // Empty, singleton, or multi-constructor nullary inductive: eliminate
            // both operands through casesOn. This is essential even for a
            // singleton: arbitrary variables `a b : T` are not definitionally
            // equal, so `Eq.refl a` alone cannot prove `a = b`.
            build_enum_decidable_eq_body(ind_name, ctor_names, &ind_type)
        } else if let Some(real_body) = (is_monomorphic && !ctor_names.is_empty())
            .then(|| self.build_decidable_eq_fielded(ind_name, &ind_type, ctors))
            .flatten()
        {
            // Monomorphic inductive (one or more ctors) whose (non-recursive)
            // ctor fields each have a resolvable `DecidableEq` instance: emit a
            // REAL decision procedure via per-field decEq dispatch + `congrArg` /
            // `noConfusion` (Track L/P/T). Multi-field ctors chain
            // `congrArg`/`Eq.trans` over the partially-applied constructor. A
            // single fielded ctor (`Pr.mk : Nat -> Nat -> Pr`) decides its lone
            // same-ctor diagonal. No `sorry`. Implementation in
            // `super::decidable_eq_fielded::build_decidable_eq_fielded`.
            real_body
        } else if let Some(real_body) = (is_monomorphic && !ctor_names.is_empty())
            .then(|| self.build_decidable_eq_recursive(ind_name, &ind_type, ctors))
            .flatten()
        {
            // Monomorphic multi-ctor inductive with DIRECT self-recursive fields
            // (`vector : Nat -> Ty`): emit a REAL decision procedure driven by the
            // type's own recursor `Ind.rec`, deciding recursive sub-terms via the
            // structural induction hypothesis (Track P). No `sorry`. Implementation
            // in `super::decidable_eq_recursive::build_decidable_eq_recursive`.
            real_body
        } else if let Some(real_body) = (is_monomorphic && !ctor_names.is_empty())
            .then(|| self.build_decidable_eq_list_recursive(ind_name, &ind_type, ctors))
            .flatten()
        {
            // Monomorphic inductive with a NESTED `List Self` field
            // (`tuple : List Ty -> Ty`): the kernel rewrites this into a mutual
            // block with an aux `Ind._List` type (`num_motives = 2`). Emit a REAL
            // decision procedure driven by the mutual `Ind.rec`, deciding recursive
            // sub-terms (both `Ind` and `Ind._List`) via structural IHs (Track T).
            // No `sorry`. Implementation in
            // `super::decidable_eq_list_recursive::build_decidable_eq_list_recursive`.
            real_body
        } else {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "deriving DecidableEq for `{ind_name}` has no proof-producing handler for \
                     this constructor/parameter shape; automatic deriving refuses `sorryAx`"
                ),
            });
        };

        // λ (a : Ind) (b : Ind) => body
        let inner_lam = Expr::lam(BinderInfo::Default, ind_type.clone(), body);
        let dec_eq_func = Expr::lam(BinderInfo::Default, ind_type.clone(), inner_lam);

        // DecidableEq is a definition (not a structure), so there's no
        // DecidableEq.mk constructor. The instance value IS the function.
        let core_instance_val = dec_eq_func;

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
}

/// For a single-constructor parametric inductive whose every field's type is one
/// of the type parameters (`inductive Pair (a b : Type) | mk : a -> b -> Pair a b`,
/// or `Box a`), return the field→parameter-index mapping. `None` for any other
/// shape (a nullary ctor, a non-parameter field type, multiple ctors, …).
fn all_param_fields(binders: &[SurfaceBinder], ctors: &[SurfaceCtor]) -> Option<Vec<usize>> {
    fn peel(e: &SurfaceExpr) -> &SurfaceExpr {
        match e {
            SurfaceExpr::Paren(_, inner) => peel(inner),
            other => other,
        }
    }
    if ctors.len() != 1 || binders.is_empty() {
        return None;
    }
    let pnames: Vec<&str> = binders.iter().map(|b| b.name.as_str()).collect();
    let mut field_params = Vec::new();
    let mut cur = peel(&ctors[0].ty);
    while let SurfaceExpr::Arrow(_, dom, cod) = cur {
        match peel(dom) {
            SurfaceExpr::Ident(_, n) => {
                let idx = pnames.iter().position(|p| p == n)?;
                field_params.push(idx);
            }
            _ => return None,
        }
        cur = peel(cod);
    }
    if field_params.is_empty() {
        None
    } else {
        Some(field_params)
    }
}

/// Multi-constructor generalization of [`all_param_fields`]: for EACH ctor,
/// require every field's type to be a bare type parameter (a nullary ctor maps
/// to `[]`), and return the per-ctor field→param-index maps in declaration
/// order. `None` if any field is not a bare parameter (e.g. a recursive `Ind a`
/// field, which needs the recursor, or an applied type). Covers `Option`/`Sum`/
/// enum-of-params shapes; feeds `build_beq_parametric_multi`.
pub(super) fn multi_ctor_param_fields(
    binders: &[SurfaceBinder],
    ctors: &[SurfaceCtor],
) -> Option<Vec<Vec<usize>>> {
    fn peel(e: &SurfaceExpr) -> &SurfaceExpr {
        match e {
            SurfaceExpr::Paren(_, inner) => peel(inner),
            other => other,
        }
    }
    if binders.is_empty() || ctors.is_empty() {
        return None;
    }
    let pnames: Vec<&str> = binders.iter().map(|b| b.name.as_str()).collect();
    let mut per_ctor = Vec::with_capacity(ctors.len());
    for ctor in ctors {
        let mut field_params = Vec::new();
        let mut cur = peel(&ctor.ty);
        while let SurfaceExpr::Arrow(_, dom, cod) = cur {
            match peel(dom) {
                SurfaceExpr::Ident(_, n) => {
                    let idx = pnames.iter().position(|p| p == n)?;
                    field_params.push(idx);
                }
                _ => return None,
            }
            cur = peel(cod);
        }
        per_ctor.push(field_params);
    }
    Some(per_ctor)
}
