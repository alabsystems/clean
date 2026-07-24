// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structure literal elaboration.
//!
//! Handles `SurfaceExpr::StructLit` (structure literals and with-syntax):
//! - `{ x := val, y := val2 }` — direct construction
//! - `{ s with x := val }` — struct update syntax

use super::*;
use crate::agent_diagnostics::nearest_string_candidates;
use clean_parser::{Projection, Span, SurfaceFieldAssign};
use std::collections::HashMap;

impl<'a> ElabCtx<'a> {
    /// Elaborate a structure literal expression.
    ///
    /// Handles three sources for the structure type:
    /// 1. With-syntax base expression: infer type from the base
    /// 2. Explicit type annotation: `{ ... : Foo }`
    /// 3. Expected type from context (bidirectional type checking)
    pub(crate) fn elab_struct_lit(
        &mut self,
        struct_type: &Option<Box<SurfaceExpr>>,
        base: &Option<Box<SurfaceExpr>>,
        fields: &[clean_parser::SurfaceFieldAssign],
    ) -> Result<Expr, ElabError> {
        // Elaborate base if present (with-syntax)
        let base_val = if let Some(base_expr) = base {
            Some(self.elaborate(base_expr)?)
        } else {
            None
        };

        // Determine the structure type expression and structure name.
        let struct_ty = if let Some(ref bv) = base_val {
            // Infer struct type from base expression's type
            let base_ty = self.infer_type(bv)?;
            let base_ty = self.metas.instantiate(&base_ty);
            self.metas.instantiate_levels(&base_ty)
        } else if let Some(ty_expr) = struct_type {
            // Explicit type annotation: { ... : Foo }
            self.elaborate(ty_expr)?
        } else if let Some(expected) = self.expected_type().cloned() {
            self.metas
                .instantiate_levels(&self.metas.instantiate(&expected))
        } else {
            return Err(ElabError::NotImplemented(
                "struct literal requires type annotation or expected type".to_string(),
            ));
        };
        let struct_ty_whnf = self.whnf(&struct_ty);
        let struct_name = self
            .try_get_struct_name_from_type(&struct_ty_whnf)
            .ok_or_else(|| {
                if base_val.is_some() {
                    ElabError::TypeMismatch {
                        expected: "structure type".to_string(),
                        actual: format!("{:?}", struct_ty_whnf),
                    }
                } else if struct_type.is_some() {
                    ElabError::UnknownStruct {
                        name: format!("{:?}", struct_ty_whnf),
                    }
                } else {
                    ElabError::NotImplemented(
                        "struct literal requires type annotation or expected type".to_string(),
                    )
                }
            })?;

        // Inherited-field structure update (`{ c with parentField := v }` where
        // `parentField` is a field of a parent that `c`'s structure `extends`).
        //
        // For an `extends` structure imported from a real Lean `.olean`, the
        // child constructor stores the parent as a single nested subobject
        // (`Child.mk (toParent : Parent) …`), and the inherited projection
        // `Child.parentField` is the *composition* `Parent.parentField
        // (Child.toParent self)` — there is no direct constructor field
        // `parentField` on `Child`. So `{ c with parentField := v }` cannot be
        // resolved by a direct field index; Lean instead rebuilds the nested
        // subobject. We mirror that by rewriting the update into a nested update
        // of the parent subobject and recursing:
        //   `{ c with parentField := v }`
        //     ⇝ `{ c with toParent := { c.toParent with parentField := v } }`
        // Only fields that are *not* direct constructor fields trigger this; the
        // native (flattened) path keeps inherited fields as direct fields, so
        // `struct_field_index` already succeeds there and this rewrite is a
        // no-op for it — native behavior is unchanged.
        if let Some(base_expr) = base {
            if let Some(rewritten) =
                self.rewrite_inherited_field_updates(&struct_name, base_expr, fields)
            {
                return self.elab_struct_lit(struct_type, &Some(base_expr.clone()), &rewritten);
            }
        } else if let Some(rewritten) =
            self.rewrite_parent_subobject_construction(&struct_name, fields)
        {
            // Base-less construction of an `extends` structure: assemble each
            // parent subobject from the flattened field spellings.
            //   `{ x := 1, y := 2 } : B`  (B extends A, x a field of A)
            //     ⇝ `{ toA := { x := 1 }, y := 2 } : B`
            // mirroring Lean's StructInst flattening through the parent
            // subobject (`src/Lean/Elab/StructInst.lean`). Native subobject
            // layout only — a structure with no recorded parents yields `None`
            // and this is a no-op.
            return self.elab_struct_lit(struct_type, base, &rewritten);
        }

        // Build constructor call: StructName.mk field1 field2 ...
        let struct_name_obj = Name::from_string(&struct_name);
        let mk_name = Name::from_string(&format!("{}.mk", struct_name));
        let mk_info = self.env.get_const(&mk_name).ok_or_else(|| {
            ElabError::UnknownIdent(format!("struct constructor {}.mk", struct_name))
        })?;
        let ind_info =
            self.env
                .get_inductive(&struct_name_obj)
                .ok_or_else(|| ElabError::UnknownStruct {
                    name: struct_name.clone(),
                })?;

        // Reuse the structure type's instantiated universe levels so the constructor
        // stays aligned with the surrounding expected/base type.
        let levels: Vec<Level> = match struct_ty_whnf.get_app_fn().kind() {
            ExprKind::Const(_, levels) => levels.to_vec(),
            _ => mk_info
                .level_params
                .iter()
                .map(|_| self.fresh_universe_param())
                .collect(),
        };
        if mk_info.level_params.len() != levels.len() {
            return Err(ElabError::TypeMismatch {
                expected: format!(
                    "{} universe levels for {}.mk",
                    mk_info.level_params.len(),
                    struct_name
                ),
                actual: format!("{} universe levels supplied", levels.len()),
            });
        }
        let level_subst: Vec<(Name, Level)> = mk_info
            .level_params
            .iter()
            .cloned()
            .zip(levels.iter().cloned())
            .collect();
        let ctor_type = mk_info.type_.instantiate_level_params(&level_subst);

        // Field names in constructor order, when available. Native structures
        // carry this table; an imported Lean structure does not (it ships only
        // the projection *functions*), so this may be empty for imports — in
        // which case we drive the construction by the constructor's field count
        // and resolve provided field names to indices via those projections.
        let all_field_name_strings: Vec<String> = self
            .env
            .get_structure_field_names(&struct_name_obj)
            .map(|fields| fields.iter().map(ToString::to_string).collect())
            .unwrap_or_default();

        // Total number of constructor fields (after parameters). For an imported
        // structure with no field-name table this is the authoritative arity.
        // `is_structure_like` only admits single-constructor inductives (or
        // natively-registered structures, which also have exactly one
        // constructor), so the first constructor is the structure's `mk`.
        let num_fields = ind_info
            .constructor_names
            .first()
            .and_then(|ctor_name| self.env.get_constructor(ctor_name))
            .map(|ctor| ctor.num_fields as usize)
            .unwrap_or(all_field_name_strings.len());

        // Build a map of provided field updates keyed by constructor field index.
        // Resolving by index (not name) keeps native and imported structures on
        // the same path: imported field names are mapped through Lean's own
        // projection functions.
        let mut field_updates: HashMap<usize, &clean_parser::SurfaceFieldAssign> = HashMap::new();
        for field_assign in fields {
            let idx = self
                .struct_field_index(&struct_name, &field_assign.name)
                .ok_or_else(|| ElabError::UnknownStructureField {
                    struct_name: struct_name_obj.clone(),
                    field: field_assign.name.clone(),
                    suggestions: nearest_string_candidates(
                        &field_assign.name,
                        all_field_name_strings.iter().map(String::as_str),
                        5,
                    ),
                })?;
            field_updates.insert(idx as usize, field_assign);
        }

        if base_val.is_none() {
            // A field omitted from a base-less literal is only *missing* when it
            // has no default. Lean structure/class fields may carry a default
            // (`field := v`), which is exactly how a default **method** on a
            // type class is encoded; an instance that omits the method inherits
            // the default. Imports ship that default as a sibling definition
            // `<Struct>.<field>._default` (no clean-side default metadata), so a
            // field with a discoverable default must NOT be reported missing.
            let missing_fields: Vec<String> = (0..num_fields)
                .filter(|idx| !field_updates.contains_key(idx))
                .filter(|idx| !self.field_has_default(&struct_name, *idx, &all_field_name_strings))
                .map(|idx| {
                    all_field_name_strings
                        .get(idx)
                        .cloned()
                        .unwrap_or_else(|| format!("field {idx}"))
                })
                .collect();
            if !missing_fields.is_empty() {
                return Err(ElabError::MissingStructureFields {
                    struct_name: struct_name_obj.clone(),
                    fields: missing_fields,
                });
            }
        }

        let mut result = Expr::const_(mk_name, levels.clone());
        let mut result_ty = ctor_type;

        // Structure constructor parameters are part of the telescope. Seed them from the
        // target structure type so later field elaboration sees the correct field types.
        let struct_args: Vec<Expr> = struct_ty_whnf.get_app_args().into_iter().cloned().collect();
        if struct_args.len() < ind_info.num_params as usize {
            return Err(ElabError::TypeMismatch {
                expected: format!(
                    "{} structure parameters for {}",
                    ind_info.num_params, struct_name
                ),
                actual: format!("{} parameters supplied", struct_args.len()),
            });
        }
        for arg in struct_args.iter().take(ind_info.num_params as usize) {
            result_ty = self.whnf(&result_ty);
            let body_ty = match result_ty.kind() {
                ExprKind::Pi(_, _, body_ty) => body_ty.instantiate(arg),
                _ => {
                    return Err(ElabError::TypeMismatch {
                        expected: format!(
                            "constructor telescope for {} with {} parameters",
                            struct_name, ind_info.num_params
                        ),
                        actual: format!("{result_ty:?}"),
                    })
                }
            };
            result = Expr::app(result, arg.clone());
            result_ty = self.metas.instantiate(&body_ty);
        }

        let (mut result, mut result_ty) = self.insert_implicit_args(result, &result_ty);

        // The structure's type-parameter arguments, used to instantiate a field
        // default (Lean's `<Struct>.<field>._default` takes the structure params
        // followed by the values of the *preceding* fields).
        let param_args: Vec<Expr> = struct_args
            .iter()
            .take(ind_info.num_params as usize)
            .cloned()
            .collect();
        // Field values built so far, in constructor order, so a later field's
        // default can depend on the values of earlier fields.
        let mut field_vals: Vec<Expr> = Vec::with_capacity(num_fields);

        // Build field values in constructor order, indexed by position so the
        // path is identical for native (named) and imported (name-less) structs.
        for idx in 0..num_fields {
            result_ty = self.whnf(&result_ty);
            let expected_field_ty = match result_ty.kind() {
                ExprKind::Pi(_, arg_ty, _) => Some(self.metas.instantiate(arg_ty)),
                _ => None,
            };
            // The field name is only used for diagnostics; imported structures
            // may not expose it, in which case we fall back to a positional name.
            let field_name_str = all_field_name_strings
                .get(idx)
                .cloned()
                .unwrap_or_else(|| format!("field {idx}"));
            let field_val = if let Some(field_assign) = field_updates.get(&idx) {
                // Field is being updated - elaborate the provided value with the
                // constructor telescope's expected field type.
                let field_val = self
                    .elaborate_with_expected_type(&field_assign.val, expected_field_ty.clone())
                    .map_err(|err| match (expected_field_ty.as_ref(), err) {
                        (Some(exp_ty), ElabError::TypeMismatch { expected, actual }) => {
                            ElabError::StructureFieldTypeMismatch {
                                struct_name: struct_name_obj.clone(),
                                field: field_name_str.clone(),
                                expected: if expected.is_empty() {
                                    exp_ty.to_string()
                                } else {
                                    expected
                                },
                                actual,
                            }
                        }
                        // A missing/unknown field surfaced while assembling a
                        // nested parent subobject (`toParent := { … }`) is
                        // already a precise, informative error against the
                        // parent; propagate it verbatim rather than reburying it
                        // as a type mismatch on the `toParent` slot (Lean reports
                        // "fields missing 'a'" for the omitted inherited field).
                        (
                            _,
                            err @ (ElabError::MissingStructureFields { .. }
                            | ElabError::UnknownStructureField { .. }),
                        ) => err,
                        (Some(exp_ty), err) => ElabError::StructureFieldTypeMismatch {
                            struct_name: struct_name_obj.clone(),
                            field: field_name_str.clone(),
                            expected: exp_ty.to_string(),
                            actual: err.to_string(),
                        },
                        (None, err) => err,
                    })?;

                if let Some(exp_ty) = expected_field_ty.as_ref() {
                    let actual_ty = self
                        .infer_type(&field_val)
                        .map(|ty| self.metas.instantiate_levels(&self.metas.instantiate(&ty)))
                        .ok();
                    self.enforce_expr_type(&field_val, exp_ty)
                        .map_err(|err| match err {
                            ElabError::TypeMismatch { actual, .. } => {
                                ElabError::StructureFieldTypeMismatch {
                                    struct_name: struct_name_obj.clone(),
                                    field: field_name_str.clone(),
                                    expected: exp_ty.to_string(),
                                    actual,
                                }
                            }
                            err => ElabError::StructureFieldTypeMismatch {
                                struct_name: struct_name_obj.clone(),
                                field: field_name_str.clone(),
                                expected: exp_ty.to_string(),
                                actual: actual_ty
                                    .as_ref()
                                    .map(ToString::to_string)
                                    .unwrap_or_else(|| err.to_string()),
                            },
                        })?;
                }

                field_val
            } else if let Some(ref bv) = base_val {
                // Field not in update set - project from base
                // Desugars to: base.field_name
                Expr::proj(struct_name_obj.clone(), idx as u32, bv.clone())
            } else if let Some(default_val) = self.field_default_value(
                &struct_name,
                idx,
                &all_field_name_strings,
                &levels,
                &param_args,
                &field_vals,
            ) {
                // Field omitted but carries a default (e.g. a default method on
                // a type class). Fill it from the default, then check it against
                // the constructor's expected field type so a wrongly-typed
                // default is rejected rather than passed to the kernel silently.
                if let Some(exp_ty) = expected_field_ty.as_ref() {
                    self.enforce_expr_type(&default_val, exp_ty)
                        .map_err(|err| ElabError::StructureFieldTypeMismatch {
                            struct_name: struct_name_obj.clone(),
                            field: field_name_str.clone(),
                            expected: exp_ty.to_string(),
                            actual: err.to_string(),
                        })?;
                }
                default_val
            } else {
                // No base, not provided, and no default - genuinely missing.
                return Err(ElabError::MissingStructureFields {
                    struct_name: struct_name_obj.clone(),
                    fields: vec![field_name_str],
                });
            };

            result = Expr::app(result, field_val.clone());
            field_vals.push(field_val.clone());

            if let ExprKind::Pi(_, _, body_ty) = result_ty.kind() {
                result_ty = body_ty.instantiate(&field_val);
            }
        }

        let result_ty = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&result_ty));
        if !self.try_unify(&result_ty, &struct_ty) {
            return Err(ElabError::TypeMismatch {
                expected: format!("{struct_ty:?}"),
                actual: format!("{result_ty:?}"),
            });
        }

        let result = self.metas.instantiate(&result);
        let result = self.metas.instantiate_levels(&result);

        Ok(result)
    }

    /// Try to extract structure name from a type expression.
    /// Returns None if the type is not a structure type.
    ///
    /// A "structure" here is either a natively-declared structure (with a
    /// clean-side field-name table) or a single-constructor inductive imported
    /// from a real Lean `.olean` (which carries no clean field table, only Lean's
    /// own projection *functions* — the same configuration the B43/B44 imported
    /// projection/match work had to handle). Recognizing the imported form lets
    /// `{ s with f := v }` work on imported structures, not just native ones.
    pub(crate) fn try_get_struct_name_from_type(&self, ty: &Expr) -> Option<String> {
        // Get the head constant of the type (ignoring arguments)
        let head = ty.get_app_fn();
        if let ExprKind::Const(name, _) = head.kind() {
            if self.is_structure_like(name) {
                return Some(name.to_string());
            }
        }
        None
    }

    /// Whether `name` names a structure usable in structure-literal / update
    /// syntax: either a natively-registered structure (has a clean field-name
    /// table) or a single-constructor inductive (the shape an imported Lean
    /// structure takes once loaded from `.olean`).
    pub(crate) fn is_structure_like(&self, name: &Name) -> bool {
        if self.env.get_structure_field_names(name).is_some() {
            return true;
        }
        self.env
            .get_inductive(name)
            .is_some_and(|ind| ind.constructor_names.len() == 1)
    }

    /// Resolve a structure field name to its 0-based index within the
    /// constructor's fields (i.e. ignoring the structure's type parameters).
    ///
    /// Native structures answer from the clean field-name table. For an imported
    /// structure (no clean table) we read the index from Lean's own projection
    /// *function* `<struct>.<field>`, whose body is `Proj(struct, idx, self)` —
    /// the authoritative, in-order field index Lean compiled. Returns `None` if
    /// the field is unknown for the structure.
    pub(crate) fn struct_field_index(&self, struct_name: &str, field_name: &str) -> Option<u32> {
        let struct_name_obj = Name::from_string(struct_name);
        let field_name_obj = Name::from_string(field_name);
        if let Some(idx) = self
            .env
            .get_structure_field_index(&struct_name_obj, &field_name_obj)
        {
            return Some(idx);
        }
        // Imported structure: derive from the projection function's body.
        let proj_fn_name = Name::from_string(&format!("{struct_name}.{field_name}"));
        let info = self.env.get_const(&proj_fn_name)?;
        let body = info.value.as_ref()?;
        Self::projection_body_index(body, &struct_name_obj)
    }

    /// If `expr` is a projection-function body `λ …. Proj(struct_name, idx, _)`,
    /// return `idx`. Mirrors `clean_olean`'s `is_projection_fn_body` shape check.
    fn projection_body_index(expr: &Expr, struct_name: &Name) -> Option<u32> {
        let mut e = expr;
        loop {
            match e.kind() {
                ExprKind::Lam(_, _, body) => e = body,
                ExprKind::MData(_, inner) => e = inner,
                ExprKind::Proj(proj_struct, idx, _) if proj_struct == struct_name => {
                    return Some(*idx)
                }
                _ => return None,
            }
        }
    }

    /// Rewrite an `extends`-inherited structure update into a nested update of
    /// the parent subobject, returning the new field list when (and only when) at
    /// least one field is inherited. Returns `None` when every updated field is a
    /// direct constructor field (the common case — no rewrite needed), so callers
    /// fall through to the ordinary update path unchanged.
    ///
    /// `{ c with parentField := v, ownField := w }`
    ///   ⇝ `{ c with toParent := { c.toParent with parentField := v }, ownField := w }`
    ///
    /// Inherited fields are grouped by the `toParent` projection that reaches
    /// them, so multiple inherited fields sharing a parent collapse into a single
    /// nested update (and the parent's other fields are preserved by the inner
    /// `with`). The rewritten update is re-elaborated, recursing through any
    /// further levels of inheritance.
    fn rewrite_inherited_field_updates(
        &self,
        struct_name: &str,
        base_expr: &SurfaceExpr,
        fields: &[SurfaceFieldAssign],
    ) -> Option<Vec<SurfaceFieldAssign>> {
        // Partition into direct fields (kept as-is) and inherited fields grouped
        // by the parent projection that reaches them, preserving declaration
        // order of the parent projections so the rewrite is deterministic.
        let mut direct: Vec<SurfaceFieldAssign> = Vec::new();
        let mut parent_order: Vec<String> = Vec::new();
        let mut inherited: HashMap<String, Vec<SurfaceFieldAssign>> = HashMap::new();
        let mut found_inherited = false;

        for field in fields {
            if self.struct_field_index(struct_name, &field.name).is_some() {
                direct.push(field.clone());
                continue;
            }
            match self.inherited_field_parent_proj(struct_name, &field.name) {
                Some(parent_proj) => {
                    found_inherited = true;
                    if !inherited.contains_key(&parent_proj) {
                        parent_order.push(parent_proj.clone());
                    }
                    inherited
                        .entry(parent_proj)
                        .or_default()
                        .push(field.clone());
                }
                // Unknown field: leave it for the main path to report a precise
                // `UnknownStructureField` error (do not trigger a rewrite).
                None => direct.push(field.clone()),
            }
        }

        if !found_inherited {
            return None;
        }

        let mut rewritten = direct;
        for parent_proj in parent_order {
            let inner_fields = inherited.remove(&parent_proj).unwrap_or_default();
            // `base.toParent`
            let base_parent = SurfaceExpr::Proj(
                Span::dummy(),
                Box::new(base_expr.clone()),
                Projection::Named(parent_proj.clone()),
            );
            // `{ base.toParent with <inherited fields> }`
            let inner_update = SurfaceExpr::StructLit {
                span: Span::dummy(),
                struct_type: None,
                base: Some(Box::new(base_parent)),
                fields: inner_fields,
            };
            rewritten.push(SurfaceFieldAssign {
                span: Span::dummy(),
                name: parent_proj,
                val: inner_update,
            });
        }

        Some(rewritten)
    }

    /// Rewrite a base-less structure literal over an `extends` structure into
    /// one that assembles each parent subobject explicitly, returning the new
    /// field list when the structure has parent subobjects. Returns `None` for
    /// a structure with no recorded `extends` parents (the common case — no
    /// rewrite needed), so callers fall through unchanged.
    ///
    /// `{ x := 1, y := 2 } : B`  (B extends A, x a field of A)
    ///   ⇝ `{ toA := { x := 1 }, y := 2 } : B`
    ///
    /// mirroring Lean's StructInst flattening through the parent subobject
    /// (`src/Lean/Elab/StructInst.lean`, `expandFields`/`addSourceFields`):
    /// provided fields that belong to a parent are grouped into a nested literal
    /// for the corresponding `toParent` slot. A `toParent` slot the caller did
    /// NOT supply directly is synthesized (even with no inherited fields) so the
    /// parent's own required/defaulted fields are resolved by the parent's
    /// elaboration — a missing inherited field is then reported against the
    /// parent (e.g. `MissingStructureFields { Base, ["a"] }`), matching Lean.
    fn rewrite_parent_subobject_construction(
        &self,
        struct_name: &str,
        fields: &[SurfaceFieldAssign],
    ) -> Option<Vec<SurfaceFieldAssign>> {
        let struct_name_obj = Name::from_string(struct_name);
        let subobjects: Vec<(String, String)> = self
            .env
            .get_structure_parents(&struct_name_obj)?
            .iter()
            .map(|(to_field, parent)| (to_field.to_string(), parent.to_string()))
            .collect();
        if subobjects.is_empty() {
            return None;
        }

        // Partition provided fields: direct fields (own fields, or an explicitly
        // provided `toParent`) are kept verbatim; inherited fields are grouped
        // by the `toParent` projection that reaches them; unknown fields are
        // kept so the main path reports a precise `UnknownStructureField`.
        let mut direct: Vec<SurfaceFieldAssign> = Vec::new();
        let mut grouped: HashMap<String, Vec<SurfaceFieldAssign>> = HashMap::new();
        let mut directly_provided: std::collections::HashSet<String> =
            std::collections::HashSet::new();

        for field in fields {
            if self.struct_field_index(struct_name, &field.name).is_some() {
                if subobjects
                    .iter()
                    .any(|(to_field, _)| to_field == &field.name)
                {
                    directly_provided.insert(field.name.clone());
                }
                direct.push(field.clone());
                continue;
            }
            // Inherited field: route it into EVERY parent subobject that has
            // this field (directly or transitively through its own `extends`
            // chain). For an ordinary single-inheritance field this matches
            // exactly one parent — identical to the old single-route behavior.
            // For a field of a *shared* ancestor in a diamond (`D extends B, C`
            // with both `B` and `C` extending `A`, and `a` a field of `A`), the
            // field belongs to both parent subobjects: clean builds the diamond
            // non-deduplicated (`D.mk (toB : B) (toC : C) …`, an `A` copy under
            // each parent), so the same provided value must populate both — else
            // the second subobject's inherited `a` is reported missing and a
            // valid literal is rejected. Both copies receive the identical
            // source value, so every projection path agrees. `{parent}.{field}`
            // exists as a registered projection iff `parent` has that field, so
            // it is the precise membership test.
            let mut routed = false;
            for (to_field, parent) in &subobjects {
                let parent_proj = Name::from_string(&format!("{parent}.{}", field.name));
                if self.env.get_const(&parent_proj).is_some() {
                    grouped
                        .entry(to_field.clone())
                        .or_default()
                        .push(field.clone());
                    routed = true;
                }
            }
            if !routed {
                direct.push(field.clone());
            }
        }

        // Synthesize a nested literal for each subobject the caller did not
        // supply directly, in constructor order.
        let mut rewritten = direct;
        let mut changed = false;
        for (to_field, parent) in &subobjects {
            if directly_provided.contains(to_field) {
                continue;
            }
            let mut inner_fields = grouped.remove(to_field).unwrap_or_default();
            // Child-first default injection (B90): a bare `F := v` override on
            // `struct_name` minted a closed `<struct>.<F>._default` definition
            // that must beat the PARENT's own default for `F`. For each parent
            // field the caller did not supply, splice that override constant in
            // as an explicit assignment. Guard: `F` must not be a constructor
            // field of `struct_name` itself — an own field named `F` shadows
            // the inherited one, and its `<struct>.<F>._default` (a dependent
            // own-default fn) belongs to the own field, not the parent's.
            if let Some(parent_fields) = self
                .env
                .get_structure_field_names(&Name::from_string(parent))
            {
                for pf in parent_fields {
                    let pf_str = pf.to_string();
                    if inner_fields.iter().any(|f| f.name == pf_str) {
                        continue;
                    }
                    if self.struct_field_index(struct_name, &pf_str).is_some() {
                        continue;
                    }
                    let override_fn =
                        Name::from_string(&format!("{struct_name}.{pf_str}._default"));
                    if self.env.get_const(&override_fn).is_some() {
                        inner_fields.push(SurfaceFieldAssign {
                            span: Span::dummy(),
                            name: pf_str,
                            val: SurfaceExpr::Ident(Span::dummy(), override_fn.to_string()),
                        });
                    }
                }
            }
            let inner_lit = SurfaceExpr::StructLit {
                span: Span::dummy(),
                struct_type: None,
                base: None,
                fields: inner_fields,
            };
            rewritten.push(SurfaceFieldAssign {
                span: Span::dummy(),
                name: to_field.clone(),
                val: inner_lit,
            });
            changed = true;
        }

        if changed {
            Some(rewritten)
        } else {
            None
        }
    }

    /// If `field_name` is an inherited field of `struct_name` (declared on a
    /// parent that `struct_name` `extends`), return the name of the `toParent`
    /// projection field that reaches it.
    ///
    /// On the imported path the inherited projection `<struct>.<field>` has body
    /// `ParentStruct.<field> (<struct>.toParent self)` — a composition through a
    /// parent projection rather than a direct kernel `Proj`. We recover the
    /// `toParent` field by inspecting that body: the inner application's head is
    /// the parent projection function `<struct>.toParent`, whose own body is the
    /// direct `Proj(<struct>, idx, self)`. Returns `None` for a direct field or
    /// any shape we do not recognize, so the rewrite is conservative.
    fn inherited_field_parent_proj(&self, struct_name: &str, field_name: &str) -> Option<String> {
        let struct_name_obj = Name::from_string(struct_name);
        let proj_fn_name = Name::from_string(&format!("{struct_name}.{field_name}"));
        let info = self.env.get_const(&proj_fn_name)?;
        let body = info.value.as_ref()?;

        // Strip leading binders / metadata to reach the composition head.
        let mut e = body;
        while let ExprKind::Lam(_, _, inner) | ExprKind::MData(_, inner) = e.kind() {
            e = inner;
        }

        // Expect `outer_proj (inner_proj self)` where `inner_proj` is a parent
        // projection function of `struct_name` returning the parent subobject.
        let ExprKind::App(_, inner_arg) = e.kind() else {
            return None;
        };
        let inner_head = inner_arg.get_app_fn();
        let ExprKind::Const(inner_name, _) = inner_head.kind() else {
            return None;
        };
        // The inner projection must itself be a *direct* field of `struct_name`
        // (its body is `Proj(struct_name, idx, self)`) — i.e. the nested parent
        // subobject slot. That is exactly the `toParent` field.
        let inner_info = self.env.get_const(inner_name)?;
        let inner_body = inner_info.value.as_ref()?;
        Self::projection_body_index(inner_body, &struct_name_obj)?;
        inner_name.last_component()
    }

    /// Whether the structure field at `idx` carries a default value usable to
    /// fill an omitted field in a base-less literal. Covers both clean-native
    /// defaults (recorded in `structure_field_defaults`) and the imported Lean
    /// shape (a sibling definition `<Struct>.<field>._default`).
    fn field_has_default(&self, struct_name: &str, idx: usize, field_names: &[String]) -> bool {
        let struct_name_obj = Name::from_string(struct_name);
        // Native: a recorded default keyed by field name.
        if let Some(field_name) = field_names.get(idx) {
            if self
                .env
                .get_structure_field_default(&struct_name_obj, &Name::from_string(field_name))
                .is_some()
            {
                return true;
            }
            // Native structures also expose the field name, so the `_default`
            // definition (if Lean-shaped) is directly addressable.
            let default_fn = Name::from_string(&format!("{struct_name}.{field_name}._default"));
            if self.env.get_const(&default_fn).is_some() {
                return true;
            }
        }
        // Imported (no field-name table): discover the `_default` definition by
        // its index, derived from the sibling projection function.
        self.imported_default_fn_for_index(struct_name, idx)
            .is_some()
    }

    /// Resolve the value used to fill an omitted structure field, if a default
    /// exists. The returned expression is fully applied and ready to occupy the
    /// field's constructor slot.
    ///
    /// Two default sources, tried in order:
    ///   1. The imported / Lean-shaped definition `<Struct>.<field>._default`,
    ///      which takes the structure's parameters followed by the *preceding*
    ///      fields' values (so a later default may depend on earlier fields). We
    ///      apply it to `param_args ++ preceding_vals`, truncated to the
    ///      definition's binder arity — the faithful `.olean` shape, registered
    ///      by no clean-side metadata.
    ///   2. The clean-native default recorded in `structure_field_defaults`,
    ///      used verbatim (the common case is a closed constant such as `0`).
    fn field_default_value(
        &self,
        struct_name: &str,
        idx: usize,
        field_names: &[String],
        struct_levels: &[Level],
        param_args: &[Expr],
        preceding_vals: &[Expr],
    ) -> Option<Expr> {
        // Prefer the Lean-shaped `_default` definition (works for both imported
        // structures and any native one that ships such a definition).
        let default_fn = field_names
            .get(idx)
            .map(|name| Name::from_string(&format!("{struct_name}.{name}._default")))
            .filter(|n| self.env.get_const(n).is_some())
            .or_else(|| self.imported_default_fn_for_index(struct_name, idx));

        if let Some(default_fn) = default_fn {
            let info = self.env.get_const(&default_fn)?;
            // Count the definition's leading binders to know how many of
            // `param_args ++ preceding_vals` it consumes (params, then prior
            // fields). Extra available arguments beyond the arity are ignored.
            let arity = Self::pi_arity(&info.type_);
            let supplied: Vec<Expr> = param_args
                .iter()
                .chain(preceding_vals.iter())
                .take(arity)
                .cloned()
                .collect();
            // A polymorphic default shares the structure's universe parameters,
            // so reuse the structure's instantiated levels when the counts
            // align; otherwise the default is universe-monomorphic (`Sort 0`).
            let levels: Vec<Level> = if info.level_params.len() == struct_levels.len() {
                struct_levels.to_vec()
            } else {
                info.level_params.iter().map(|_| Level::zero()).collect()
            };
            return Some(Expr::apps(Expr::const_(default_fn, levels), supplied));
        }

        // Fall back to a clean-native recorded default (used verbatim).
        let field_name = field_names.get(idx)?;
        self.env
            .get_structure_field_default(
                &Name::from_string(struct_name),
                &Name::from_string(field_name),
            )
            .cloned()
    }

    /// Count the number of leading `Pi` binders of `ty` (its arity).
    fn pi_arity(ty: &Expr) -> usize {
        let mut e = ty;
        let mut n = 0;
        loop {
            match e.kind() {
                ExprKind::Pi(_, _, body) => {
                    n += 1;
                    e = body;
                }
                ExprKind::MData(_, inner) => e = inner,
                _ => return n,
            }
        }
    }

    /// For an imported structure (no field-name table), find the field default
    /// definition `<Struct>.<field>._default` whose field sits at constructor
    /// index `idx`. The field name is not recoverable from kernel data, so we
    /// scan the environment for `<Struct>.*._default` definitions and match the
    /// one whose sibling projection `<Struct>.*` projects index `idx`.
    fn imported_default_fn_for_index(&self, struct_name: &str, idx: usize) -> Option<Name> {
        let prefix = format!("{struct_name}.");
        let suffix = "._default";
        for info in self.env.constants() {
            let full = info.name.to_string();
            let Some(rest) = full.strip_prefix(&prefix) else {
                continue;
            };
            let Some(field) = rest.strip_suffix(suffix) else {
                continue;
            };
            // A nested name like `Foo.bar.baz._default` would also match the
            // prefix/suffix; require the projection name to resolve to a field
            // index, which only the genuine field projection does.
            if field.is_empty() || field.contains('.') {
                continue;
            }
            if self
                .struct_field_index(struct_name, field)
                .is_some_and(|i| i as usize == idx)
            {
                return Some(info.name.clone());
            }
        }
        None
    }
}
