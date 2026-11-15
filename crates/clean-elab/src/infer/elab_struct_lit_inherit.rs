// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structure-literal inheritance and default-field machinery.
//!
//! Split from `elab_struct_lit.rs` (audit r7: the file crossed the paragon
//! 1000-line gate at 1242 lines when the structure-literal work landed).
//! This half owns the `extends`-inheritance rewrites (inherited-field
//! updates, parent-subobject construction) and the `_default`-field
//! synthesis; the sibling keeps literal elaboration itself.

use super::*;
use clean_kernel::expr::BinderInfo;
use clean_parser::{Projection, Span, SurfaceFieldAssign};
use std::collections::HashMap;

impl<'a> ElabCtx<'a> {
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
    pub(super) fn rewrite_inherited_field_updates(
        &self,
        struct_name: &SurfaceName,
        base_expr: &SurfaceExpr,
        fields: &[SurfaceFieldAssign],
    ) -> Option<Vec<SurfaceFieldAssign>> {
        // Partition into direct fields (kept as-is) and inherited fields grouped
        // by the parent projection that reaches them, preserving declaration
        // order of the parent projections so the rewrite is deterministic.
        let mut direct: Vec<SurfaceFieldAssign> = Vec::new();
        let mut parent_order: Vec<SurfaceName> = Vec::new();
        let mut inherited: HashMap<SurfaceName, Vec<SurfaceFieldAssign>> = HashMap::new();
        let mut found_inherited = false;

        for field in fields {
            if self.struct_field_index(struct_name, &field.name).is_some() {
                direct.push(field.clone());
                continue;
            }
            match self
                .inherited_field_parent_proj(struct_name, &field.name)
                .or_else(|| self.inherited_field_parent_from_metadata(struct_name, &field.name))
            {
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
    pub(super) fn rewrite_parent_subobject_construction(
        &self,
        struct_name: &SurfaceName,
        fields: &[SurfaceFieldAssign],
    ) -> Option<Vec<SurfaceFieldAssign>> {
        let subobjects: Vec<(SurfaceName, SurfaceName)> = self
            .env
            .get_structure_parents(struct_name.name())?
            .iter()
            .map(|(to_field, parent)| {
                (
                    SurfaceName::from_name(to_field.clone()),
                    SurfaceName::from_name(parent.clone()),
                )
            })
            .collect();
        if subobjects.is_empty() {
            return None;
        }

        // Partition provided fields: direct fields (own fields, or an explicitly
        // provided `toParent`) are kept verbatim; inherited fields are grouped
        // by the `toParent` projection that reaches them; unknown fields are
        // kept so the main path reports a precise `UnknownStructureField`.
        let mut direct: Vec<SurfaceFieldAssign> = Vec::new();
        let mut grouped: HashMap<SurfaceName, Vec<SurfaceFieldAssign>> = HashMap::new();
        let mut directly_provided: std::collections::HashSet<SurfaceName> =
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
            // Membership: a Clean-native structure materializes a constant
            // `<parent>.<field>` for every field it can reach, so that test
            // was complete for it; an olean-IMPORTED structure declares NO
            // constant for an inherited field (Lean composes the projection on
            // the fly), so `PartialOrder.le` never exists and the walk has to
            // go through the parents' own tables and parents — the same
            // reachability `inherited_field_subobject_hop` uses.
            let mut routed = false;
            for (to_field, parent) in &subobjects {
                let parent_proj = crate::namespace::append_names(parent.name(), field.name.name());
                let reaches = self.env.get_const(&parent_proj).is_some()
                    || crate::name_resolution::inherited_field_subobject_hop(
                        self.env,
                        parent.name(),
                        field.name.name(),
                    )
                    .is_some()
                    || self
                        .env
                        .get_structure_field_index(parent.name(), field.name.name())
                        .is_some();
                if reaches {
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
        let field_infos = self.structure_field_binder_infos(struct_name);
        for (to_field, parent) in &subobjects {
            if directly_provided.contains(to_field) {
                continue;
            }
            let mut inner_fields = grouped.remove(to_field).unwrap_or_default();
            // An INSTANCE-IMPLICIT parent slot that no provided field routes
            // into is Lean's typeclass-synthesis case, not a nested literal:
            // leave it absent so the field loop resolves it from the local and
            // global instances (`[LE α]` in scope fills `toLE`). Minting `{ }`
            // here instead reported `Missing field(s) for LE: le`.
            let slot_is_inst = self
                .struct_field_index(struct_name, to_field)
                .and_then(|i| field_infos.get(i as usize).copied())
                == Some(BinderInfo::InstImplicit);
            if inner_fields.is_empty() && slot_is_inst {
                continue;
            }
            // Child-first default injection (B90): a bare `F := v` override on
            // `struct_name` minted a closed `<struct>.<F>._default` definition
            // that must beat the PARENT's own default for `F`. For each parent
            // field the caller did not supply, splice that override constant in
            // as an explicit assignment. Guard: `F` must not be a constructor
            // field of `struct_name` itself — an own field named `F` shadows
            // the inherited one, and its `<struct>.<F>._default` (a dependent
            // own-default fn) belongs to the own field, not the parent's.
            if let Some(parent_fields) = self.env.get_structure_field_names(parent.name()) {
                for pf in parent_fields {
                    let parent_field = SurfaceName::from_name(pf.clone());
                    if inner_fields.iter().any(|f| f.name == parent_field) {
                        continue;
                    }
                    if self
                        .struct_field_index(struct_name, &parent_field)
                        .is_some()
                    {
                        continue;
                    }
                    let override_fn =
                        crate::namespace::append_names(struct_name.name(), pf).str("_default");
                    // A Lean-shaped default (binder names on record) is a
                    // FUNCTION over the fields it uses, not a closed value:
                    // the field loop applies it by name
                    // (`elab_struct_default`), so it is not spliced here.
                    if self.env.get_const(&override_fn).is_some()
                        && !self.has_default_fn_binder_table(&override_fn)
                    {
                        inner_fields.push(SurfaceFieldAssign {
                            span: Span::dummy(),
                            name: parent_field,
                            val: SurfaceExpr::Ident(
                                Span::dummy(),
                                SurfaceName::from_name(override_fn),
                            ),
                        });
                    }
                }
            }
            // An omitted CLASS parent none of whose fields the literal wrote
            // (and with no child override to splice) is left absent: the
            // field loop synthesizes it as an instance first — Lean's
            // `addParentInstanceFields` — and only falls back to a nested
            // `{ }` from the hierarchy's defaults when synthesis fails.
            // Minting `{ }` here pre-empted the synthesis, so `instance :
            // Unique' Box where uniq := …` failed `Missing field(s) for
            // Inhabited: default` with `Inhabited Box` in scope.
            if inner_fields.is_empty() && self.omitted_class_parent(parent, fields) {
                continue;
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

    /// The binder info of each constructor FIELD of `struct_name`, in
    /// constructor order (parameters skipped), read off the constructor's own
    /// type. An olean-imported class stores every parent slot as an
    /// instance-implicit binder (`Preorder.mk {α} [toLE : LE α] [toLT : LT α]
    /// …`), which is what tells Lean's structure-instance elaborator to fill a
    /// missing parent by TYPECLASS SYNTHESIS rather than by building it —
    /// `Function.Injective.preorder [Preorder β] [LE α] [LT α] … : Preorder α
    /// where le_refl := …` takes its `toLE`/`toLT` from the two locals. A
    /// Clean-native `class … extends` constructor carries default binders
    /// there, so the native path is untouched by anything keyed on this.
    pub(super) fn structure_field_binder_infos(
        &self,
        struct_name: &SurfaceName,
    ) -> Vec<BinderInfo> {
        let struct_name_obj = struct_name.name().clone();
        let Some(ind) = self.env.get_inductive(&struct_name_obj) else {
            return Vec::new();
        };
        let Some(ctor_name) = ind.constructor_names.first() else {
            return Vec::new();
        };
        let Some(ctor) = self.env.get_const(ctor_name) else {
            return Vec::new();
        };
        let mut infos = Vec::new();
        let mut ty = &ctor.type_;
        let mut seen = 0usize;
        while let ExprKind::Pi(bd, _, body) = ty.kind() {
            if seen >= ind.num_params as usize {
                infos.push(bd.info);
            }
            seen += 1;
            ty = body;
        }
        infos
    }

    /// If `field_name` is an inherited field of `struct_name` (declared on a
    /// parent that `struct_name` `extends`), return the name of the `toParent`
    /// projection field that reaches it.
    ///
    /// The inherited projection `<struct>.<field>` has body
    /// `ParentStruct.<field> (<struct>.toParent self)` — a composition through a
    /// parent projection rather than a direct kernel `Proj`. We recover the
    /// `toParent` field by inspecting that body: the inner application's head is
    /// the parent projection function `<struct>.toParent`, whose own body is the
    /// direct `Proj(<struct>, idx, self)`. Returns `None` for a direct field or
    /// any shape we do not recognize, so the rewrite is conservative.
    ///
    /// CORRECTED 2026-08-24: this comment used to open "on the IMPORTED path".
    /// That was wrong in both directions. Such a constant exists only on the
    /// SOURCE-ELABORATION path — Clean's own `build_inherited_projections`
    /// mints it — while Lean 4 declares none and an imported structure carries
    /// no `extends` metadata at all (`register_structure_parents` has one
    /// caller, `crate::register`). So this decompiler is reachable ONLY for
    /// source-elaborated structures, and it is exactly the dependency that
    /// [`Self::inherited_field_parent_from_metadata`] removes. Evidence and
    /// counts: `designs/2026-08-24-inherited-projection-parity.md`.
    pub(super) fn inherited_field_parent_proj(
        &self,
        struct_name: &SurfaceName,
        field_name: &SurfaceName,
    ) -> Option<SurfaceName> {
        let proj_fn_name = crate::namespace::append_names(struct_name.name(), field_name.name());
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
        Self::projection_body_index(inner_body, struct_name.name())?;
        let exact = SurfaceName::from_name(inner_name.clone());
        (exact.parent() == *struct_name).then(|| exact.last_component())
    }

    /// The `toParent` hop for an inherited field, read from the structure's
    /// recorded `extends` METADATA instead of from a materialized projection
    /// constant's body.
    ///
    /// [`Self::inherited_field_parent_proj`] recovers the hop by decompiling
    /// `<struct>.<field> := Parent.<field> (<struct>.toParent self)`. That works
    /// only while such a constant exists — which is a Clean-only artefact:
    /// Lean 4 composes inherited-field access on the fly and declares NO
    /// constant (measured against real Lean 4 `Init`: 1,235 inherited
    /// (structure, field) pairs, 0 declared;
    /// `designs/2026-08-24-inherited-projection-parity.md`). This path answers
    /// the same question from `Environment::get_structure_parents`, so
    /// `{ c with inheritedField := v }` keeps rewriting when the constant is
    /// absent. First parent that reaches the field wins — the same rule
    /// `build_inherited_projections` uses.
    pub(super) fn inherited_field_parent_from_metadata(
        &self,
        struct_name: &SurfaceName,
        field_name: &SurfaceName,
    ) -> Option<SurfaceName> {
        crate::name_resolution::inherited_field_subobject_hop(
            self.env,
            struct_name.name(),
            field_name.name(),
        )
        .map(SurfaceName::from_name)
    }

    /// Whether the structure field at `idx` carries a default value usable to
    /// fill an omitted field in a base-less literal. Covers both clean-native
    /// defaults (recorded in `structure_field_defaults`) and the imported Lean
    /// shape (a sibling definition `<Struct>.<field>._default`).
    pub(super) fn field_has_default(
        &self,
        struct_name: &SurfaceName,
        idx: usize,
        field_names: &[SurfaceName],
    ) -> bool {
        // Native: a recorded default keyed by field name.
        if let Some(field_name) = field_names.get(idx) {
            if self
                .env
                .get_structure_field_default(struct_name.name(), field_name.name())
                .is_some()
            {
                return true;
            }
            // Native structures also expose the field name, so the `_default`
            // definition (if Lean-shaped) is directly addressable.
            let default_fn = crate::namespace::append_names(struct_name.name(), field_name.name())
                .str("_default");
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
    pub(super) fn field_default_value(
        &self,
        struct_name: &SurfaceName,
        idx: usize,
        field_names: &[SurfaceName],
        struct_levels: &[Level],
        param_args: &[Expr],
        preceding_vals: &[Expr],
    ) -> Option<Expr> {
        // Prefer the Lean-shaped `_default` definition (works for both imported
        // structures and any native one that ships such a definition).
        let default_fn = field_names
            .get(idx)
            .map(|name| {
                crate::namespace::append_names(struct_name.name(), name.name()).str("_default")
            })
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
            .get_structure_field_default(struct_name.name(), field_name.name())
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
    fn imported_default_fn_for_index(&self, struct_name: &SurfaceName, idx: usize) -> Option<Name> {
        for info in self.env.constants() {
            let full = SurfaceName::from_name(info.name.clone());
            if full.last_component() != SurfaceName::generated_path("_default") {
                continue;
            }
            let projection = full.parent();
            // Exactly one field component under the actual structure owner.
            // Dots within a quoted component remain data, not path separators.
            if projection.parent() != *struct_name {
                continue;
            }
            let field = projection.last_component();
            if self
                .struct_field_index(struct_name, &field)
                .is_some_and(|i| i as usize == idx)
            {
                return Some(info.name.clone());
            }
        }
        None
    }
}
