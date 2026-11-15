//! Structure-literal support that is not the field loop itself: recognising
//! a structure from its type, reading a field out of a `with`/spread source
//! (Lean's `addSourceFields`), and resolving a field name to its constructor
//! index for native and olean-imported structures.
//!
//! Split out of `elab_struct_lit.rs` to keep that file under the paragon
//! 1000-line limit; every item here is a method on [`ElabCtx`].

use super::*;

impl<'a> ElabCtx<'a> {
    /// Try to extract structure name from a type expression.
    /// Returns None if the type is not a structure type.
    ///
    /// A "structure" here is either a natively-declared structure (with a
    /// clean-side field-name table) or a single-constructor inductive imported
    /// from a real Lean `.olean` (which carries no clean field table, only Lean's
    /// own projection *functions* — the same configuration the B43/B44 imported
    /// projection/match work had to handle). Recognizing the imported form lets
    /// `{ s with f := v }` work on imported structures, not just native ones.
    pub(crate) fn try_get_struct_name_from_type(&self, ty: &Expr) -> Option<SurfaceName> {
        // Get the head constant of the type (ignoring arguments)
        let head = ty.get_app_fn();
        if let ExprKind::Const(name, _) = head.kind() {
            if self.is_structure_like(name) {
                return Some(SurfaceName::from_name(name.clone()));
            }
        }
        None
    }

    /// The value of the target structure's field `idx` (named `field_name`
    /// when actual field metadata is available)
    /// taken from the `with`-source `src_val`, whose structure is `src_struct`.
    /// `None` when this source cannot provide the field, in which case the
    /// caller falls through to the field's default and then to
    /// `MissingStructureFields` — Lean's order.
    ///
    /// Lean's rule (`addSourceFields`, `src/Lean/Elab/StructInst.lean`):
    ///
    /// > a missing field always comes from the first source that can provide it
    ///
    /// matched by *flattened field name* between source and target, and read
    /// out with `mkProjection` (which walks the source's own parent chain).
    pub(super) fn source_field_value(
        &mut self,
        target_struct: &SurfaceName,
        idx: usize,
        field_name: Option<&SurfaceName>,
        src_struct: Option<&SurfaceName>,
        src_val: &Expr,
        expected_field_ty: Option<&Expr>,
    ) -> Option<Expr> {
        let src_struct = src_struct?;

        // Same structure: the source's field `idx` IS the target's field `idx`.
        // Positional, so it works for an imported structure with no field-name
        // table — and it is the only path the pre-2026-08-31 code had.
        if src_struct == target_struct {
            return Some(Expr::proj(
                target_struct.name().clone(),
                idx as u32,
                src_val.clone(),
            ));
        }

        // Different structure: match an actual typed field name, through the
        // source's parents. A diagnostic fallback such as "field 0" is not a
        // field identity when an imported target has no field-name table.
        if let Some(field_name) = field_name {
            if let Some(projected) = self.project_named_field(src_struct, src_val, field_name, 0) {
                return Some(projected);
            }
        }

        // Clean stores an `extends` parent as a nested subobject field, where
        // Lean stores the parent's fields flattened. So Lean's "fill each
        // flattened field of the parent from the source, then `etaStructReduce'`
        // them back into the parent" collapses here into a single step: the
        // target's `toParent` slot is filled by the source itself, when the
        // source IS that parent. This is the `{ h₁ with uniq := … } : Unique α`
        // shape with `h₁ : Inhabited α` — Lean prints `{ toInhabited := h₁, … }`.
        //
        // Guarded by a kernel def-eq check against the slot's own type, so a
        // same-named-but-differently-parameterised source (`Inhabited β` into a
        // `Unique α`) is refused here rather than handed to the kernel.
        let expected_field_ty = expected_field_ty?;
        let slot_whnf = self.whnf(expected_field_ty);
        if self.try_get_struct_name_from_type(&slot_whnf).as_ref() != Some(src_struct) {
            return None;
        }
        let src_ty = self.infer_type(src_val).ok()?;
        if self.is_def_eq(&src_ty, expected_field_ty) {
            return Some(src_val.clone());
        }
        None
    }

    /// Project `field_name` out of `src_val`, a value of structure `src_struct`,
    /// hopping through `src_struct`'s own parent subobjects when the field is
    /// inherited rather than direct. Mirrors Lean's `mkProjection`.
    ///
    /// `depth` bounds the parent walk: each hop moves strictly up a structure's
    /// `extends` chain, so a well-formed hierarchy terminates long before the
    /// cap, but a cyclic `extends` record (which the elaborator does not itself
    /// validate here) must not spin.
    pub(super) fn project_named_field(
        &mut self,
        src_struct: &SurfaceName,
        src_val: &Expr,
        field_name: &SurfaceName,
        depth: usize,
    ) -> Option<Expr> {
        const MAX_PARENT_HOPS: usize = 32;
        if depth >= MAX_PARENT_HOPS {
            return None;
        }
        if let Some(idx) = self.struct_field_index(src_struct, field_name) {
            return Some(Expr::proj(src_struct.name().clone(), idx, src_val.clone()));
        }
        let hop = self
            .inherited_field_parent_proj(src_struct, field_name)
            .or_else(|| self.inherited_field_parent_from_metadata(src_struct, field_name))?;
        let hop_idx = self.struct_field_index(src_struct, &hop)?;
        let parent_val = Expr::proj(src_struct.name().clone(), hop_idx, src_val.clone());
        // Read the parent's structure name off the projection's own type rather
        // than from `extends` metadata: an imported structure carries no parent
        // metadata at all (`register_structure_parents` has one caller,
        // `crate::register`), but its subobject field still has a type.
        let parent_ty = self.infer_type(&parent_val).ok()?;
        let parent_ty = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&parent_ty));
        let parent_ty = self.whnf(&parent_ty);
        let parent_struct = self.try_get_struct_name_from_type(&parent_ty)?;
        self.project_named_field(&parent_struct, &parent_val, field_name, depth + 1)
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
    pub(crate) fn struct_field_index(
        &self,
        struct_name: &SurfaceName,
        field_name: &SurfaceName,
    ) -> Option<u32> {
        let struct_name_obj = struct_name.name().clone();
        let field_name_obj = field_name.name().clone();
        if let Some(idx) = self
            .env
            .get_structure_field_index(&struct_name_obj, &field_name_obj)
        {
            return Some(idx);
        }
        // Imported structure: derive from the projection function's body.
        let proj_fn_name = struct_name.append(field_name).into_name();
        let info = self.env.get_const(&proj_fn_name)?;
        let body = info.value.as_ref()?;
        Self::projection_body_index(body, &struct_name_obj)
    }

    /// If `expr` is a projection-function body `λ …. Proj(struct_name, idx, _)`,
    /// return `idx`. Mirrors `clean_olean`'s `is_projection_fn_body` shape check.
    pub(super) fn projection_body_index(expr: &Expr, struct_name: &Name) -> Option<u32> {
        let mut e = expr;
        loop {
            match e.kind() {
                ExprKind::Lam(_, _, body) => e = body,
                ExprKind::MData(_, inner) => e = inner,
                ExprKind::Proj(proj_struct, idx, _) if proj_struct == struct_name => {
                    return Some(*idx);
                }
                _ => return None,
            }
        }
    }
}
