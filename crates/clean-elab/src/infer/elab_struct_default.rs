// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structure-field defaults applied the way Lean applies them — BY NAME,
//! through a fixpoint over the whole nested literal — and the parent
//! subobject a literal omits, built from those defaults.
//!
//! Lean mints, for every field declared with a default, a sibling definition
//! `<Struct>.<field>._default` whose VALUE is abstracted with
//! `mkLambdaFVars (usedOnly := true)` over the structure's parameters and the
//! flattened fields the default uses, so its lambdas are named after exactly
//! those fields. Ground truth on the pinned v4.30.0-rc2 with Mathlib
//! (`pp.explicit`):
//!
//! ```text
//! Preorder.lt._default     = fun {α} le => @id (α → α → Prop) fun a b => And (le a b) (Not (le b a))
//! LinearOrder.min._default = fun {α} le toDecidableLE => @id (α → α → α) fun a b => @ite α (le a b) (toDecidableLE a b) a b
//! ```
//!
//! The consumer, `DefaultFields.mkDefaultValue?` in
//! `src/Lean/Elab/StructInst.lean`, walks those lambdas: an EXPLICIT binder is
//! instantiated with the literal's field of that NAME (searched through the
//! whole nested literal, parent subobjects included), any other binder with a
//! fresh metavariable, and the `@id T v` marker is stripped. The value is
//! substituted, not beta-reduced — `LinearOrder.ofSubsingleton` prints
//! `@ite α ((fun x x_1 => True) a b) …`. It runs as a fixpoint
//! (`propagateLoop`), so a default may use a field that comes LATER in
//! constructor order: `LinearOrder.min` (slot 1, inside `toMin`) uses
//! `toDecidableLE` (slot 5), and `toDecidableLT._default` uses `le_refl`,
//! three subobjects deep. Kernel terms keep no binder names, so the names
//! come from `clean_olean::DefaultFnBinderState`, read off the raw `.olean`
//! at import; a `_default` constant with no entry there is Clean-native and
//! keeps the positional rule in `field_default_value`.
//!
//! Positional application — `param_args ++ preceding_vals` cut to the arity,
//! which `field_default_value` did for every imported `_default` until
//! 2026-09-11 — hands `Preorder.lt._default` the `toLE` INSTANCE where the
//! relation `le` is expected, and would hand `LinearOrder.min._default`
//! `toPartialOrder` for `le`. Measured: `Pi.preorder` and
//! `LinearOrder.ofSubsingleton` in `Mathlib/Order/Basic.lean` were the rows
//! blocked on it.
//!
//! The same machinery builds the parent subobject a literal OMITS. Lean's
//! `addMissingFields` expands a missing `toParent` slot into a nested `{ }`
//! whose leaves come from the sources first and then from defaults searched
//! through the hierarchy child-first (`getDefaultFnForField?` over
//! `collectStructNames`): `Preorder.lt._default` answers the `lt` of the `LT`
//! nested in a `Preorder`, so `Pi.preorder`'s `toLT` is
//! `LT.mk fun a b => a ≤ b ∧ ¬b ≤ a` with no `LT` instance in scope, exactly
//! as `#print Pi.preorder` shows. An instance-implicit parent slot is still
//! tried by synthesis FIRST (`Function.Injective.preorder [LT α] … :
//! Preorder α` takes the local), the nested `{ }` only when that fails.
//!
//! Every literal of one nested tree — the outermost `{ … }` and the parent
//! literals it opens, whether minted here or routed by
//! `rewrite_parent_subobject_construction` — shares one field namespace
//! ([`StructLitTree`]) and one fixpoint, run when the outermost literal
//! finishes. A literal that is merely a field VALUE of struct type (not a
//! parent) starts its own tree; Lean flattens parents only.

use super::*;
use clean_kernel::expr::BinderInfo;

/// One constructor slot of a literal in flight.
pub(super) struct ScopeSlot {
    pub(super) name: SurfaceName,
    pub(super) value: Expr,
    /// `Some(parent)` when the slot is a parent subobject (`toParent : Parent`).
    pub(super) parent_struct: Option<SurfaceName>,
    /// The value is the placeholder metavariable of a DEFERRED field.
    pub(super) placeholder: bool,
}

/// One structure literal of a nested tree.
pub(super) struct FieldScope {
    pub(super) struct_name: SurfaceName,
    pub(super) slots: Vec<ScopeSlot>,
    /// `with`-bases and `__ :=` spreads, with their structure when known.
    pub(super) sources: Vec<(Option<SurfaceName>, Expr)>,
}

pub(super) enum PendingKind {
    /// A Lean-shaped default whose named fields were not all available yet.
    NamedDefault {
        default_fn: Name,
        levels: Vec<Level>,
    },
    /// An `autoParam` script held back until every deferred default is in,
    /// as Lean runs tactic blocks after default propagation.
    AutoParam { stx: Name, goal: Expr },
}

pub(super) struct PendingField {
    pub(super) struct_name: SurfaceName,
    /// Diagnostic spelling only (`field 3` when the structure has no table).
    pub(super) field: String,
    pub(super) placeholder: Expr,
    pub(super) expected_ty: Expr,
    pub(super) kind: PendingKind,
}

/// A structure literal and the parent subobject literals nested in it —
/// Lean's `Struct` tree — sharing one field namespace and one fixpoint.
#[derive(Default)]
pub(super) struct StructLitTree {
    pub(super) scopes: Vec<FieldScope>,
    /// Indices into `scopes` of the literals still being elaborated,
    /// outermost first.
    pub(super) open: Vec<usize>,
    pub(super) pending: Vec<PendingField>,
}

/// `@id T v` → `v`: the marker Lean's `addDefaults` wraps every default in
/// and `mkDefaultValue?` strips (`e.isAppOfArity ``id 2`).
fn strip_id_marker(e: Expr) -> Expr {
    let stripped = {
        let args = e.get_app_args();
        match e.get_app_fn().kind() {
            ExprKind::Const(name, _) if args.len() == 2 && name.to_string() == "id" => {
                Some(args[1].clone())
            }
            _ => None,
        }
    };
    stripped.unwrap_or(e)
}

/// Whether `e` mentions `target` as a subterm (structural, no memo: the terms
/// walked here are field values and the placeholders are leaves).
fn mentions(e: &Expr, target: &Expr) -> bool {
    if e == target {
        return true;
    }
    match e.kind() {
        ExprKind::App(f, a) => mentions(f, target) || mentions(a, target),
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
            mentions(t, target) || mentions(b, target)
        }
        ExprKind::Let(_, t, v, b, _) => {
            mentions(t, target) || mentions(v, target) || mentions(b, target)
        }
        ExprKind::Proj(_, _, s) | ExprKind::MData(_, s) => mentions(s, target),
        _ => false,
    }
}

impl ElabCtx<'_> {
    /// Open a literal's field scope: joined to the enclosing tree when the
    /// literal is a PARENT subobject of the literal being elaborated,
    /// otherwise as a new tree.
    pub(super) fn struct_scope_enter(
        &mut self,
        joined: bool,
        struct_name: &SurfaceName,
        sources: Vec<(Option<SurfaceName>, Expr)>,
    ) {
        let scope = FieldScope {
            struct_name: struct_name.clone(),
            slots: Vec::new(),
            sources,
        };
        match self.struct_lit_trees.last_mut() {
            Some(tree) if joined => {
                let idx = tree.scopes.len();
                tree.scopes.push(scope);
                tree.open.push(idx);
            }
            _ => self.struct_lit_trees.push(StructLitTree {
                scopes: vec![scope],
                open: vec![0],
                pending: Vec::new(),
            }),
        }
    }

    /// Record a built constructor slot of the innermost open literal.
    pub(super) fn struct_scope_push_slot(
        &mut self,
        name: &SurfaceName,
        value: Expr,
        parent_struct: Option<SurfaceName>,
        placeholder: bool,
    ) {
        if let Some(tree) = self.struct_lit_trees.last_mut() {
            if let Some(&idx) = tree.open.last() {
                tree.scopes[idx].slots.push(ScopeSlot {
                    name: name.clone(),
                    value,
                    parent_struct,
                    placeholder,
                });
            }
        }
    }

    /// Close the innermost open literal. When it was the outermost one of its
    /// tree, run the tree's fixpoint (on success) and drop the tree.
    pub(super) fn struct_scope_leave(&mut self, ok: bool) -> Result<(), ElabError> {
        let Some(tree) = self.struct_lit_trees.last_mut() else {
            return Ok(());
        };
        tree.open.pop();
        if !tree.open.is_empty() {
            return Ok(());
        }
        let result = if ok {
            self.run_pending_struct_fields()
        } else {
            Ok(())
        };
        self.struct_lit_trees.pop();
        result
    }

    /// The structure names of the current tree, outermost first — Lean's
    /// `collectStructNames`, the search order for `<S>.<field>._default`.
    pub(super) fn struct_scope_chain(&self) -> Vec<SurfaceName> {
        self.struct_lit_trees
            .last()
            .map(|tree| tree.scopes.iter().map(|s| s.struct_name.clone()).collect())
            .unwrap_or_default()
    }

    pub(super) fn struct_tree_has_pending(&self) -> bool {
        self.struct_lit_trees
            .last()
            .is_some_and(|tree| !tree.pending.is_empty())
    }

    pub(super) fn struct_tree_defer(&mut self, pending: PendingField) {
        if let Some(tree) = self.struct_lit_trees.last_mut() {
            tree.pending.push(pending);
        }
    }

    /// The placeholders of the current tree that no fixpoint step has
    /// assigned yet: a candidate field value mentioning one is not available
    /// (Lean postpones a default whose value still contains a missing-field
    /// metavariable).
    fn unassigned_placeholders(&self) -> Vec<Expr> {
        self.struct_lit_trees
            .last()
            .map(|tree| {
                tree.pending
                    .iter()
                    .map(|p| p.placeholder.clone())
                    .filter(|m| self.metas.instantiate(m) == *m)
                    .collect()
            })
            .unwrap_or_default()
    }

    /// The literal tree's field of FLATTENED name `name` — Lean's
    /// `getFieldValue?` over the whole `Struct` tree: a slot of any literal of
    /// the tree, a leaf reached by projecting through a parent-subobject slot
    /// (`mkProjection`), or a field of any source. Innermost literal first.
    /// `None` while the value is not available yet (a deferred placeholder,
    /// or a value that still mentions one).
    pub(super) fn lookup_flat_field(&mut self, name: &SurfaceName) -> Option<Expr> {
        let (slots, sources) = {
            let tree = self.struct_lit_trees.last()?;
            let slots: Vec<(SurfaceName, Expr, Option<SurfaceName>, bool)> = tree
                .scopes
                .iter()
                .rev()
                .flat_map(|scope| {
                    scope.slots.iter().rev().map(|s| {
                        (
                            s.name.clone(),
                            s.value.clone(),
                            s.parent_struct.clone(),
                            s.placeholder,
                        )
                    })
                })
                .collect();
            let sources: Vec<(Option<SurfaceName>, Expr)> = tree
                .scopes
                .iter()
                .rev()
                .flat_map(|scope| scope.sources.iter().cloned())
                .collect();
            (slots, sources)
        };
        let holes = self.unassigned_placeholders();
        let available = |this: &mut Self, candidate: Expr| -> Option<Expr> {
            let candidate = this.metas.instantiate(&candidate);
            if !holes.iter().any(|h| mentions(&candidate, h)) {
                return Some(candidate);
            }
            // A projection out of a container that carries a hole elsewhere
            // (`Preorder.mk (LE.mk le) (LT.mk ?lt) …` asked for `toLE`) is
            // still available once the projection reduces.
            let reduced = this.whnf(&candidate);
            (!holes.iter().any(|h| mentions(&reduced, h))).then_some(reduced)
        };
        for (slot_name, value, parent_struct, placeholder) in slots {
            // A deferred slot whose placeholder is still unassigned is not a
            // value anyone can use yet.
            if placeholder && self.metas.instantiate(&value) == value {
                continue;
            }
            if &slot_name == name {
                if let Some(v) = available(self, value.clone()) {
                    return Some(v);
                }
                continue;
            }
            if let Some(parent) = parent_struct {
                if let Some(projected) = self.project_named_field(&parent, &value, name, 0) {
                    if let Some(v) = available(self, projected) {
                        return Some(v);
                    }
                }
            }
        }
        for (src_struct, src_val) in sources {
            let Some(src_struct) = src_struct else {
                continue;
            };
            if let Some(projected) = self.project_named_field(&src_struct, &src_val, name, 0) {
                if let Some(v) = available(self, projected) {
                    return Some(v);
                }
            }
        }
        None
    }

    /// Whether `default_fn` is Lean-shaped: its binder names were recorded at
    /// import (`clean_olean::DefaultFnBinderState`).
    pub(super) fn has_default_fn_binder_table(&self, default_fn: &Name) -> bool {
        self.env
            .get_ext_state::<clean_olean::DefaultFnBinderState>(clean_olean::default_fn_binder_idx())
            .is_some_and(|table| table.binders.contains_key(default_fn))
    }

    /// `<S>.<field>._default` for the first `S` of `chain` that has one WITH a
    /// recorded binder table — `getDefaultFnForField?`, child-first. A
    /// `_default` with no table is Clean-native and is not answered here.
    pub(super) fn named_default_fn(
        &self,
        chain: &[SurfaceName],
        field: &SurfaceName,
    ) -> Option<Name> {
        let table = self
            .env
            .get_ext_state::<clean_olean::DefaultFnBinderState>(
                clean_olean::default_fn_binder_idx(),
            )?;
        chain
            .iter()
            .map(|s| crate::namespace::append_names(s.name(), field.name()).str("_default"))
            .find(|n| table.binders.contains_key(n) && self.env.get_const(n).is_some())
    }

    /// Apply `default_fn` as `mkDefaultValue?` does: walk its value's leading
    /// lambdas against the recorded binder names, an explicit binder taking
    /// the tree's field of that name (its type unified with the binder's, which
    /// solves the parameter metavariables), any other binder a fresh
    /// metavariable; then strip the `id` marker. `Ok(None)` when a named field
    /// is not available yet or does not fit — the caller defers or moves on.
    pub(super) fn apply_named_default(
        &mut self,
        default_fn: &Name,
        struct_levels: &[Level],
    ) -> Result<Option<Expr>, ElabError> {
        let (level_params, value) = {
            let Some(info) = self.env.get_const(default_fn) else {
                return Ok(None);
            };
            let Some(value) = info.value.clone() else {
                return Ok(None);
            };
            (info.level_params.clone(), value)
        };
        let Some(binders) =
            self.env
                .get_ext_state::<clean_olean::DefaultFnBinderState>(
                    clean_olean::default_fn_binder_idx(),
                )
                .and_then(|table| table.binders.get(default_fn).cloned())
        else {
            return Ok(None);
        };
        // A default shares the structure's universe parameters; when the
        // counts disagree the default is universe-monomorphic.
        let levels: Vec<Level> = if level_params.len() == struct_levels.len() {
            struct_levels.to_vec()
        } else {
            level_params.iter().map(|_| Level::zero()).collect()
        };
        let mut e = value.instantiate_level_params_direct(&level_params, &levels);
        for (binder_name, _) in &binders {
            let (info, ty, body) = match e.kind() {
                ExprKind::Lam(bd, ty, body) => {
                    (bd.info, ty.as_ref().clone(), body.as_ref().clone())
                }
                _ => break,
            };
            let ty = self.metas.instantiate(&ty);
            if info == BinderInfo::Default {
                let Some(val) =
                    self.lookup_flat_field(&SurfaceName::from_name(binder_name.clone()))
                else {
                    return Ok(None);
                };
                let val_ty = self.infer_type(&val)?;
                if !self.try_unify(&val_ty, &ty) {
                    return Ok(None);
                }
                e = body.instantiate(&val);
            } else {
                let meta = self.fresh_meta(ty);
                e = body.instantiate(&meta);
            }
        }
        Ok(Some(strip_id_marker(e)))
    }

    /// The parent structure when `field` is a parent-subobject slot of
    /// `struct_name` (`(toParent, Parent)` in the recorded `extends` table,
    /// which `Lean.structureExt` fills for imported structures).
    pub(super) fn subobject_parent_struct(
        &self,
        struct_name: &SurfaceName,
        field: &SurfaceName,
    ) -> Option<SurfaceName> {
        self.env
            .get_structure_parents(struct_name.name())?
            .iter()
            .find(|(to_field, _)| to_field == field.name())
            .map(|(_, parent)| SurfaceName::from_name(parent.clone()))
    }

    /// Is `parent` a class none of whose fields (direct or through its own
    /// parents) the literal `fields` wrote? The condition under which Lean's
    /// `addParentInstanceFields` synthesizes an omitted parent.
    pub(super) fn omitted_class_parent(
        &self,
        parent: &SurfaceName,
        fields: &[clean_parser::SurfaceFieldAssign],
    ) -> bool {
        let parent_name = parent.name().clone();
        if !self.instances.is_class(&parent_name) {
            return false;
        }
        let mut stack = vec![parent_name];
        let mut seen = std::collections::HashSet::new();
        while let Some(s) = stack.pop() {
            if !seen.insert(s.clone()) {
                continue;
            }
            if let Some(names) = self.env.get_structure_field_names(&s) {
                if names
                    .iter()
                    .any(|n| fields.iter().any(|f| f.name.name() == n))
                {
                    return false;
                }
            }
            if let Some(parents) = self.env.get_structure_parents(&s) {
                stack.extend(parents.iter().map(|(_, p)| p.clone()));
            }
        }
        true
    }

    /// Lean's `propagateLoop`: keep applying the deferred defaults whose named
    /// fields have become available until none is left, then run the held
    /// `autoParam` scripts. A default still unresolved when no step makes
    /// progress is reported missing.
    fn run_pending_struct_fields(&mut self) -> Result<(), ElabError> {
        loop {
            let pending = match self.struct_lit_trees.last_mut() {
                Some(tree) => std::mem::take(&mut tree.pending),
                None => return Ok(()),
            };
            if pending.is_empty() {
                return Ok(());
            }
            let (named, autos): (Vec<PendingField>, Vec<PendingField>) = pending
                .into_iter()
                .partition(|p| matches!(p.kind, PendingKind::NamedDefault { .. }));
            if named.is_empty() {
                for p in autos {
                    self.discharge_pending_autoparam(p)?;
                }
                return Ok(());
            }
            let mut progress = false;
            let mut still: Vec<PendingField> = Vec::new();
            for p in named {
                let PendingKind::NamedDefault { default_fn, levels } = &p.kind else {
                    continue;
                };
                let (default_fn, levels) = (default_fn.clone(), levels.clone());
                match self.apply_named_default(&default_fn, &levels)? {
                    Some(val) => {
                        self.assign_pending_field(&p, val)?;
                        progress = true;
                    }
                    None => still.push(p),
                }
            }
            if !progress {
                let struct_name = still[0].struct_name.name().clone();
                let fields = still.iter().map(|p| p.field.clone()).collect();
                return Err(ElabError::MissingStructureFields {
                    struct_name,
                    fields,
                });
            }
            if let Some(tree) = self.struct_lit_trees.last_mut() {
                tree.pending = still;
                tree.pending.extend(autos);
            }
        }
    }

    fn assign_pending_field(&mut self, p: &PendingField, val: Expr) -> Result<(), ElabError> {
        let expected = self.metas.instantiate(&p.expected_ty);
        self.enforce_expr_type(&val, &expected).map_err(|err| {
            ElabError::StructureFieldTypeMismatch {
                struct_name: p.struct_name.name().clone(),
                field: p.field.clone(),
                expected: expected.to_string(),
                actual: err.to_string(),
            }
        })?;
        if self.try_unify(&p.placeholder, &val) {
            Ok(())
        } else {
            Err(ElabError::StructureFieldTypeMismatch {
                struct_name: p.struct_name.name().clone(),
                field: p.field.clone(),
                expected: expected.to_string(),
                actual: format!(
                    "the deferred default `{}` could not be assigned to the field",
                    crate::error_render::term(&val)
                ),
            })
        }
    }

    fn discharge_pending_autoparam(&mut self, p: PendingField) -> Result<(), ElabError> {
        let PendingKind::AutoParam { stx, goal } = &p.kind else {
            return Ok(());
        };
        let goal = self.metas.instantiate(goal);
        let val = self.discharge_autoparam_field(&p.struct_name, &p.field, stx, &goal)?;
        if self.try_unify(&p.placeholder, &val) {
            Ok(())
        } else {
            Err(ElabError::StructureFieldTypeMismatch {
                struct_name: p.struct_name.name().clone(),
                field: p.field.clone(),
                expected: goal.to_string(),
                actual: "the autoParam proof could not be assigned to the field".to_string(),
            })
        }
    }
}
