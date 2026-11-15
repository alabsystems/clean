// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Structure literal elaboration.
//!
//! Handles `SurfaceExpr::StructLit` (structure literals and with-syntax):
//! - `{ x := val, y := val2 }` — direct construction
//! - `{ s with x := val }` — struct update syntax

use super::elab_struct_default::{PendingField, PendingKind};
use super::*;
use crate::agent_diagnostics::nearest_string_candidates;
use clean_parser::{Span, SurfaceFieldAssign};
use std::collections::HashMap;

/// Mathlib's spread marker in structure-instance notation: a field spelled
/// `__ := e` is not a field named `__`, it contributes `e` as an additional
/// `with`-source (`Mathlib/Tactic/Spread.lean`).
const SPREAD_FIELD_NAME: &str = "__";
#[cfg(test)]
#[path = "elab_struct_lit_metadata_tests.rs"]
mod metadata_tests;

impl<'a> ElabCtx<'a> {
    /// Elaborate a structure literal expression.
    ///
    /// Handles three sources for the structure type, in Lean's priority order
    /// (`getStructName`, `src/Lean/Elab/StructInst.lean`):
    /// 1. Explicit type annotation: `{ ... : Foo }`
    /// 2. Expected type from context (bidirectional type checking)
    /// 3. With-syntax base expression: infer type from the base
    pub(crate) fn elab_struct_lit(
        &mut self,
        struct_type: &Option<Box<SurfaceExpr>>,
        base: &Option<Box<SurfaceExpr>>,
        fields: &[SurfaceFieldAssign],
    ) -> Result<Expr, ElabError> {
        // A literal opened for a PARENT subobject of the literal being
        // elaborated joins that literal's field tree; any other literal is a
        // tree of its own. The flag is consumed here so nothing nested deeper
        // (a literal inside a field's lambda) inherits it. See
        // `elab_struct_default`.
        let joined = std::mem::take(&mut self.struct_lit_join_parent);
        let mut entered = false;
        let result = self.elab_struct_lit_inner(struct_type, base, fields, joined, &mut entered);
        if !entered {
            return result;
        }
        match result {
            Ok(value) => {
                // Closing the outermost literal of a tree runs its default
                // fixpoint, which assigns the deferred fields' placeholders.
                self.struct_scope_leave(true)?;
                Ok(self.metas.instantiate(&value))
            }
            Err(err) => {
                let _ = self.struct_scope_leave(false);
                Err(err)
            }
        }
    }

    fn elab_struct_lit_inner(
        &mut self,
        struct_type: &Option<Box<SurfaceExpr>>,
        base: &Option<Box<SurfaceExpr>>,
        fields: &[SurfaceFieldAssign],
        joined: bool,
        entered: &mut bool,
    ) -> Result<Expr, ElabError> {
        // Elaborate base if present (with-syntax).
        //
        // The source is elaborated with NO expected type. Lean's
        // `getStructSources` resolves each `sᵢ` in `{ s₁, …, sₙ with … }` as a
        // local ident and reads its type with `inferType` — the structure
        // instance's own expected type never reaches it. That matters now that
        // the expected type outranks the source below: in
        // `{ h₁ with uniq := … } : Unique α` with `h₁ : Inhabited α`, leaving
        // `Unique α` in `current_expected_type` while elaborating `h₁` asks the
        // elaborator to make an `Inhabited α` into a `Unique α`.
        let base_val = if let Some(base_expr) = base {
            Some(self.elaborate_with_expected_type(base_expr, None)?)
        } else {
            None
        };

        // SPREAD fields: `__ := e` contributes `e` as an additional SOURCE, and
        // is not a field named `__`.
        //
        // `__ :=` is MATHLIB syntax (`Mathlib/Tactic/Spread.lean`), not Lean's.
        // Measured against the pinned `lean` v4.30.0-rc2 with no Mathlib on the
        // path, `{ __ := s, d := 7 }` is rejected verbatim:
        //
        //     error: `__` is not a field of structure `Deriv2`
        //     error: Fields missing: `b`
        //
        // and Lean core declares no `__` field syntax — `normalizeField`
        // (`src/Lean/Elab/StructInst.lean:473`) reports it as an unknown field,
        // which is precisely the error Clean was reporting.
        //
        // Mathlib's macro rewrites the whole literal, appending each spread to
        // the `with`-source list:
        //
        //     `{ $srcs,* with … __ := e … }`
        //       ⇝ `let_impl_detail __spread.0 := e; { $srcs, __spread.0 with … }`
        //
        // so a spread is a SOURCE — it fills every field it can provide, not
        // just a parent slot. Ground truth with the real Mathlib checkout on
        // `LEAN_PATH` (`set_option pp.parens true`):
        //
        //     def mkD2 : Base2 → Deriv2 :=
        //     fun s => (have __spread.0 := s; { toBase2 := __spread.0, d := 7 })
        //
        //     def mkD2FromSelf : Deriv2 → Deriv2 :=
        //     fun x => (have __spread.0 := x;
        //               { b := 1, c := __spread.0.c, d := __spread.0.d })
        //
        // Elaborated with NO expected type, matching the macro's
        // `elabLetImplDetail` (`elabTerm valStx none`).
        let spread_stx: Vec<&SurfaceExpr> = fields
            .iter()
            .filter(|f| f.name.is_unescaped_component(SPREAD_FIELD_NAME))
            .map(|f| &f.val)
            .collect();
        let without_spreads: Vec<SurfaceFieldAssign>;
        let fields: &[SurfaceFieldAssign] = if spread_stx.is_empty() {
            fields
        } else {
            without_spreads = fields
                .iter()
                .filter(|f| !f.name.is_unescaped_component(SPREAD_FIELD_NAME))
                .cloned()
                .collect();
            &without_spreads
        };
        let mut source_vals: Vec<Expr> = base_val.iter().cloned().collect();
        let spread_count = spread_stx.len();
        for stx in spread_stx {
            let val = self.elaborate_with_expected_type(stx, None)?;
            source_vals.push(val);
        }

        // Determine the structure type expression and structure name.
        //
        // PRIORITY — Lean 4 `getStructName` (`src/Lean/Elab/StructInst.lean`):
        //
        //   "If the expected type is available and it is a structure, then we
        //    use it. Otherwise, we use the type of the first source."
        //
        // and the `{ … : T }` ascription is folded into the expected type by
        // `expandStructInstExpectedType` before that runs, so it outranks the
        // source too. The `with`-source is a LAST resort, used only when there
        // is no usable expected type.
        //
        // This used to read the source FIRST, which made `{ src with f := v }`
        // resolve its fields against `src`'s structure rather than against the
        // structure being built. Ground truth, pinned `lean` v4.30.0-rc2:
        //
        //     structure Base where b : Nat
        //     structure Deriv extends Base where d : Nat
        //     def mkD (s : Base) : Deriv := { s with d := 7 }
        //     #print mkD    -- fun s => { toBase := s, d := 7 }
        //
        // Clean reported `Unknown structure field d on Base`, because it had
        // decided the literal was building a `Base`.
        let type_from_source;
        let struct_ty = if let Some(ty_expr) = struct_type {
            // Explicit type annotation: { ... : Foo }
            type_from_source = false;
            self.elaborate(ty_expr)?
        } else {
            let expected = self.expected_type().cloned().map(|expected| {
                self.metas
                    .instantiate_levels(&self.metas.instantiate(&expected))
            });
            // "…available and it is a structure": an expected type that is a
            // metavariable, or whose head is not a structure, does not count and
            // falls through to the source.
            let expected_is_struct = expected.as_ref().is_some_and(|expected| {
                let whnf = self.whnf(expected);
                self.try_get_struct_name_from_type(&whnf).is_some()
            });
            // "…the type of the FIRST source": the `with` base when there is
            // one, otherwise the first spread, in source order.
            match (expected, expected_is_struct, source_vals.first().cloned()) {
                (Some(expected), true, _) => {
                    type_from_source = false;
                    expected
                }
                (_, _, Some(first)) => {
                    type_from_source = true;
                    let first_ty = self.infer_type(&first)?;
                    let first_ty = self.metas.instantiate(&first_ty);
                    self.metas.instantiate_levels(&first_ty)
                }
                (Some(expected), false, None) => {
                    type_from_source = false;
                    expected
                }
                (None, _, None) => {
                    return Err(ElabError::NotImplemented(
                        "struct literal requires type annotation or expected type".to_string(),
                    ));
                }
            }
        };
        let struct_ty_whnf = self.whnf(&struct_ty);
        let struct_name = self
            .try_get_struct_name_from_type(&struct_ty_whnf)
            .ok_or_else(|| {
                if type_from_source {
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
        // Another module's private structure (G21 B3): Lean refuses `{...}`
        // from an importer.
        let ctor_of_struct = self
            .env
            .get_inductive(struct_name.name())
            .and_then(|ind| ind.constructor_names.first().cloned());
        if let Some(ctor) = ctor_of_struct {
            self.check_imported_private_ctor(
                struct_name.name(),
                &ctor,
                imported_private_access::CtorNotation::StructInstance,
            )?;
        }

        // Each source's own structure, when it has one. `None` for a source
        // whose type is not structure-like (which can only happen when the
        // expected type supplied the structure).
        let mut source_structs: Vec<Option<SurfaceName>> = Vec::with_capacity(source_vals.len());
        for source_val in &source_vals {
            let ty = self.infer_type(source_val)?;
            let ty = self.metas.instantiate_levels(&self.metas.instantiate(&ty));
            let ty = self.whnf(&ty);
            source_structs.push(self.try_get_struct_name_from_type(&ty));
        }
        // The pre-existing single-`with` update path: exactly one source, it is
        // the `with` base (not a spread), and it is the structure being built.
        let source_is_target = spread_count == 0
            && source_structs.len() == 1
            && source_structs[0].as_ref() == Some(&struct_name);

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
        //
        // Only when the source's structure IS the structure being built: the
        // rewrite projects `base.toParent` out of the source, which exists only
        // then. A source of a *different* structure supplies fields through
        // [`Self::source_field_value`] (in `elab_struct_lit_source.rs`) instead.
        if let (Some(base_expr), true) = (base, source_is_target) {
            if let Some(rewritten) =
                self.rewrite_inherited_field_updates(&struct_name, base_expr, fields)
            {
                return self.elab_struct_lit_inner(
                    struct_type,
                    &Some(base_expr.clone()),
                    &rewritten,
                    joined,
                    entered,
                );
            }
        } else if source_vals.is_empty() {
            // SOURCE-less construction of an `extends` structure: assemble each
            // parent subobject from the flattened field spellings.
            //   `{ x := 1, y := 2 } : B`  (B extends A, x a field of A)
            //     ⇝ `{ toA := { x := 1 }, y := 2 } : B`
            // mirroring Lean's StructInst flattening through the parent
            // subobject (`src/Lean/Elab/StructInst.lean`). Native subobject
            // layout only — a structure with no recorded parents yields `None`
            // and this is a no-op.
            if let Some(rewritten) =
                self.rewrite_parent_subobject_construction(&struct_name, fields)
            {
                return self.elab_struct_lit_inner(struct_type, base, &rewritten, joined, entered);
            }
        }

        // Open this literal's field scope — joined to the enclosing tree
        // when it builds a parent subobject — and take the default-function
        // search chain (the tree's structures, outermost first).
        let scope_sources: Vec<(Option<SurfaceName>, Expr)> = source_structs
            .iter()
            .cloned()
            .zip(source_vals.iter().cloned())
            .collect();
        self.struct_scope_enter(joined, &struct_name, scope_sources);
        *entered = true;
        let default_chain = self.struct_scope_chain();

        // Build constructor call: StructName.<ctor> field1 field2 ...
        //
        // `.mk` is only the DEFAULT constructor name. `structure Foo where` mints
        // `Foo.mk`, but `structure Foo where intro :: …` — and every core `Prop`
        // structure written that way, `Iff.intro` / `And.intro` / `Exists.intro`
        // — mints something else, and hardcoding `.mk` made the struct-instance
        // form unusable at exactly those types. That is the dominant Mathlib
        // `where` idiom: an `↔` statement proved by `mp`/`mpr` fields.
        //
        // `.mk` is still tried FIRST, so this is weakening-only: a structure
        // that has one is resolved byte-identically to before, and the
        // sole-constructor fallback is reached only where the old code raised
        // `UnknownIdent`. A multi-constructor inductive has no sole constructor
        // and still fails, with the same message.
        let struct_name_obj = struct_name.name().clone();
        let mk_name = match self.env.get_const(&struct_name.name().clone().str("mk")) {
            Some(_) => struct_name.name().clone().str("mk"),
            None => self
                .env
                .get_inductive(&struct_name_obj)
                .and_then(|ind| match ind.constructor_names.as_slice() {
                    [only] => Some(only.clone()),
                    _ => None,
                })
                .ok_or_else(|| {
                    ElabError::UnknownIdent(format!("struct constructor {}.mk", struct_name))
                })?,
        };
        let mk_info = self
            .env
            .get_const(&mk_name)
            .ok_or_else(|| ElabError::UnknownIdent(format!("struct constructor {}", mk_name)))?;
        let ind_info =
            self.env
                .get_inductive(&struct_name_obj)
                .ok_or_else(|| ElabError::UnknownStruct {
                    name: struct_name.to_string(),
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
        let all_field_names: Vec<SurfaceName> = self
            .env
            .get_structure_field_names(&struct_name_obj)
            .map(|fields| fields.iter().cloned().map(SurfaceName::from_name).collect())
            .unwrap_or_default();
        let all_field_name_strings: Vec<String> =
            all_field_names.iter().map(ToString::to_string).collect();

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
        let mut field_updates: HashMap<usize, &SurfaceFieldAssign> = HashMap::new();
        for field_assign in fields {
            let idx = self
                .struct_field_index(&struct_name, &field_assign.name)
                .ok_or_else(|| ElabError::UnknownStructureField {
                    struct_name: struct_name_obj.clone(),
                    field: field_assign.name.to_string(),
                    suggestions: nearest_string_candidates(
                        &field_assign.name.to_string(),
                        all_field_name_strings.iter().map(String::as_str),
                        5,
                    ),
                })?;
            // A field may be assigned at most ONCE.
            //
            // This used to be a bare `insert`, so a repeated field silently
            // overwrote the earlier binding and the DROPPED assignment was
            // never elaborated at all. That is a trust hole, not a style issue:
            //
            //     def p : P := { x := sorry, x := 1, y := 3 }
            //
            // was accepted with NO `sorry axioms:` line and no warning, while
            // the same `sorry` without the duplicate is correctly refused. An
            // unresolvable identifier in the dropped slot escaped the same way.
            // Lean rejects a duplicate field outright, which also removes the
            // question of which binding wins — `{ }` kept the LAST while
            // `instance ... where` kept the FIRST, so the two surface forms
            // disagreed and each leaked through its own discarded slot.
            if let Some(previous) = field_updates.insert(idx as usize, field_assign) {
                return Err(ElabError::Unsupported {
                    feature: format!(
                        "structure literal assigns field `{}` more than once (also assigned as `{}`). Each field may be given at most one value — a repeat would silently discard an assignment without elaborating it.",
                        field_assign.name, previous.name
                    ),
                });
            }
        }

        if source_vals.is_empty() && !joined {
            // A field omitted from a source-less literal is only *missing* when it
            // has no default. Lean structure/class fields may carry a default
            // (`field := v`), which is exactly how a default **method** on a
            // type class is encoded; an instance that omits the method inherits
            // the default. Imports ship that default as a sibling definition
            // `<Struct>.<field>._default` (no clean-side default metadata), so a
            // field with a discoverable default must NOT be reported missing.
            // An instance-implicit slot (an imported class's parent, `[toLE :
            // LE α]`) is filled by typeclass synthesis in the field loop, as
            // Lean does; it is not "missing" here.
            let field_infos = self.structure_field_binder_infos(&struct_name);
            // An `autoParam` field (`f : T := by tac`) is discharged by its own
            // script in the field loop; it is not "missing" here either.
            let field_autoparams = self.structure_field_autoparams(&struct_name);
            let missing_fields: Vec<String> = (0..num_fields)
                .filter(|idx| !field_updates.contains_key(idx))
                .filter(|idx| field_infos.get(*idx).copied() != Some(BinderInfo::InstImplicit))
                .filter(|idx| field_autoparams.get(*idx).is_none_or(Option::is_none))
                .filter(|idx| !self.field_has_default(&struct_name, *idx, &all_field_names))
                // A parent subobject is built from the hierarchy's defaults,
                // and a field with a Lean-shaped default found child-first
                // through the tree is filled by name (`elab_struct_default`).
                .filter(|idx| {
                    all_field_names.get(*idx).is_none_or(|name| {
                        self.subobject_parent_struct(&struct_name, name).is_none()
                            && self.named_default_fn(&default_chain, name).is_none()
                    })
                })
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
        // Per constructor field, the `autoParam` tactic script constant when
        // the field is `f : T := by tac` (`Lean.Syntax` value; see
        // `infer::auto_param`).
        let field_autoparams = self.structure_field_autoparams(&struct_name);

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
                        actual: crate::error_render::term(&result_ty),
                    });
                }
            };
            result = Expr::app(result, arg.clone());
            result_ty = self.metas.instantiate(&body_ty);
        }

        // NO implicit-argument insertion past the parameters. Every binder that
        // remains in the telescope is a FIELD: Lean's structure constructor is
        // exactly `params ++ fields`, and a field keeps the binder info it was
        // declared with — an olean-imported class stores each parent slot as an
        // instance-implicit binder (`Applicative.mk {f} [toFunctor : Functor f]
        // [toPure : Pure f] …`; `Preorder.mk {α} [toLE : LE α] [toLT : LT α] …`).
        // Until 2026-09-10 this line called `insert_implicit_args` here, which
        // walked exactly those binders: it SYNTHESIZED `Functor f` from the
        // environment (or minted a metavariable) for a slot the literal was
        // about to supply, and left the field loop below one binder short per
        // parent, so `toPure := { pure := … }` was elaborated against no
        // expected type ("struct literal requires type annotation or expected
        // type") and every `where` instance of an imported class with parents
        // failed. Clean-native structures never showed it because their own
        // constructors carry parent slots as default binders.

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
            let (expected_field_ty, field_binder_info) = match result_ty.kind() {
                ExprKind::Pi(bd, arg_ty, _) => {
                    (Some(self.metas.instantiate(arg_ty)), Some(bd.info))
                }
                _ => (None, None),
            };
            // The field name is only used for diagnostics; imported structures
            // may not expose it, in which case we fall back to a positional name.
            let field_name_str = all_field_name_strings
                .get(idx)
                .cloned()
                .unwrap_or_else(|| format!("field {idx}"));
            // The typed identity of the slot. A structure with no field table
            // gets the diagnostic spelling as ONE generated component
            // (`field 3`), which can collide with no real field.
            let field_name_typed: SurfaceName =
                all_field_names.get(idx).cloned().unwrap_or_else(|| {
                    SurfaceName::from_name(Name::anon().str(field_name_str.clone()))
                });
            let slot_parent = all_field_names
                .get(idx)
                .and_then(|name| self.subobject_parent_struct(&struct_name, name));
            let mut deferred = false;
            let field_val = if let Some(field_assign) = field_updates.get(&idx) {
                // Field is being updated - elaborate the provided value with the
                // constructor telescope's expected field type.
                //
                // A parent subobject given as its own literal joins this
                // literal's field tree (see `elab_struct_default`).
                if slot_parent.is_some()
                    && matches!(field_assign.val, SurfaceExpr::StructLit { .. })
                {
                    self.struct_lit_join_parent = true;
                }
                let elaborated =
                    self.elaborate_with_expected_type(&field_assign.val, expected_field_ty.clone());
                self.struct_lit_join_parent = false;
                let field_val =
                    elaborated.map_err(|err| match (expected_field_ty.as_ref(), err) {
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
            } else if let Some(from_source) = {
                // Field not in the update set — take it from a source.
                //
                // Lean, `addSourceFields`: "a missing field always comes from
                // the FIRST source that can provide it", sources in syntactic
                // order (`with` bases first, then spreads).
                let mut found = None;
                for i in 0..source_vals.len() {
                    let val = source_vals[i].clone();
                    let src_struct = source_structs[i].clone();
                    found = self.source_field_value(
                        &struct_name,
                        idx,
                        all_field_names.get(idx),
                        src_struct.as_ref(),
                        &val,
                        expected_field_ty.as_ref(),
                    );
                    if found.is_some() {
                        break;
                    }
                }
                found
            } {
                from_source
            } else if let Some(from_tree) = joined
                .then_some(())
                .and_then(|()| self.lookup_flat_field(&field_name_typed))
            {
                // A leaf of a parent literal, filled from the enclosing
                // literal's sources or fields — Lean's `addMissingFields` hands
                // the sources down into every nested parent `{ }`.
                if let Some(exp_ty) = expected_field_ty.as_ref() {
                    self.enforce_expr_type(&from_tree, exp_ty).map_err(|err| {
                        ElabError::StructureFieldTypeMismatch {
                            struct_name: struct_name_obj.clone(),
                            field: field_name_str.clone(),
                            expected: exp_ty.to_string(),
                            actual: err.to_string(),
                        }
                    })?;
                }
                from_tree
            } else if let Some(default_fn) =
                self.named_default_fn(&default_chain, &field_name_typed)
            {
                // A Lean-shaped `<S>.<field>._default` (its binder names on
                // record), applied BY NAME the way `mkDefaultValue?` applies
                // it; deferred behind a placeholder when a field it names is
                // not available yet (`elab_struct_default`).
                match self.apply_named_default(&default_fn, &levels)? {
                    Some(default_val) => {
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
                    }
                    None => {
                        let exp_ty = expected_field_ty.clone().ok_or_else(|| {
                            ElabError::MissingStructureFields {
                                struct_name: struct_name_obj.clone(),
                                fields: vec![field_name_str.clone()],
                            }
                        })?;
                        let placeholder = self.fresh_meta(exp_ty.clone());
                        self.struct_tree_defer(PendingField {
                            struct_name: struct_name.clone(),
                            field: field_name_str.clone(),
                            placeholder: placeholder.clone(),
                            expected_ty: exp_ty,
                            kind: PendingKind::NamedDefault {
                                default_fn,
                                levels: levels.clone(),
                            },
                        });
                        deferred = true;
                        placeholder
                    }
                }
            } else if let Some(default_val) = self.field_default_value(
                &struct_name,
                idx,
                &all_field_names,
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
            } else if let (Some(stx), Some(exp_ty)) = (
                field_autoparams.get(idx).cloned().flatten(),
                expected_field_ty.as_ref(),
            ) {
                // `f : T := by tac` and nothing supplied `f`: run Lean's own
                // script against `T` (the `autoParam` wrapper stripped),
                // exactly as Lean's structure-instance elaborator does —
                // `Preorder.lt_iff_le_not_ge := by intros; rfl`. A failing
                // script fails the field with Lean's wording; a script the
                // decoder cannot read fails it too, never a substitute.
                let goal = clean_kernel::inductive::consume_type_annotations(exp_ty).clone();
                if self.struct_tree_has_pending() {
                    // Held until the deferred defaults are in — Lean runs
                    // tactic blocks after default propagation, and this goal
                    // may mention a field still being defaulted.
                    let placeholder = self.fresh_meta(exp_ty.clone());
                    self.struct_tree_defer(PendingField {
                        struct_name: struct_name.clone(),
                        field: field_name_str.clone(),
                        placeholder: placeholder.clone(),
                        expected_ty: exp_ty.clone(),
                        kind: PendingKind::AutoParam { stx, goal },
                    });
                    deferred = true;
                    placeholder
                } else {
                    self.discharge_autoparam_field(&struct_name, &field_name_str, &stx, &goal)?
                }
            } else if let Some(inst) = expected_field_ty
                .as_ref()
                .filter(|_| field_binder_info == Some(BinderInfo::InstImplicit))
                .and_then(|ty| self.resolve_instance(ty))
            {
                // An INSTANCE-IMPLICIT constructor slot — an olean-imported
                // class's parent, `Preorder.mk {α} [toLE : LE α] [toLT : LT α]
                // …` — that nothing supplied is filled by typeclass synthesis,
                // exactly as Lean's structure-instance elaborator fills it:
                // `Function.Injective.preorder [Preorder β] [LE α] [LT α] … :
                // Preorder α where le_refl := …` takes `toLE`/`toLT` from the
                // two locals, and `{ toLE := inst.toLE, le_refl := … }` takes
                // `toLT` from `Preorder.toLT inst`. Tried after an explicit
                // value, a source and a recorded default, so nothing that
                // resolved before resolves differently now.
                inst
            } else if let Some(inst) = slot_parent
                .as_ref()
                .filter(|parent| {
                    !joined && source_vals.is_empty() && self.omitted_class_parent(parent, fields)
                })
                .and(expected_field_ty.as_ref())
                .and_then(|ty| self.resolve_instance(ty))
            {
                // An omitted parent that is a CLASS, none of whose fields the
                // literal wrote, is synthesized as an instance BEFORE any field
                // or default is consulted — Lean's `addParentInstanceFields`
                // (`Lean/Elab/StructInst.lean`), all-or-nothing, whether or
                // not the child is a class and whatever the constructor
                // binder's kind. `Unique extends Inhabited` has an EXPLICIT
                // `toInhabited` slot, so `instance : Unique (∀ a, β a) where
                // uniq := …` used to build `{ }` for it from defaults and fail
                // `Missing field(s) for Inhabited: default` (`Pi.unique`,
                // `Fin.instUnique`, measured 2026-09-12).
                inst
            } else if let (true, Some(exp_ty)) = (slot_parent.is_some(), expected_field_ty.as_ref())
            {
                // An omitted parent subobject nothing above filled: Lean's
                // `addMissingFields` builds it as a nested `{ }` whose leaves
                // come from the sources and then from the hierarchy's defaults
                // (`Pi.preorder`'s `toLT` is `LT.mk fun a b => a ≤ b ∧ ¬b ≤ a`
                // from `Preorder.lt._default`, with no `LT` instance in
                // scope). The nested literal joins this one's field tree.
                let nested = SurfaceExpr::StructLit {
                    span: Span::dummy(),
                    struct_type: None,
                    base: None,
                    fields: Vec::new(),
                };
                self.struct_lit_join_parent = true;
                let built = self.elaborate_with_expected_type(&nested, Some(exp_ty.clone()));
                self.struct_lit_join_parent = false;
                built.map_err(|err| match err {
                    err @ (ElabError::MissingStructureFields { .. }
                    | ElabError::UnknownStructureField { .. }) => err,
                    err => ElabError::StructureFieldTypeMismatch {
                        struct_name: struct_name_obj.clone(),
                        field: field_name_str.clone(),
                        expected: exp_ty.to_string(),
                        actual: err.to_string(),
                    },
                })?
            } else {
                // No base, not provided, and no default - genuinely missing.
                return Err(ElabError::MissingStructureFields {
                    struct_name: struct_name_obj.clone(),
                    fields: vec![field_name_str],
                });
            };

            result = Expr::app(result, field_val.clone());
            field_vals.push(field_val.clone());
            self.struct_scope_push_slot(
                &field_name_typed,
                field_val.clone(),
                slot_parent.clone(),
                deferred,
            );

            if let ExprKind::Pi(_, _, body_ty) = result_ty.kind() {
                result_ty = body_ty.instantiate(&field_val);
            }
        }

        let result_ty = self
            .metas
            .instantiate_levels(&self.metas.instantiate(&result_ty));
        if !self.try_unify(&result_ty, &struct_ty) {
            return Err(ElabError::TypeMismatch {
                expected: crate::error_render::term(&struct_ty),
                actual: crate::error_render::term(&result_ty),
            });
        }

        let result = self.metas.instantiate(&result);
        let result = self.metas.instantiate_levels(&result);

        Ok(result)
    }
}
