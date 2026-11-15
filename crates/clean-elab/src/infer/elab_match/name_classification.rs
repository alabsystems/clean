// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Resolve pattern names before coverage, motive inference, or binder lowering.

use super::*;

enum PatternName {
    Constructor(SurfaceName),
    /// A global carrying `@[match_pattern]`: Lean's `processId` reads it like
    /// a constructor and the pattern elaborator unfolds it
    /// (`match_pattern_unfold.rs`). Never a binder (G29).
    MatchPatternDef(Name),
    Binder,
    Unresolved,
}

impl<'a> ElabCtx<'a> {
    /// Clean's native prelude represents these two exported constructors as
    /// reducible definitions. Recognize their exact stored representation only
    /// after ordinary resolution selected that global, never from user spelling
    /// before local/namespace shadowing and never by unfolding arbitrary defs.
    fn native_prelude_pattern_alias(&self, resolved: &Name) -> Option<SurfaceName> {
        self.native_prelude_pattern_alias_of(resolved)
    }

    /// Whether the global `resolved` is what a bare pattern identifier
    /// resolving to it denotes as a CONSTRUCTOR ([`Self::classify_match_pattern_name`]):
    /// a constructor, or the native prelude's `true`/`false`.
    pub(in crate::infer) fn names_pattern_constructor(&self, resolved: &Name) -> bool {
        self.env.get_constructor(resolved).is_some()
            || self.native_prelude_pattern_alias_of(resolved).is_some()
    }

    fn native_prelude_pattern_alias_of(&self, resolved: &Name) -> Option<SurfaceName> {
        if let Some(unit) = self.unit_unit_pattern_alias(resolved) {
            return Some(unit);
        }
        let component = ["true", "false"]
            .into_iter()
            .find(|component| resolved == &Name::anon().str(*component))?;
        let alias = self.env.get_const(resolved)?;
        let bool_name = Name::anon().str("Bool");
        let bool_type = Expr::const_(bool_name.clone(), vec![]);
        let target = bool_name.clone().str(component);
        let target_expr = Expr::const_(target.clone(), vec![]);
        if alias.name != *resolved
            || alias.kind != clean_kernel::env::ConstantKind::Definition
            || !alias.level_params.is_empty()
            || !alias.is_reducible
            || alias.reducibility != Reducibility::Reducible
            || alias.type_ != bool_type
            || alias.value.as_ref() != Some(&target_expr)
            || !self.is_const_accessible(&target)
        {
            return None;
        }
        let constructor = self.env.get_constructor(&target)?;
        (constructor.inductive_name == bool_name
            && constructor.level_params.is_empty()
            && constructor.num_fields == 0
            && constructor.type_ == bool_type)
            .then(|| SurfaceName::from_name(target))
    }

    /// `Unit.unit` is Lean's `@[match_pattern] abbrev Unit.unit : Unit :=
    /// PUnit.unit` (`Init/Prelude.lean`), so `()` / `Unit.unit` in a pattern
    /// is the constructor `PUnit.unit` (G29). Clean's builtin prelude stores
    /// the same reducible definition without the attribute; recognize exactly
    /// that stored representation, as for `true`/`false` above.
    fn unit_unit_pattern_alias(&self, resolved: &Name) -> Option<SurfaceName> {
        if *resolved != Name::from_string("Unit.unit") {
            return None;
        }
        let alias = self.env.get_const(resolved)?;
        let target = Name::from_string("PUnit.unit");
        let target_expr = Expr::const_(target.clone(), vec![Level::succ(Level::zero())]);
        if alias.name != *resolved
            || alias.kind != clean_kernel::env::ConstantKind::Definition
            || !alias.level_params.is_empty()
            || !alias.is_reducible
            || alias.type_ != Expr::const_(Name::from_string("Unit"), vec![])
            || alias.value.as_ref() != Some(&target_expr)
            || !self.is_const_accessible(&target)
        {
            return None;
        }
        let constructor = self.env.get_constructor(&target)?;
        (constructor.num_fields == 0 && constructor.num_params == 0)
            .then(|| SurfaceName::from_name(target))
    }

    fn pattern_binder_eligible(name: &SurfaceName) -> bool {
        !name.is_anonymous()
            && !name.is_relative_constructor()
            && (name.parent().is_anonymous()
                || name
                    .component_syntax()
                    .iter()
                    .all(|origin| matches!(origin, clean_parser::NameComponentSyntax::Generated)))
    }

    /// `bare_identifier` is true for a `SurfacePattern::Var` (a name written
    /// with no argument list), false for the head of a `SurfacePattern::Ctor`.
    fn classify_match_pattern_name(
        &mut self,
        name: &SurfaceName,
        expected: Option<&SurfaceName>,
        bare_identifier: bool,
    ) -> Result<PatternName, ElabError> {
        if name.is_anonymous() {
            return Err(ElabError::UnknownIdent(name.to_string()));
        }
        if name.is_relative_constructor() {
            let selected =
                expected.map(|owner| owner.append(&SurfaceName::from_name(name.name().clone())));
            return match selected {
                Some(selected)
                    if self.env.get_constructor(selected.name()).is_some()
                        && self.is_const_accessible(selected.name()) =>
                {
                    Ok(PatternName::Constructor(selected))
                }
                _ => Err(ElabError::UnknownIdent(name.to_string())),
            };
        }

        // Reuse actual local/namespace/alias/privacy resolution, but do not
        // retain fresh universes, metas, auto-implicit binders, or probe state.
        // In particular, a known constructor remains known even when its owner
        // differs from the scrutinee. Such a name must never become a binder.
        let mut resolved = PatternName::Unresolved;
        self.with_optional_temporary_local_scope(|this| {
            let old_body = this.in_term_body;
            let old_expected = this.current_expected_type.take();
            this.in_term_body = true;
            let result = this.elab_ident(name);
            this.in_term_body = old_body;
            this.current_expected_type = old_expected;
            resolved = match result {
                Ok(expr) => match expr.kind() {
                    ExprKind::Const(owner, _) if this.env.get_constructor(owner).is_some() => {
                        PatternName::Constructor(SurfaceName::from_name(owner.clone()))
                    }
                    ExprKind::Const(owner, _) => this
                        .native_prelude_pattern_alias(owner)
                        .map(PatternName::Constructor)
                        .unwrap_or_else(|| {
                            if this.env.is_match_pattern(owner) {
                                PatternName::MatchPatternDef(owner.clone())
                            } else {
                                PatternName::Binder
                            }
                        }),
                    // A `@[match_pattern]` global with implicit parameters
                    // resolves applied to their metavariables.
                    _ => match expr.get_app_fn().kind() {
                        ExprKind::Const(owner, _) if this.env.is_match_pattern(owner) => {
                            PatternName::MatchPatternDef(owner.clone())
                        }
                        _ => PatternName::Binder,
                    },
                },
                Err(
                    ElabError::UnknownIdent(_)
                    | ElabError::UnknownIdentWithSuggestions { .. }
                    | ElabError::UnknownIdentDeferred { .. },
                ) => PatternName::Unresolved,
                Err(error) => return Err(error),
            };
            Ok(None::<()>)
        })?;
        if matches!(resolved, PatternName::Unresolved) {
            if let Some(expected) = expected {
                // Retain the existing expected-family shorthand only after
                // actual reference resolution found no local or global owner,
                // and, for a bare identifier, only for a constructor with NO
                // explicit fields (the same nullary-only rule
                // elab_decl_value.rs applies). A bare pattern identifier
                // carries no arguments, so a constructor that takes explicit
                // fields cannot be what it denotes; in Lean 4 an unresolved
                // bare identifier in a pattern is a binder (`| H.h mk _ => mk`
                // binds `mk` even when the field type has a two-field `mk`
                // constructor). A constructor-application head keeps the
                // shorthand; its arity is checked against the arguments.
                if let Some(constructor) = self.resolve_ctor_name(name, expected) {
                    if bare_identifier && self.ctor_explicit_field_count(&constructor)? == 0 {
                        // Lean 4 reads a bare pattern identifier that ordinary
                        // name resolution does not find as a BINDER, even when
                        // the scrutinee's type has a constructor of that short
                        // name: `| some c => 0 | _ => 1` over `Option U` (with
                        // `U.c` not opened) is a catch-all, and Lean 4.8.0
                        // evaluates it to `0` on `some U.a`. This shorthand
                        // made it a constructor test, so `rfl` proved the
                        // false `q (some U.a) = 1` (measured 2026-09-24/25).
                        // The two readings differ, and a Clean source written
                        // for the shorthand would silently change meaning
                        // under Lean's — so neither is chosen: refuse, and
                        // name both spellings that are unambiguous.
                        return Err(ElabError::Unsupported {
                            feature: format!(
                                "pattern `{name}`: an identifier that does not resolve by ordinary name resolution is a pattern variable in Lean 4, but `{constructor}` is a constructor of the scrutinee type `{expected}`. Write `.{last}` or `{constructor}` for the constructor, or rename the variable",
                                last = constructor.last_component()
                            ),
                        });
                    }
                    if !bare_identifier {
                        if !self.is_const_accessible(constructor.name()) {
                            return Err(ElabError::UnknownIdent(name.to_string()));
                        }
                        return Ok(PatternName::Constructor(constructor));
                    }
                }
                let candidates = self
                    .env
                    .get_inductive(expected.name())
                    .map(|ind| {
                        ind.constructor_names
                            .iter()
                            .filter(|candidate| {
                                SurfaceName::from_name((*candidate).clone()).has_suffix(name)
                            })
                            .count()
                    })
                    .unwrap_or(0);
                if candidates > 1 {
                    return Err(ElabError::NotImplemented(format!(
                        "ambiguous constructor pattern {name} for {expected}"
                    )));
                }
            }
        }
        match resolved {
            PatternName::Constructor(ref constructor)
                if !self.is_const_accessible(constructor.name()) =>
            {
                Err(ElabError::UnknownIdent(name.to_string()))
            }
            PatternName::Constructor(_) | PatternName::MatchPatternDef(_) => Ok(resolved),
            _ if Self::pattern_binder_eligible(name) => Ok(PatternName::Binder),
            _ => Err(ElabError::UnknownIdent(name.to_string())),
        }
    }

    /// How a bare pattern identifier reads under ordinary name resolution, for
    /// the equation-lemma statements of lifted `mutual` members
    /// (`mutual_lift/arms.rs`): `Some(true)` a constructor, `Some(false)` a
    /// pattern variable, `None` when the reading is refused or ambiguous.
    pub(in crate::infer) fn bare_pattern_name_is_constructor(
        &mut self,
        name: &SurfaceName,
    ) -> Option<bool> {
        match self.classify_match_pattern_name(name, None, true) {
            Ok(PatternName::Constructor(_)) => Some(true),
            Ok(PatternName::Binder) => Some(false),
            // A `@[match_pattern]` name is neither; its reading is refused.
            _ => None,
        }
    }

    /// Ordinary-resolution constructor reading of every bare identifier in the
    /// patterns of `val`'s whole-body match, for the surface equation
    /// normalizers (`elab_decl_value::PatternIdents`). No scrutinee type is
    /// consulted, so the type-namespace shorthand never applies.
    pub(in crate::infer) fn pattern_idents(
        &mut self,
        val: &SurfaceExpr,
    ) -> elab_decl_value::PatternIdents<'a> {
        let mut names = Vec::new();
        let mut heads = Vec::new();
        for arm in elab_decl_value::whole_body_match_arms(val) {
            elab_decl_value::collect_pattern_idents(&arm.pattern, &mut names);
            elab_decl_value::collect_pattern_ctor_heads(&arm.pattern, &mut heads);
        }
        let mut ctors = HashMap::new();
        let mut match_patterns = std::collections::HashSet::new();
        for name in names {
            match self.classify_match_pattern_name(&name, None, true) {
                Ok(PatternName::Constructor(ctor)) => {
                    ctors.insert(name, ctor.into_name());
                }
                Ok(PatternName::MatchPatternDef(_)) => {
                    match_patterns.insert(name);
                }
                _ => {}
            }
        }
        // An unqualified constructor-application head, read as the bare
        // identifiers above are: by ordinary resolution, with no scrutinee
        // type. A head that resolves to no constructor gets no entry.
        let mut ctor_heads = HashMap::new();
        for name in heads {
            if let Ok(PatternName::Constructor(ctor)) =
                self.classify_match_pattern_name(&name, None, false)
            {
                ctor_heads.insert(name, ctor.into_name());
            }
        }
        elab_decl_value::PatternIdents::new(self.env, ctors, ctor_heads, match_patterns)
    }

    /// Refuse a NON-LINEAR pattern — one that binds the same variable twice
    /// (`| some x, some x => …`). Lean 4 rejects it ("variable `x` occurred
    /// more than once"); it has no meaning as an equality test, and Clean used
    /// to elaborate it by silently keeping one of the two bindings, accepting
    /// a definition Lean has no meaning for (measured 2026-09-24/25, class N
    /// of the literal-pattern battery). A name counts as a binder unless
    /// ordinary name resolution makes it a constructor; each `|` alternative
    /// of an or-pattern is checked on its own.
    pub(in crate::infer) fn check_pattern_linear(
        &mut self,
        pattern: &SurfacePattern,
    ) -> Result<(), ElabError> {
        // Each binder occurrence with the `|` branches it sits under: two
        // occurrences are in the same alternative unless some or-node puts
        // them on different sides.
        type Occurrence = (SurfaceName, Vec<(usize, bool)>);
        fn collect(
            pat: &SurfacePattern,
            path: &mut Vec<(usize, bool)>,
            next_or: &mut usize,
            out: &mut Vec<Occurrence>,
        ) {
            match pat {
                SurfacePattern::Var(name) => out.push((name.clone(), path.clone())),
                SurfacePattern::As(name, inner) => {
                    out.push((name.clone(), path.clone()));
                    collect(inner, path, next_or, out);
                }
                SurfacePattern::NumeralAdd(inner, _) => collect(inner, path, next_or, out),
                SurfacePattern::Or(a, b) => {
                    let id = *next_or;
                    *next_or += 1;
                    path.push((id, false));
                    collect(a, path, next_or, out);
                    path.pop();
                    path.push((id, true));
                    collect(b, path, next_or, out);
                    path.pop();
                }
                SurfacePattern::Ctor(_, subs) => {
                    for sub in subs {
                        collect(sub, path, next_or, out);
                    }
                }
                _ => {}
            }
        }
        let mut occurrences = Vec::new();
        collect(pattern, &mut Vec::new(), &mut 0, &mut occurrences);
        let same_alternative = |a: &[(usize, bool)], b: &[(usize, bool)]| {
            !a.iter().any(|(id, side)| {
                b.iter()
                    .any(|(other, other_side)| id == other && side != other_side)
            })
        };
        for (i, (name, path)) in occurrences.iter().enumerate() {
            if name.is_unescaped_component("_") || name.is_anonymous() {
                continue;
            }
            let repeated = occurrences[..i]
                .iter()
                .any(|(prev, prev_path)| prev == name && same_alternative(prev_path, path));
            if repeated
                && !matches!(
                    self.classify_match_pattern_name(name, None, true),
                    Ok(PatternName::Constructor(_) | PatternName::MatchPatternDef(_))
                )
            {
                return Err(ElabError::Unsupported {
                    feature: format!(
                        "non-linear pattern: variable `{name}` occurred more than once in one pattern. Lean 4 rejects this; bind a second name and compare the two with `if` or a guard"
                    ),
                });
            }
        }
        Ok(())
    }

    /// Resolve a whole pattern while its original outer local scope is still
    /// intact. The returned tree contains explicit constructor nodes; its Var
    /// nodes are genuine binders, not failed constructor lookups. Temporary
    /// telescope locals exist only to instantiate dependent field types.
    pub(in crate::infer) fn normalize_match_pattern_names(
        &mut self,
        pattern: &SurfacePattern,
        expected_type: &Expr,
    ) -> Result<SurfacePattern, ElabError> {
        let mut normalized = None;
        self.with_optional_temporary_local_scope(|this| {
            normalized = Some(this.normalize_match_pattern_names_inner(pattern, expected_type)?);
            Ok(None::<()>)
        })?;
        normalized.ok_or_else(|| {
            ElabError::InternalInvariant("pattern-name normalization returned no pattern".into())
        })
    }

    fn normalize_match_pattern_names_inner(
        &mut self,
        pattern: &SurfacePattern,
        expected_type: &Expr,
    ) -> Result<SurfacePattern, ElabError> {
        let expected = self.get_type_name(expected_type).ok();
        let (constructor, arguments) = match pattern {
            SurfacePattern::Var(name) => {
                match self.classify_match_pattern_name(name, expected.as_ref(), true)? {
                    PatternName::Constructor(constructor) => (constructor, &[][..]),
                    PatternName::MatchPatternDef(owner) => {
                        self.check_match_pattern_def_type(&owner, expected_type)?;
                        let unfolded = self.unfold_match_pattern_def(&owner, &[])?;
                        return self.normalize_match_pattern_names_inner(&unfolded, expected_type);
                    }
                    PatternName::Binder => return Ok(pattern.clone()),
                    PatternName::Unresolved => {
                        unreachable!("classifier discharges unresolved names")
                    }
                }
            }
            SurfacePattern::Ctor(name, arguments) => {
                if name.same_syntax(&SurfaceName::generated_path("Prod.mk")) {
                    // Another module's private structure (G21 B3).
                    if let Some(owner) = expected.as_ref() {
                        self.check_imported_private_anon_pattern(owner.name(), name)?;
                    }
                    if let Some((constructor, fields)) = expected
                        .as_ref()
                        .and_then(|owner| self.remap_anon_tuple_to_structure(owner, arguments))
                    {
                        return self.normalize_match_pattern_names_inner(
                            &SurfacePattern::Ctor(constructor, fields),
                            expected_type,
                        );
                    }
                    (name.clone(), arguments.as_slice())
                } else {
                    match self.classify_match_pattern_name(name, expected.as_ref(), false)? {
                        PatternName::Constructor(constructor) => {
                            (constructor, arguments.as_slice())
                        }
                        PatternName::MatchPatternDef(owner) => {
                            self.check_match_pattern_def_type(&owner, expected_type)?;
                            let unfolded = self.unfold_match_pattern_def(&owner, arguments)?;
                            return self
                                .normalize_match_pattern_names_inner(&unfolded, expected_type);
                        }
                        _ => return Err(ElabError::UnknownIdent(name.to_string())),
                    }
                }
            }
            SurfacePattern::As(name, inner) => {
                if !Self::pattern_binder_eligible(name) {
                    return Err(ElabError::UnknownIdent(name.to_string()));
                }
                return Ok(SurfacePattern::As(
                    name.clone(),
                    Box::new(self.normalize_match_pattern_names_inner(inner, expected_type)?),
                ));
            }
            SurfacePattern::Or(left, right) => {
                return Ok(SurfacePattern::Or(
                    Box::new(self.normalize_match_pattern_names_inner(left, expected_type)?),
                    Box::new(self.normalize_match_pattern_names_inner(right, expected_type)?),
                ))
            }
            SurfacePattern::StructInst {
                fields,
                ellipsis,
                ty,
            } => {
                // `{ f := p, .. }` denotes a constructor application of the
                // scrutinee's structure. Expand it here — the one place the
                // scrutinee type is known — and re-enter so the resulting
                // `Ctor` goes through the very same field-type walk below.
                let expanded = self.expand_struct_instance_pattern(
                    fields,
                    *ellipsis,
                    ty.as_deref(),
                    expected_type,
                )?;
                return self.normalize_match_pattern_names_inner(&expanded, expected_type);
            }
            // `n + k` is a pattern on `Nat` only. Lean refuses it at any other
            // scrutinee type (at `Int` its `n` "only occurs in positions that
            // are inaccessible to pattern matching"; at a type without `+`,
            // `Bool`, the `HAdd` problem "is stuck"), and Clean's reading of
            // it at `Int` was an arm that never matches (review r6, X7: `| k +
            // 1 => k`). The message is the one every other `n + k` refusal
            // gives (`ensure_nat_pattern_scrutinee`), which this one now
            // precedes, nested fields included.
            SurfacePattern::NumeralAdd(..) => {
                let scrutinee = self.metas.instantiate(expected_type);
                let scrutinee = self.whnf(&scrutinee);
                if let ExprKind::Const(head, _) = scrutinee.get_app_fn().kind() {
                    if head != &Name::from_string("Nat") {
                        return Err(ElabError::NotImplemented(format!(
                            "match pattern: numeral-add patterns are only supported for Nat \
                             scrutinees, got {} (Lean refuses them too: at `Int` the variable \
                             only occurs in positions that are inaccessible to pattern \
                             matching; at a type without `+` the `HAdd` problem is stuck)",
                            crate::error_render::term(&scrutinee)
                        )));
                    }
                }
                return Ok(pattern.clone());
            }
            _ => return Ok(pattern.clone()),
        };
        let expected = expected.ok_or_else(|| {
            ElabError::NotImplemented(
                "constructor pattern requires an inductive scrutinee type".into(),
            )
        })?;
        let actual_type = self.metas.instantiate(expected_type);
        let actual_type = self.metas.instantiate_levels(&actual_type);
        let actual_type = self.whnf(&actual_type);
        if !matches!(actual_type.get_app_fn().kind(), ExprKind::Const(_, _)) {
            return Err(ElabError::TypeMismatch {
                expected: format!("registered inductive scrutinee for constructor `{constructor}`"),
                actual: format!("{actual_type}"),
            });
        }
        if !self.is_const_accessible(constructor.name()) {
            return Err(ElabError::UnknownIdent(constructor.to_string()));
        }
        let info = self
            .env
            .get_constructor(constructor.name())
            .ok_or_else(|| ElabError::UnknownIdent(constructor.to_string()))?;
        let constructor = if &info.inductive_name == expected.name() {
            constructor
        } else {
            // Preserve the existing registered nested-container/auxiliary and
            // anonymous-tuple correspondences, never a mere matching suffix.
            self.remap_container_ctor_to_field_aux(&expected, &constructor)
                .or_else(|| {
                    self.remap_anonymous_tuple_ctor(&expected, &constructor, arguments.len())
                })
                .ok_or_else(|| ElabError::TypeMismatch {
                    expected: format!("constructor of {expected}"),
                    actual: format!("constructor {constructor} of {}", info.inductive_name),
                })?
        };
        let arguments =
            self.expand_implicit_ctor_field_patterns("match pattern", &constructor, arguments)?;
        let field_types = self.compute_ctor_field_types(constructor.name(), expected_type)?;
        if arguments.len() != field_types.len() {
            return Err(ElabError::InternalInvariant(
                "constructor field metadata mismatch".into(),
            ));
        }
        let mut fields = Vec::with_capacity(arguments.len());
        let mut prior = Vec::with_capacity(arguments.len());
        for (argument, ty) in arguments.iter().zip(field_types) {
            let ty = Self::open_field_type_with_fvars(&ty, &prior);
            let ty = self.beta_reduce_predicate_field_ty(&ty, &prior);
            fields.push(self.normalize_match_pattern_names_inner(argument, &ty)?);
            prior.push(self.push_local(SurfaceName::generated_path("_"), ty));
        }
        for _ in &prior {
            self.pop_local();
        }
        Ok(SurfacePattern::Ctor(constructor, fields))
    }
}

/// Structure-instance patterns (`{ f := p, .. }`).
///
/// Lean has no separate pattern grammar: `Lean.Parser.Term.structInst` parses in
/// pattern position and the match elaborator runs the ordinary structure-instance
/// elaboration over it (`Lean/Elab/PatternVar.lean:304-313` collects the pattern
/// variables inside each field value). Clean's pattern parser records the named
/// fields verbatim as [`SurfacePattern::StructInst`]; this module turns them into
/// the constructor pattern the rest of the pipeline already understands, at the
/// one point where the scrutinee type is known.
impl ElabCtx<'_> {
    /// Maximum parent-chain depth walked when routing an inherited field name.
    /// A structure hierarchy deeper than this is pathological; the bound keeps a
    /// cyclic `structure_parents` table (which registration should never mint,
    /// but which an imported module could) from looping.
    const STRUCT_PATTERN_PARENT_DEPTH: usize = 16;

    /// Is `field` a field of `struct_name` or of one of its parents?
    fn struct_pattern_field_is_reachable(
        &self,
        struct_name: &SurfaceName,
        field: &SurfaceName,
        depth: usize,
    ) -> bool {
        if depth >= Self::STRUCT_PATTERN_PARENT_DEPTH {
            return false;
        }
        if self.struct_field_index(struct_name, field).is_some() {
            return true;
        }
        let Some(parents) = self.env.get_structure_parents(struct_name.name()) else {
            return false;
        };
        let parents: Vec<Name> = parents.iter().map(|(_, parent)| parent.clone()).collect();
        parents.into_iter().any(|parent| {
            self.struct_pattern_field_is_reachable(
                &SurfaceName::from_name(parent),
                field,
                depth + 1,
            )
        })
    }

    /// Expand `{ f := p, … }` against `struct_name` into `S.mk …`.
    ///
    /// Fields naming a PARENT's field are routed into the parent subobject slot
    /// and expanded recursively, which is what Lean's flattened structure-instance
    /// notation means (`{ le := l, .. } : Preorder α` fills `toLE := LE.mk l`).
    /// Slots nothing names become `Wildcard`; with no `..` a missing EXPLICIT
    /// field is an error, exactly as a structure literal with a missing field is.
    fn build_struct_instance_ctor_pattern(
        &mut self,
        struct_name: &SurfaceName,
        assignments: Vec<(SurfaceName, SurfacePattern)>,
        ellipsis: bool,
        depth: usize,
    ) -> Result<SurfacePattern, ElabError> {
        if depth >= Self::STRUCT_PATTERN_PARENT_DEPTH {
            return Err(ElabError::InternalInvariant(format!(
                "structure-instance pattern parent chain for `{struct_name}` exceeds depth {}",
                Self::STRUCT_PATTERN_PARENT_DEPTH
            )));
        }
        let inductive =
            self.env
                .get_inductive(struct_name.name())
                .ok_or_else(|| ElabError::TypeMismatch {
                    expected: "registered structure for a `{ … }` pattern".to_string(),
                    actual: struct_name.to_string(),
                })?;
        let [sole_ctor] = inductive.constructor_names.as_slice() else {
            return Err(ElabError::TypeMismatch {
                expected: format!(
                    "single-constructor structure for a `{{ … }}` pattern, got `{struct_name}`"
                ),
                actual: format!("{} constructors", inductive.constructor_names.len()),
            });
        };
        let ctor_name = SurfaceName::from_name(sole_ctor.clone());
        let ctor = self
            .env
            .get_constructor(ctor_name.name())
            .ok_or_else(|| ElabError::UnknownIdent(ctor_name.to_string()))?;
        let num_fields = ctor.num_fields as usize;
        let field_infos = self.ctor_field_binder_infos(ctor)?;

        let mut slots: Vec<Option<SurfacePattern>> = vec![None; num_fields];
        let set_slot = |slots: &mut Vec<Option<SurfacePattern>>,
                        index: usize,
                        name: &SurfaceName,
                        pattern: SurfacePattern|
         -> Result<(), ElabError> {
            let slot = slots.get_mut(index).ok_or_else(|| {
                ElabError::InternalInvariant(format!(
                    "structure `{struct_name}` field `{name}` index {index} exceeds constructor arity {num_fields}"
                ))
            })?;
            if slot.is_some() {
                return Err(ElabError::DuplicateStructureField {
                    struct_name: struct_name.name().clone(),
                    field: name.to_string(),
                });
            }
            *slot = Some(pattern);
            Ok(())
        };

        // Direct fields first; everything else is held for parent routing so a
        // child field always wins over an inherited one of the same name.
        let mut inherited: Vec<(SurfaceName, SurfacePattern)> = Vec::new();
        for (name, pattern) in assignments {
            if let Some(index) = self.struct_field_index(struct_name, &name) {
                set_slot(&mut slots, index as usize, &name, pattern)?;
            } else {
                inherited.push((name, pattern));
            }
        }

        if !inherited.is_empty() {
            let parents: Vec<(Name, Name)> = self
                .env
                .get_structure_parents(struct_name.name())
                .map(<[(Name, Name)]>::to_vec)
                .unwrap_or_default();

            for (parent_field, parent_struct) in parents {
                let parent_field = SurfaceName::from_name(parent_field);
                let parent_struct = SurfaceName::from_name(parent_struct);
                let mut routed = Vec::new();
                inherited.retain(|(name, pattern)| {
                    if self.struct_pattern_field_is_reachable(&parent_struct, name, 0) {
                        routed.push((name.clone(), pattern.clone()));
                        false
                    } else {
                        true
                    }
                });
                if routed.is_empty() {
                    continue;
                }
                // The `..` travels DOWN with the routed fields. Lean's
                // flattened structure-instance notation names a parent's fields
                // as if they were the child's, so without `..` an unnamed
                // inherited field is missing exactly as an unnamed direct one
                // is — measured against pinned lean v4.30.0-rc2:
                //
                //     structure P where p1 : Nat; p2 : Nat
                //     structure C extends P where c1 : Nat
                //     def f : C -> Nat | { p1 := x, c1 := y } => x + y
                //     -- error: Fields missing: `p2`
                //
                // and two levels deep `| { c1 := y } => y` reports
                // "Fields missing: `g1`, `p1`", so the requirement is
                // RECURSIVE. Passing `true` here wildcarded those slots
                // silently, which widens which values the arm matches.
                let parent_pattern = self.build_struct_instance_ctor_pattern(
                    &parent_struct,
                    routed,
                    ellipsis,
                    depth + 1,
                )?;
                let index = self
                    .struct_field_index(struct_name, &parent_field)
                    .ok_or_else(|| ElabError::InternalInvariant(format!(
                        "structure `{struct_name}` has no field index for its recorded parent slot `{parent_field}`"
                    )))?;
                set_slot(&mut slots, index as usize, &parent_field, parent_pattern)?;
            }
            if let Some((name, _)) = inherited.first() {
                let suggestions = self
                    .env
                    .get_structure_field_names(struct_name.name())
                    .map(|fields| fields.iter().map(ToString::to_string).collect())
                    .unwrap_or_default();
                return Err(ElabError::UnknownStructureField {
                    struct_name: struct_name.name().clone(),
                    field: name.to_string(),
                    suggestions,
                });
            }
        }

        // With no `..` every EXPLICIT field must be named, as in a structure
        // literal ("Fields missing: `b`", measured against pinned lean
        // v4.30.0-rc2). A slot whose name is unknown (an imported structure with
        // no decoded field table) is reported positionally rather than waved
        // through — silently wildcarding it would make the pattern match values
        // the author did not write it for.
        //
        // ONE MEASURED DIVERGENCE, deliberate and in the refusing direction: for
        // a field carrying a DEFAULT, Lean materialises the default VALUE as the
        // pattern at that slot — `structure D where a : Nat; b : Nat := 5` with
        // `fun | { a := x } => x` becomes `D.mk x 5`, and pinned Lean then
        // reports the match non-exhaustive ("Missing cases: (D.mk _ Nat.zero)
        // …"). Clean refuses the omission instead of minting a literal pattern
        // nobody wrote. Both spellings are errors today; the refusal is the one
        // that cannot silently change which values an arm matches. Pinned by
        // `test_struct_instance_pattern_defaulted_field_omission_is_refused`.
        if !ellipsis {
            let field_names = self
                .env
                .get_structure_field_names(struct_name.name())
                .map(<[Name]>::to_vec)
                .unwrap_or_default();
            let missing: Vec<String> = slots
                .iter()
                .enumerate()
                // EVERY slot, not only the explicit ones. A PATTERN is not a
                // literal: pinned lean v4.30.0-rc2 refuses
                // `structure S where mk :: {n : Nat} (m : Nat)` matched by
                // `fun | { m := y } => y` with "Fields missing: `n`", because
                // an implicit field is INFERRED in a term and MATCHED in a
                // pattern — wildcarding it silently widens which values the arm
                // accepts, the same defect as wildcarding an inherited field.
                // (Naming such a field is what Lean accepts and Clean still
                // refuses downstream, in `expand_implicit_ctor_field_patterns`'s
                // arity gate; that refusal is pinned beside this one.)
                .filter(|(index, slot)| slot.is_none() && field_infos.get(*index).is_some())
                .map(|(index, _)| {
                    field_names
                        .get(index)
                        .map_or_else(|| format!("#{index}"), ToString::to_string)
                })
                .collect();
            if !missing.is_empty() {
                return Err(ElabError::MissingStructureFields {
                    struct_name: struct_name.name().clone(),
                    fields: missing,
                });
            }
        }

        let sub_pats = slots
            .into_iter()
            .map(|slot| slot.unwrap_or(SurfacePattern::Wildcard))
            .collect();
        Ok(SurfacePattern::Ctor(ctor_name, sub_pats))
    }

    /// Turn a [`SurfacePattern::StructInst`] into the constructor pattern it
    /// denotes against `expected_type`.
    pub(in crate::infer) fn expand_struct_instance_pattern(
        &mut self,
        fields: &[(SurfaceName, SurfacePattern)],
        ellipsis: bool,
        ty: Option<&SurfaceExpr>,
        expected_type: &Expr,
    ) -> Result<SurfacePattern, ElabError> {
        let struct_name =
            self.get_type_name(expected_type)
                .map_err(|_| ElabError::TypeMismatch {
                    expected: "structure type for a `{ … }` pattern".to_string(),
                    actual: crate::error_render::term(expected_type),
                })?;
        // `{ … : S }`: the ascription must name the scrutinee's structure. Lean
        // elaborates the ascription and unifies; naming a different structure is
        // a type error either way, and refusing here keeps the annotation from
        // being silently ignored.
        if let Some(ty) = ty {
            let annotated = struct_instance_ascription_name(ty).ok_or_else(|| {
                ElabError::NotImplemented(
                    "structure-instance pattern ascription must name a structure".to_string(),
                )
            })?;
            // The annotation is compared by NAME COMPONENTS, never by display
            // string: a bare `S` written inside `namespace N` still names `N.S`,
            // so a prefix of the scrutinee's structure name plus the written
            // spelling must rebuild it exactly. The display-string form
            // (`ends_with(".{annotated}")`) is the mere-suffix reading this
            // file's own neighbour warns against — it matches across component
            // boundaries whenever a component is escaped or a spelling happens
            // to end the same way, which is how a mis-ascription would be
            // silently ignored rather than reported.
            let mut prefix = struct_name.parent();
            let mut matches = annotated.name() == struct_name.name();
            while !matches {
                matches = prefix.append(&annotated).name() == struct_name.name();
                if prefix.is_anonymous() {
                    break;
                }
                prefix = prefix.parent();
            }
            if !matches {
                return Err(ElabError::TypeMismatch {
                    expected: struct_name.to_string(),
                    actual: annotated.to_string(),
                });
            }
        }
        self.build_struct_instance_ctor_pattern(&struct_name, fields.to_vec(), ellipsis, 0)
    }
}

/// The structure NAME of a `{ … : S }` pattern's ascription: `S`, or the head
/// of an applied `S α β`. `None` for anything that does not name a structure,
/// which the caller reports rather than ignoring.
fn struct_instance_ascription_name(ty: &SurfaceExpr) -> Option<SurfaceName> {
    match ty {
        SurfaceExpr::Ident(_, name) if !name.is_anonymous() && !name.is_relative_constructor() => {
            Some(name.clone())
        }
        SurfaceExpr::Paren(_, inner) => struct_instance_ascription_name(inner),
        SurfaceExpr::App(_, func, _) => struct_instance_ascription_name(func),
        _ => None,
    }
}
