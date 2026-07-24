// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Match elaboration helper utilities.
//!
//! Type name extraction, type argument extraction, and decreasing argument detection.
//! Used by match, if-let, do-match, and projection elaboration.

use super::super::*;
use crate::stack_safe;
use std::ops::Range;

impl<'a> ElabCtx<'a> {
    /// Authenticate one executable recursor packet once per immutable
    /// elaboration environment. The kernel routine proves both cross-table
    /// metadata coherence and subject reduction for every iota RHS; caching is
    /// essential because match lowering may consult the same packet once per
    /// arm and nested-pattern column.
    pub(in crate::infer) fn authenticate_recursor_cached(
        &self,
        name: &Name,
    ) -> Result<(), ElabError> {
        if let Some(cached) = self.recursor_auth_cache.borrow().get(name).cloned() {
            return cached.map_err(|detail| {
                ElabError::InternalInvariant(format!(
                    "recursor metadata `{name}` failed authentication: {detail}"
                ))
            });
        }
        let verdict = self.env.authenticate_recursor_readonly(name);
        self.recursor_auth_cache
            .borrow_mut()
            .insert(name.clone(), verdict.clone());
        verdict.map_err(|detail| {
            ElabError::InternalInvariant(format!(
                "recursor metadata `{name}` failed authentication: {detail}"
            ))
        })
    }

    /// Authenticate an imported plain-definition `casesOn` against the exact
    /// canonical wrapper over its already-authenticated primitive recursor.
    pub(in crate::infer) fn authenticate_imported_cases_on_cached(
        &self,
        cases_name: &Name,
        rec_name: &Name,
        minor_rules: &[clean_kernel::RecursorRule],
    ) -> Result<(), ElabError> {
        if let Some(cached) = self.cases_on_auth_cache.borrow().get(cases_name).cloned() {
            return cached.map_err(|detail| {
                ElabError::InternalInvariant(format!(
                    "imported cases eliminator `{cases_name}` failed authentication: {detail}"
                ))
            });
        }
        let minor_arities: Vec<(u32, u32)> = minor_rules
            .iter()
            .map(|rule| {
                let recursive_fields =
                    u32::try_from(rule.recursive_fields.iter().filter(|flag| **flag).count())
                        .map_err(|_| {
                            ElabError::InternalInvariant(format!(
                        "minor rule for `{}` has more recursive fields than can be represented",
                        rule.constructor_name
                    ))
                        })?;
                Ok((rule.num_fields, recursive_fields))
            })
            .collect::<Result<_, ElabError>>()?;
        let verdict =
            self.env
                .authenticate_cases_on_wrapper_readonly(cases_name, rec_name, &minor_arities);
        self.cases_on_auth_cache
            .borrow_mut()
            .insert(cases_name.clone(), verdict.clone());
        verdict.map_err(|detail| {
            ElabError::InternalInvariant(format!(
                "imported cases eliminator `{cases_name}` failed authentication: {detail}"
            ))
        })
    }

    /// Return the selected inductive member's motive slot in the eliminator.
    ///
    /// Every member of an ordinary mutual block sees the same global motive
    /// order.  Restored nested blocks retain the original members in that order
    /// and append erased helper motives after them.  A match on a later original
    /// member must therefore put its real motive in that member's slot, not in
    /// slot zero.
    pub(in crate::infer) fn selected_motive_index(
        &self,
        ind_info: &clean_kernel::InductiveVal,
        num_motives: usize,
        context: &str,
    ) -> Result<usize, ElabError> {
        let matches: Vec<usize> = ind_info
            .all_names
            .iter()
            .enumerate()
            .filter_map(|(index, name)| (name == &ind_info.name).then_some(index))
            .collect();
        if matches.len() != 1 || matches[0] >= num_motives {
            return Err(ElabError::InternalInvariant(format!(
                "{context}: selected member `{}` has motive slots {matches:?} in block {:?}, but the eliminator declares {num_motives} motives",
                ind_info.name, ind_info.all_names
            )));
        }
        Ok(matches[0])
    }

    /// Build a constant inhabitant of a function telescope.
    ///
    /// `expected` is the kernel-authored type of a motive (or another function
    /// premise) and `body` is independent of its arguments.  Opening each Pi
    /// with a fresh free variable before recursing is important for dependent
    /// telescopes: later binder domains are instantiated exactly as the kernel
    /// declared them, then abstracted back into the returned lambda.
    pub(in crate::infer) fn constant_over_telescope(
        &mut self,
        expected: &Expr,
        body: Expr,
    ) -> Expr {
        let expected = self.whnf(expected);
        let ExprKind::Pi(info, domain, codomain) = expected.kind() else {
            return body;
        };

        let fvar = self.fresh_fvar();
        let opened = codomain.instantiate(&Expr::fvar(fvar));
        let inner = self
            .constant_over_telescope(&opened, body)
            .abstract_fvar(fvar);
        Expr::lam(*info, domain.as_ref().clone(), inner)
    }

    /// Build exactly `count` constant lambdas from the front of `expected`.
    ///
    /// Unlike [`Self::constant_over_telescope`], this stops before a function-
    /// valued conclusion.  Recursor minor premises need this distinction when
    /// the match result itself is a function: only constructor fields (and, for
    /// `rec`, induction hypotheses) belong to the minor's binder prefix.
    pub(in crate::infer) fn constant_over_telescope_prefix(
        &mut self,
        expected: &Expr,
        count: usize,
        body: Expr,
    ) -> Option<Expr> {
        if count == 0 {
            return Some(body);
        }
        let expected = self.whnf(expected);
        let ExprKind::Pi(info, domain, codomain) = expected.kind() else {
            return None;
        };

        let fvar = self.fresh_fvar();
        let opened = codomain.instantiate(&Expr::fvar(fvar));
        let inner = self
            .constant_over_telescope_prefix(&opened, count - 1, body)?
            .abstract_fvar(fvar);
        Some(Expr::lam(*info, domain.as_ref().clone(), inner))
    }

    /// Return `PUnit.{u}` and its genuine inhabitant `PUnit.unit.{u}`, where
    /// `u` is the sort of `result_ty`.
    ///
    /// Mutual/nested eliminators require motive and minor slots for every
    /// member of the block, even when the major premise belongs to only one
    /// member.  The other slots are unreachable, but unreachable code must
    /// still be represented by a kernel-checkable term rather than an axiom.
    /// A constant `PUnit` motive gives those slots an independently inhabited
    /// result type without requiring `result_ty` itself to have a closed value.
    ///
    /// This helper is deliberately gated on the canonical polymorphic PUnit
    /// declaration shape.  Small hand-built test environments may omit PUnit;
    /// callers then retain their original result motive and must provide a real
    /// wildcard/default inhabitant or fail closed.
    pub(in crate::infer) fn punit_dummy_at_result_sort(
        &self,
        result_ty: &Expr,
    ) -> Result<Option<(Expr, Expr)>, ElabError> {
        let punit_name = Name::from_string("PUnit");
        let unit_name = Name::from_string("PUnit.unit");
        if self.env.get_inductive(&punit_name).is_none() {
            return Ok(None);
        }
        let punit = self.authenticate_inductive_metadata(&punit_name)?;
        let mut unit = None;
        for ctor_name in &punit.constructor_names {
            let (ctor, parent) = self.authenticate_constructor_metadata(ctor_name)?;
            if parent.name != punit_name {
                return Err(ElabError::InternalInvariant(format!(
                    "PUnit constructor `{ctor_name}` belongs to `{}`",
                    parent.name
                )));
            }
            if ctor_name == &unit_name {
                unit = Some(ctor);
            }
        }
        let unit = unit.ok_or_else(|| {
            ElabError::InternalInvariant(
                "registered PUnit metadata does not contain `PUnit.unit`".to_string(),
            )
        })?;
        if punit.level_params.len() != 1
            || punit.num_params != 0
            || punit.num_indices != 0
            || punit.all_names != [punit_name.clone()]
            || punit.constructor_names != [unit_name.clone()]
            || unit.inductive_name != punit_name
            || unit.level_params.len() != 1
            || unit.num_params != 0
            || unit.num_fields != 0
            || unit.constructor_idx != 0
        {
            return Err(ElabError::InternalInvariant(
                "registered PUnit/PUnit.unit metadata has a noncanonical declaration shape"
                    .to_string(),
            ));
        }

        // Once canonical PUnit is present, an invalid result type is not a
        // reason to silently select the branch-typed fallback. Propagate the
        // type error so any level-equality work performed by `infer_sort` stays
        // within the enclosing transactional elaboration scope.
        let u = self.infer_sort(result_ty)?;
        Ok(Some((
            Expr::const_(punit_name, vec![u.clone()]),
            Expr::const_(unit_name, vec![u]),
        )))
    }

    /// Return recursor rules in the global minor-premise order, including the
    /// restored companions of a nested-inductive block.
    ///
    /// During nested elimination the kernel temporarily creates auxiliary
    /// inductives.  Restore deliberately erases those public constants and
    /// retains their recursors as `<first-original>.rec_1`, `.rec_2`, ...;
    /// their rules are re-keyed to the real container constructors.  Elaboration
    /// must therefore use this metadata, never reconstruct names such as
    /// `T._List`.  Ordinary mutual blocks still use each member's own `.rec`.
    pub(in crate::infer) fn recursor_minor_rules(
        &self,
        ind_info: &clean_kernel::InductiveVal,
        rec_val: &clean_kernel::RecursorVal,
    ) -> Result<Vec<clean_kernel::RecursorRule>, ElabError> {
        let ind_info = self.authenticate_inductive_metadata(&ind_info.name)?;
        self.authenticate_recursor_cached(&rec_val.name)?;
        let wanted = rec_val.num_minors as usize;
        let mut rules = Vec::with_capacity(wanted);
        let first = ind_info.all_names.first().unwrap_or(&ind_info.name);

        // Original members remain in `all_names` after restore.  Read each
        // member's own rule slice so this also handles ordinary mutual blocks.
        for member in &ind_info.all_names {
            let member_ind = self.authenticate_inductive_metadata(member)?;
            if member_ind.all_names != ind_info.all_names {
                return Err(ElabError::InternalInvariant(format!(
                    "mutual-family metadata for `{member}` lists {:?}, expected {:?}",
                    member_ind.all_names, ind_info.all_names
                )));
            }
            let member_rec_name = Name::from_string(&format!("{member}.rec"));
            let member_rec = self.env.get_recursor(&member_rec_name).ok_or_else(|| {
                ElabError::InternalInvariant(format!(
                    "missing recursor metadata `{member_rec_name}` while authenticating the minor telescope of `{}`",
                    rec_val.name
                ))
            })?;
            self.authenticate_recursor_cached(&member_rec_name)?;
            if member_rec.inductive_name != *member {
                return Err(ElabError::InternalInvariant(format!(
                    "family recursor `{member_rec_name}` identifies `{}` instead of member `{member}`",
                    member_rec.inductive_name
                )));
            }
            if member_rec.num_motives != rec_val.num_motives
                || member_rec.num_minors != rec_val.num_minors
            {
                return Err(ElabError::InternalInvariant(format!(
                    "family recursor `{member_rec_name}` declares {}/{} motives/minors, but `{}` declares {}/{}",
                    member_rec.num_motives,
                    member_rec.num_minors,
                    rec_val.name,
                    rec_val.num_motives,
                    rec_val.num_minors
                )));
            }
            rules.extend(member_rec.rules.iter().cloned());
        }

        // Any missing rules belong to erased nested auxiliaries and are exposed
        // by the kernel as consecutively numbered companion recursors.
        let mut companion_idx = 1usize;
        while rules.len() < wanted {
            let name = Name::from_string(&format!("{first}.rec_{companion_idx}"));
            let companion = self.env.get_recursor(&name).ok_or_else(|| {
                ElabError::InternalInvariant(format!(
                    "missing restored companion recursor `{name}` while authenticating the minor telescope of `{}`",
                    rec_val.name
                ))
            })?;
            self.authenticate_recursor_cached(&name)?;
            if companion.inductive_name != *first {
                return Err(ElabError::InternalInvariant(format!(
                    "restored companion recursor `{name}` identifies family head `{}`, expected `{first}`",
                    companion.inductive_name
                )));
            }
            if companion.num_motives != rec_val.num_motives
                || companion.num_minors != rec_val.num_minors
            {
                return Err(ElabError::InternalInvariant(format!(
                    "restored companion recursor `{name}` declares {}/{} motives/minors, but `{}` declares {}/{}",
                    companion.num_motives,
                    companion.num_minors,
                    rec_val.name,
                    rec_val.num_motives,
                    rec_val.num_minors
                )));
            }
            if companion.rules.is_empty() {
                return Err(ElabError::InternalInvariant(format!(
                    "restored companion recursor `{name}` has no minor rules"
                )));
            }
            rules.extend(companion.rules.iter().cloned());
            companion_idx += 1;
        }

        if rules.len() != wanted {
            return Err(ElabError::TypeMismatch {
                expected: format!("{wanted} authenticated minor rules for {}", rec_val.name),
                actual: format!("{} restored rules", rules.len()),
            });
        }
        // The rule packet is an authority boundary for minor telescopes. Every
        // rule must agree with the genuine constructor metadata; callers must
        // never treat a missing/short recursive-field vector as all-false.
        for rule in &rules {
            let ctor = self
                .env
                .get_constructor(&rule.constructor_name)
                .ok_or_else(|| {
                    ElabError::InternalInvariant(format!(
                        "minor rule for missing constructor `{}` in recursor `{}`",
                        rule.constructor_name, rec_val.name
                    ))
                })?;
            let num_fields = ctor.num_fields as usize;
            if rule.num_fields as usize != num_fields {
                return Err(ElabError::TypeMismatch {
                    expected: format!(
                        "{} field binders for {}",
                        rule.num_fields, rule.constructor_name
                    ),
                    actual: format!("constructor metadata declares {num_fields} fields"),
                });
            }
            if rule.recursive_fields.len() != num_fields {
                return Err(ElabError::TypeMismatch {
                    expected: format!(
                        "{num_fields} recursive-field flags for {}",
                        rule.constructor_name
                    ),
                    actual: format!("{} flags", rule.recursive_fields.len()),
                });
            }
        }
        Ok(rules)
    }

    /// Authenticate the exact slice occupied by a selected inductive's minors
    /// within the global minor order of a multi-motive eliminator.
    ///
    /// Ordinary mutual blocks may place sibling minors before the selected
    /// member (`Odd` follows `Even`, for example), while restored nested helper
    /// minors generally follow the original members.  The selected constructor
    /// list must occur exactly once, contiguously and in declaration order.  A
    /// missing primary constructor must never be reclassified as an auxiliary
    /// slot whose PUnit inhabitant could accidentally type-check.
    pub(in crate::infer) fn validate_primary_minor_boundary(
        &self,
        ind_info: &clean_kernel::InductiveVal,
        minor_rules: &[clean_kernel::RecursorRule],
        emitted_primary_names: &[Option<Name>],
        context: &str,
    ) -> Result<Range<usize>, ElabError> {
        let expected = &ind_info.constructor_names;
        let primary_count = expected.len();
        if primary_count == 0 {
            return Err(ElabError::InternalInvariant(format!(
                "{context}: selected inductive `{}` has no constructors",
                ind_info.name
            )));
        }
        let matching_starts: Vec<usize> = minor_rules
            .windows(primary_count)
            .enumerate()
            .filter_map(|(start, window)| {
                window
                    .iter()
                    .zip(expected)
                    .all(|(rule, ctor)| &rule.constructor_name == ctor)
                    .then_some(start)
            })
            .collect();
        let primary_range = matching_starts
            .first()
            .copied()
            .filter(|_| matching_starts.len() == 1)
            .map(|start| start..start + primary_count);
        let primary_outside_slice = primary_range.as_ref().is_some_and(|range| {
            minor_rules.iter().enumerate().any(|(index, rule)| {
                !range.contains(&index) && expected.contains(&rule.constructor_name)
            })
        });
        if primary_range.is_none() || primary_outside_slice {
            let actual: Vec<String> = minor_rules
                .iter()
                .map(|rule| rule.constructor_name.to_string())
                .collect();
            return Err(ElabError::InternalInvariant(format!(
                "{context}: recursor minor order does not contain exactly one authenticated slice for the selected inductive; expected {:?}, matching starts {matching_starts:?}, got {actual:?}",
                expected
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
            )));
        }

        let emitted_matches = emitted_primary_names.len() == primary_count
            && emitted_primary_names
                .iter()
                .zip(expected)
                .all(|(actual, expected)| actual.as_ref() == Some(expected));
        if !emitted_matches {
            let actual: Vec<String> = emitted_primary_names
                .iter()
                .map(|name| {
                    name.as_ref()
                        .map_or_else(|| "<catch-all/unknown>".to_string(), ToString::to_string)
                })
                .collect();
            return Err(ElabError::NotImplemented(format!(
                "{context}: non-exhaustive or non-declaration-order primary match; expected exactly {:?}, emitted {actual:?}",
                expected
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
            )));
        }

        Ok(primary_range.expect("validated unique primary minor slice"))
    }

    /// Extract the type name from an expression (for casesOn lookup).
    /// Returns the base name of the type constructor.
    pub(in crate::infer) fn get_type_name(&self, ty: &Expr) -> Result<String, ElabError> {
        let ty = self.whnf(ty);
        stack_safe(|| match ty.kind() {
            ExprKind::Const(name, _) => Ok(name.to_string()),
            ExprKind::App(func, _) => {
                // Recurse on the function to get the base type name
                // e.g., `Option Nat` -> `Option`
                self.get_type_name(func)
            }
            ExprKind::FVar(id) => {
                // After WHNF, FVar means an opaque type variable.
                // Check if the FVar's binding name matches a known inductive —
                // this handles type parameters that shadow real types, e.g.,
                // `fun (Nat : Type) (n : Nat) => match n with ...` where the
                // local `Nat` FVar shadows the global `Nat` constant.
                for (name, fvar, _) in self.locals.iter().rev() {
                    if *fvar == *id {
                        let name_obj = Name::from_string(name);
                        if self.env.get_inductive(&name_obj).is_some() {
                            return Ok(name.clone());
                        }
                        break;
                    }
                }
                Err(ElabError::NotImplemented(format!(
                    "cannot extract type name from opaque type variable FVar({id:?})"
                )))
            }
            _ => Err(ElabError::NotImplemented(format!(
                "cannot extract type name from {ty:?}"
            ))),
        })
    }

    /// Beta-reduce an un-applied (or partially-applied) *predicate* field type
    /// against the already-bound earlier field values, so its type constructor
    /// becomes nameable.
    ///
    /// The anonymous-constructor pattern `⟨x, hp, hq⟩` is desugared by the parser
    /// to a right-nested `Prod.mk` tuple pattern, which the match machinery
    /// elaborates against the scrutinee's type even when that type is a
    /// *dependent* `Exists`/`Sigma` rather than a genuine `Prod`.
    /// `compute_ctor_field_types` then computes the "second component" type as the
    /// bare predicate `β = fun w => …` (the inductive's parameter), because
    /// `Prod`'s second field is non-dependent — whereas the *real* constructor
    /// (`Exists.intro` / `Sigma.mk`) types that field as `β w`, the predicate
    /// applied to the witness `w` (the first field). A bare `Lam` has no nameable
    /// head, so `get_type_name` (used to pick the field's nested `casesOn`) bails
    /// with "cannot extract type name from Lam(…)".
    ///
    /// When `field_ty` reduces to such a predicate `Lam`, apply it to the most
    /// recently-bound earlier field (the witness) and re-normalize:
    /// `(fun w => p w ∧ q w) x` reduces to `p x ∧ q x` — a `Const`-headed `And`
    /// that `get_type_name` can name and whose nested destructure the kernel
    /// accepts. A non-`Lam` field type (every genuine `Prod`/`Sigma`/inductive
    /// field) is returned unchanged, so previously-working shapes are
    /// byte-for-byte identical.
    ///
    /// SOUNDNESS (elaboration-completeness only): `β x` is *definitionally equal*
    /// to the constructor's declared field type — it is the same application, and
    /// whnf only performs β/δ/ι-reduction — so the field binder emitted into the
    /// lowered `casesOn` minor-premise type checks against the eliminator's
    /// expected minor exactly as the un-reduced form would. This never changes
    /// what the kernel accepts; it only lets the elaborator *name* the field's
    /// type constructor. No kernel/TCB code is touched, and the lowered term is
    /// still fully kernel-re-checked.
    pub(in crate::infer) fn beta_reduce_predicate_field_ty(
        &self,
        field_ty: &Expr,
        prior_fvars: &[FVarId],
    ) -> Expr {
        let reduced = self.whnf(field_ty);
        let ExprKind::Lam(..) = reduced.kind() else {
            return field_ty.clone();
        };
        // Apply the predicate to the witness — the most recently-bound earlier
        // field. For the binary `Prod.mk` anonymous tuple this is the sole
        // preceding field (the `∃`/`Σ` witness). With no earlier field there is
        // nothing to apply, so leave the type unchanged (a genuine
        // function-valued field, not the Prod-over-dependent case).
        let Some(&witness) = prior_fvars.last() else {
            return field_ty.clone();
        };
        let applied = Expr::app(reduced, Expr::fvar(witness));
        self.whnf(&applied)
    }

    /// The expected/checked type of one match arm.
    ///
    /// For a **constant** motive this is the shared `default` branch type (the
    /// first-arm body type), unchanged. For a **dependent** motive — where the
    /// match's expected type depends on the scrutinee — the arm whose pattern is
    /// `ctorᵢ field₀ … fieldₙ` has expected type `R[scrutinee := ctorᵢ field…]`,
    /// recovered by instantiating the abstracted motive body
    /// (`R[scrutinee := BVar(0)]`) at this arm's constructor value.
    ///
    /// `ctor_value` is the constructor applied to its params and bound field
    /// fvars (as built by `build_ctor_value`); for a nullary constructor it is
    /// the bare constructor constant. When the motive is constant this argument
    /// is ignored, so callers may pass any placeholder.
    pub(in crate::infer) fn arm_branch_ty(&self, default: &Expr, ctor_value: &Expr) -> Expr {
        let Some(dep_body) = &self.match_dependent_motive else {
            return default.clone();
        };
        let k = self.match_dependent_motive_indices;
        if k == 0 {
            // Non-indexed dependent motive: a single binder (the scrutinee).
            return dep_body.instantiate(ctor_value);
        }
        // Indexed dependent motive: `dep_body` lives under `k + 1` binders
        // (`BVar(0)` = major, `BVar(k)` = idx₀). The per-arm expected type is
        // `motive idx(ctorᵢ)… (ctorᵢ fields…)`, so we instantiate the major
        // binder with `ctor_value` and each index binder with the constructor's
        // *own* index value, read off the constructor value's inferred type
        // (`Tᵢ idx₀ … idx_{k-1}`).
        let ctor_index_args = self
            .infer_type(ctor_value)
            .map(|ty| {
                let ty = self.whnf(&ty);
                let mut args: Vec<Expr> = Vec::new();
                let mut head = &ty;
                while let ExprKind::App(func, arg) = head.kind() {
                    args.push((**arg).clone());
                    head = func;
                }
                args.reverse();
                // Trailing `k` spine args are the indices (params precede them).
                if args.len() >= k {
                    args.split_off(args.len() - k)
                } else {
                    args
                }
            })
            .unwrap_or_default();
        if ctor_index_args.len() != k {
            // Could not recover the constructor's indices — fall back to the
            // constant default rather than emit a mis-shifted type.
            return default.clone();
        }
        // `instantiate_rev` maps `vals[0]` → `BVar(0)` (major), `vals[i]` →
        // `BVar(i)`. Index binder `BVar(i)` (for i in 1..=k) is idx_{k-i}, so the
        // index args (`[idx₀ … idx_{k-1}]`) are supplied in reverse after the
        // ctor value.
        let mut vals: Vec<Expr> = Vec::with_capacity(k + 1);
        vals.push(ctor_value.clone());
        vals.extend(ctor_index_args.into_iter().rev());
        dep_body.instantiate_rev(&vals)
    }

    /// Build the dependent arm branch type for the constructor `full_ctor`
    /// applied to `field_fvars`, or return `default` when the motive is constant.
    ///
    /// Centralizes the `build_ctor_value` + `arm_branch_ty` pairing so each arm
    /// path computes the per-branch expected type identically.
    pub(in crate::infer) fn dependent_arm_branch_ty(
        &self,
        default: &Expr,
        full_ctor: &str,
        scrutinee_ty: &Expr,
        field_fvars: &[FVarId],
    ) -> Result<Expr, ElabError> {
        if self.match_dependent_motive.is_none() {
            return Ok(default.clone());
        }
        let ctor_value =
            self.build_ctor_value(&Name::from_string(full_ctor), scrutinee_ty, field_fvars)?;
        Ok(self.arm_branch_ty(default, &ctor_value))
    }

    /// Build the **index-generalized dependent motive body** for a match on an
    /// indexed family whose expected return type varies with the index.
    ///
    /// For `def rebuild (n) (v : IVec n) : IVec n := match v with …` the motive
    /// is NOT the constant `fun (n') (v') => branch_ty`; it must be the
    /// dependent `fun (idx₀ … idx_{k-1}) (major) => R[indices := idx][scrutinee
    /// := major]`, so each minor premise's expected type
    /// (`motive idx(ctorᵢ)… (ctorᵢ fields…)`) differs per branch and the kernel
    /// accepts the differently-typed arm bodies.
    ///
    /// Returns the abstracted body (under `k + 1` binders: `BVar(0)` = major,
    /// `BVar(k)` = idx₀) when:
    /// 1. there is an instantiated expected type,
    /// 2. the scrutinee elaborated to a bare `FVar`,
    /// 3. every index argument is a *distinct* `FVar` (the variable-index case
    ///    of dependent elimination — what `match v` over a parameter index
    ///    produces), and
    /// 4. abstracting those fvars actually changes the expected type (i.e. it
    ///    genuinely depends on the index or scrutinee).
    ///
    /// Returns `None` — keeping the existing constant-motive path byte-for-byte
    /// — when any condition fails (e.g. a non-variable index `IVec (succ k)`,
    /// which needs full unfold/generalization beyond this targeted fix, or an
    /// expected type independent of the indices).
    ///
    /// The index fvars are abstracted in binder order (idx₀ first … scrutinee
    /// last) so `abstract_fvar`'s "new binder at `BVar(0)`, shift others up"
    /// semantics leave idx₀ at the outermost `BVar(k)` and the scrutinee/major
    /// at the innermost `BVar(0)`, matching the motive lambda telescope built by
    /// the caller.
    pub(in crate::infer) fn build_indexed_dependent_motive_body(
        &mut self,
        expected: &Expr,
        index_args: &[Expr],
        scrutinee_expr: &Expr,
    ) -> Option<Expr> {
        let ExprKind::FVar(scrutinee_fvar) = scrutinee_expr.kind() else {
            return None;
        };

        let expected = self
            .metas
            .instantiate_levels(&self.metas.instantiate(expected));

        // Each index is abstracted in binder order (idx₀ outermost). A *variable*
        // index abstracts its own fvar directly. A *non-variable* index (e.g.
        // `Nat.succ k`) is abstracted by its whole expression: we replace every
        // structural occurrence of that index term with a fresh fvar, then
        // abstract the fresh fvar. This is sound — the fresh fvar is closed, so no
        // de-Bruijn shifting is needed, and `arm_branch_ty` re-specializes each
        // binder with the constructor's *own* index value (read off its inferred
        // type), so the cons arm gets `motive (succ k) …` and the kernel re-checks
        // the result.
        //
        // Each index handle (fvar) must be distinct and not the scrutinee — both a
        // duplicate and a self-reference would mis-shift the binder telescope.
        let mut handles: Vec<FVarId> = Vec::with_capacity(index_args.len());
        let mut body = expected.clone();
        for idx in index_args {
            let handle = match idx.kind() {
                ExprKind::FVar(id) => *id,
                _ => {
                    // Non-variable index: introduce a fresh fvar handle and rewrite
                    // its occurrences in the in-progress body.
                    let fresh = self.fresh_fvar();
                    body = crate::tactic::equality::replace_expr(&body, idx, &Expr::fvar(fresh));
                    fresh
                }
            };
            if handles.contains(&handle) || handle == *scrutinee_fvar {
                return None;
            }
            handles.push(handle);
        }

        // Abstract idx₀ … idx_{k-1} (outermost-first) then the scrutinee last,
        // so the scrutinee lands at BVar(0) (the major premise) and idx₀ at the
        // outermost BVar(k).
        for id in &handles {
            body = body.abstract_fvar(*id);
        }
        body = body.abstract_fvar(*scrutinee_fvar);

        // Only treat this as dependent when abstraction genuinely changed the
        // type — otherwise the constant-motive path is correct and unchanged.
        if body != expected {
            return Some(body);
        }

        // PREDECESSOR-REFINEMENT (Track S — `Vec.tail`). The straightforward
        // whole-index abstraction was a no-op: the scrutinee's index term does NOT
        // occur in the expected type. This is the index-*unification* case, where
        // the return type is expressed via the index's *predecessor*:
        //
        //   def Vec.tail {α}{n} (v : Vec α (Nat.succ n)) : Vec α n :=
        //     match v with | Vec.cons _ tl => tl
        //
        // The scrutinee index is `Nat.succ n`, but the expected type is `Vec α n`
        // (mentioning the predecessor `n`, not `Nat.succ n`). A constant motive
        // forces the `cons` minor to inhabit `Vec α n`, yet the bound tail is
        // `tl : Vec α n'` with `n'` the cons-bound index — unrelated to `n` without
        // the equation `Nat.succ n' = Nat.succ n`.
        //
        // For a single `Nat.succ <sub>` index we instead build the index-refining
        // motive `fun (m : Nat) (_ : Vec α m) => E[<sub> := Nat.pred m]`. At the
        // scrutinee's own index `Nat.succ n` this reduces (iota) to
        // `E[<sub> := Nat.pred (Nat.succ n)] ≡ E[<sub> := n] = E`, so the function's
        // declared return type is recovered. At the `cons` constructor's refined
        // index `Nat.succ n'`, `arm_branch_ty` re-specializes the binder to give
        // `E[<sub> := Nat.pred (Nat.succ n')] ≡ E[<sub> := n']` = `Vec α n'`, which
        // `tl : Vec α n'` inhabits. The kernel re-checks the whole lowered term, so
        // the `Nat.pred ∘ Nat.succ` iota-reduction is the soundness gate.
        self.build_succ_pred_refined_motive_body(&expected, index_args, scrutinee_fvar)
    }

    /// The single-`Nat.succ`-index predecessor-refinement fallback for
    /// [`build_indexed_dependent_motive_body`]. Returns the abstracted motive body
    /// (under the `(index)(major)` binder telescope) when the family has exactly
    /// one index, that index is `Nat.succ <sub>`, and the expected type genuinely
    /// mentions `<sub>` (so the predecessor rewrite changes it). Otherwise `None`,
    /// leaving the constant-motive path byte-for-byte unchanged.
    ///
    /// SOUNDNESS: the rewrite only substitutes `<sub> := Nat.pred (index-binder)`;
    /// the resulting motive is re-checked by the kernel (it re-checks the lowered
    /// `casesOn` application). `Nat.pred (Nat.succ x)` iota-reduces to `x`, so the
    /// reachable `cons` minor recovers its real `Vec α n'` result type — no axiom,
    /// no `sorry`. Restricted to the single-index `Nat.succ` shape; multi-index or
    /// non-`Nat` index families return `None` (they need full index unification,
    /// out of scope for this targeted slice).
    fn build_succ_pred_refined_motive_body(
        &mut self,
        expected: &Expr,
        index_args: &[Expr],
        scrutinee_fvar: &FVarId,
    ) -> Option<Expr> {
        // Single index only: the `(m)(major)` telescope this fallback targets.
        let [idx] = index_args else {
            return None;
        };
        // The index must be `Nat.succ <sub>` (the predecessor-expressible shape).
        let idx_w = self.whnf(idx);
        let ExprKind::App(head, sub) = idx_w.kind() else {
            return None;
        };
        let ExprKind::Const(head_name, _) = head.kind() else {
            return None;
        };
        if *head_name != Name::from_string("Nat.succ") {
            return None;
        }
        let sub = sub.as_ref().clone();

        // Build `Nat.pred (BVar(1))` — the index binder is `BVar(1)` under the
        // motive's `(index)(major)` telescope (major is `BVar(0)`). We rewrite
        // `<sub>` to a fresh fvar first (so the abstraction machinery is uniform),
        // then abstract that fvar at the index position.
        let pred_fvar = self.fresh_fvar();
        if pred_fvar == *scrutinee_fvar {
            return None;
        }
        let pred_handle = Expr::fvar(pred_fvar);
        let body = crate::tactic::equality::replace_expr(expected, &sub, &pred_handle);
        // The rewrite must genuinely change the expected type — otherwise `<sub>`
        // does not occur and there is nothing to refine (keep the constant motive).
        if body == *expected {
            return None;
        }
        // Wrap each occurrence of the predecessor handle as `Nat.pred <handle>`, so
        // after abstraction the index binder appears under `Nat.pred`.
        let nat_pred = Expr::const_(Name::from_string("Nat.pred"), vec![]);
        let body = crate::tactic::equality::replace_expr(
            &body,
            &pred_handle,
            &Expr::app(nat_pred, pred_handle.clone()),
        );

        // Abstract the index handle (→ BVar at the index binder) then the scrutinee
        // (→ BVar(0), the major), matching the motive lambda telescope.
        let body = body.abstract_fvar(pred_fvar);
        let body = body.abstract_fvar(*scrutinee_fvar);
        Some(body)
    }

    /// Authenticate an inductive side-table packet against its constant and
    /// exact type telescope.
    pub(in crate::infer) fn authenticate_inductive_metadata(
        &self,
        ind_name: &Name,
    ) -> Result<&clean_kernel::InductiveVal, ElabError> {
        let ind = self.env.get_inductive(ind_name).ok_or_else(|| {
            ElabError::InternalInvariant(format!(
                "missing registered inductive metadata `{ind_name}`"
            ))
        })?;
        if ind.name != *ind_name {
            return Err(ElabError::InternalInvariant(format!(
                "inductive registry key `{ind_name}` contains packet `{}`",
                ind.name
            )));
        }
        let constant = self.env.get_const(ind_name).ok_or_else(|| {
            ElabError::InternalInvariant(format!(
                "inductive metadata `{ind_name}` has no matching constant declaration"
            ))
        })?;
        if constant.name != *ind_name
            || constant.kind != clean_kernel::env::ConstantKind::Definition
            || constant.level_params != ind.level_params
            || constant.type_ != ind.type_
        {
            return Err(ElabError::InternalInvariant(format!(
                "inductive metadata `{ind_name}` disagrees with its constant declaration"
            )));
        }
        let expected_arity = ind.num_params as usize + ind.num_indices as usize;
        let mut cursor = &ind.type_;
        for binder_index in 0..expected_arity {
            let ExprKind::Pi(_, _, body) = cursor.kind() else {
                return Err(ElabError::InternalInvariant(format!(
                    "inductive metadata `{ind_name}` telescope ends before binder {binder_index} of {expected_arity}"
                )));
            };
            cursor = body;
        }
        if !matches!(cursor.kind(), ExprKind::Sort(_)) {
            return Err(ElabError::InternalInvariant(format!(
                "inductive metadata `{ind_name}` has binders beyond its declared parameter/index arity or does not end in a sort: {cursor:?}"
            )));
        }
        let occurrences = ind
            .all_names
            .iter()
            .filter(|member| *member == ind_name)
            .count();
        if occurrences != 1 {
            return Err(ElabError::InternalInvariant(format!(
                "inductive metadata `{ind_name}` occurs {occurrences} times in its mutual-family list"
            )));
        }
        let mut seen = std::collections::HashSet::with_capacity(ind.constructor_names.len());
        if let Some(duplicate) = ind
            .constructor_names
            .iter()
            .find(|ctor_name| !seen.insert((*ctor_name).clone()))
        {
            return Err(ElabError::InternalInvariant(format!(
                "inductive metadata `{ind_name}` repeats constructor `{duplicate}`"
            )));
        }
        Ok(ind)
    }

    /// Authenticate a constructor side-table packet, its constant mirror, its
    /// parent/index registration, and the complete constructor return spine.
    pub(in crate::infer) fn authenticate_constructor_metadata(
        &self,
        ctor_name: &Name,
    ) -> Result<(&clean_kernel::ConstructorVal, &clean_kernel::InductiveVal), ElabError> {
        let ctor = self.env.get_constructor(ctor_name).ok_or_else(|| {
            ElabError::InternalInvariant(format!(
                "missing registered constructor metadata `{ctor_name}`"
            ))
        })?;
        if ctor.name != *ctor_name {
            return Err(ElabError::InternalInvariant(format!(
                "constructor registry key `{ctor_name}` contains packet `{}`",
                ctor.name
            )));
        }
        let constant = self.env.get_const(ctor_name).ok_or_else(|| {
            ElabError::InternalInvariant(format!(
                "constructor metadata `{ctor_name}` has no matching constant declaration"
            ))
        })?;
        if constant.name != *ctor_name
            || constant.kind != clean_kernel::env::ConstantKind::Definition
            || constant.level_params != ctor.level_params
            || constant.type_ != ctor.type_
        {
            return Err(ElabError::InternalInvariant(format!(
                "constructor metadata `{ctor_name}` disagrees with its constant declaration"
            )));
        }
        let ind = self.authenticate_inductive_metadata(&ctor.inductive_name)?;
        if ctor.num_params != ind.num_params || ctor.level_params != ind.level_params {
            return Err(ElabError::InternalInvariant(format!(
                "constructor metadata `{ctor_name}` parameter packet disagrees with inductive `{}`",
                ctor.inductive_name
            )));
        }
        if ind.constructor_names.get(ctor.constructor_idx as usize) != Some(ctor_name) {
            return Err(ElabError::InternalInvariant(format!(
                "constructor metadata `{ctor_name}` has index {} inconsistent with inductive `{}`",
                ctor.constructor_idx, ctor.inductive_name
            )));
        }

        let telescope_arity = ctor.num_params as usize + ctor.num_fields as usize;
        let mut return_ty = &ctor.type_;
        for binder_index in 0..telescope_arity {
            let ExprKind::Pi(_, _, body) = return_ty.kind() else {
                return Err(ElabError::InternalInvariant(format!(
                    "constructor metadata `{ctor_name}` telescope ends before binder {binder_index} of {telescope_arity}"
                )));
            };
            return_ty = body;
        }
        let return_levels = match return_ty.get_app_fn().kind() {
            ExprKind::Const(name, levels) if name == &ctor.inductive_name => levels,
            _ => {
                return Err(ElabError::InternalInvariant(format!(
                    "constructor metadata `{ctor_name}` does not return inductive `{}` after its declared telescope: {return_ty:?}",
                    ctor.inductive_name
                )));
            }
        };
        let expected_levels: Vec<Level> =
            ind.level_params.iter().cloned().map(Level::param).collect();
        if return_levels.as_slice() != expected_levels.as_slice() {
            return Err(ElabError::InternalInvariant(format!(
                "constructor metadata `{ctor_name}` returns `{}` at universe levels {return_levels:?}, expected {expected_levels:?}",
                ctor.inductive_name
            )));
        }
        let return_args = return_ty.get_app_args();
        let expected_return_args = ind.num_params as usize + ind.num_indices as usize;
        if return_args.len() != expected_return_args {
            return Err(ElabError::InternalInvariant(format!(
                "constructor metadata `{ctor_name}` return spine supplies {} arguments to `{}`, expected {expected_return_args}",
                return_args.len(), ctor.inductive_name
            )));
        }
        for param_index in 0..ind.num_params as usize {
            let expected_bvar =
                Expr::bvar(ctor.num_params + ctor.num_fields - 1 - param_index as u32);
            if return_args[param_index] != &expected_bvar {
                return Err(ElabError::InternalInvariant(format!(
                    "constructor metadata `{ctor_name}` return parameter {param_index} is {:?}, expected {expected_bvar:?}",
                    return_args[param_index]
                )));
            }
        }
        Ok((ctor, ind))
    }

    /// The `BinderInfo` of each of a constructor's `num_fields` *field* binders,
    /// in field order (the Pi binders after the `num_params` parameter binders).
    ///
    /// The environment only exposes registered constructors here, so a truncated
    /// telescope or disagreement with the constant/inductive registries is an
    /// internal metadata error, never a reason to guess binder explicitness.
    pub(in crate::infer) fn ctor_field_binder_infos(
        &self,
        ctor: &clean_kernel::ConstructorVal,
    ) -> Result<Vec<BinderInfo>, ElabError> {
        let (ctor, _) = self.authenticate_constructor_metadata(&ctor.name)?;
        let mut ty = &ctor.type_;
        // Skip the parameter binders.
        for param_index in 0..ctor.num_params {
            let ExprKind::Pi(_, _, codomain) = ty.kind() else {
                return Err(ElabError::InternalInvariant(format!(
                    "constructor metadata `{}` telescope ends before parameter {param_index}",
                    ctor.name
                )));
            };
            ty = codomain;
        }
        // Read the binder info off each field binder.
        let mut infos = Vec::with_capacity(ctor.num_fields as usize);
        for field_index in 0..ctor.num_fields {
            let ExprKind::Pi(binder, _, codomain) = ty.kind() else {
                return Err(ElabError::InternalInvariant(format!(
                    "constructor metadata `{}` telescope ends before field {field_index}",
                    ctor.name
                )));
            };
            infos.push(binder.info);
            ty = codomain;
        }
        Ok(infos)
    }

    /// Expand a match-pattern constructor's *explicit-only* field patterns into a
    /// full-length field-pattern list, inserting a `Wildcard` at each implicit
    /// field position.
    ///
    /// In Lean, implicit constructor fields (the `{n : Nat}` index witnesses of an
    /// indexed family, e.g. `Vec.cons : {n : Nat} → α → Vec α n → Vec α (n+1)`)
    /// are NOT written in patterns — they are solved by index unification. The
    /// user writes `Vec.cons x rest` (two explicit patterns), but the constructor
    /// has three fields. This helper bridges that gap so the downstream
    /// field-binding loops, which walk one binder per `num_fields` position, line
    /// up unchanged.
    ///
    /// Behavior:
    /// - When it has no implicit fields, or the user already supplied exactly
    ///   `num_fields` patterns (every field written explicitly), the patterns
    ///   are returned unchanged and the historical `num_fields` arity check
    ///   applies. Unknown or malformed constructor metadata is rejected.
    /// - Otherwise the arity is checked against the count of *explicit* fields and
    ///   a `Wildcard` is materialized at each implicit field position, yielding a
    ///   `num_fields`-length list.
    ///
    /// SOUNDNESS: this only inserts non-binding `Wildcard` placeholders at
    /// positions the surface syntax omits; it never drops or reorders a
    /// user-written pattern, and a genuinely wrong *explicit* arity still errors
    /// (now reported against the explicit-field count the user actually writes).
    pub(in crate::infer) fn expand_implicit_ctor_field_patterns(
        &self,
        context: &str,
        full_ctor: &str,
        sub_pats: &[SurfacePattern],
    ) -> Result<Vec<SurfacePattern>, ElabError> {
        // A trailing `..` ellipsis (`.Ctor x ..`) stands for "the remaining
        // explicit fields are all wildcards". Detect it here; the leading
        // user-written patterns are everything before the marker.
        let has_ellipsis = matches!(sub_pats.last(), Some(SurfacePattern::Ellipsis));
        let explicit_user_pats: &[SurfacePattern] = if has_ellipsis {
            &sub_pats[..sub_pats.len() - 1]
        } else {
            sub_pats
        };

        let ctor = self
            .env
            .get_constructor(&Name::from_string(full_ctor))
            .ok_or_else(|| ElabError::UnknownIdent(full_ctor.to_string()))?;
        let num_fields = ctor.num_fields as usize;
        let field_infos = self.ctor_field_binder_infos(ctor)?;

        let num_explicit = field_infos
            .iter()
            .filter(|info| matches!(info, BinderInfo::Default))
            .count();

        // With a trailing `..`, the leading patterns must not exceed the explicit
        // field count; the ellipsis fills the rest. Pad up to `num_explicit` and
        // fall through to the implicit-field interleaving below.
        let owned_pats: Vec<SurfacePattern>;
        let sub_pats: &[SurfacePattern] = if has_ellipsis {
            super::ensure_ctor_pattern_arity_at_most(
                context,
                full_ctor,
                num_explicit,
                explicit_user_pats.len(),
            )?;
            let mut padded = explicit_user_pats.to_vec();
            padded.resize(num_explicit, SurfacePattern::Wildcard);
            owned_pats = padded;
            &owned_pats
        } else {
            sub_pats
        };

        // Idempotence: a list that is already `num_fields` long with a
        // non-binding `Wildcard` at every implicit position is this helper's
        // own output shape — the pattern pipeline normalizes arm patterns more
        // than once (ctor-ordered rec planning expands before the rec-arm
        // elaboration re-normalizes), so re-entry must be identity rather than
        // re-checking against the explicit-only count, which rejected every
        // recursive match over an indexed family with implicit index fields.
        // A user-written pattern at an implicit position (`.cons a b c`) is NOT
        // all-wildcard there and still falls through to the loud arity error.
        // The narrow acceptance this adds (a user spelling `_` herself at every
        // implicit slot, at full field arity) elaborates identically to the
        // explicit-only spelling.
        if num_explicit < num_fields
            && sub_pats.len() == num_fields
            && field_infos.iter().zip(sub_pats.iter()).all(|(info, pat)| {
                matches!(info, BinderInfo::Default) || matches!(pat, SurfacePattern::Wildcard)
            })
        {
            return Ok(sub_pats.to_vec());
        }

        // No implicit fields: explicit count == num_fields, so the historical
        // `num_fields` check is exactly right and patterns pass through
        // byte-for-byte (preserving every previously-working shape).
        if num_explicit == num_fields {
            super::ensure_ctor_pattern_arity(context, full_ctor, Some(num_fields), sub_pats.len())?;
            return Ok(sub_pats.to_vec());
        }

        // Narrowed check: the user writes one pattern per *explicit* field. This
        // is the load-bearing soundness gate — an implicit constructor field
        // (e.g. an indexed family's `{n : Nat}` index witness) is NOT written in
        // a pattern, so writing `num_fields` patterns is a genuine arity error,
        // not a free pass. The check is narrowed (to `num_explicit`), never
        // removed.
        super::ensure_ctor_pattern_arity(context, full_ctor, Some(num_explicit), sub_pats.len())?;

        // Interleave: user pattern at each explicit position, fresh `Wildcard`
        // at each implicit position.
        let mut expanded = Vec::with_capacity(num_fields);
        let mut user_iter = sub_pats.iter();
        for info in &field_infos {
            if matches!(info, BinderInfo::Default) {
                let Some(pattern) = user_iter.next().cloned() else {
                    return Err(ElabError::InternalInvariant(format!(
                        "constructor pattern `{full_ctor}` lost an explicit field after exact arity validation"
                    )));
                };
                expanded.push(pattern);
            } else {
                expanded.push(SurfacePattern::Wildcard);
            }
        }
        Ok(expanded)
    }

    /// Resolve a match-pattern constructor name to its fully-qualified form.
    ///
    /// Pattern constructor names historically resolved only as (1) the bare
    /// `ctor` name and (2) `TypeName.ctor`. Term references, by contrast,
    /// resolve through opened namespaces via the [`NamespaceState`] alias table
    /// (see `elab_ident`). This helper closes that gap so that, after
    /// `open Foo` (or `open Foo renaming bar -> baz`, `export Foo (bar)`), a
    /// pattern naming the opened constructor resolves to the qualified name.
    ///
    /// Resolution order, returning the first match that is a genuine
    /// constructor of `type_name`:
    /// 1. `ctor_name` taken as already fully qualified.
    /// 2. `TypeName.ctor` (the long-standing implicit qualification).
    /// 3. The opened-namespace alias table (`open` / `export`).
    ///
    /// SOUNDNESS: a candidate is only accepted when it names a registered
    /// constructor whose `inductive_name` equals `type_name`. This prevents an
    /// opened alias (or stray constant) from mis-resolving to a constructor of
    /// an unrelated inductive, or to a non-constructor constant.
    ///
    /// [`NamespaceState`]: crate::namespace::NamespaceState
    pub(in crate::infer) fn resolve_ctor_name(
        &self,
        ctor_name: &str,
        type_name: &str,
    ) -> Option<String> {
        // 1. Treat `ctor_name` as already qualified.
        if self.ctor_belongs_to(ctor_name, type_name) {
            return Some(ctor_name.to_string());
        }

        // 2. Implicit `TypeName.ctor` qualification (only meaningful for an
        //    unqualified pattern name).
        if !ctor_name.contains('.') {
            let qualified = format!("{type_name}.{ctor_name}");
            if self.ctor_belongs_to(&qualified, type_name) {
                return Some(qualified);
            }
        }

        // 3. Opened-namespace alias table, mirroring term-reference resolution.
        if let Some(target) = self.namespace_state.resolve(ctor_name) {
            let target_str = target.to_string();
            if self.ctor_belongs_to(&target_str, type_name) {
                return Some(target_str);
            }
        }

        // 4. Suffix match against the inductive's OWN constructor list — the
        //    authoritative source. A pattern written relative to an enclosing
        //    namespace (`Two.a` for the constructor `M.Two.a` of inductive
        //    `M.Two`) is neither a literal constructor name (step 1 fails) nor
        //    bare-name-qualifiable (step 2 is skipped because it already contains
        //    a dot), yet it unambiguously denotes the unique constructor of
        //    `type_name` whose full name ends in `.{ctor_name}` (or equals it).
        //    Without this, a qualified pattern fails to resolve and the
        //    ctor-ordered `casesOn` builder silently bails to a source-order
        //    fallback that mis-binds the minors (every arm collapses onto the
        //    first body — the "match iota-reduces to the first arm" bug). The
        //    match is read off the kernel's constructor list, so it can only
        //    resolve to a genuine constructor of `type_name`; constructor short
        //    names are unique within one inductive, so the suffix is unambiguous.
        if let Some(ind) = self.env.get_inductive(&Name::from_string(type_name)) {
            let dotted = format!(".{ctor_name}");
            for full in &ind.constructor_names {
                let full_str = full.to_string();
                if full_str == ctor_name || full_str.ends_with(&dotted) {
                    return Some(full_str);
                }
            }
        }

        None
    }

    /// Fully-qualify a match-pattern constructor name, with a legacy fallback.
    ///
    /// Returns the namespace-aware resolution from
    /// [`resolve_ctor_name`](Self::resolve_ctor_name) when it succeeds. When no
    /// genuine constructor is found, falls back to the historical literal
    /// qualification (`ctor_name` as-is if it already contains a dot, otherwise
    /// `TypeName.ctor`) so downstream arity / unknown-constructor diagnostics
    /// keep reporting the name the user wrote.
    pub(in crate::infer) fn ctor_pattern_full_name(
        &self,
        ctor_name: &str,
        type_name: &str,
    ) -> String {
        self.resolve_ctor_name(ctor_name, type_name)
            .unwrap_or_else(|| {
                if ctor_name.contains('.') {
                    ctor_name.to_string()
                } else {
                    format!("{type_name}.{ctor_name}")
                }
            })
    }

    /// Remap a container constructor pattern onto the nested-aux mirror type
    /// (#3396 FIX-FV Part 2, construction/pattern direction).
    ///
    /// When a nested inductive (e.g. `Value` with `aggregate : List Value`) is
    /// eliminated, the kernel synthesises an auxiliary mirror type
    /// `Value._List` whose constructors duplicate the container's
    /// (`Value._List.nil`, `Value._List.cons`) with self-references replaced by
    /// the aux type. A pattern like `| .aggregate (x :: xs) =>` binds the
    /// `aggregate` field at type `Value._List`, but the sub-pattern's
    /// constructor (`List.cons`) belongs to `List`, not `Value._List`, so the
    /// naive `inductive_name` check rejects it.
    ///
    /// This helper detects exactly that situation and returns the mirrored aux
    /// constructor name (`Value._List.cons`). It is purely structural and
    /// soundness-preserving: the remapped name must be a *real, registered*
    /// constructor of the aux inductive `field_type_name`, with the SAME suffix
    /// and the SAME field count as the container constructor the user wrote.
    /// The aux constructor's signature is the kernel-generated mirror of the
    /// container's (head field unchanged, tail field re-typed to the aux), so
    /// matching against it binds precisely the right field types. The lowered
    /// `casesOn` is re-checked by the kernel — this can only narrow, never widen,
    /// what type-checks. Returns `None` when no such mirror exists (the caller
    /// then reports the original "does not belong" diagnostic unchanged).
    pub(in crate::infer) fn remap_container_ctor_to_field_aux(
        &self,
        field_type_name: &str,
        container_ctor_full: &str,
    ) -> Option<String> {
        // The field type must be a nested-aux mirror inductive. Aux types are
        // generated with names of the shape `<Parent>._<Container>`; require the
        // `._` marker so we never remap onto an unrelated user inductive that
        // merely happens to share a constructor suffix.
        if !field_type_name.contains("._") {
            return None;
        }
        let aux_ind = Name::from_string(field_type_name);
        // The aux inductive must actually exist as a registered inductive.
        self.env.get_inductive(&aux_ind)?;
        // Suffix of the container constructor the user wrote (e.g. `nil`/`cons`).
        let suffix = container_ctor_full.rsplit_once('.').map(|(_, s)| s)?;
        let aux_ctor = format!("{field_type_name}.{suffix}");
        let aux_info = self.env.get_constructor(&Name::from_string(&aux_ctor))?;
        // Soundness gate: the candidate must genuinely belong to the aux
        // inductive and mirror the container ctor's field count exactly.
        if aux_info.inductive_name != aux_ind {
            return None;
        }
        let container_info = self
            .env
            .get_constructor(&Name::from_string(container_ctor_full))?;
        if aux_info.num_fields != container_info.num_fields {
            return None;
        }
        Some(aux_ctor)
    }

    /// Remap the anonymous-constructor placeholder `Prod.mk` (produced by the
    /// parser for a `⟨…⟩` pattern) onto the field type's actual sole constructor.
    ///
    /// The parser desugars `⟨a, b⟩` to a right-nested binary `Prod.mk a b`
    /// pattern, but such an anonymous constructor may destructure any
    /// single-constructor inductive — `And`, `Exists`, `Sigma`, `Subtype`, a
    /// structure — not just `Prod`. At the *top* level `elaborate_ctor_arm` never
    /// checks that the pattern ctor belongs to the scrutinee (it lowers via the
    /// scrutinee's own `casesOn`), so `⟨hp, hq⟩` on `P ∧ Q` already works. In a
    /// *nested* field position, however, `resolve_nested_ctor_pattern` must name a
    /// real constructor of the field inductive to build the field's nested
    /// `casesOn`, so the `Prod.mk` placeholder has to be resolved to (here)
    /// `And.intro` / `Exists.intro` / `Sigma.mk`.
    ///
    /// Returns the field inductive's sole constructor when the written ctor is the
    /// `Prod.mk` placeholder, does not belong to the field inductive, and that
    /// inductive has exactly ONE constructor whose field count matches the
    /// (binary) sub-pattern count — the And/Exists/Sigma shape the right-nested
    /// encoding lines up with. Returns `None` otherwise, so a genuinely wrong
    /// nested constructor still reports the original "does not belong" diagnostic,
    /// and a real `Prod` field (where `Prod.mk` belongs) never reaches this path.
    ///
    /// SOUNDNESS: the remapped name is a *real, registered* constructor of the
    /// field inductive with a matching field count, so the field binders line up
    /// one-to-one and the emitted nested `casesOn` is re-checked by the kernel —
    /// this can only narrow, never widen, what type-checks.
    pub(in crate::infer) fn remap_anonymous_tuple_ctor(
        &self,
        field_type_name: &str,
        written_ctor_full: &str,
        num_sub_pats: usize,
    ) -> Option<String> {
        // Only the parser's anonymous-tuple placeholder is remapped. A genuine
        // `Prod` field keeps `Prod.mk` (it belongs, so this path is never reached
        // for it).
        if written_ctor_full != "Prod.mk" {
            return None;
        }
        let ind = self
            .env
            .get_inductive(&Name::from_string(field_type_name))?;
        // Anonymous-constructor resolution targets a single-constructor type.
        let [sole_ctor] = ind.constructor_names.as_slice() else {
            return None;
        };
        let ctor_info = self.env.get_constructor(sole_ctor)?;
        // The binary `Prod.mk` placeholder carries exactly two sub-patterns; only
        // remap when the target constructor's field count matches, so the field
        // binders line up one-to-one. A different arity is the flattened
        // anonymous-constructor case, out of scope for this shape.
        if ctor_info.num_fields as usize != num_sub_pats {
            return None;
        }
        Some(sole_ctor.to_string())
    }

    /// Remap a TOP-LEVEL anonymous-constructor pattern (`⟨a, b, c⟩`) onto a
    /// single-constructor type's flat N-ary constructor when that type is NOT
    /// `Prod`.
    ///
    /// The parser desugars `⟨a, b, c⟩` to a right-nested *binary* `Prod.mk`
    /// pattern (`Prod.mk a (Prod.mk b c)`). For a genuine `Prod` scrutinee that
    /// nesting mirrors the type; a single-constructor *structure* whose real
    /// constructor is not `Prod.mk` fails to line up ("cannot extract type
    /// name" for N ≥ 3, a shape unification mismatch for N = 2). Named-ctor
    /// patterns (`| T.mk a b c =>`) already work, so this resolves the `Prod.mk`
    /// placeholder to the real constructor and flattens the right-nested spine
    /// into its N fields.
    ///
    /// Applies when the scrutinee is a single-constructor inductive whose sole
    /// constructor is not `Prod.mk` and the written pattern flattens to exactly
    /// N leaves, in either regime:
    /// - **N ≥ 3** — the binary nesting can never line up with a flat N-ary
    ///   constructor, so remapping is unconditional.
    /// - **N = 2 for a *native structure*** (one with a field-name table —
    ///   a user `structure`, or `Sigma`/`PSigma`/`Subtype`). A user 2-field
    ///   structure is mishandled by the placeholder path; `Sigma`/`PSigma`/
    ///   `Subtype` already work, and their named-ctor lowering is identical, so
    ///   behavior is preserved. `And`/`Exists`/`Iff` (no field table, N = 2)
    ///   are deliberately excluded and keep their existing placeholder path.
    ///
    /// Returns `None` otherwise, leaving every currently-working shape on its
    /// existing path.
    ///
    /// SOUNDNESS: the remapped name is the scrutinee's real, registered
    /// constructor, and the flattened leaves are bound one-to-one against its
    /// declared field types via the same lowering the named-constructor pattern
    /// uses; the emitted `casesOn` is re-checked by the kernel, so a wrong
    /// flattening can only be *rejected*, never silently accepted.
    pub(in crate::infer) fn remap_anon_tuple_to_structure(
        &self,
        type_name: &str,
        sub_pats: &[SurfacePattern],
    ) -> Option<(String, Vec<SurfacePattern>)> {
        let type_name_obj = Name::from_string(type_name);
        let ind = self.env.get_inductive(&type_name_obj)?;
        // Anonymous-constructor resolution targets a single-constructor type.
        let [sole_ctor] = ind.constructor_names.as_slice() else {
            return None;
        };
        let sole_full = sole_ctor.to_string();
        // A genuine `Prod` keeps the placeholder (it belongs); nothing to remap.
        if sole_full == "Prod.mk" {
            return None;
        }
        let ctor_info = self.env.get_constructor(sole_ctor)?;
        let n = ctor_info.num_fields as usize;
        if n < 2 {
            return None;
        }
        // N = 2 only for a *native structure* (it has a field-name table). This
        // fixes a user 2-field structure while leaving And/Exists/Iff (which
        // have no field table and whose placeholder path works) untouched;
        // Sigma/PSigma/Subtype have a field table but their named-ctor lowering
        // matches their working placeholder path, so behavior is preserved.
        if n == 2 && self.env.get_structure_field_names(&type_name_obj).is_none() {
            return None;
        }
        let flat = Self::flatten_right_nested_prod(sub_pats, n)?;
        Some((sole_full, flat))
    }

    /// Flatten a right-nested binary `Prod.mk` anonymous-tuple pattern into
    /// exactly `n` leaf sub-patterns. `sub_pats` are the arguments of the
    /// OUTERMOST `Prod.mk` (`⟨a, b, c⟩` ⇒ `[a, Prod.mk[b, c]]`), which flattens
    /// to `[a, b, c]` for `n = 3`. Peels the left element off each binary node
    /// `n - 1` times; the remaining pattern is the final leaf (re-wrapped as a
    /// `Prod.mk` sub-pattern when the last field is itself a genuine pair).
    /// Returns `None` unless the spine yields exactly `n` leaves — a written
    /// arity other than `n` is left for the caller to reject downstream.
    fn flatten_right_nested_prod(
        sub_pats: &[SurfacePattern],
        n: usize,
    ) -> Option<Vec<SurfacePattern>> {
        let mut leaves: Vec<SurfacePattern> = Vec::with_capacity(n);
        let mut cur: Vec<SurfacePattern> = sub_pats.to_vec();
        for _ in 0..n.saturating_sub(1) {
            if cur.len() != 2 {
                return None;
            }
            let mut it = cur.into_iter();
            let head = it.next()?;
            let tail = it.next()?;
            leaves.push(head);
            cur = match tail {
                SurfacePattern::Ctor(name, inner) if name == "Prod.mk" => inner,
                other => vec![other],
            };
        }
        let last = if cur.len() == 1 {
            cur.into_iter().next()?
        } else {
            SurfacePattern::Ctor("Prod.mk".to_string(), cur)
        };
        leaves.push(last);
        (leaves.len() == n).then_some(leaves)
    }

    /// Whether `name` is a registered constructor of inductive `type_name`.
    ///
    /// Used by [`resolve_ctor_name`](Self::resolve_ctor_name) as the soundness
    /// gate: a resolved name must be a real constructor of the scrutinee's
    /// inductive, never an unrelated constant or a constructor of another type.
    fn ctor_belongs_to(&self, name: &str, type_name: &str) -> bool {
        self.env
            .get_constructor(&Name::from_string(name))
            .is_some_and(|info| info.inductive_name == Name::from_string(type_name))
    }

    /// Extract type arguments from a type application (#386)
    ///
    /// For `List Nat`, returns `[Nat]`. For `Map String Int`, returns `[String, Int]`.
    /// For non-application types (like `Nat`), returns empty vec.
    pub(in crate::infer) fn extract_type_args(&self, ty: &Expr, num_params: u32) -> Vec<Expr> {
        let ty = self.whnf(ty);
        let mut args = Vec::new();
        let mut curr = &ty;

        // Collect args from spine of applications
        while let ExprKind::App(func, arg) = curr.kind() {
            args.push((**arg).clone());
            curr = func;
        }

        // Args were collected in reverse order (innermost first)
        args.reverse();

        // Take only the number of parameters expected
        args.truncate(num_params as usize);
        args
    }

    /// The ordered *applied* domain type of each of eliminator `cases_on_name`'s
    /// motives — `[Primary, Aux…]`, length `num_motives`.
    ///
    /// Post-B0-B5 a nested container aux (the real `List`) is erased from
    /// `ind_info.all_names`, so for a param-less primary the recursor type is the
    /// authoritative source for the auxiliary motive domains (e.g. `List Value`).
    /// Otherwise — an imported eliminator (no registered recursor) or a parametric
    /// primary — reconstruct from the surviving `all_names` siblings applied to
    /// `major_ty`'s parameters (genuinely-mutual imported blocks keep their
    /// siblings there). The caller supplies `num_motives` from the recursor (or
    /// `all_names.len()` when the eliminator is a plain imported constant).
    pub(in crate::infer) fn block_motive_domains(
        &self,
        cases_on_name: &Name,
        ind_info: &clean_kernel::inductive::InductiveVal,
        major_ty: &Expr,
        num_motives: usize,
    ) -> Vec<Expr> {
        if num_motives == 0 {
            return Vec::new();
        }
        if let Some(rec) = self.env.get_recursor(cases_on_name).cloned() {
            // Instantiate the recursor's leading parameter binders with the
            // scrutinee's type arguments, then read every motive binder's applied
            // domain. This handles a PARAMETRIC nested primary (e.g. `Rose α` with
            // a `List (Rose α)` field), where the motive domains reference the
            // parameter and must be substituted; a param-less primary skips the
            // loop and reads the domains directly.
            let major_whnf = self.whnf(major_ty);
            let type_args = self.extract_type_args(&major_whnf, ind_info.num_params);
            let np = rec.num_params as usize;
            if type_args.len() >= np {
                let mut rec_ty = rec.type_.clone();
                let mut peeled = true;
                for arg in type_args.iter().take(np) {
                    if let ExprKind::Pi(_, _, body) = rec_ty.kind() {
                        rec_ty = body.instantiate(arg);
                    } else {
                        peeled = false;
                        break;
                    }
                }
                if peeled {
                    let doms = super::motive_domains_from_rec_type(&rec_ty, num_motives);
                    if doms.len() == num_motives {
                        return doms;
                    }
                }
            }
        }
        // Fallback: each surviving block member applied to the major's type args.
        let whnf = self.whnf(major_ty);
        let levels = match whnf.get_app_fn().kind() {
            ExprKind::Const(_, ls) => ls.to_vec(),
            _ => vec![],
        };
        let type_args = self.extract_type_args(&whnf, ind_info.num_params);
        ind_info
            .all_names
            .iter()
            .map(|member| {
                let mut a = Expr::const_(member.clone(), levels.clone());
                for arg in &type_args {
                    a = Expr::app(a, arg.clone());
                }
                a
            })
            .collect()
    }

    /// The eliminator's *motive universe* level for a match whose minor premises
    /// all produce a value of `branch_ty`.
    ///
    /// The motive is `fun (…) => branch_ty`, so its codomain is `branch_ty`,
    /// whose type is `Sort u`. The motive therefore maps into `Sort u`, and the
    /// recursor's motive-universe parameter must be exactly `u` — the universe
    /// that `branch_ty` *inhabits*, i.e. `infer_sort(branch_ty)`.
    ///
    /// This holds uniformly, including when `branch_ty` is itself a sort: e.g.
    /// `branch_ty = Type = Sort 1` lives in `Sort 2`, so the motive
    /// `fun _ => Type` has type `T → Sort 2` and the motive universe is `2`
    /// (NOT `1`, the level *inside* the sort). A type-valued match such as
    /// `def T.eval : T → Type | T.t => Int` is the witness: its motive returns
    /// `Type`, so the recursor must be instantiated at motive universe `2`.
    pub(in crate::infer) fn motive_universe_level(
        &mut self,
        branch_ty: &Expr,
    ) -> Result<Level, ElabError> {
        self.infer_sort(branch_ty)
    }

    /// Build the universe level list for `T.casesOn` / `T.rec`.
    ///
    /// Looks up the actual `RecursorVal` from the environment to determine the
    /// correct number and order of universe parameters (#422). The recursor's
    /// `level_params` is authoritative:
    /// - For non-Prop-only inductives: `[motive_univ, ...ind_level_params]`
    /// - For Prop-only inductives: `[...ind_level_params]` (no motive universe)
    ///
    /// Imported `casesOn` definitions need not have a `RecursorVal` under their
    /// own name, but their constant declaration is still mandatory and its
    /// level-parameter packet is authoritative. Missing or inconsistent
    /// metadata is a typed error; universe levels are never guessed.
    pub(in crate::infer) fn eliminator_levels(
        &mut self,
        elim_name: &Name,
        scrutinee_ty: &Expr,
        branch_ty: &Expr,
    ) -> Result<Vec<Level>, ElabError> {
        let scrutinee_ty_inst = self.metas.instantiate(scrutinee_ty);
        let scrutinee_ty_inst = self.metas.instantiate_levels(&scrutinee_ty_inst);
        let scrutinee_ty_whnf = self.whnf(&scrutinee_ty_inst);

        let (scrutinee_ind_name, scrutinee_ind_levels) = match scrutinee_ty_whnf.get_app_fn().kind()
        {
            ExprKind::Const(name, levels) => (name.clone(), levels.to_vec()),
            _ => {
                return Err(ElabError::TypeMismatch {
                    expected: format!(
                        "registered inductive scrutinee for eliminator `{elim_name}`"
                    ),
                    actual: format!("{scrutinee_ty_whnf:?}"),
                });
            }
        };
        let ind_info = self.authenticate_inductive_metadata(&scrutinee_ind_name)?;
        let ind_level_count = ind_info.level_params.len();
        if scrutinee_ind_levels.len() != ind_level_count {
            return Err(ElabError::InternalInvariant(format!(
                "scrutinee `{scrutinee_ind_name}` supplies {} universe levels, inductive metadata requires {ind_level_count}",
                scrutinee_ind_levels.len()
            )));
        }

        // Look up the recursor to determine its exact level_params.
        if let Some(rec_val) = self.env.get_recursor(elim_name).cloned() {
            self.authenticate_recursor_cached(elim_name)?;
            if rec_val.name != *elim_name || rec_val.inductive_name != scrutinee_ind_name {
                return Err(ElabError::InternalInvariant(format!(
                    "recursor metadata `{elim_name}` identifies inductive `{}` instead of scrutinee `{scrutinee_ind_name}`",
                    rec_val.inductive_name
                )));
            }
            let rec_level_count = rec_val.level_params.len();
            if rec_level_count != ind_level_count && rec_level_count != ind_level_count + 1 {
                return Err(ElabError::InternalInvariant(format!(
                    "recursor metadata `{elim_name}` declares {rec_level_count} universe parameters for inductive `{scrutinee_ind_name}` with {ind_level_count}"
                )));
            }
            let has_motive_univ = rec_level_count == ind_level_count + 1;
            let mut levels = Vec::with_capacity(rec_level_count);
            if has_motive_univ {
                levels.push(self.motive_universe_level(branch_ty)?);
            }
            levels.extend(scrutinee_ind_levels);
            return Ok(levels);
        }

        // Fallback: recursor not in env. This is the IMPORT path — a real Lean
        // `.olean` ships `T.casesOn` / `T.recOn` as a plain *definitional
        // constant* (not a registered recursor), so `get_recursor` returned
        // `None`. The eliminator constant itself is still present, and its
        // declared `level_params` is authoritative for the universe arity we
        // must emit.
        //
        // Crucially, whether the eliminator carries a *motive universe*
        // parameter depends on large-elimination eligibility, exactly as in the
        // recursor-present branch: a Prop-valued inductive that only eliminates
        // into `Prop` (e.g. `Or`, with two constructors) has an eliminator whose
        // `level_params` is just the inductive's — NO extra motive universe. A
        // type-valued or subsingleton-eligible Prop inductive (e.g. `And`, `Eq`,
        // `Acc`, single ctor / all-Prop fields) carries the extra motive
        // universe. Unconditionally prepending a motive level (the historical
        // heuristic) over-counts the levels for an imported Prop-only eliminator
        // — `Or.casesOn.{u}` against a constant declaring zero level params —
        // which the kernel rejects with a level-count mismatch. We therefore
        // gate the motive level on the eliminator constant's declared arity
        // relative to the inductive's own level params.
        let elim_const = self.env.get_const(elim_name).ok_or_else(|| {
            ElabError::InternalInvariant(format!(
                "missing imported eliminator constant `{elim_name}`"
            ))
        })?;
        let elim_level_count = elim_const.level_params.len();
        if elim_level_count != ind_level_count && elim_level_count != ind_level_count + 1 {
            return Err(ElabError::InternalInvariant(format!(
                "imported eliminator `{elim_name}` declares {elim_level_count} universe parameters for inductive `{scrutinee_ind_name}` with {ind_level_count}"
            )));
        }
        let has_motive_univ = elim_level_count == ind_level_count + 1;

        let mut levels = Vec::with_capacity(elim_level_count);
        if has_motive_univ {
            levels.push(self.motive_universe_level(branch_ty)?);
        }
        levels.extend(scrutinee_ind_levels);
        Ok(levels)
    }

    /// Apply the inductive parameters to a recursor/casesOn constant.
    ///
    /// Eliminators take the inductive parameters before the motive.
    pub(in crate::infer) fn apply_eliminator_params(
        &self,
        mut eliminator: Expr,
        scrutinee_ty: &Expr,
        type_name: &str,
    ) -> Result<Expr, ElabError> {
        let expected_name = Name::from_string(type_name);
        let num_params = self
            .authenticate_inductive_metadata(&expected_name)?
            .num_params;
        let (actual_name, params) =
            self.exact_eliminator_parameter_args(scrutinee_ty, num_params)?;
        if actual_name != expected_name {
            return Err(ElabError::TypeMismatch {
                expected: format!("fully applied inductive `{expected_name}`"),
                actual: format!("scrutinee headed by `{actual_name}`"),
            });
        }
        for arg in params {
            eliminator = Expr::app(eliminator, arg);
        }
        Ok(eliminator)
    }

    /// Apply exactly `num_params` leading type arguments of the scrutinee type
    /// as the eliminator's parameters.
    ///
    /// Unlike [`apply_eliminator_params`], the parameter count is supplied by the
    /// caller rather than read from the inductive. This matters for *index-
    /// promoting* eliminators (e.g. `Eq.casesOn`, whose recursor `num_params`=2
    /// promotes the first `Eq` index into a parameter even though the inductive
    /// `Eq` has `num_params`=1): the recursor's declared parameter count is the
    /// authoritative number of leading spine args to consume before the motive.
    pub(in crate::infer) fn apply_eliminator_params_count(
        &self,
        mut eliminator: Expr,
        scrutinee_ty: &Expr,
        num_params: u32,
    ) -> Result<Expr, ElabError> {
        let (_, params) = self.exact_eliminator_parameter_args(scrutinee_ty, num_params)?;
        for arg in params {
            eliminator = Expr::app(eliminator, arg);
        }
        Ok(eliminator)
    }

    /// Recover an exact, fully-applied inductive spine before consuming its
    /// leading eliminator parameters.  `extract_type_args` intentionally
    /// truncates and is useful for optional shape probes; it is not an
    /// authority boundary.  Mandatory eliminator construction must reject a
    /// partial/over-applied type rather than silently applying fewer parameters
    /// and leaving the kernel to diagnose a remote malformed application.
    fn exact_eliminator_parameter_args(
        &self,
        scrutinee_ty: &Expr,
        num_params: u32,
    ) -> Result<(Name, Vec<Expr>), ElabError> {
        let scrutinee_ty = self.whnf(scrutinee_ty);
        let mut args = Vec::new();
        let mut head = &scrutinee_ty;
        while let ExprKind::App(function, argument) = head.kind() {
            args.push(argument.as_ref().clone());
            head = function;
        }
        args.reverse();

        let ExprKind::Const(ind_name, _) = head.kind() else {
            return Err(ElabError::TypeMismatch {
                expected: "fully applied registered inductive scrutinee".to_string(),
                actual: format!("{scrutinee_ty:?}"),
            });
        };
        let ind_info = self.authenticate_inductive_metadata(ind_name)?;
        let total_args = ind_info.num_params as usize + ind_info.num_indices as usize;
        if args.len() != total_args {
            return Err(ElabError::InternalInvariant(format!(
                "eliminator scrutinee `{ind_name}` supplies {} type arguments, inductive metadata requires {total_args}",
                args.len()
            )));
        }
        if num_params as usize > args.len() {
            return Err(ElabError::InternalInvariant(format!(
                "eliminator requests {num_params} parameters from `{ind_name}`, whose fully applied scrutinee has {} arguments",
                args.len()
            )));
        }
        args.truncate(num_params as usize);
        Ok((ind_name.clone(), args))
    }

    /// Try to construct a default value of a type by finding a nullary constructor (#3420).
    ///
    /// For common types like `Bool`, `Nat`, `Unit`, etc., this finds their
    /// zero-argument constructor (e.g., `Bool.false`, `Nat.zero`). Returns
    /// `None` if the type is not an inductive or has no nullary constructors.
    ///
    /// Used by the nested inductive match elaborator to avoid introducing sorry
    /// axioms in auxiliary minor premises that are structurally required but
    /// never evaluated at runtime.
    pub(in crate::infer) fn try_default_value_of_type(
        &self,
        ty: &Expr,
    ) -> Result<Option<Expr>, ElabError> {
        let Ok(type_name) = self.get_type_name(ty) else {
            return Ok(None);
        };
        let ind_name = Name::from_string(&type_name);
        if self.env.get_inductive(&ind_name).is_none() {
            return Ok(None);
        }
        let ind_info = self.authenticate_inductive_metadata(&ind_name)?;

        // Authenticate the complete constructor roster before selecting a
        // default. Returning as soon as the first nullary constructor is seen
        // would let corruption in a later constructor hide behind declaration
        // order and make the same inductive packet alternately trusted or
        // rejected depending on which helper happened to inspect it first.
        let mut default_ctor = None;
        for ctor_name in &ind_info.constructor_names {
            let (ctor_info, authenticated_parent) =
                self.authenticate_constructor_metadata(ctor_name)?;
            if authenticated_parent.name != ind_name {
                return Err(ElabError::InternalInvariant(format!(
                    "inductive metadata `{ind_name}` references constructor `{ctor_name}` of `{}`",
                    authenticated_parent.name
                )));
            }
            if ctor_info.num_fields == 0 && default_ctor.is_none() {
                default_ctor = Some(ctor_name.clone());
            }
        }

        match default_ctor {
            Some(ctor_name) => self.build_ctor_value(&ctor_name, ty, &[]).map(Some),
            None => Ok(None),
        }
    }

    /// Check if a match scrutinee is the decreasing argument of a recursive definition (#381)
    ///
    /// Returns true if:
    /// 1. We're in a recursive definition context (`recursive_def_ctx` is Some)
    /// 2. The scrutinee is an identifier matching the decreasing argument name
    ///
    /// When true, the match should use `T.rec` instead of `T.casesOn` to provide
    /// the inductive hypothesis for recursive calls.
    pub(in crate::infer) fn is_match_on_decreasing_arg(&self, scrutinee: &SurfaceExpr) -> bool {
        stack_safe(|| {
            if let Some(ref ctx) = self.recursive_def_ctx {
                // Check if scrutinee is an identifier matching the decreasing arg
                if let SurfaceExpr::Ident(_, name) = scrutinee {
                    return name == &ctx.decreasing_arg_name;
                }
                // Handle wrapper expressions that don't change identity
                match scrutinee {
                    SurfaceExpr::Paren(_, inner) => return self.is_match_on_decreasing_arg(inner),
                    SurfaceExpr::Ascription(_, inner, _) => {
                        return self.is_match_on_decreasing_arg(inner)
                    }
                    SurfaceExpr::Explicit(_, inner) => {
                        return self.is_match_on_decreasing_arg(inner)
                    }
                    _ => {}
                }
            }
            false
        })
    }
}
