// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Inductive type construction — main entry point.
//!
//! `add_inductive` validates and registers an inductive type declaration,
//! then delegates recursor and noConfusion generation to sibling modules:
//! - `inductive_fixed_indices`: fixed-index computation and promotion
//! - `inductive_recursor`: `.rec`, `.casesOn`, `.recOn` generation
//! - `inductive_no_confusion`: `.noConfusionType`, `.noConfusion` generation

use crate::expr::{Expr, ExprKind};
use crate::inductive::{
    check_positivity, count_pi_args, get_return_type, is_recursive, is_reflexive, mentions_name,
    validate_inductive, validate_inductive_strict, ConstructorVal, InductiveDecl, InductiveError,
    InductiveVal,
};
use crate::level::Level;
use crate::name::Name;

use super::decl_add::find_undef_level_param;
use super::inductive_fixed_indices::{fixed_indices_to_params, CtorInfo};
use super::types::{ConstantInfo, EnvError};
use super::Environment;

/// Select the auxiliary declarations generated alongside the family's
/// types, constructors, principal recursors and their iota rules.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum GeneratedAuxDefs {
    /// Default: generate everything (Clean-native environments).
    Generate,
    /// Ordinary source elaboration can produce the pinned constructor helpers.
    Source,
    /// Rebuild the auxiliary eliminators for reference comparison.
    Eliminators,
    /// Kernel certificate only — replay/import lanes carry the SOURCE
    /// spellings of the aux definitions instead (see `add_inductive_core`).
    Skip,
}

impl Environment {
    /// Add an inductive type declaration to the environment
    ///
    /// This validates the declaration, then adds:
    /// - The inductive type(s) as constants
    /// - All constructors as constants
    /// - The recursor(s) as constants
    ///
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn add_inductive(&mut self, decl: InductiveDecl) -> Result<(), EnvError> {
        self.add_inductive_impl(decl, GeneratedAuxDefs::Generate)
    }

    /// Admit an ordinary source family and its constructor auxiliaries.
    /// The checked source ordinal and supported specialized constructor
    /// definitions are built in the same transaction as their family.
    ///
    /// # Errors
    /// Same error surface as [`Self::add_inductive`].
    pub fn add_source_inductive(&mut self, decl: InductiveDecl) -> Result<(), EnvError> {
        self.add_inductive_impl(decl, GeneratedAuxDefs::Source)
    }

    /// [`Self::add_inductive`] restricted to the family's KERNEL CERTIFICATE:
    /// types, constructors, `rec`, and any nested `rec_N` companions with
    /// their iota rules. Imported auxiliary eliminators (`casesOn`, `recOn`)
    /// and convenience definitions come from the source.
    ///
    /// Why this exists (kernel-parity sweep, 2026-06-12): when a family is
    /// replayed from an imported Lean environment, Clean's generated
    /// convenience definitions silently SHADOW the source's own spellings —
    /// and they are not Lean-faithful (Lean 4.30 generates the heterogeneous
    /// `noConfusionType` with per-side parameter copies and `HEq` equality
    /// chains; Clean generates the classic homogeneous `Eq` form), so every
    /// imported proof elaborated against Lean's spelling fails its re-check.
    /// With the aux definitions skipped, the importer/graduation lane carries
    /// the SOURCE definitions through the ordinary checked `add_decl` path —
    /// Lean-faithful bytes, kernel-re-earned.
    ///
    /// # Errors
    ///
    /// Same error surface as [`Self::add_inductive`].
    pub fn add_inductive_core(&mut self, decl: InductiveDecl) -> Result<(), EnvError> {
        self.add_inductive_impl(decl, GeneratedAuxDefs::Skip)
    }

    /// Checked inductive admission on an environment that is discarded on
    /// failure, so without the transaction snapshot: `self` is consumed, and
    /// on `Err` whatever prefix of the admission ran is dropped with it,
    /// unread. The auxiliary policy selects the entries the kernel regenerates.
    ///
    /// For a scratch copy that exists only to be admitted into
    /// ([`Self::lean_replay_admit_block`]): there the snapshot was a second
    /// copy of the whole environment per replayed block, plus its drop on
    /// success, and nothing ever read it. Measured 2026-09-30 on Mathlib
    /// `Order/Basic`'s import header, the import re-admits every nested
    /// family that way, and the copies and drops were ~9% of the import.
    pub(super) fn into_scratch_with_inductive(
        mut self,
        decl: InductiveDecl,
        aux_defs: GeneratedAuxDefs,
    ) -> Result<Self, EnvError> {
        self.add_inductive_impl_inner(decl, aux_defs)?;
        Ok(self)
    }

    fn add_inductive_impl(
        &mut self,
        decl: InductiveDecl,
        aux_defs: GeneratedAuxDefs,
    ) -> Result<(), EnvError> {
        // Inductive admission mutates several coupled tables (constants,
        // verification provenance, inductives, constructors, recursors, and
        // generated auxiliary declarations).  No error may expose a prefix of
        // that mutation sequence: callers commonly recover from a rejected
        // declaration and continue using the same environment.
        //
        // Keep the transaction boundary here, shared by both the full and
        // kernel-certificate entry points.  The inner routine is free to stage
        // provisional declarations needed for mutual/nested checking; on any
        // failure the exact pre-call environment is restored, including its
        // generation counter and auxiliary registries.
        let snapshot = self.clone();
        match self.add_inductive_impl_inner(decl, aux_defs) {
            Ok(()) => Ok(()),
            Err(error) => {
                *self = snapshot;
                Err(error)
            }
        }
    }

    /// Families and constructors share a constant namespace, including names
    /// introduced together in one mutual block. Check it before provisional
    /// type-checking can overwrite a family with one of its constructors.
    fn check_inductive_name_disjointness(decl: &InductiveDecl) -> Result<(), EnvError> {
        let mut names = hashbrown::HashSet::new();
        for family in &decl.types {
            if !names.insert(&family.name) {
                return Err(EnvError::DuplicateName(family.name.clone()));
            }
        }
        for family in &decl.types {
            for constructor in &family.constructors {
                if !names.insert(&constructor.name) {
                    return Err(EnvError::DuplicateName(constructor.name.clone()));
                }
            }
        }
        Ok(())
    }

    fn add_inductive_impl_inner(
        &mut self,
        mut decl: InductiveDecl,
        aux_defs: GeneratedAuxDefs,
    ) -> Result<(), EnvError> {
        // This is intra-block uniqueness, not old-environment freshness: a
        // genuinely identical re-registration below remains an allowed no-op.
        Self::check_inductive_name_disjointness(&decl)?;
        // Parameterized container-nested inductives are handled by the
        // Lean-parity elimination + restore pipeline below (design
        // 2026-07-02-parameterized-nested-inductives.md; the former
        // reject-all guard at this spot was removed in brick B5). The
        // surviving rejections are Lean's own — NestedParamsContainLocals at
        // collect time, plus post-transform block-agreement and strict
        // field-occurrence validation — and the design's flagged divergence
        // (dependent-parameter containers, §7) rejects at post-transform
        // positivity rather than being unfolded.
        // Validate the inductive declaration (positivity, return types)
        validate_inductive(&decl).map_err(EnvError::Inductive)?;

        // F1: Nested positivity check (#2156).
        // When a constructor argument involves an existing inductive type applied
        // to the type being defined (e.g., Container Bad → Bad), verify that the
        // type being defined appears strictly positively within the container's
        // constructors. Without this, types like:
        //   inductive Container (A : Type) | mk : (A → Nat) → Container A
        //   inductive Bad | mk : Container Bad → Bad
        // would be accepted despite Bad appearing negatively inside Container.mk.
        let nested_types = self.check_nested_positivity(&decl)?;

        // [R12] Idempotent re-registration, evaluated on the USER's
        // declaration BEFORE elimination: post-restore the environment stores
        // exactly the user's spelling (round-trip law), and the aux mirrors
        // are erased — so an identical re-add of a nested family must be
        // recognized here, not after the transform. Require complete ordered
        // family/constructor payload agreement, modulo fixed-index promotion
        // for non-nested blocks. Name membership alone does not validate the
        // supplied declaration. Later duplicate checks still protect names
        // introduced by elimination.
        if self.check_inductive_reregistration(&decl)? {
            return Ok(());
        }

        // [R13] Clone the user's constructor types before elimination
        // overwrites `decl` — the restore pass hard-checks round-trip
        // identity against these.
        let pre_elim_ctor_types: Vec<(Name, Expr)> = decl
            .types
            .iter()
            .flat_map(|t| {
                t.constructors
                    .iter()
                    .map(|c| (c.name.clone(), c.type_.clone()))
            })
            .collect();

        // Nested inductive elimination (#3239).
        // When a constructor uses a container inductive applied to a type being
        // defined (e.g., Tree.node : List Tree → Tree), transform the declaration
        // into a mutual inductive with auxiliary types that mirror the containers.
        // This must happen before structural validation so the auxiliary types
        // are included in all subsequent checks.
        // Reference: Lean 4 `elim_nested_inductive_fn` (inductive.cpp:882-1077).
        let mut nested_aux_entries = Vec::new();
        if let Some((transformed, entries)) = self
            .eliminate_nested_inductives(&decl, &nested_types)
            .map_err(EnvError::Inductive)?
        {
            decl = transformed;
            nested_aux_entries = entries;
            // Elimination adds auxiliary families and constructors. They must
            // satisfy the same namespace invariant before provisional entries
            // are installed for the transformed block's type-checking.
            Self::check_inductive_name_disjointness(&decl)?;
        }
        let n_orig = decl.types.len() - nested_aux_entries.len();

        // F3: Structural validation — matches add_decl's Phase 1 checks (#2156).
        // Check duplicate level params, metavariables, free variables, and
        // undefined level parameter references in all type expressions.
        Self::check_inductive_structural(&decl)?;

        // Promote fixed indices to parameters (Lean 4's fixedIndicesToParams).
        // This must run before any derived property computation so that
        // num_indices, num_fields, and recursor generation all use the
        // correct parameter/index boundary.
        //
        // Skipped when nested elimination fired (design §1.4): Lean has no
        // in-kernel promotion, and a post-elimination `num_params` bump would
        // desynchronize the aux telescopes (built with the original `p`) and
        // contradict the shard's `num_params` on replay.
        if nested_aux_entries.is_empty() {
            let new_num_params = fixed_indices_to_params(&decl);
            if new_num_params > decl.num_params {
                decl.num_params = new_num_params;
            }
        }

        // [R2] Block-agreement hard checks on the (possibly transformed)
        // block: exact shared-parameter telescopes across members and ctor
        // prefixes, and mutual same-universe agreement — Lean
        // inductive.cpp:225-231, :249-251, :284-287. Clean historically had
        // NEITHER check; nested elimination mass-produces multi-member blocks
        // and relies on both (INV-TEL(i), design
        // 2026-07-02-parameterized-nested-inductives.md §1.4/§5). Runs AFTER
        // fixed-index promotion, which can raise `num_params`.
        let result_levels = self.check_block_agreement(&decl)?;

        // [R8] Strict field-occurrence validation on the final block: every
        // embedded block occurrence must be a valid inductive application
        // (exact param spine, exact arity, exact head levels, block-free
        // indices — Lean is_valid_ind_app). Post-transform (container
        // occurrences already eliminated) and post-promotion (param/index
        // boundary final); applies to EVERY inductive, closing the
        // pre-existing non-uniform-occurrence hole from which the recursor
        // generator emitted ill-typed IHs (design §5.3).
        validate_inductive_strict(&decl).map_err(EnvError::Inductive)?;

        // Check for duplicate names
        for ind_type in &decl.types {
            if self.constants.contains_key(&ind_type.name)
                || self.inductives.contains_key(&ind_type.name)
            {
                return Err(EnvError::DuplicateName(ind_type.name.clone()));
            }
            for ctor in &ind_type.constructors {
                if self.constants.contains_key(&ctor.name)
                    || self.constructors.contains_key(&ctor.name)
                {
                    return Err(EnvError::DuplicateName(ctor.name.clone()));
                }
            }
        }

        // F3 + F2: Type-check inductive types and constructors (#2156).
        // Temporarily registers inductive types as constants so the TypeChecker
        // can resolve self-references in constructor types. On failure, rolls back.
        self.check_inductive_well_typed(&decl, &result_levels)?;

        // Collect all inductive names up front (for mutual block checks)
        let all_ind_names: Vec<Name> = decl.types.iter().map(|t| t.name.clone()).collect();

        // Lean computes `isRec` and `isReflexive` ONCE for the whole block —
        // over every constructor of every type, a nested block's auxiliary
        // types included — and stores the same value on every type
        // (`inductive.cpp` `declare_inductive_types`, v4.30.0-rc2). Read per
        // type, the non-recursive member of a recursive mutual block was
        // non-recursive here, so the kernel gave it the structure and
        // unit-like eta Lean's `is_non_rec_structure` refuses
        // (`replay_forged/ReplayForgedMutualEta`), and the `.olean` replay
        // could not compare a stored flag with the regenerated one.
        let block_recursive = decl
            .types
            .iter()
            .any(|t| is_recursive(&all_ind_names, &t.constructors));
        let block_reflexive = decl
            .types
            .iter()
            .any(|t| is_reflexive(&all_ind_names, &t.constructors));

        // Recursors are inserted provisionally and earn FullKernelCheck only
        // after every mutual sibling exists, their current values type-check,
        // and their constant/metadata tables agree in release mode.
        let mut generated_recursor_names = Vec::new();

        // Process each inductive type. Aux mirrors (indices >= n_orig) get
        // ONLY their kernel certificate (type + ctors + InductiveVal + rec);
        // casesOn/recOn generation is gated to originals ([R11]) — the
        // restore pass erases every aux registration afterward, so nothing
        // else may exist for them.
        for (member_idx, (ind_type, result_level)) in
            decl.types.iter().zip(&result_levels).enumerate()
        {
            let is_aux_member = member_idx >= n_orig;
            // Calculate derived properties
            let type_arity = count_pi_args(&ind_type.type_);
            let num_indices = type_arity.saturating_sub(decl.num_params);

            let all_names = all_ind_names.clone();
            let ctor_names: Vec<Name> = ind_type
                .constructors
                .iter()
                .map(|c| c.name.clone())
                .collect();

            // Add the inductive type as a constant FIRST, so the TypeChecker
            // can resolve self-references when computing large_elim below.
            let ind_const = ConstantInfo::new(
                ind_type.name.clone(),
                decl.level_params.clone(),
                ind_type.type_.clone(),
                None, // Inductive types have no value
                false,
            );
            self.install_resident_constant(ind_type.name.clone(), ind_const);
            self.declaration_verification.insert(
                ind_type.name.clone(),
                super::DeclarationVerification::FullKernelCheck,
            );

            // Add constructors (before large_elim so TypeChecker sees them)
            for (idx, ctor) in ind_type.constructors.iter().enumerate() {
                let ctor_arity = count_pi_args(&ctor.type_);
                let num_fields = ctor_arity.saturating_sub(decl.num_params);

                let ctor_val = ConstructorVal {
                    name: ctor.name.clone(),
                    inductive_name: ind_type.name.clone(),
                    level_params: decl.level_params.clone(),
                    type_: ctor.type_.clone(),
                    num_params: decl.num_params,
                    num_fields,
                    constructor_idx: Self::usize_to_u32(idx),
                };

                // Add constructor as constant
                let ctor_const = ConstantInfo::new(
                    ctor.name.clone(),
                    decl.level_params.clone(),
                    ctor.type_.clone(),
                    None, // Constructors have no value
                    false,
                );
                self.install_resident_constant(ctor.name.clone(), ctor_const);
                self.declaration_verification.insert(
                    ctor.name.clone(),
                    super::DeclarationVerification::FullKernelCheck,
                );
                self.constructors.insert(ctor.name.clone(), ctor_val);
            }

            // Compute large_elim AFTER type and constructors are registered,
            // so the TypeChecker can resolve self-references in constructor
            // field types (e.g., Acc.intro's `h : ∀ y, r y x → Acc r y`).
            // Decided on the block's result level up to whnf, never the
            // syntactic codomain (Lean `m_is_not_zero`).
            let large_elim = !super::elim_analysis::elim_only_at_universe_zero(
                self,
                self.zero_reading(),
                result_level,
                &ind_type.constructors,
                decl.num_params,
                decl.types.len(),
            );

            // Create and register InductiveVal
            let ind_val = InductiveVal {
                name: ind_type.name.clone(),
                level_params: decl.level_params.clone(),
                type_: ind_type.type_.clone(),
                num_params: decl.num_params,
                num_indices,
                all_names,
                constructor_names: ctor_names,
                is_recursive: block_recursive,
                is_reflexive: block_reflexive,
                is_large_elim: large_elim,
                // Set true when a constructor uses a container inductive applied
                // to this type (detected by check_nested_positivity, #2156 F1).
                is_nested: nested_types.contains(&ind_type.name),
            };
            self.inductives.insert(ind_type.name.clone(), ind_val);

            // Precompute constructor field info once, shared by rec/casesOn/recOn
            let ctor_infos = self.compute_ctor_infos(ind_type, &decl);

            // For mutual inductives, collect ctor_infos from ALL types.
            // Lean 4's declare_recursors() collects motives (Cs) for all types
            // and minor premises from all constructors across all types.
            // Reference: lean4/src/kernel/inductive.cpp:752-776
            let all_ctor_infos: Vec<CtorInfo> = decl
                .types
                .iter()
                .flat_map(|t| self.compute_ctor_infos(t, &decl))
                .collect();

            // Compute the minor index offset for this type within the mutual block.
            // Even's constructors start at minor 0, Odd's start at Even's ctor count, etc.
            let minor_idx_offset: usize = decl
                .types
                .iter()
                .take_while(|t| t.name != ind_type.name)
                .map(|t| t.constructors.len())
                .sum();

            // Generate and add recursor.
            //
            // Propositional truncation `∥A∥` (the second known-sound HIT) uses a
            // bespoke prop-restricted recursor `{A}{P} → isProp P → (A→P) → ∥A∥ A
            // → P`; the generic one-minor-per-constructor schema cannot express
            // the `squash`-via-`isProp` premise. For that exact shape we build
            // the recursor directly and skip the structural `casesOn` / `recOn` /
            // `below` (constructor injectivity and structural recursion are not
            // valid through a path constructor — SOUNDNESS-CRITICAL).
            //
            // Suspension `Susp A` (the third known-sound HIT) uses a bespoke
            // dependent recursor `{A}{C} → C(north A) → C(south A) → ((a:A) →
            // PathP (λ i. C (merid A a @ i)) cn cs) → (x:Susp A) → C x`; the
            // generic schema's path-minor builder is tuned for S¹'s field-less
            // `loop` and cannot express the `merid` path *family* (a field `a:A`
            // plus point-constructor endpoints applied to the parameter). For
            // that exact shape we build the recursor directly and likewise skip
            // the structural `casesOn` / `recOn` / `below` (SOUNDNESS-CRITICAL).
            let is_trunc_hit = crate::inductive::is_prop_truncation_shape(&decl);
            let is_susp_hit = crate::inductive::is_suspension_shape(&decl);
            let rec_name = ind_type.name.clone().str("rec");
            if self.constants.contains_key(&rec_name) || self.recursors.contains_key(&rec_name) {
                return Err(EnvError::DuplicateName(rec_name));
            }
            let rec_val = if is_trunc_hit {
                self.build_truncation_recursor(ind_type, &decl)?
            } else if is_susp_hit {
                self.build_suspension_recursor(ind_type, &decl)?
            } else {
                self.build_recursor(
                    &ind_type.name,
                    &decl,
                    result_level,
                    &ctor_infos,
                    &all_ctor_infos,
                    minor_idx_offset,
                    self.zero_reading(),
                )?
            };

            // Add recursor as constant
            let rec_const = ConstantInfo::new(
                rec_name.clone(),
                rec_val.level_params.clone(),
                rec_val.type_.clone(),
                None, // Recursors don't have a value (they compute via rules)
                false,
            );
            self.install_resident_constant(rec_name.clone(), rec_const);
            self.declaration_verification.insert(
                rec_name.clone(),
                super::DeclarationVerification::StructuralOnly,
            );
            // Retained for the aux-eliminator value builders below (the maps
            // take ownership of rec_val).
            let rec_ty_for_aux = rec_val.type_.clone();
            let rec_levels_for_aux = rec_val.level_params.clone();
            self.recursors.insert(rec_name.clone(), rec_val);
            generated_recursor_names.push(rec_name.clone());

            // Higher Inductive Type (any constructor returning a `CubicalPath`):
            // only the dependent `rec` is generated — NO structural `casesOn` /
            // `recOn`. This is uniform across all three HITs:
            //
            //   * `∥A∥` / `Susp A` use a *bespoke* `rec` (above); the generic
            //     casesOn/recOn schema cannot even express their minors (the
            //     `isProp`-squash premise; the `merid` path *family*), so a
            //     generated structural eliminator would be ill-typed.
            //
            //   * `S¹` uses the *generic* `rec` (its field-less `loop` path-minor
            //     IS expressible). The generic schema would happily also emit a
            //     structural `S¹.casesOn` / `S¹.recOn`, and those are in fact the
            //     same path-respecting eliminator as `rec` (just a different
            //     argument order) — but they are UNUSED (every S¹ elimination
            //     goes through `rec`) and untested as a trusted recursor. Rather
            //     than ship two more untested members of the kernel TCB, and to
            //     keep the rule uniform — *no* HIT exposes structural
            //     casesOn/recOn through a path constructor — we skip them too.
            //
            // This mirrors the existing `noConfusion` / `below` / `brecOn` skips
            // (also gated on `has_path_constructor`): constructor injectivity and
            // structural recursion are not guarantees Clean ships for a path
            // constructor. SOUNDNESS-CONSERVATIVE.
            if is_trunc_hit || is_susp_hit || Self::has_path_constructor(ind_type) {
                continue;
            }

            // Generate and add casesOn (non-recursive eliminator).
            //
            // Skipped under `GeneratedAuxDefs::Skip` together with recOn:
            // in Lean these are value-bearing DEFINITIONS that delta-unfold
            // to `rec` (the kernel closes `casesOn … stuck-major ≡ rec …
            // stuck-major` by unfolding); Clean's recursor-table entries
            // have no value, so a replayed Lean proof that needs that
            // unfolding sticks. The replay lanes carry Lean's own
            // definitions instead (kernel-parity sweep, 2026-06-12 —
            // `List.zipWith.match_1.eq_2`).
            if aux_defs == GeneratedAuxDefs::Skip || is_aux_member {
                continue;
            }
            let cases_name = ind_type.name.clone().str("casesOn");
            if self.constants.contains_key(&cases_name) || self.recursors.contains_key(&cases_name)
            {
                return Err(EnvError::DuplicateName(cases_name));
            }
            let cases_val = self.build_cases_on(
                &ind_type.name,
                &decl,
                result_level,
                &ctor_infos,
                &all_ctor_infos,
                minor_idx_offset,
                self.zero_reading(),
            )?;

            // Definitional VALUE (residual-to-zero campaign, 2026-07-02): in
            // Lean, casesOn/recOn are value-bearing definitions delegating to
            // `rec`; the kernel closes `casesOn … stuck-major ≡ rec …
            // stuck-major` by delta unfolding. Clean's value-less entries left
            // variable-scrutinee eliminators permanently stuck (iota needs a
            // constructor head), rejecting Lean-elaborated equation lemmas
            // (`List.tail.eq_1`, `*.match_1.eq_N`, `filter_singleton`, …).
            // The value is the telescope-reordering wrapper over `rec`; the
            // rule-table entry stays as the constructor-head fast path. See
            // `inductive_aux_values.rs` for the soundness note.
            debug_assert_eq!(
                cases_val.level_params, rec_levels_for_aux,
                "casesOn and rec must derive identical level-param lists"
            );
            let cases_minor_arities: Vec<(u32, u32)> = all_ctor_infos
                .iter()
                .map(|(_, num_fields, flags, _, _)| {
                    (
                        *num_fields,
                        Self::usize_to_u32(flags.iter().filter(|f| **f).count()),
                    )
                })
                .collect();
            let cases_value = self.build_aux_eliminator_value(
                &cases_name,
                &rec_name,
                &cases_val.level_params,
                &cases_val.type_,
                &rec_ty_for_aux,
                cases_val.num_params,
                cases_val.num_motives,
                cases_val.num_indices,
                cases_val.num_minors as usize,
                Some(&cases_minor_arities),
            )?;
            // Lean stores casesOn as an abbreviation. Its iota rules remain
            // the constructor-head fast path.
            let cases_const = ConstantInfo::new(
                cases_name.clone(),
                cases_val.level_params.clone(),
                cases_val.type_.clone(),
                Some(cases_value),
                true,
            );
            self.install_resident_constant(cases_name.clone(), cases_const);
            self.declaration_verification.insert(
                cases_name.clone(),
                super::DeclarationVerification::StructuralOnly,
            );
            self.recursors.insert(cases_name.clone(), cases_val);
            generated_recursor_names.push(cases_name);

            // Generate and add recOn (recursor with major premise first)
            let rec_on_name = ind_type.name.clone().str("recOn");
            if self.constants.contains_key(&rec_on_name)
                || self.recursors.contains_key(&rec_on_name)
            {
                return Err(EnvError::DuplicateName(rec_on_name));
            }
            let rec_on_val = self.build_rec_on(
                &ind_type.name,
                &decl,
                result_level,
                &ctor_infos,
                &all_ctor_infos,
                minor_idx_offset,
                &rec_ty_for_aux,
                self.zero_reading(),
            )?;

            // recOn value: same reordering wrapper; minors pass through
            // verbatim (identical premise types to rec's).
            debug_assert_eq!(
                rec_on_val.level_params, rec_levels_for_aux,
                "recOn and rec must derive identical level-param lists"
            );
            let rec_on_value = self.build_aux_eliminator_value(
                &rec_on_name,
                &rec_name,
                &rec_on_val.level_params,
                &rec_on_val.type_,
                &rec_ty_for_aux,
                rec_on_val.num_params,
                rec_on_val.num_motives,
                rec_on_val.num_indices,
                rec_on_val.num_minors as usize,
                None,
            )?;
            // Lean stores recOn as a value-bearing abbreviation too.
            let rec_on_const = ConstantInfo::new(
                rec_on_name.clone(),
                rec_on_val.level_params.clone(),
                rec_on_val.type_.clone(),
                Some(rec_on_value),
                true,
            );
            self.install_resident_constant(rec_on_name.clone(), rec_on_const);
            self.declaration_verification.insert(
                rec_on_name.clone(),
                super::DeclarationVerification::StructuralOnly,
            );
            self.recursors.insert(rec_on_name.clone(), rec_on_val);
            generated_recursor_names.push(rec_on_name);
        }

        // Mandatory authority gate (not debug-only): all mutual siblings now
        // exist, so validate the exact current type/value and the recursor
        // metadata consumed by iota/K reduction before upgrading provenance.
        for name in &generated_recursor_names {
            self.validate_and_stamp_recursor(name)?;
        }

        // RESTORE (design §4, brick B3): map the checked transformed block
        // back to Lean's post-restore artifact set — original ctor types in
        // container spelling (round-trip-checked), `<first>.rec_N` renamed
        // aux recursors in BOTH tables, every `_nested.*` registration
        // erased. Restore computes its rewrite before committing; any later
        // validation error is propagated to the outer family transaction,
        // which restores the exact pre-admission environment before returning.
        // Passes 2/3 below then generate from the RESTORED spellings.
        let restored_types = if nested_aux_entries.is_empty() {
            None
        } else {
            // The outer admission transaction restores the complete pre-family
            // environment if `?` propagates a post-compute restore failure.
            Some(self.restore_nested_block(
                &decl,
                &nested_aux_entries,
                &pre_elim_ctor_types,
                aux_defs != GeneratedAuxDefs::Skip,
            )?)
        };
        let effective_types: &[crate::inductive::InductiveType] = match &restored_types {
            Some(types) => types,
            None => &decl.types,
        };
        // Sugar passes consume a decl whose members/ctors match the
        // registered (restored) environment.
        let effective_decl = match &restored_types {
            Some(types) => InductiveDecl {
                level_params: decl.level_params.clone(),
                num_params: decl.num_params,
                types: types.clone(),
            },
            None => decl.clone(),
        };

        let ordinary_auxiliaries = matches!(
            aux_defs,
            GeneratedAuxDefs::Generate | GeneratedAuxDefs::Source
        );
        let source_auxiliaries = if aux_defs == GeneratedAuxDefs::Source {
            effective_types
                .first()
                .and_then(|family| self.checked_source_constructor_auxiliaries(&family.name))
        } else {
            None
        };
        let generate_no_confusion = source_auxiliaries.is_none() && ordinary_auxiliaries;
        if let Some(staged) = source_auxiliaries {
            *self = staged;
        } else if aux_defs == GeneratedAuxDefs::Source {
            for family in effective_types {
                if let Some(staged) = self.checked_source_constructor_index(&family.name) {
                    *self = staged;
                }
            }
        }

        // Pass 2: Build NoConfusion for families outside the source profile.
        // This is a separate pass to handle mutual inductives correctly — when
        // building Even.noConfusionType, Odd must already be in the environment.
        // The first pass above registers all types, constructors, and recursors
        // before any NoConfusion is built (#2044).
        //
        // Convention: `build_no_confusion_type`/`build_no_confusion` dispatch
        // on `num_params`. The classic scheme is retained for 0-param families
        // outside the source profile. Parameterized types use Lean v4.30's
        // heterogeneous scheme (P-first, primed second-major params, per-param
        // Eq/HEq premises + HEq major). See
        // designs/2026-07-03-noconfusion-ctoridx-convention.md.
        // noConfusion is a block-level construction. Reject the complete
        // mutual declaration if any member is Prop-valued, still indexed (the
        // current generator supports parameters only), or contains a path
        // constructor. The same predicate gates late regeneration, preventing
        // the repair path from reinterpreting a rejected block as a singleton.
        let generate_no_confusion =
            generate_no_confusion && self.no_confusion_block_eligibility(&effective_decl).is_ok();
        if generate_no_confusion {
            let prerequisites_ready = self
                .no_confusion_prerequisite_issue(&effective_decl)
                .is_none();
            // Build the complete block before editing the environment, then use
            // the same two-phase transaction as late regeneration: all
            // noConfusionType declarations are checked with every generated
            // pair name absent; only checked type definitions are provisionally
            // visible while noConfusion theorems are checked, and theorem names
            // remain absent throughout. Missing prerequisites simply leave the
            // complete pair absent for the later Eq/HEq retry.
            let candidates = effective_types
                .iter()
                .map(|ind_type| self.build_no_confusion_candidate(&ind_type.name, &effective_decl))
                .collect::<Result<Vec<_>, _>>();
            match candidates {
                Ok(candidates) => {
                    let occupied_target = effective_types.iter().find_map(|ind_type| {
                        ["noConfusionType", "noConfusion"]
                            .into_iter()
                            .map(|suffix| ind_type.name.clone().str(suffix))
                            .find(|name| self.get_const(name).is_some())
                    });
                    if let Some(occupied) = occupied_target {
                        // A restored nested family promises a complete canonical
                        // generated pair.  Treat a pre-existing target as an
                        // invariant failure and restore the entire pre-family
                        // environment; otherwise a bogus declaration can make
                        // registration appear successful while silently
                        // suppressing noConfusion generation.  Ordinary and
                        // bootstrap declarations retain the historical
                        // best-effort behavior.
                        if !nested_aux_entries.is_empty() {
                            return Err(EnvError::Inductive(
                                InductiveError::NestedRestoreInvariant(format!(
                                    "restored noConfusion target is already occupied: {occupied}"
                                )),
                            ));
                        }
                    } else {
                        // `add_inductive` performs the single generation bump for
                        // the whole operation below; the shared transaction must
                        // not add a second one here.
                        if let Err(issue) =
                            self.install_no_confusion_candidates_transactionally(&candidates, false)
                        {
                            if prerequisites_ready && !nested_aux_entries.is_empty() {
                                return Err(EnvError::Inductive(
                                    InductiveError::NestedRestoreInvariant(format!(
                                        "restored noConfusion installation failed: {issue:?}"
                                    )),
                                ));
                            }
                        }
                    }
                }
                Err(issue) => {
                    if prerequisites_ready && !nested_aux_entries.is_empty() {
                        return Err(EnvError::Inductive(InductiveError::NestedRestoreInvariant(
                            format!("restored noConfusion generation failed: {issue:?}"),
                        )));
                    }
                }
            }
        }

        // Pass 3: Build .below and .brecOn for recursive types (#1217).
        // These require the recursor to be registered and PUnit/PProd in
        // the environment. Like NoConfusion, failures are silently skipped.
        for ind_type in effective_types.iter().filter(|t| {
            // Skip Higher Inductive Types: `.below`/`.brecOn` encode structural
            // recursion, which is not valid through a path constructor.
            ordinary_auxiliaries && !Self::has_path_constructor(t)
        }) {
            let ctor_infos = self.compute_ctor_infos(ind_type, &effective_decl);
            self.generate_below_brec_on(ind_type, &effective_decl, &ctor_infos);
        }

        // Validate metadata consistency for all recursors ACTUALLY created (#1394).
        //
        // `rec` is generated under every policy; `casesOn`/`recOn` are generated
        // under both auxiliary-generation policies (the `Skip` lane leaves them to
        // be carried from the source through `add_decl`). Validating `casesOn`/
        // `recOn` unconditionally panicked under `Skip` (`add_inductive_core`),
        // because `validate_recursor_metadata` reports the deliberately-absent
        // recursor as an "unknown recursor". This is a debug-assertion-only guard
        // (`#[cfg(debug_assertions)]`, off in release) — it never affects which
        // members are installed or any soundness check; it only validates the
        // ones this call actually generated.
        #[cfg(debug_assertions)]
        {
            let generated_suffixes: &[&str] = match aux_defs {
                GeneratedAuxDefs::Generate
                | GeneratedAuxDefs::Source
                | GeneratedAuxDefs::Eliminators => &["rec", "casesOn", "recOn"],
                GeneratedAuxDefs::Skip => &["rec"],
            };
            // This suffix walk covers original family members. Renamed
            // container-major `rec_N` companions are not suffix-derived from
            // `effective_types`; restore validates and stamps them directly.
            for ind_type in effective_types {
                for suffix in generated_suffixes {
                    let rec_name = ind_type.name.clone().str(suffix);
                    // HITs generate only a bespoke `rec`; their `casesOn`/`recOn`
                    // are intentionally absent. Validate the recursors that exist.
                    if self.get_recursor(&rec_name).is_none() {
                        continue;
                    }
                    if let Err(msg) = self.validate_recursor_metadata(&rec_name) {
                        panic!(
                            "add_inductive metadata inconsistency for {}: {msg}",
                            rec_name
                        );
                    }
                }
            }
        }

        self.generation += 1;
        Ok(())
    }

    /// Structural validation for inductive declarations (#2156 F3).
    ///
    /// Performs the same Phase 1 checks as `add_decl`:
    /// - No duplicate universe level parameters
    /// - No metavariables (expression or level) in type expressions
    /// - No free variables (FVar) in type expressions
    /// - All Level::Param references are declared in `level_params`
    fn check_inductive_structural(decl: &InductiveDecl) -> Result<(), EnvError> {
        // Check for duplicate level params
        for (i, p) in decl.level_params.iter().enumerate() {
            if decl.level_params[..i].contains(p) {
                let name = decl
                    .types
                    .first()
                    .map_or_else(Name::anon, |t| t.name.clone());
                return Err(EnvError::DuplicateLevelParam {
                    name,
                    param: p.clone(),
                });
            }
        }

        // Check each inductive type and constructor expression
        for ind_type in &decl.types {
            Self::check_expr_well_formed(&ind_type.name, &ind_type.type_, &decl.level_params)?;
            for ctor in &ind_type.constructors {
                Self::check_expr_well_formed(&ctor.name, &ctor.type_, &decl.level_params)?;
            }
        }

        // Loose-bvar closedness (design §5.4): type formers and constructor
        // types are top-level declarations and must be closed. Metavariable
        // and free-variable checks above are blind to loose bvars, so an
        // arithmetic bug in a transformation pass (e.g. nested-inductive aux
        // construction) could otherwise smuggle an open term into the
        // registered environment.
        for ind_type in &decl.types {
            if ind_type.type_.loose_bvar_range() != 0 {
                return Err(EnvError::Inductive(InductiveError::InvalidType(format!(
                    "type former of {} contains loose bound variables",
                    ind_type.name
                ))));
            }
            for ctor in &ind_type.constructors {
                if ctor.type_.loose_bvar_range() != 0 {
                    return Err(EnvError::Inductive(InductiveError::InvalidType(format!(
                        "constructor {} contains loose bound variables",
                        ctor.name
                    ))));
                }
            }
        }

        Ok(())
    }

    /// Check a single expression for metavariables, free variables, and
    /// undefined level parameter references.
    fn check_expr_well_formed(
        name: &Name,
        expr: &Expr,
        level_params: &[Name],
    ) -> Result<(), EnvError> {
        if expr.has_expr_mvar_quick() || expr.has_level_mvar_quick() {
            return Err(EnvError::ContainsMetavar { name: name.clone() });
        }
        if expr.has_fvar_quick() {
            return Err(EnvError::ContainsFreeVar {
                name: name.clone(),
                fvars: super::types::collect_fvar_ids_for_diagnostics(&[expr]),
            });
        }
        if let Some(undef) = find_undef_level_param(expr, level_params) {
            return Err(EnvError::UndefinedLevelParam {
                name: name.clone(),
                param: undef,
            });
        }
        Ok(())
    }

    /// [R2] Block-agreement hard checks (Lean `check_inductive_types`,
    /// inductive.cpp:225-231 param agreement, :249-251 same-universe
    /// `is_equivalent`, :284-287 ctor param prefixes), run on the possibly
    /// nested-transformed block:
    ///
    /// 1. every member's type former carries at least `num_params` Pi
    ///    binders whose domains are STRUCTURALLY identical to the first
    ///    member's (the shared telescope — Lean compares with `is_def_eq`;
    ///    structural equality is strictly stricter, hence fail-closed, and
    ///    is what the recursor generator's INV-TEL(i) contract actually
    ///    consumes; every Lean-elaborated or aux-mirrored block is
    ///    byte-identical here);
    /// 2. every constructor likewise opens with the shared telescope;
    /// 3. all members' result sorts are equivalent levels: Lean's
    ///    `is_equivalent` under the Lean theories (`tc/level_profile.rs`,
    ///    `docs/DECISIONS.md` R150; `replay_forged/ReplayForgedMutualLevel`),
    ///    and `is_geq` both ways under `Extended`, which is semantic equality
    ///    and so admits blocks Lean refuses.
    ///
    /// Clean historically had NONE of these; inputs violating them fed the
    /// recursor generator outside its contract (design
    /// `2026-07-02-parameterized-nested-inductives.md` §1.4/§5).
    ///
    /// The result levels are found as Lean's loop finds them, up to whnf
    /// between binders (`Environment::member_result_level`), and returned in
    /// member order: they are the one source every later decision reads (the
    /// per-field universe bound, large elimination, K, noConfusion, below).
    /// Coq-sourced records legitimately have codomains that are sorts only up
    /// to reduction — `LetIn(T := …) in Sort u` (ζ, the HB `mixin_of`
    /// records) or `Const(c)` with `c` unfolding to a sort (δ, the
    /// `predArgType`-style carriers) — and so does
    /// `def MyProp : Type := Prop; inductive B : MyProp`, whose level is `0`.
    fn check_block_agreement(&self, decl: &InductiveDecl) -> Result<Vec<Level>, EnvError> {
        let p = decl.num_params as usize;
        let Some(first) = decl.types.first() else {
            return Ok(Vec::new());
        };

        // Reference telescope + result level from the first member.
        let mut reference: Vec<&Expr> = Vec::with_capacity(p);
        let mut cursor: &Expr = &first.type_;
        for _ in 0..p {
            match &cursor.kind {
                ExprKind::Pi(_, domain, body) => {
                    reference.push(domain);
                    cursor = body;
                }
                _ => return Err(EnvError::Inductive(InductiveError::InvalidParams)),
            }
        }
        let result_levels = self.block_result_levels(decl)?;
        let Some(first_level) = result_levels.first() else {
            return Ok(result_levels);
        };

        let check_prefix = |name: &Name, ty: &Expr| -> Result<(), EnvError> {
            let mut cursor = ty;
            for (idx, expected) in reference.iter().enumerate() {
                match &cursor.kind {
                    ExprKind::Pi(_, domain, body) => {
                        if domain.as_ref() != *expected {
                            return Err(EnvError::Inductive(InductiveError::InvalidType(format!(
                                "{name}: parameter {idx} disagrees with the block's \
                                     shared parameter telescope"
                            ))));
                        }
                        cursor = body;
                    }
                    _ => return Err(EnvError::Inductive(InductiveError::InvalidParams)),
                }
            }
            Ok(())
        };

        for (member, level) in decl.types.iter().zip(&result_levels) {
            check_prefix(&member.name, &member.type_)?;
            // Lean's `is_equivalent` under the Lean theories
            // (`tc/level_profile.rs`); `is_geq` both ways under `Extended`.
            let same_universe = match self.kernel_theory().level_construction() {
                crate::level::LevelConstruction::Clean => {
                    Level::is_geq(level, first_level) && Level::is_geq(first_level, level)
                }
                crate::level::LevelConstruction::LeanKernel => {
                    self.levels_equiv_in_theory(level, first_level)
                }
            };
            if !same_universe {
                return Err(EnvError::Inductive(InductiveError::InvalidType(format!(
                    "mutual member {} lives in a different universe than {} \
                     (Lean requires equivalent result levels across a block)",
                    member.name, first.name
                ))));
            }
            for ctor in &member.constructors {
                check_prefix(&ctor.name, &ctor.type_)?;
            }
        }
        Ok(result_levels)
    }

    /// Type-check inductive types and constructors using the TypeChecker (#2156 F3+F2).
    ///
    /// To type-check constructor types (which reference the inductive being defined),
    /// we temporarily register the inductive types as constants. This mirrors Lean 4's
    /// approach where the type checker has access to types being defined.
    ///
    /// Also performs universe constraint checking (#2156 F2): for non-Prop inductives,
    /// verifies that the constructor type's sort does not exceed the inductive type's
    /// sort, which ensures all constructor field sorts are within bounds.
    fn check_inductive_well_typed(
        &mut self,
        decl: &InductiveDecl,
        result_levels: &[Level],
    ) -> Result<(), EnvError> {
        // Step 1: Temporarily register all inductive types as constants.
        // The TypeChecker needs these to resolve Const references to the types
        // being defined (e.g., recursive references in constructor types).
        //
        // These inserts and the removals of step 3 move the count but not the
        // generation. That is sound for the caches keyed on
        // `(generation, num_constants)` only while no earlier state with a
        // warm cache held the key this window reaches, so nothing cached
        // before it is served inside it. `forget_decl` bumps when it lowers
        // the count. Two writers lower it without a bump, each safe for its
        // own reason: `forget_family_member` runs on a clone, whose native-fold
        // cache starts empty and is not queried before the removals, and it
        // removes more names (recursors, `casesOn`, `recOn`) than this window
        // re-adds; `restore_nested_block` erases aux names inside an admission
        // that only adds names, so the count never falls below its value
        // before that admission, which ends in a bump or in a restored
        // snapshot whose cache is empty. A native-fold verdict computed
        // inside this window that reads a provisional name refuses (each is
        // a value-less definition), so serving it later at the same key,
        // before the admission's own bump, can only withhold a fold. On
        // failure the admission restores a snapshot, whose caches start
        // empty, or drops its scratch copy.
        let mut temp_names: Vec<Name> = Vec::new();
        for ind_type in &decl.types {
            let ind_const = ConstantInfo::new(
                ind_type.name.clone(),
                decl.level_params.clone(),
                ind_type.type_.clone(),
                None,
                false,
            );
            self.constants.insert(ind_type.name.clone(), ind_const);
            temp_names.push(ind_type.name.clone());
        }

        // Step 1b: Temporarily register all constructors as constants too. Most
        // constructor types reference only the inductive and their own
        // fields/params, so for ordinary inductives this is inert. It is REQUIRED
        // for HIT path constructors whose types reference sibling *point*
        // constructors (e.g. S¹'s `loop : Path (λ_:I. S¹) base base` mentions
        // `base`); without `base` registered, type-checking `loop`'s type fails.
        // All types are registered before any constructor so mutual references
        // resolve.
        for ind_type in &decl.types {
            for ctor in &ind_type.constructors {
                let ctor_const = ConstantInfo::new(
                    ctor.name.clone(),
                    decl.level_params.clone(),
                    ctor.type_.clone(),
                    None,
                    false,
                );
                self.constants.insert(ctor.name.clone(), ctor_const);
                temp_names.push(ctor.name.clone());
            }
        }

        // Step 2: Run type checking (immutable borrow of self)
        let result = self.do_inductive_type_check(decl, result_levels);

        // Step 3: Remove temporary registrations regardless of success/failure.
        // They will be re-added properly by the main registration loop.
        for name in &temp_names {
            self.constants.remove(name);
            // A missing constant must never retain a validation stamp.  The
            // permanent registration below installs a fresh FullKernelCheck
            // stamp only after all temporary type checks succeed.
            self.declaration_verification.remove(name);
        }

        result
    }

    /// Whether `ind_type` is a Higher Inductive Type — i.e. has at least one
    /// *path* constructor (a constructor whose return type is a `CubicalPath`,
    /// e.g. S¹'s `loop`). Used to skip `noConfusion` generation, which would be
    /// unsound for path constructors.
    pub(crate) fn has_path_constructor(ind_type: &crate::inductive::InductiveType) -> bool {
        ind_type
            .constructors
            .iter()
            .any(|c| matches!(get_return_type(&c.type_).kind, ExprKind::CubicalPath { .. }))
    }

    /// Inner type-checking logic for inductive declarations.
    ///
    /// Requires that the inductive types are already registered as constants
    /// (even temporarily) so the TypeChecker can resolve references.
    fn do_inductive_type_check(
        &self,
        decl: &InductiveDecl,
        result_levels: &[Level],
    ) -> Result<(), EnvError> {
        let settings = self.checker_settings();
        let mut tc = crate::tc::TypeChecker::with_mode(self, settings.mode);
        // Coq lane: cumulative subtyping (`Prop ≤ Set ≤ Type`), mirroring
        // `decl_add.rs` — an inductive whose constructor fields apply a
        // collapsed-universe constant at a `Prop` argument (the Berardi
        // `retract` Prop-record class) is well-typed under the SAME rule the
        // env re-checks every other Coq declaration with. No-op (identical to
        // the non-cumulative check) when the env flag is off, i.e. the
        // Lean/olean lane.
        tc.set_cumulative(settings.cumulative);

        // F3 + F2: Single-pass type checking and universe constraint verification.
        //
        // For each inductive type and its constructors:
        //   F3: infer_sort verifies well-typedness (the expression inhabits a sort).
        //   F2: Per-field universe check matching Lean 4's check_constructors
        //       (kernel/inductive.cpp). Each non-parameter constructor field's sort
        //       must be ≤ the inductive's result sort level.
        //
        // F2 detail: For an inductive in Sort l (l ≠ 0), each non-parameter
        // constructor field's sort must not exceed l. For Prop (l = 0), this
        // check is skipped: Prop is impredicative, so Prop inductives may have
        // fields in higher universes. The restriction for Prop is on elimination
        // (large_elim), not construction.
        //
        // The previous whole-type comparison (ctor_sort ≤ ind_sort) was unsound
        // because imax semantics collapse field contributions when the codomain
        // is Prop, masking per-field violations (#2362).
        for (ind_type, result_level) in decl.types.iter().zip(result_levels) {
            // F3: Verify inductive type expression is well-typed
            let _ = tc
                .infer_sort(&ind_type.type_)
                .map_err(|e| EnvError::TypeCheckFailed {
                    name: ind_type.name.clone(),
                    source: e,
                })?;

            // The result level is the one `check_block_agreement` found up to
            // whnf (Lean's `m_result_level`): a Coq record whose codomain is a
            // sort only up to ζ/δ (`LetIn(T:=…) in Sort`, `Const(def=Type)`)
            // contributes its real level to the per-field F2 bound, and a
            // δ-`Prop` codomain is exempt from it exactly as `Prop` is.

            // F2 applies only to non-Prop inductives
            // Lean skips the bound only for a result level that IS `0`
            // (`is_zero`, inductive.cpp:439), Clean's `Extended` for one that
            // evaluates to `0` everywhere.
            let check_universe = !self.level_is_zero_in_theory(result_level);

            for ctor in &ind_type.constructors {
                // F3: Verify constructor type expression is well-typed
                let _ = tc
                    .infer_sort(&ctor.type_)
                    .map_err(|e| EnvError::TypeCheckFailed {
                        name: ctor.name.clone(),
                        source: e,
                    })?;

                // F2: Per-field universe check — each non-parameter field's sort
                // must satisfy is_geq(result_level, field_sort)
                if check_universe {
                    let field_sorts = tc
                        .ctor_field_sort_levels(&ctor.type_, decl.num_params)
                        .map_err(|e| EnvError::TypeCheckFailed {
                            name: ctor.name.clone(),
                            source: e,
                        })?;
                    for field_sort in &field_sorts {
                        if !self.level_geq_in_theory(result_level, field_sort) {
                            return Err(EnvError::Inductive(InductiveError::UniverseMismatch(
                                ctor.name.clone(),
                            )));
                        }
                    }
                }
            }
        }

        Ok(())
    }

    /// F1: Check nested positivity through container inductives (#2156).
    ///
    /// For each constructor argument that applies a previously-declared inductive
    /// type to arguments mentioning the type being defined, look up the container's
    /// constructors, substitute the actual arguments for its parameters, and verify
    /// that the type being defined still appears strictly positively.
    ///
    /// This catches unsound types like:
    /// ```text
    /// inductive Container (A : Type) | mk : (A → Nat) → Container A
    /// inductive Bad | mk : Container Bad → Bad
    /// ```
    /// where Bad appears negatively inside Container.mk after substitution.
    fn check_nested_positivity(
        &self,
        decl: &InductiveDecl,
    ) -> Result<std::collections::HashSet<Name>, EnvError> {
        let all_names: Vec<&Name> = decl.types.iter().map(|t| &t.name).collect();
        let mut nested_types = std::collections::HashSet::new();

        for ind_type in &decl.types {
            for ctor in &ind_type.constructors {
                // Fresh visited set per constructor. The visited set prevents
                // infinite recursion within a single check chain (e.g., List.cons
                // references List A → List A). Keyed by container NAME only:
                // the former (container, param_args) key compared instantiation
                // args by structural equality, and for parameterized outer
                // declarations (`num_params > 0`) those args carry de Bruijn
                // indices that SHIFT at each substitution round — the key never
                // hit and the walk regressed unboundedly (first exposed when
                // the reject-all-parameterized guard was removed, design
                // 2026-07-02-parameterized-nested-inductives.md B5). A
                // name-keyed guard terminates; cross-instantiation negative
                // occurrences this pre-pass no longer re-verifies are caught
                // by the soundness-bearing post-transform strict validation
                // ([R8]: a negative container shape surfaces verbatim as a
                // block name in an aux-mirror Pi domain → NonPositive).
                let mut visited = std::collections::HashSet::new();
                let found = self.check_nested_in_ctor_type(
                    &ctor.type_,
                    &ctor.name,
                    &all_names,
                    decl.num_params,
                    &mut visited,
                )?;
                if found {
                    nested_types.insert(ind_type.name.clone());
                }
            }
        }
        Ok(nested_types)
    }

    /// Walk a constructor type's Pi domains (skipping parameters) and check each
    /// domain for nested inductive occurrences. Returns true if nesting was found.
    fn check_nested_in_ctor_type(
        &self,
        expr: &Expr,
        ctor_name: &Name,
        all_names: &[&Name],
        num_params: u32,
        visited: &mut std::collections::HashSet<Name>,
    ) -> Result<bool, EnvError> {
        let mut ty = expr;
        let mut pi_idx = 0u32;
        let mut found_nested = false;
        while let ExprKind::Pi(_, domain, body) = &ty.kind {
            if pi_idx >= num_params
                && self.check_nested_in_domain(domain, ctor_name, all_names, visited)?
            {
                found_nested = true;
            }
            ty = body;
            pi_idx += 1;
        }
        Ok(found_nested)
    }

    /// Check a single constructor argument domain for nested inductive uses.
    /// Returns true if a nested container use was found.
    ///
    /// If the domain is an application `Container arg1 ... argN` where Container
    /// is a known inductive in the environment (not one being defined) and some
    /// argI mentions a type being defined, substitute the args into Container's
    /// constructor types and check positivity.
    fn check_nested_in_domain(
        &self,
        expr: &Expr,
        ctor_name: &Name,
        all_names: &[&Name],
        visited: &mut std::collections::HashSet<Name>,
    ) -> Result<bool, EnvError> {
        let mut found_nested = false;
        let head = expr.get_app_fn();
        if let ExprKind::Const(container_name, _) = &head.kind {
            // Skip if the container is one of the types being defined —
            // those are handled by the standard mutual positivity check.
            if all_names.contains(&container_name) {
                return Ok(false);
            }

            // Check if the container is a known inductive in the environment
            if let Some(container_val) = self.inductives.get(container_name) {
                let args = expr.get_app_args();

                // Only relevant if some argument mentions a type being defined
                let mentions_defined = args
                    .iter()
                    .any(|arg| all_names.iter().any(|name| mentions_name(arg, name)));

                if mentions_defined {
                    self.check_through_container(
                        container_val,
                        &args,
                        ctor_name,
                        all_names,
                        visited,
                    )?;
                    found_nested = true;
                }
            }
        }

        // Recurse into nested applications within Pi domains.
        // E.g., for `(Container Bad → X) → Bad`, check within the inner Pi.
        if let ExprKind::Pi(_, domain, codomain) = &expr.kind {
            if self.check_nested_in_domain(domain, ctor_name, all_names, visited)? {
                found_nested = true;
            }
            if self.check_nested_in_domain(codomain, ctor_name, all_names, visited)? {
                found_nested = true;
            }
        }

        Ok(found_nested)
    }

    /// Look up a container inductive's constructors, substitute actual arguments
    /// for parameters, and check that all types being defined appear positively
    /// in the instantiated constructor types.
    ///
    /// Uses `visited` keyed by container name to prevent infinite recursion
    /// when a container's constructors reference the same container type
    /// (e.g., List.cons has `List A → List A`). Cross-instantiation negative
    /// occurrences are re-verified by the post-transform strict validation
    /// ([R8]), which is the soundness-bearing check.
    fn check_through_container(
        &self,
        container_val: &InductiveVal,
        args: &[&Expr],
        ctor_name: &Name,
        all_names: &[&Name],
        visited: &mut std::collections::HashSet<Name>,
    ) -> Result<(), EnvError> {
        // Cycle guard: skip containers already checked through in this chain.
        // Name-keyed (NOT (name, args)): instantiation args shift their de
        // Bruijn indices under parameterized outer declarations, so an
        // arg-sensitive key never terminates (design B5 fix).
        if !visited.insert(container_val.name.clone()) {
            return Ok(());
        }
        let n_params = container_val.num_params as usize;

        for container_ctor_name in &container_val.constructor_names {
            let container_ctor = match self.constructors.get(container_ctor_name) {
                Some(c) => c,
                None => continue,
            };

            // Instantiate the container constructor's parameters with actual args.
            // The constructor type is: Π (p1 : T1) ... (pN : TN). body
            // We strip the parameter Pi binders and substitute each with the
            // corresponding actual argument.
            let mut instantiated = container_ctor.type_.clone();
            for arg in args.iter().take(n_params) {
                if let ExprKind::Pi(_, _, body) = &instantiated.kind {
                    instantiated = body.instantiate(arg);
                } else {
                    break;
                }
            }

            // Check that all types being defined appear positively in the
            // instantiated constructor type (which now has the actual arguments
            // substituted for the container's parameters).
            for name in all_names {
                check_positivity(name, &instantiated, 0, all_names).map_err(|_| {
                    EnvError::Inductive(InductiveError::NonPositive(
                        (*name).clone(),
                        ctor_name.clone(),
                    ))
                })?;
            }

            // Recursively check for nested inductives within the instantiated
            // constructor's domains (handles double-nesting).
            self.check_nested_in_ctor_type(&instantiated, ctor_name, all_names, 0, visited)?;
        }
        Ok(())
    }
}
