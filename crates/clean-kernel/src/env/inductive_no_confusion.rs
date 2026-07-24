// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! noConfusionType and noConfusion generation for inductive types.
//!
//! For each non-Prop inductive type, generates:
//! - `T.noConfusionType`: A definition that returns the type of evidence
//!   obtainable from equality of two constructors
//! - `T.noConfusion`: A recursor-like constant that converts an equality
//!   proof into noConfusionType evidence
//!
//! Extracted from `inductive_builder.rs` for maintainability.

use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::inductive::{
    count_pi_args, get_return_type, Constructor, InductiveDecl, InductiveError, InductiveType,
    RecursorArgOrder,
};
use crate::level::Level;
use crate::name::Name;
use crate::tc::{LocalContext, TypeChecker};
use std::collections::HashSet;
use std::sync::Arc;

use super::inductive_fixed_indices::{fresh_univ_name, ind_const_with_levels, is_prop_former_type};
use super::types::{ConstantInfo, ConstantKind, EnvError, Reducibility};
use super::{ConstantSource, Declaration, DeclarationVerification, Environment};

/// Why a noConfusion mutual block was not regenerated.
///
/// The regeneration API reports fail-closed outcomes instead of silently
/// retrying permanently unsupported families on every initialization pass.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NoConfusionRegenerationIssue {
    /// A Prop-valued member makes the entire mutual block ineligible.
    PropValued { member: Name },
    /// An indexed member is not supported by the current generator.
    Indexed { member: Name },
    /// A path constructor makes constructor disjointness/injectivity unsound.
    HigherInductive { member: Name },
    /// Stored mutual-block or constructor metadata was incomplete/inconsistent.
    InvalidBlockMetadata { detail: String },
    /// Equality has not been initialized yet.
    PendingEquality,
    /// The heterogeneous equality surface needed by parameterized families is
    /// not complete yet.
    PendingHeterogeneousEquality,
    /// Canonical declaration construction failed before any environment edit.
    GenerationFailed { member: Name, detail: String },
    /// A generated declaration failed its fresh strict kernel check.
    KernelCheckFailed { member: Name, detail: String },
}

/// One block-level noConfusion regeneration diagnostic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NoConfusionRegenerationDiagnostic {
    /// The complete stored mutual block, in declaration order. For malformed
    /// metadata this is the best validated name list available.
    pub block: Vec<Name>,
    /// The fail-closed outcome for this block.
    pub issue: NoConfusionRegenerationIssue,
}

/// Detailed result of a noConfusion regeneration pass.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct NoConfusionRegenerationReport {
    /// Exact constant names whose canonical payloads earned a fresh full check.
    pub repaired_names: Vec<Name>,
    /// Blocks skipped or left unchanged, with a concrete reason.
    pub diagnostics: Vec<NoConfusionRegenerationDiagnostic>,
}

#[derive(Clone)]
pub(super) struct NoConfusionCandidate {
    member: Name,
    nct_name: Name,
    nc_name: Name,
    nct_decl: Declaration,
    nc_decl: Declaration,
    nct_const: ConstantInfo,
    nc_const: ConstantInfo,
}

#[derive(Clone)]
struct NoConfusionSnapshot {
    name: Name,
    constant: Option<ConstantInfo>,
    verification: Option<DeclarationVerification>,
}

/// A temporary lazy-source view that makes target pair names genuinely absent
/// during strict validation while forwarding every unrelated dependency.
#[derive(Debug)]
struct NoConfusionMaskedSource {
    inner: Arc<dyn ConstantSource>,
    masked: HashSet<Name>,
}

impl ConstantSource for NoConfusionMaskedSource {
    fn get(&self, name: &Name) -> Option<&ConstantInfo> {
        if self.masked.contains(name) {
            None
        } else {
            self.inner.get(name)
        }
    }

    fn contains(&self, name: &Name) -> bool {
        !self.masked.contains(name) && self.inner.contains(name)
    }

    fn names(&self) -> Vec<Name> {
        self.inner
            .names()
            .into_iter()
            .filter(|name| !self.masked.contains(name))
            .collect()
    }
}

impl Environment {
    /// Return whether every member of a mutual block is supported by the
    /// current noConfusion generator.
    ///
    /// Eligibility is deliberately block-wide. A noConfusion declaration is
    /// generated from the complete mutual declaration, so accepting one member
    /// while another is Prop-valued, indexed, or a HIT would let regeneration
    /// reinterpret the block under a weaker declaration than the kernel
    /// originally checked.
    pub(crate) fn no_confusion_block_eligibility(
        decl: &InductiveDecl,
    ) -> Result<(), NoConfusionRegenerationIssue> {
        for member in &decl.types {
            if is_prop_former_type(&member.type_) {
                return Err(NoConfusionRegenerationIssue::PropValued {
                    member: member.name.clone(),
                });
            }
            if count_pi_args(&member.type_) > decl.num_params {
                return Err(NoConfusionRegenerationIssue::Indexed {
                    member: member.name.clone(),
                });
            }
            if member.constructors.iter().any(|constructor| {
                matches!(
                    get_return_type(&constructor.type_).kind,
                    ExprKind::CubicalPath { .. }
                )
            }) {
                return Err(NoConfusionRegenerationIssue::HigherInductive {
                    member: member.name.clone(),
                });
            }
        }
        Ok(())
    }

    /// Reconstruct a complete, ordered mutual declaration from stored kernel
    /// metadata. No missing constructor/member is filtered out: any mismatch
    /// fails closed before candidate construction or environment mutation.
    fn reconstruct_no_confusion_block(
        &self,
        seed: &Name,
    ) -> Result<InductiveDecl, NoConfusionRegenerationDiagnostic> {
        let fail = |block: &[Name], detail: String| NoConfusionRegenerationDiagnostic {
            block: block.to_vec(),
            issue: NoConfusionRegenerationIssue::InvalidBlockMetadata { detail },
        };

        let Some(seed_value) = self.inductives.get(seed) else {
            return Err(fail(
                std::slice::from_ref(seed),
                format!("missing seed inductive {seed}"),
            ));
        };
        let block_names = seed_value.all_names.clone();
        if block_names.is_empty() {
            return Err(fail(
                std::slice::from_ref(seed),
                format!("{seed} has an empty all_names block"),
            ));
        }
        let mut unique_members = HashSet::with_capacity(block_names.len());
        for member in &block_names {
            if !unique_members.insert(member.clone()) {
                return Err(fail(
                    &block_names,
                    format!("duplicate mutual member {member} in all_names"),
                ));
            }
        }
        if !unique_members.contains(seed) {
            return Err(fail(
                &block_names,
                format!("seed {seed} is absent from its own all_names block"),
            ));
        }

        // Generated auxiliary names may replace imported noConfusion stubs,
        // but they must never overwrite a declaration that is structurally
        // registered as an inductive, constructor, or recursor. Namespace
        // prefixes do not make such collisions impossible (for example, a
        // mutual member can itself be named `T.noConfusion`).
        for member in &block_names {
            for suffix in ["noConfusionType", "noConfusion"] {
                let target = Name::from_string(&format!("{member}.{suffix}"));
                if self.inductives.contains_key(&target)
                    || self.constructors.contains_key(&target)
                    || self.recursors.contains_key(&target)
                {
                    return Err(fail(
                        &block_names,
                        format!(
                            "generated target {target} collides with registered kernel metadata"
                        ),
                    ));
                }
            }
        }

        let level_params = seed_value.level_params.clone();
        let num_params = seed_value.num_params;
        let mut types = Vec::with_capacity(block_names.len());
        let mut unique_constructors = HashSet::new();

        for member_name in &block_names {
            let Some(member) = self.inductives.get(member_name) else {
                return Err(fail(
                    &block_names,
                    format!("missing mutual member metadata for {member_name}"),
                ));
            };
            if member.name != *member_name {
                return Err(fail(
                    &block_names,
                    format!(
                        "mutual member key {member_name} contains metadata for {}",
                        member.name
                    ),
                ));
            }
            if member.all_names != block_names {
                return Err(fail(
                    &block_names,
                    format!("{member_name} has a different or reordered all_names block"),
                ));
            }
            if member.level_params != level_params || member.num_params != num_params {
                return Err(fail(
                    &block_names,
                    format!("{member_name} disagrees on block levels or parameter count"),
                ));
            }
            if is_prop_former_type(&member.type_) {
                return Err(NoConfusionRegenerationDiagnostic {
                    block: block_names.clone(),
                    issue: NoConfusionRegenerationIssue::PropValued {
                        member: member_name.clone(),
                    },
                });
            }
            if member.num_indices > 0 || count_pi_args(&member.type_) > num_params {
                return Err(NoConfusionRegenerationDiagnostic {
                    block: block_names.clone(),
                    issue: NoConfusionRegenerationIssue::Indexed {
                        member: member_name.clone(),
                    },
                });
            }

            let Some(member_constant) = self.get_const(member_name) else {
                return Err(fail(
                    &block_names,
                    format!("missing inductive constant for {member_name}"),
                ));
            };
            if member_constant.name != *member_name
                || member_constant.level_params != level_params
                || member_constant.type_ != member.type_
            {
                return Err(fail(
                    &block_names,
                    format!("inductive constant payload disagrees with {member_name} metadata"),
                ));
            }

            let mut constructors = Vec::with_capacity(member.constructor_names.len());
            for (index, constructor_name) in member.constructor_names.iter().enumerate() {
                if !unique_constructors.insert(constructor_name.clone()) {
                    return Err(fail(
                        &block_names,
                        format!("duplicate constructor {constructor_name} in mutual block"),
                    ));
                }
                let Some(constructor) = self.constructors.get(constructor_name) else {
                    return Err(fail(
                        &block_names,
                        format!("missing constructor metadata for {constructor_name}"),
                    ));
                };
                if constructor.name != *constructor_name
                    || constructor.inductive_name != *member_name
                    || constructor.level_params != level_params
                    || constructor.num_params != num_params
                    || constructor.constructor_idx as usize != index
                {
                    return Err(fail(
                        &block_names,
                        format!("constructor metadata mismatch for {constructor_name}"),
                    ));
                }
                let Some(constructor_constant) = self.get_const(constructor_name) else {
                    return Err(fail(
                        &block_names,
                        format!("missing constructor constant for {constructor_name}"),
                    ));
                };
                if constructor_constant.name != *constructor_name
                    || constructor_constant.level_params != level_params
                    || constructor_constant.type_ != constructor.type_
                {
                    return Err(fail(
                        &block_names,
                        format!(
                            "constructor constant payload disagrees with {constructor_name} metadata"
                        ),
                    ));
                }
                constructors.push(Constructor {
                    name: constructor.name.clone(),
                    type_: constructor.type_.clone(),
                });
            }

            types.push(InductiveType {
                name: member.name.clone(),
                type_: member.type_.clone(),
                constructors,
            });
        }

        // Validate the inverse ownership relation as well as every listed
        // constructor. Otherwise an extra constructor metadata row could be
        // silently omitted from the reconstructed declaration and the repair
        // would generate a principle for a weaker block than the environment
        // actually records.
        for (constructor_key, constructor) in &self.constructors {
            if unique_members.contains(&constructor.inductive_name) {
                if &constructor.name != constructor_key {
                    return Err(fail(
                        &block_names,
                        format!(
                            "constructor key {constructor_key} contains metadata for {}",
                            constructor.name
                        ),
                    ));
                }
                if !unique_constructors.contains(constructor_key) {
                    return Err(fail(
                        &block_names,
                        format!(
                            "constructor {constructor_key} is owned by {} but absent from its ordered constructor_names list",
                            constructor.inductive_name
                        ),
                    ));
                }
            }
        }

        let decl = InductiveDecl {
            level_params,
            num_params,
            types,
        };
        Self::no_confusion_block_eligibility(&decl).map_err(|issue| {
            NoConfusionRegenerationDiagnostic {
                block: block_names.clone(),
                issue,
            }
        })?;
        Ok(decl)
    }

    fn no_confusion_pair_requires_regeneration(&self, member: &Name) -> bool {
        let nct_name = Name::from_string(&format!("{member}.noConfusionType"));
        let nc_name = Name::from_string(&format!("{member}.noConfusion"));
        let member_needs_repair = |name: &Name| {
            self.constants.get(name).is_none_or(|constant| {
                constant.value.is_none()
                    || constant.kind != ConstantKind::Definition
                    || !constant.is_reducible
                    || constant.reducibility != Reducibility::Reducible
            }) || self.declaration_verification(name)
                != Some(DeclarationVerification::FullKernelCheck)
        };

        if member_needs_repair(&nct_name) || member_needs_repair(&nc_name) {
            return true;
        }

        // Source environments using the legacy casesOn recursor layout need a
        // canonical pair rebuilt against the registered recursor metadata.
        let cases_on_name = Name::from_string(&format!("{member}.casesOn"));
        self.recursors.get(&cases_on_name).is_some_and(|recursor| {
            recursor.arg_order == crate::inductive::RecursorArgOrder::MajorAfterMinors
        })
    }

    pub(super) fn no_confusion_prerequisite_issue(
        &self,
        decl: &InductiveDecl,
    ) -> Option<NoConfusionRegenerationIssue> {
        if ["Eq", "Eq.refl", "Eq.ndrec"]
            .into_iter()
            .any(|name| self.get_const(&Name::from_string(name)).is_none())
        {
            return Some(NoConfusionRegenerationIssue::PendingEquality);
        }
        if decl.num_params > 0
            && ["HEq", "HEq.refl", "eq_of_heq"]
                .into_iter()
                .any(|name| self.get_const(&Name::from_string(name)).is_none())
        {
            return Some(NoConfusionRegenerationIssue::PendingHeterogeneousEquality);
        }
        None
    }

    /// Compute the sort level of each constructor field (after stripping params).
    ///
    /// Returns a `Vec<Level>` with one entry per field. Each entry is the universe
    /// level `l` such that the field's type lives in `Sort(l)`. Used by
    /// `build_no_confusion_type` to:
    /// - Skip Prop-valued fields (`l.is_zero()`) — proof irrelevance makes all
    ///   proofs of the same Prop equal, so equalities are trivially satisfied.
    /// - Supply the correct universe level for `@Eq.{l}` on each non-Prop field,
    ///   instead of using the inductive's result sort for all fields (#1301).
    ///
    /// Follows Lean 4 `NoConfusion.lean` which uses `isProof` to skip proof fields
    /// and `mkEqHEq` to compute per-field equality with the correct universe.
    ///
    /// `pub(super)`: shared with the v4.30 heterogeneous builder
    /// (`inductive_no_confusion_hetero.rs`).
    pub(super) fn compute_ctor_field_sort_levels(
        &self,
        ctor_type: &Expr,
        num_params: u32,
        ctor_name: &Name,
    ) -> Result<Vec<Level>, EnvError> {
        self.compute_ctor_field_sort_levels_inner(ctor_type, num_params, ctor_name, None)
    }

    /// Compute field sort levels with an optional fallback level for when
    /// `infer_sort` fails on non-Prop fields. Used during regeneration after
    /// all modules are loaded, where the inductive's own result sort provides
    /// a sound conservative approximation. Part of #3134.
    ///
    /// `pub(super)`: shared with the v4.30 heterogeneous builder
    /// (`inductive_no_confusion_hetero.rs`).
    pub(super) fn compute_ctor_field_sort_levels_with_fallback(
        &self,
        ctor_type: &Expr,
        num_params: u32,
        ctor_name: &Name,
        fallback_level: &Level,
    ) -> Result<Vec<Level>, EnvError> {
        self.compute_ctor_field_sort_levels_inner(
            ctor_type,
            num_params,
            ctor_name,
            Some(fallback_level),
        )
    }

    fn compute_ctor_field_sort_levels_inner(
        &self,
        ctor_type: &Expr,
        num_params: u32,
        ctor_name: &Name,
        fallback_level: Option<&Level>,
    ) -> Result<Vec<Level>, EnvError> {
        let mut ctx = LocalContext::new();
        let mut current = ctor_type.clone();
        let mut arg_idx = 0u32;
        let mut sort_levels = Vec::new();

        while let ExprKind::Pi(bi, domain, body) = &current.kind {
            if arg_idx >= num_params {
                // This is a field. Infer its sort using a TypeChecker with the
                // current local context (which has FVars for all params and
                // earlier fields).
                let tc = TypeChecker::with_context_and_mode(self, ctx.clone(), self.mode());
                match tc.infer_sort(domain) {
                    Ok(level) => sort_levels.push(level),
                    Err(e) => {
                        // Structural Prop fallback (#2044): if the field type's
                        // head constant returns Prop, Level::zero() is correct
                        // regardless of infer_sort failure (e.g., universe-level
                        // bugs in init code). For non-Prop fields, propagate the
                        // error — silently treating a non-Prop field as Prop
                        // weakens the NoConfusion principle (soundness bug).
                        //
                        // Fallback level: when a fallback is provided (e.g., the
                        // inductive's own result sort level during regeneration),
                        // use it for non-Prop fields instead of propagating the
                        // error. This handles cases where infer_sort fails because
                        // a field type references complex expressions that the TC
                        // can't fully reduce during noConfusion generation. The
                        // inductive's result sort is a conservative approximation:
                        // fields must live in a universe at most as large as the
                        // inductive itself. Part of #3134.
                        if self.is_field_type_structurally_prop(domain) {
                            sort_levels.push(Level::zero());
                        } else if let Some(fb) = fallback_level {
                            sort_levels.push(fb.clone());
                        } else {
                            return Err(EnvError::TypeCheckFailed {
                                name: ctor_name.clone(),
                                source: e,
                            });
                        }
                    }
                }
            }

            // Open the binder: create an FVar for this variable and substitute
            // BVar(0) with it in the body.
            let fvar_id = ctx.push(Name::anon(), (**domain).clone(), *bi);
            current = body.instantiate(&Expr::fvar(fvar_id));
            arg_idx += 1;
        }

        Ok(sort_levels)
    }

    /// Check if a type expression is structurally known to be in Prop (Sort 0).
    ///
    /// Lightweight structural check used when `infer_sort` fails. Determines if
    /// the expression's head constant returns Prop by examining the constant's
    /// declared type in the environment. Returns `true` only if definitively Prop;
    /// returns `false` for unknown or ambiguous cases (conservative for soundness).
    fn is_field_type_structurally_prop(&self, e: &Expr) -> bool {
        // Strip MData (transparent metadata wrappers) before extracting
        // the head constant, since get_app_fn does not pierce MData.
        let head = e.strip_mdata().get_app_fn();
        if let ExprKind::Const(name, _) = &head.kind {
            if let Some(const_info) = self.constants.get(name) {
                let return_sort = Self::strip_pi_codomain(&const_info.type_);
                if let ExprKind::Sort(level) = &return_sort.kind {
                    return level.is_zero();
                }
            }
        }
        false
    }

    /// Walk through Pi binders (and MData/Squash wrappers) to find the innermost codomain.
    fn strip_pi_codomain(e: &Expr) -> &Expr {
        let mut cur = e;
        loop {
            match &cur.kind {
                ExprKind::Pi(_, _, body) => cur = body,
                ExprKind::MData(_, inner) | ExprKind::Squash(inner) => cur = inner,
                _ => return cur,
            }
        }
    }

    /// Build noConfusionType for an inductive type (type + value as a definition).
    ///
    /// Following Lean 4 `mkNoConfusionType` from `NoConfusion.lean`:
    /// For `inductive Nat | zero | succ (n : Nat)`, generates:
    /// ```text
    /// Nat.noConfusionType : {P : Sort u} → Nat → Nat → Sort u
    /// Nat.noConfusionType P zero zero       = (P → P)
    /// Nat.noConfusionType P zero (succ _)   = P
    /// Nat.noConfusionType P (succ _) zero   = P
    /// Nat.noConfusionType P (succ a) (succ b) = (a = b → P) → P
    /// ```
    ///
    /// Returns `(type, value, level_params)` where:
    /// - `type`: The type of noConfusionType (Pi type)
    /// - `value`: The lambda expression implementing the definition
    /// - `level_params`: Universe parameters (result universe + inductive levels)
    ///
    /// Convention dispatch (designs/2026-07-03-noconfusion-ctoridx-convention.md):
    /// - `num_params = 0`: the classic quadratic builder below. For 0-param
    ///   types the classic and v4.30 heterogeneous schemes COINCIDE byte-for-
    ///   byte (design §1.2), so this path is intentionally untouched — it is
    ///   the 0-param invariance guarantee (design §6/A6).
    /// - `num_params > 0`: the v4.30 heterogeneous quadratic builder
    ///   (`inductive_no_confusion_hetero.rs`) — P-first binder order, primed
    ///   second-major params, per-param Eq/HEq premises, HEq major.
    pub(crate) fn build_no_confusion_type(
        &self,
        ind_name: &Name,
        decl: &InductiveDecl,
    ) -> Result<(Expr, Expr, Vec<Name>), EnvError> {
        if decl.num_params == 0 {
            self.build_no_confusion_type_inner(ind_name, decl, None)
        } else {
            self.build_no_confusion_type_hetero(ind_name, decl, None)
        }
    }

    /// Build noConfusionType with a fallback sort level for fields whose sort
    /// can't be inferred. Used during post-load regeneration where all modules
    /// are available but some field types still resist sort inference.
    /// Part of #3134. Same convention dispatch as [`Self::build_no_confusion_type`].
    fn build_no_confusion_type_with_fallback(
        &self,
        ind_name: &Name,
        decl: &InductiveDecl,
        fallback_level: &Level,
    ) -> Result<(Expr, Expr, Vec<Name>), EnvError> {
        if decl.num_params == 0 {
            self.build_no_confusion_type_inner(ind_name, decl, Some(fallback_level))
        } else {
            self.build_no_confusion_type_hetero(ind_name, decl, Some(fallback_level))
        }
    }

    /// Classic quadratic builder — `num_params = 0` ONLY (see the dispatch in
    /// [`Self::build_no_confusion_type`]; parameterized types route to the
    /// v4.30 heterogeneous builder). The parameter-handling code below is kept
    /// verbatim so the 0-param output stays byte-identical (design §6/A6).
    fn build_no_confusion_type_inner(
        &self,
        ind_name: &Name,
        decl: &InductiveDecl,
        fallback_level: Option<&Level>,
    ) -> Result<(Expr, Expr, Vec<Name>), EnvError> {
        let ind_type = decl
            .types
            .iter()
            .find(|t| &t.name == ind_name)
            .ok_or_else(|| EnvError::UnknownInductive(ind_name.clone()))?;

        // Universe parameter for the result type — freshen to avoid collision.
        let result_univ_name = fresh_univ_name(&decl.level_params);
        let mut level_params = vec![result_univ_name.clone()];
        level_params.extend(decl.level_params.clone());

        let num_params = decl.num_params;

        // Collect constructor info: (name, num_fields, field_types, field_sort_levels)
        // field_types are the domain types of the Pi binders after stripping params,
        // with BVar indices relative to the ctor's own Pi chain.
        // field_sort_levels are the universe levels of each field's type, used to:
        // - skip Prop fields (proof irrelevance) when level.is_zero()
        // - provide correct @Eq universe levels for non-Prop fields
        let ctor_infos: Vec<(Name, u32, Vec<Expr>, Vec<Level>)> = ind_type
            .constructors
            .iter()
            .map(|ctor| {
                let ctor_arity = count_pi_args(&ctor.type_);
                let num_fields = ctor_arity.saturating_sub(num_params);
                let field_types = self.get_constructor_field_types(&ctor.type_, num_params);
                let field_sort_levels = if let Some(fb) = fallback_level {
                    self.compute_ctor_field_sort_levels_with_fallback(
                        &ctor.type_,
                        num_params,
                        &ctor.name,
                        fb,
                    )?
                } else {
                    self.compute_ctor_field_sort_levels(&ctor.type_, num_params, &ctor.name)?
                };
                Ok((
                    ctor.name.clone(),
                    num_fields,
                    field_types,
                    field_sort_levels,
                ))
            })
            .collect::<Result<Vec<_>, EnvError>>()?;

        // Build type: {params...} → (P : Sort u) → (a : Ind params) → (b : Ind params) → Sort u
        let result_univ = Level::param(result_univ_name.clone());
        let ind_const = ind_const_with_levels(ind_name, &decl.level_params);

        // Collect parameter binders from the inductive type definition.
        let param_binders = self.collect_pi_binders(&ind_type.type_, num_params);

        // --- Build the TYPE expression ---
        // Layout (inside-out binders): params(n) | P | a | b | result
        //
        // Build ind_applied for 'a' binder domain (depth = num_params + 1)
        let mut ind_applied_a = ind_const.clone();
        for i in 0..num_params {
            ind_applied_a = Expr::app(ind_applied_a, Expr::bvar(num_params - i));
        }

        // Build ind_applied for 'b' binder domain (depth = num_params + 2)
        let mut ind_applied_b = ind_const.clone();
        for i in 0..num_params {
            ind_applied_b = Expr::app(ind_applied_b, Expr::bvar(num_params + 1 - i));
        }

        let mut no_conf_type_ty = Expr::pi(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::Sort(result_univ.clone())), // P : Sort u
            Expr::pi(
                BinderInfo::Default,
                ind_applied_a.clone(), // a : Ind params
                Expr::pi(
                    BinderInfo::Default,
                    ind_applied_b.clone(), // b : Ind params
                    Expr::from_kind(ExprKind::Sort(result_univ.clone())), // result : Sort u
                ),
            ),
        );

        // Wrap with implicit parameter binders (outermost first, iterate in reverse)
        for (_bi, param_ty) in param_binders.iter().rev() {
            no_conf_type_ty = Expr::pi(BinderInfo::Implicit, param_ty.clone(), no_conf_type_ty);
        }

        // --- Build the VALUE expression ---
        // Following Lean 4 NoConfusion.lean:72-145 (quadratic construction).
        //
        // Value = λ params. λ P. λ a. λ b.
        //   Ind.casesOn.{succ u, levels...} params (λ _ : Ind params. Sort u)
        //     alt_0 ... alt_{nc-1}
        //     a
        //
        // For casesOn, the universe is bumped: succ u (eliminating into Sort u,
        // which itself lives in Sort (succ u)).

        let cases_on_name = Name::from_string(&format!("{ind_name}.casesOn"));

        // casesOn level params: first is the motive universe (succ u here),
        // rest are the inductive's level params.
        let mut cases_on_levels: Vec<Level> = Vec::new();
        cases_on_levels.push(Level::succ(Level::param(result_univ_name.clone())));
        cases_on_levels.extend(decl.level_params.iter().map(|p| Level::param(p.clone())));

        // Per-field sort levels are now used instead of the inductive's result sort
        // for @Eq universe levels (see compute_ctor_field_sort_levels and #1301).

        // === Mutual / restored nested-inductive support ===
        //
        // A registered casesOn may expose more motives/minors than the restored
        // declaration: nested restore erases temporary helper inductives but
        // deliberately retains their companion premises. Ordinary mutual blocks
        // also need every sibling premise. The helper below reads the registered
        // telescope and rule metadata, inserts the real premise for this member,
        // and pads all unreachable premises with exact-telescope constant terms.
        // PUnit.{u} — a closed inhabitant of `Sort u`, used as every dummy minor's
        // result. `PUnit.unit.{u}` is NOT needed: noConfusionType eliminates into
        // `Sort u`, so each minor returns a TYPE (here `PUnit`), not a value.
        let punit_u = Expr::const_(Name::from_string("PUnit"), vec![result_univ.clone()]);

        // Build the body of the value inside all lambdas.
        // Lambda binder context (outermost to innermost):
        //   params_0 ... params_{np-1} | P | a | b
        //
        // At the body depth (inside λ params. λ P. λ a. λ b):
        //   b = BVar(0), a = BVar(1), P = BVar(2)
        //   params: param_0 = BVar(np+2), ..., param_{np-1} = BVar(3)
        let np = num_params as usize;

        // Build Ind applied to params at body depth (np + 3 binders above)
        // Used for motive domain type and casesOn param args
        let ind_applied_body = {
            let mut e = ind_const.clone();
            for i in 0..np {
                // param_0 (outermost) at BVar(np + 2), param_last at BVar(3)
                e = Expr::app(e, Expr::bvar((np + 2 - i) as u32));
            }
            e
        };

        // Motive for casesOn: λ (_ : Ind params). Sort u
        // The motive is a lambda; inside it, the Ind params need to be lifted by 1
        let motive = Expr::lam(
            BinderInfo::Default,
            ind_applied_body.clone(),
            Expr::from_kind(ExprKind::Sort(Level::param(result_univ_name.clone()))),
        );

        // Build outer casesOn alternatives — one per constructor of 'a'.
        let nc = ctor_infos.len();
        let mut outer_alts: Vec<Expr> = Vec::with_capacity(nc);

        for (i, (_ctor_name_i, num_fields_i, field_types_i, field_sort_levels_i)) in
            ctor_infos.iter().enumerate()
        {
            let ki = *num_fields_i as usize;

            // alt_i = λ (a_f_0 : F_0). ... λ (a_f_{ki-1} : F_{ki-1}).
            //           <inner casesOn on b>
            //
            // Inside the alt_i lambdas (ki additional binders):
            //   a_f_{ki-1} = BVar(0), ..., a_f_0 = BVar(ki-1)
            //   b = BVar(ki), a = BVar(ki+1), P = BVar(ki+2)
            //   params: param_0 = BVar(ki+np+2), ..., param_{np-1} = BVar(ki+3)

            // Build Ind applied to params at alt_i depth
            let ind_applied_alt_i = {
                let mut e = ind_const.clone();
                for j in 0..np {
                    e = Expr::app(e, Expr::bvar((ki + np + 2 - j) as u32));
                }
                e
            };

            // Motive for inner casesOn (same structure, just lifted)
            let motive_inner = Expr::lam(
                BinderInfo::Default,
                ind_applied_alt_i.clone(),
                Expr::from_kind(ExprKind::Sort(Level::param(result_univ_name.clone()))),
            );

            // Build inner casesOn alternatives — one per constructor of 'b'.
            let mut inner_alts: Vec<Expr> = Vec::with_capacity(nc);

            for (j, (_ctor_name_j, num_fields_j, field_types_j, _field_sort_levels_j)) in
                ctor_infos.iter().enumerate()
            {
                let kj = *num_fields_j as usize;

                if i == j {
                    // Same constructor (diagonal case).
                    // inner_alt = λ (b_f_0 : G_0). ... λ (b_f_{kj-1} : G_{kj-1}).
                    //   (Eq F_0 a_f_0 b_f_0 → ... → Eq F_{ki-1} a_f_{ki-1} b_f_{ki-1} → P) → P
                    //
                    // Inside these lambdas (kj = ki additional binders):
                    //   b_f_{kj-1} = BVar(0), ..., b_f_0 = BVar(kj-1)
                    //   a_f_{ki-1} = BVar(kj), ..., a_f_0 = BVar(kj+ki-1)
                    //   b = BVar(kj+ki), a = BVar(kj+ki+1), P = BVar(kj+ki+2)
                    //   params: param_0 = BVar(kj+ki+np+2)

                    // P at this depth:
                    let p_idx = (kj + ki + 2) as u32;

                    // Build the equality chain for non-Prop fields:
                    //   (f_0 = g_0 → ... → f_{k-1} = g_{k-1} → P) → P
                    // Prop-valued fields are skipped (proof irrelevance — Lean 4
                    // NoConfusion.lean:41 `if (isProof f1) then continue`).
                    // Start from P and prepend equalities right-to-left.
                    let mut eq_chain = Expr::bvar(p_idx);

                    // Iterate fields in reverse order (innermost equality first in the chain).
                    for field_idx in (0..ki).rev() {
                        // Skip Prop-valued fields: proof irrelevance makes all proofs
                        // of the same Prop definitionally equal, so the equality is
                        // trivially satisfied and omitted from the chain (#1301).
                        let field_sort = &field_sort_levels_i[field_idx];
                        if field_sort.is_zero() {
                            continue;
                        }

                        // a_f_{field_idx} at current depth:
                        //   a_f_0 = BVar(kj + ki - 1), ..., a_f_{ki-1} = BVar(kj)
                        let a_field = Expr::bvar((kj + ki - 1 - field_idx) as u32);
                        // b_f_{field_idx} at current depth:
                        //   b_f_0 = BVar(kj - 1), ..., b_f_{kj-1} = BVar(0)
                        let b_field = Expr::bvar((kj - 1 - field_idx) as u32);

                        // Build the equality expression for this field.
                        //
                        // The field type from the ctor's Pi chain (field_types_i[field_idx])
                        // has BVar references:
                        //   BVar(x) for x < field_idx → earlier fields
                        //   BVar(x) for x >= field_idx → params (x - field_idx = param offset)
                        //
                        // We remap these to the current context:
                        //   earlier fields → a's fields: a_f_x = BVar(kj + ki - 1 - x)
                        //   params → BVar(kj + ki + 3 + (x - field_idx))
                        let field_type_a = self.remap_ctor_field_type(
                            &field_types_i[field_idx],
                            field_idx,
                            np,
                            ki,
                            kj,
                        );

                        // Check if this field's type depends on earlier fields.
                        // If so, a's and b's fields have different types and we
                        // need HEq (heterogeneous equality) instead of Eq.
                        // Lean 4 NoConfusion.lean:45 uses isDefEq at elaboration
                        // time; we check structurally at build time.
                        let is_dependent =
                            Self::field_type_is_dependent(&field_types_i[field_idx], field_idx, 0);

                        let eq_expr = if is_dependent {
                            // Dependent field: use @HEq.{field_sort} type_a a type_b b
                            let field_type_b = self.remap_ctor_field_type_for_b(
                                &field_types_i[field_idx],
                                field_idx,
                                np,
                                ki,
                                kj,
                            );
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        Expr::app(
                                            Expr::const_(
                                                Name::from_string("HEq"),
                                                vec![field_sort.clone()],
                                            ),
                                            field_type_a,
                                        ),
                                        a_field,
                                    ),
                                    field_type_b,
                                ),
                                b_field,
                            )
                        } else {
                            // Independent field: use @Eq.{field_sort} type a b
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        Expr::const_(
                                            Name::from_string("Eq"),
                                            vec![field_sort.clone()],
                                        ),
                                        field_type_a,
                                    ),
                                    a_field,
                                ),
                                b_field,
                            )
                        };

                        // Prepend: Pi(Default, eq_expr, shifted_chain)
                        // Inside the new Pi body, all BVars shift up by 1
                        eq_chain = Expr::pi(BinderInfo::Default, eq_expr, eq_chain.lift(1));
                    }

                    // Wrap: (eq_chain → P) → P
                    // eq_chain is the full (f_0 = g_0 → ... → P) type.
                    // We want (eq_chain → P) → P, but eq_chain already ends in P.
                    // So the result is: eq_chain → P  (where P is at the outer depth)
                    // Wait — re-reading the Lean 4 semantics:
                    //   mkNoConfusionCtorArg returns: (f1=g1 → ... → fk=gk → P)
                    //   mkArrow k P gives: (f1=g1 → ... → fk=gk → P) → P
                    // So we need to wrap eq_chain (which is f1=g1→...→fk=gk→P) with → P.
                    let result = Expr::pi(BinderInfo::Default, eq_chain, Expr::bvar(p_idx + 1));

                    // Wrap with lambdas for b's fields
                    let mut inner_alt = result;
                    for field_idx in (0..kj).rev() {
                        // Field type for b_f_{field_idx}: need to lift to correct depth.
                        // field_types_j[field_idx] has BVars relative to the ctor's Pi chain.
                        // In the ctor Pi chain, BVar(0) = previous field, BVar(k-1) = first field,
                        // BVar(k) and above = params.
                        //
                        // We need to remap: the params become the outer params, and earlier
                        // fields become the b_f variables. We also need to account for the
                        // outer binders (ki fields of a, b, a, P, params).
                        //
                        // For simple cases (field type is closed or just Ind params),
                        // we use the Ind type applied to params at the correct depth.
                        let remaining_b_fields = kj - 1 - field_idx;
                        let depth_under_remaining = remaining_b_fields;
                        let field_ty = self.lift_ctor_field_type(
                            &field_types_j[field_idx],
                            field_idx,
                            num_params,
                            (ki + 3) as u32, // extra binders above: a's fields + b + a + P
                            depth_under_remaining as u32,
                        );
                        inner_alt = Expr::lam(BinderInfo::Default, field_ty, inner_alt);
                    }

                    inner_alts.push(inner_alt);
                } else {
                    // Different constructor — return P.
                    // inner_alt = λ (b_f_0 : G_0). ... λ (b_f_{kj-1} : G_{kj-1}). P
                    //
                    // Inside the kj lambdas:
                    //   P = BVar(kj + ki + 2)
                    let p_idx = (kj + ki + 2) as u32;
                    let mut inner_alt = Expr::bvar(p_idx);

                    for field_idx in (0..kj).rev() {
                        let remaining_b_fields = kj - 1 - field_idx;
                        let depth_under_remaining = remaining_b_fields;
                        let field_ty = self.lift_ctor_field_type(
                            &field_types_j[field_idx],
                            field_idx,
                            num_params,
                            (ki + 3) as u32,
                            depth_under_remaining as u32,
                        );
                        inner_alt = Expr::lam(BinderInfo::Default, field_ty, inner_alt);
                    }

                    inner_alts.push(inner_alt);
                }
            }

            let inner_params: Vec<Expr> = (0..np)
                .map(|j| Expr::bvar((ki + np + 2 - j) as u32))
                .collect();
            let dummy_motive_result = Expr::from_kind(ExprKind::Sort(result_univ.clone()));
            let inner_cases = self.apply_cases_on_with_restored_padding(
                decl,
                ind_name,
                &cases_on_name,
                &cases_on_levels,
                &inner_params,
                &motive_inner,
                &inner_alts,
                &Expr::bvar(ki as u32),
                &dummy_motive_result,
                &punit_u,
            )?;

            // Wrap with lambdas for a's fields
            let mut outer_alt = inner_cases;
            for field_idx in (0..ki).rev() {
                let remaining_a_fields = ki - 1 - field_idx;
                let depth_under_remaining = remaining_a_fields;
                let field_ty = self.lift_ctor_field_type(
                    &field_types_i[field_idx],
                    field_idx,
                    num_params,
                    3, // extra binders above: b + a + P
                    depth_under_remaining as u32,
                );
                outer_alt = Expr::lam(BinderInfo::Default, field_ty, outer_alt);
            }

            outer_alts.push(outer_alt);
        }

        let outer_params: Vec<Expr> = (0..np).map(|j| Expr::bvar((np + 2 - j) as u32)).collect();
        let dummy_motive_result = Expr::from_kind(ExprKind::Sort(result_univ.clone()));
        let body = self.apply_cases_on_with_restored_padding(
            decl,
            ind_name,
            &cases_on_name,
            &cases_on_levels,
            &outer_params,
            &motive,
            &outer_alts,
            &Expr::bvar(1),
            &dummy_motive_result,
            &punit_u,
        )?;

        // Wrap body in lambdas: λ P. λ a. λ b. body
        // Build ind_applied for lambda binder types at the correct depths
        let mut ind_applied_lam_a = ind_const.clone();
        for i in 0..np {
            // At P|a depth (np + 1 binders above), param_0 = BVar(np), param_last = BVar(1)
            ind_applied_lam_a = Expr::app(ind_applied_lam_a, Expr::bvar((np - i) as u32));
        }

        let mut ind_applied_lam_b = ind_const.clone();
        for i in 0..np {
            // At P|a|b depth (np + 2 binders above), param_0 = BVar(np+1), param_last = BVar(2)
            ind_applied_lam_b = Expr::app(ind_applied_lam_b, Expr::bvar((np + 1 - i) as u32));
        }

        let mut value = Expr::lam(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::Sort(Level::param(result_univ_name.clone()))), // P : Sort u
            Expr::lam(
                BinderInfo::Default,
                ind_applied_lam_a, // a : Ind params
                Expr::lam(
                    BinderInfo::Default,
                    ind_applied_lam_b, // b : Ind params
                    body,
                ),
            ),
        );

        // Wrap with parameter lambdas (outermost first, iterate in reverse)
        for (_bi, param_ty) in param_binders.iter().rev() {
            value = Expr::lam(BinderInfo::Implicit, param_ty.clone(), value);
        }

        Ok((no_conf_type_ty, value, level_params))
    }

    /// Remap a constructor field type's BVar indices for use as a lambda binder
    /// domain in the noConfusionType value expression.
    ///
    /// In the ctor's Pi chain, field at `field_idx` sees:
    /// - BVar(0)..BVar(field_idx-1) = earlier fields (field_{field_idx-1}..field_0)
    /// - BVar(field_idx)..BVar(field_idx+np-1) = params
    ///
    /// In the noConfusionType lambda chain at nesting depth `field_idx`:
    /// - BVar(0)..BVar(field_idx-1) = earlier fields (same positions — 1:1 mapping)
    /// - BVar(field_idx + extra_above)..BVar(field_idx + extra_above + np - 1) = params
    ///
    /// Earlier field BVars are unchanged; param BVars shift by `extra_above`.
    fn lift_ctor_field_type(
        &self,
        field_ty: &Expr,
        field_idx: usize,
        _num_params: u32,
        extra_above: u32,
        _depth_under_remaining: u32,
    ) -> Expr {
        self.remap_binder_bvars(field_ty, field_idx, extra_above, 0)
    }

    /// Apply a restored `casesOn` using its registered telescope as the source
    /// of truth for motive/minor arity.  Nested restore deliberately removes
    /// the temporary auxiliary inductive declarations while retaining their
    /// companion motives and minors on the primary eliminator.  Consequently
    /// `decl.types.len()` and the visible constructor count can be smaller than
    /// `RecursorVal::{num_motives,num_minors}`.
    ///
    /// The target member receives the real motive/minors.  Every other original
    /// member and every restored companion receives a constant dummy term built
    /// over the *exact next Pi telescope*, so dependent container constructors
    /// remain well typed without reconstructing erased `_nested.*` declarations.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn apply_cases_on_with_restored_padding(
        &self,
        decl: &InductiveDecl,
        ind_name: &Name,
        cases_on_name: &Name,
        cases_on_levels: &[Level],
        params: &[Expr],
        real_motive: &Expr,
        real_alts: &[Expr],
        major: &Expr,
        dummy_motive_result: &Expr,
        dummy_minor_result: &Expr,
    ) -> Result<Expr, EnvError> {
        let rec = self.recursors.get(cases_on_name).ok_or_else(|| {
            EnvError::Inductive(InductiveError::NestedRestoreInvariant(format!(
                "missing registered recursor metadata for {cases_on_name}"
            )))
        })?;
        if rec.num_indices != 0 {
            return Err(EnvError::Inductive(InductiveError::NestedRestoreInvariant(
                format!(
                    "noConfusion padding requires an index-free recursor, but {cases_on_name} has {} indices",
                    rec.num_indices
                ),
            )));
        }

        let target_pos = decl
            .types
            .iter()
            .position(|t| &t.name == ind_name)
            .ok_or_else(|| EnvError::UnknownInductive(ind_name.clone()))?;
        let registered_motives = rec.num_motives as usize;
        if target_pos >= registered_motives {
            return Err(EnvError::Inductive(InductiveError::NestedRestoreInvariant(
                format!(
                    "{cases_on_name} has no motive at target position {target_pos}; registered motive count is {registered_motives}"
                ),
            )));
        }
        if registered_motives < decl.types.len() {
            return Err(EnvError::Inductive(InductiveError::NestedRestoreInvariant(
                format!(
                    "{cases_on_name} registers {registered_motives} motives for {} visible declaration members",
                    decl.types.len()
                ),
            )));
        }
        let target = &decl.types[target_pos];
        if target.constructors.len() != real_alts.len() {
            return Err(EnvError::Inductive(InductiveError::NestedRestoreInvariant(
                format!(
                    "{ind_name} noConfusion built {} real minors for {} constructors",
                    real_alts.len(),
                    target.constructors.len()
                ),
            )));
        }

        // Restored minor order is all original members in declaration order,
        // followed by the creation-ordered companion recursors `<first>.rec_N`.
        let mut minor_names: Vec<Name> = decl
            .types
            .iter()
            .flat_map(|ty| ty.constructors.iter().map(|ctor| ctor.name.clone()))
            .collect();
        let first = decl
            .types
            .first()
            .ok_or_else(|| EnvError::UnknownInductive(ind_name.clone()))?
            .name
            .clone();
        let mut companion_idx = 1usize;
        while minor_names.len() < rec.num_minors as usize {
            let companion_name = Name::from_string(&format!("{first}.rec_{companion_idx}"));
            let companion = self.recursors.get(&companion_name).ok_or_else(|| {
                EnvError::Inductive(InductiveError::NestedRestoreInvariant(format!(
                    "{cases_on_name} declares {} minors, but restored companion {companion_name} is missing",
                    rec.num_minors
                )))
            })?;
            minor_names.extend(
                companion
                    .rules
                    .iter()
                    .map(|rule| rule.constructor_name.clone()),
            );
            companion_idx += 1;
        }
        if minor_names.len() != rec.num_minors as usize {
            return Err(EnvError::Inductive(InductiveError::NestedRestoreInvariant(
                format!(
                    "{cases_on_name} minor metadata mismatch: telescope says {}, restored rules enumerate {}",
                    rec.num_minors,
                    minor_names.len()
                ),
            )));
        }

        // Universe-arity guard: noConfusion generation supplies
        // `[succ(result_univ)] ++ decl.level_params`, which assumes a
        // LARGE-eliminating casesOn. A Prop-only eliminator (e.g. a
        // template-polymorphic `prod` on the Lean lane) declares only the
        // declaration's own universe params and genuinely cannot host a
        // Sort-valued noConfusion motive — fail closed here instead of
        // tripping the substitution-arity invariant below.
        if rec.level_params.len() != cases_on_levels.len() {
            return Err(EnvError::Inductive(InductiveError::NestedRestoreInvariant(
                format!(
                    "{cases_on_name} declares {} universe parameters, but noConfusion \
                     generation supplied {} universe arguments (Prop-only eliminators \
                     cannot host a Sort-valued noConfusion motive)",
                    rec.level_params.len(),
                    cases_on_levels.len()
                ),
            )));
        }

        let mut app = Expr::const_(cases_on_name.clone(), cases_on_levels.to_vec());
        let mut cursor = rec
            .type_
            .instantiate_level_params_direct(&rec.level_params, cases_on_levels);
        let apply_next = |app: &mut Expr, cursor: &mut Expr, arg: Expr| {
            let ExprKind::Pi(_, _, body) = cursor.kind() else {
                return Err(EnvError::Inductive(InductiveError::NestedRestoreInvariant(
                    format!(
                        "{cases_on_name} telescope ended before all registered arguments were applied"
                    ),
                )));
            };
            *cursor = body.instantiate(&arg);
            *app = Expr::app(app.clone(), arg);
            Ok(())
        };

        for param in params {
            apply_next(&mut app, &mut cursor, param.clone())?;
        }
        for motive_idx in 0..rec.num_motives as usize {
            let motive = if motive_idx == target_pos {
                real_motive.clone()
            } else {
                let ExprKind::Pi(_, expected, _) = cursor.kind() else {
                    return Err(EnvError::Inductive(InductiveError::NestedRestoreInvariant(
                        format!("{cases_on_name} telescope ended before motive {motive_idx}"),
                    )));
                };
                constant_over_pi_telescope(expected, dummy_motive_result)
            };
            apply_next(&mut app, &mut cursor, motive)?;
        }

        if rec.arg_order == RecursorArgOrder::MajorAfterMotive {
            apply_next(&mut app, &mut cursor, major.clone())?;
        }

        for ctor_name in minor_names {
            let minor = target
                .constructors
                .iter()
                .position(|ctor| ctor.name == ctor_name)
                .map(|idx| real_alts[idx].clone())
                .unwrap_or_else(|| {
                    let ExprKind::Pi(_, expected, _) = cursor.kind() else {
                        return dummy_minor_result.clone();
                    };
                    constant_over_pi_telescope(expected, dummy_minor_result)
                });
            apply_next(&mut app, &mut cursor, minor)?;
        }

        if rec.arg_order == RecursorArgOrder::MajorAfterMinors {
            apply_next(&mut app, &mut cursor, major.clone())?;
        }
        Ok(app)
    }

    /// Generic BVar remapping over Expr trees.
    ///
    /// Recurses over all ExprKind variants, incrementing `depth` through
    /// binding forms (Pi, Lam, Let). Only the BVar case differs between
    /// callers — provided via the `map_bvar` closure.
    ///
    /// Consolidates `remap_binder_bvars`, `remap_ctor_bvars`, and
    /// `remap_ctor_bvars_for_b` which previously duplicated ~200 LOC
    /// of identical recursive structure. Part of #2070.
    fn remap_bvars<F>(e: &Expr, depth: u32, map_bvar: &F) -> Expr
    where
        F: Fn(u32, u32) -> Expr,
    {
        match &e.kind {
            ExprKind::BVar(idx) => map_bvar(*idx, depth),
            ExprKind::App(f, a) => {
                let nf = Self::remap_bvars(f, depth, map_bvar);
                let na = Self::remap_bvars(a, depth, map_bvar);
                Expr::app(nf, na)
            }
            ExprKind::Pi(bi, domain, body) => {
                let nd = Self::remap_bvars(domain, depth, map_bvar);
                let nb = Self::remap_bvars(body, depth + 1, map_bvar);
                Expr::pi(*bi, nd, nb)
            }
            ExprKind::Lam(bi, domain, body) => {
                let nd = Self::remap_bvars(domain, depth, map_bvar);
                let nb = Self::remap_bvars(body, depth + 1, map_bvar);
                Expr::lam(*bi, nd, nb)
            }
            ExprKind::Sort(_) | ExprKind::Const(_, _) | ExprKind::FVar(_) | ExprKind::Lit(_) => {
                e.clone()
            }
            ExprKind::Let(name, ty, val, body, nd) => {
                let nty = Self::remap_bvars(ty, depth, map_bvar);
                let nval = Self::remap_bvars(val, depth, map_bvar);
                let nbody = Self::remap_bvars(body, depth + 1, map_bvar);
                Expr::from_kind(ExprKind::Let(
                    name.clone(),
                    std::sync::Arc::new(nty),
                    std::sync::Arc::new(nval),
                    std::sync::Arc::new(nbody),
                    *nd,
                ))
            }
            ExprKind::Proj(name, idx, e_inner) => {
                let ne = Self::remap_bvars(e_inner, depth, map_bvar);
                Expr::from_kind(ExprKind::Proj(name.clone(), *idx, std::sync::Arc::new(ne)))
            }
            ExprKind::MData(md, e_inner) => {
                let ne = Self::remap_bvars(e_inner, depth, map_bvar);
                Expr::from_kind(ExprKind::MData(md.clone(), std::sync::Arc::new(ne)))
            }
            ExprKind::Squash(e_inner) => {
                let ne = Self::remap_bvars(e_inner, depth, map_bvar);
                Expr::from_kind(ExprKind::Squash(std::sync::Arc::new(ne)))
            }
            // Extension variants (SProp, Cubical, etc.) — not expected in ctor field types
            _ => e.clone(),
        }
    }

    /// Recursive BVar remapping for lambda binder domain types.
    ///
    /// Selectively shifts only param BVars (those >= field_idx in the ctor context)
    /// by `extra_above`, leaving earlier-field BVars unchanged.
    fn remap_binder_bvars(&self, e: &Expr, field_idx: usize, extra_above: u32, depth: u32) -> Expr {
        Self::remap_bvars(e, depth, &|idx, depth| {
            if idx < depth {
                // Bound by an inner binder in the field type itself — leave alone
                Expr::bvar(idx)
            } else {
                let ctor_idx = (idx - depth) as usize;
                if ctor_idx < field_idx {
                    // Earlier field reference — maps 1:1 to the outer lambdas
                    Expr::bvar(idx)
                } else {
                    // Param reference — shift by extra_above
                    Expr::bvar(idx + extra_above)
                }
            }
        })
    }

    /// Check if a constructor field type depends on earlier fields.
    ///
    /// Returns true if the field type contains any BVar reference to an
    /// earlier field (BVar(x) where x < field_idx in the ctor's context).
    /// This is used to decide between Eq (independent) and HEq (dependent)
    /// in noConfusionType generation. Lean 4 NoConfusion.lean:45 uses
    /// `isDefEq` at elaboration time; we check structurally at build time.
    fn field_type_is_dependent(e: &Expr, field_idx: usize, depth: u32) -> bool {
        match &e.kind {
            ExprKind::BVar(idx) => {
                if *idx < depth {
                    false // Bound by inner binder
                } else {
                    let ctor_idx = (*idx - depth) as usize;
                    ctor_idx < field_idx // References an earlier field
                }
            }
            ExprKind::App(f, a) => {
                Self::field_type_is_dependent(f, field_idx, depth)
                    || Self::field_type_is_dependent(a, field_idx, depth)
            }
            ExprKind::Pi(_, domain, body) | ExprKind::Lam(_, domain, body) => {
                Self::field_type_is_dependent(domain, field_idx, depth)
                    || Self::field_type_is_dependent(body, field_idx, depth + 1)
            }
            ExprKind::Let(_, ty, val, body, _) => {
                Self::field_type_is_dependent(ty, field_idx, depth)
                    || Self::field_type_is_dependent(val, field_idx, depth)
                    || Self::field_type_is_dependent(body, field_idx, depth + 1)
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                Self::field_type_is_dependent(inner, field_idx, depth)
            }
            _ => false,
        }
    }

    /// Remap a constructor field type for b's fields in the diagonal case.
    ///
    /// Same as `remap_ctor_field_type` but maps earlier field refs to b's
    /// fields instead of a's fields. Used for HEq on dependent field types.
    fn remap_ctor_field_type_for_b(
        &self,
        field_ty: &Expr,
        field_idx: usize,
        np: usize,
        ki: usize,
        kj: usize,
    ) -> Expr {
        self.remap_ctor_bvars_for_b(field_ty, field_idx, np, ki, kj, 0)
    }

    fn remap_ctor_bvars_for_b(
        &self,
        e: &Expr,
        field_idx: usize,
        _np: usize,
        ki: usize,
        kj: usize,
        depth: u32,
    ) -> Expr {
        Self::remap_bvars(e, depth, &|idx, depth| {
            if idx < depth {
                Expr::bvar(idx)
            } else {
                let ctor_idx = (idx - depth) as usize;
                let new_idx = if ctor_idx < field_idx {
                    // Earlier field reference: map to b's field
                    // ctor BVar(x) → b_f_x = BVar(kj - 1 - x)
                    (kj - 1 - ctor_idx) as u32 + depth
                } else {
                    // Param reference (same as a's remapping)
                    let param_offset = ctor_idx - field_idx;
                    (kj + ki + 3 + param_offset) as u32 + depth
                };
                Expr::bvar(new_idx)
            }
        })
    }

    /// Remap a constructor field type's BVar indices from the ctor's Pi chain context
    /// to the noConfusionType diagonal case context.
    ///
    /// In the ctor's Pi chain (after stripping params), field at `field_idx` sees:
    /// - BVar(0)..BVar(field_idx-1) = earlier fields (field_{field_idx-1}..field_0)
    /// - BVar(field_idx)..BVar(field_idx+np-1) = params (param_{np-1}..param_0)
    ///
    /// In the diagonal case body (inside all inner alt lambdas):
    /// - BVar(0)..BVar(kj-1) = b's fields
    /// - BVar(kj)..BVar(kj+ki-1) = a's fields
    /// - BVar(kj+ki) = b, BVar(kj+ki+1) = a, BVar(kj+ki+2) = P
    /// - BVar(kj+ki+3)..BVar(kj+ki+2+np) = params
    ///
    /// We map earlier field refs to a's fields and param refs to params.
    fn remap_ctor_field_type(
        &self,
        field_ty: &Expr,
        field_idx: usize,
        np: usize,
        ki: usize,
        kj: usize,
    ) -> Expr {
        self.remap_ctor_bvars(field_ty, field_idx, np, ki, kj, 0)
    }

    fn remap_ctor_bvars(
        &self,
        e: &Expr,
        field_idx: usize,
        _np: usize,
        ki: usize,
        kj: usize,
        depth: u32,
    ) -> Expr {
        Self::remap_bvars(e, depth, &|idx, depth| {
            if idx < depth {
                // Bound by an inner binder in the field type itself — leave alone
                Expr::bvar(idx)
            } else {
                let ctor_idx = (idx - depth) as usize;
                let new_idx = if ctor_idx < field_idx {
                    // Earlier field reference: map to a's field
                    // ctor BVar(x) → a_f_x = BVar(kj + ki - 1 - x) in outer context
                    (kj + ki - 1 - ctor_idx) as u32 + depth
                } else {
                    // Param reference: BVar(field_idx + p) → BVar(kj + ki + 3 + p)
                    let param_offset = ctor_idx - field_idx;
                    (kj + ki + 3 + param_offset) as u32 + depth
                };
                Expr::bvar(new_idx)
            }
        })
    }

    /// Build noConfusion for an inductive type as a **reducible definition**.
    ///
    /// Following Lean 4 `mkNoConfusionCoreImp`, noConfusion is a definition (not a
    /// recursor). Its value body uses `Eq.ndrec` and `T.casesOn` to produce the
    /// noConfusionType evidence from an equality proof.
    ///
    /// For `inductive Nat | zero | succ (n : Nat)`, generates:
    /// ```text
    /// Nat.noConfusion.{u} : {P : Sort u} → {a b : Nat} → a = b → Nat.noConfusionType P a b
    /// Nat.noConfusion = fun {P} {a} {b} h =>
    ///   @Eq.ndrec Nat a (fun b' => Nat.noConfusionType P a b')
    ///     (@Nat.casesOn (fun x => Nat.noConfusionType P x x) a
    ///       (fun k => k)                     -- zero minor
    ///       (fun n k => k (Eq.refl n)))      -- succ minor
    ///     b h
    /// ```
    ///
    /// Returns `(type, value, level_params)` for registration as a definition.
    ///
    /// Convention dispatch (designs/2026-07-03-noconfusion-ctoridx-convention.md):
    /// `num_params = 0` keeps the classic builder below (byte-identical to the
    /// v4.30 output there, design §1.2/§6-A6); `num_params > 0` routes to the
    /// v4.30 heterogeneous builder (per-param Eq/HEq premises + HEq major).
    pub(crate) fn build_no_confusion(
        &self,
        ind_name: &Name,
        decl: &InductiveDecl,
    ) -> Result<(Expr, Expr, Vec<Name>), EnvError> {
        if decl.num_params == 0 {
            self.build_no_confusion_inner(ind_name, decl, None)
        } else {
            self.build_no_confusion_hetero(ind_name, decl, None)
        }
    }

    /// Build noConfusion with a fallback sort level for fields whose sort
    /// can't be inferred. Part of #3134. Same convention dispatch as
    /// [`Self::build_no_confusion`].
    fn build_no_confusion_with_fallback(
        &self,
        ind_name: &Name,
        decl: &InductiveDecl,
        fallback_level: &Level,
    ) -> Result<(Expr, Expr, Vec<Name>), EnvError> {
        if decl.num_params == 0 {
            self.build_no_confusion_inner(ind_name, decl, Some(fallback_level))
        } else {
            self.build_no_confusion_hetero(ind_name, decl, Some(fallback_level))
        }
    }

    /// Classic builder — `num_params = 0` ONLY (see the dispatch in
    /// [`Self::build_no_confusion`]). Kept verbatim for 0-param byte
    /// invariance (design §6/A6).
    fn build_no_confusion_inner(
        &self,
        ind_name: &Name,
        decl: &InductiveDecl,
        fallback_level: Option<&Level>,
    ) -> Result<(Expr, Expr, Vec<Name>), EnvError> {
        let ind_type = decl
            .types
            .iter()
            .find(|t| &t.name == ind_name)
            .ok_or_else(|| EnvError::UnknownInductive(ind_name.clone()))?;

        // Universe parameter for the result type — freshen to avoid collision.
        let result_univ_name = fresh_univ_name(&decl.level_params);
        let mut level_params = vec![result_univ_name.clone()];
        level_params.extend(decl.level_params.clone());

        let type_arity = count_pi_args(&ind_type.type_);

        let result_univ = Level::param(result_univ_name.clone());
        let ind_const = ind_const_with_levels(ind_name, &decl.level_params);
        let num_params = decl.num_params;

        // Collect parameter binders from the inductive type definition.
        let param_binders = self.collect_pi_binders(&ind_type.type_, num_params);

        // Compute the inductive's sort level (for Eq and Eq.ndrec universe args).
        let ind_sort_level = {
            let mut cur = ind_type.type_.clone();
            for _ in 0..type_arity {
                if let ExprKind::Pi(_, _, body) = &cur.kind {
                    cur = (**body).clone();
                } else {
                    break;
                }
            }
            if let ExprKind::Sort(level) = &cur.kind {
                level.clone()
            } else {
                return Err(EnvError::InductiveCodomainNotSort {
                    name: ind_name.clone(),
                    num_params,
                });
            }
        };
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![ind_sort_level.clone()]);

        // noConfusionType const needs all level params (result_univ + ind levels)
        let mut no_conf_type_levels = vec![Level::param(result_univ_name.clone())];
        no_conf_type_levels.extend(decl.level_params.iter().map(|p| Level::param(p.clone())));
        let no_conf_type_const = Expr::const_(
            Name::from_string(&format!("{ind_name}.noConfusionType")),
            no_conf_type_levels.clone(),
        );

        // ===== Build the TYPE expression (unchanged from before) =====
        // Layout: params(n) | P | a | b | h | result
        //
        // At depth n+3 (h binder): P=bvar(2), a=bvar(1), b=bvar(0)
        // At depth n+4 (result): h=bvar(0), P=bvar(3), a=bvar(2), b=bvar(1)

        let mut ind_applied_a = ind_const.clone();
        for i in 0..num_params {
            ind_applied_a = Expr::app(ind_applied_a, Expr::bvar(num_params - i));
        }

        let mut ind_applied_b = ind_const.clone();
        for i in 0..num_params {
            ind_applied_b = Expr::app(ind_applied_b, Expr::bvar(num_params + 1 - i));
        }

        let mut ind_applied_eq = ind_const.clone();
        for i in 0..num_params {
            ind_applied_eq = Expr::app(ind_applied_eq, Expr::bvar(num_params + 2 - i));
        }

        let eq_ty = Expr::app(
            Expr::app(Expr::app(eq_const, ind_applied_eq), Expr::bvar(1)),
            Expr::bvar(0),
        );

        let mut result_ty = no_conf_type_const.clone();
        for i in 0..num_params {
            result_ty = Expr::app(result_ty, Expr::bvar(num_params + 3 - i));
        }
        result_ty = Expr::app(result_ty, Expr::bvar(3)); // P
        result_ty = Expr::app(result_ty, Expr::bvar(2)); // a
        result_ty = Expr::app(result_ty, Expr::bvar(1)); // b

        let mut no_conf_ty = Expr::pi(
            BinderInfo::Implicit,
            Expr::from_kind(ExprKind::Sort(result_univ.clone())),
            Expr::pi(
                BinderInfo::Implicit,
                ind_applied_a.clone(),
                Expr::pi(
                    BinderInfo::Implicit,
                    ind_applied_b.clone(),
                    Expr::pi(BinderInfo::Default, eq_ty, result_ty),
                ),
            ),
        );

        for (_bi, param_ty) in param_binders.iter().rev() {
            no_conf_ty = Expr::pi(BinderInfo::Implicit, param_ty.clone(), no_conf_ty);
        }

        // ===== Build the VALUE expression (new for #2162) =====
        // Value body (inside the outermost lambdas for params, P, a, b, h):
        //
        //   @Eq.ndrec.{ind_sort, result_univ}
        //     {T params}        -- α
        //     {a}               -- a
        //     {fun b' => noConfusionType params P a b'}  -- motive
        //     (@T.casesOn.{result_univ, ...}
        //       {fun x => noConfusionType params P x x}  -- casesOn motive
        //       minor₁ ... minorₙ                        -- minors
        //       a)                                        -- major
        //     {b}               -- b
        //     h                 -- equality proof
        //
        // De Bruijn layout after binding params(n), P, a, b, h:
        //   h = BVar(0), b = BVar(1), a = BVar(2), P = BVar(3)
        //   p_m = BVar(4), ..., p_1 = BVar(n+3)

        let n = num_params;

        // Helper: build (T p₁...pₘ) at the given extra depth offset from the
        // body context. At offset 0: p_m=BVar(4), ..., p_1=BVar(n+3)
        let build_ind_applied_at = |extra_depth: u32| -> Expr {
            let mut app = ind_const.clone();
            for i in 0..n {
                app = Expr::app(app, Expr::bvar(n + 3 + extra_depth - i));
            }
            app
        };

        // Helper: build (noConfusionType p₁...pₘ P x y) at given depth with given x, y
        let build_nct_app = |extra_depth: u32, p_ref: Expr, x: Expr, y: Expr| -> Expr {
            let mut app = no_conf_type_const.clone();
            for i in 0..n {
                app = Expr::app(app, Expr::bvar(n + 3 + extra_depth - i));
            }
            app = Expr::app(app, p_ref);
            app = Expr::app(app, x);
            Expr::app(app, y)
        };

        // Eq.ndrec motive: fun b' => noConfusionType params P a b'
        // Inside this lambda, b' = BVar(0), h = BVar(1), b = BVar(2),
        // a = BVar(3), P = BVar(4), p_m = BVar(5), ..., p_1 = BVar(n+4)
        let ndrec_motive = Expr::lam(
            BinderInfo::Default,
            build_ind_applied_at(0), // b' : T params (domain)
            build_nct_app(
                1,             // extra depth for b' binding
                Expr::bvar(4), // P
                Expr::bvar(3), // a
                Expr::bvar(0), // b' (the lambda variable)
            ),
        );

        // casesOn motive: fun x => noConfusionType params P x x
        // Inside this lambda, x = BVar(0), h = BVar(1), b = BVar(2),
        // a = BVar(3), P = BVar(4), p_m = BVar(5), ..., p_1 = BVar(n+4)
        let cases_motive = Expr::lam(
            BinderInfo::Default,
            build_ind_applied_at(0), // x : T params (domain)
            build_nct_app(
                1,             // extra depth for x binding
                Expr::bvar(4), // P
                Expr::bvar(0), // x
                Expr::bvar(0), // x (diagonal: noConfusionType P x x)
            ),
        );

        // Build minors for each constructor.
        //
        // The casesOn motive is `fun x => noConfusionType P x x`, so the minor
        // for constructor cᵢ with fields f₁...fₖ has type:
        //   (f₁ : F₁) → ... → (fₖ : Fₖ) → noConfusionType P (cᵢ f...) (cᵢ f...)
        // where noConfusionType for the diagonal case uses:
        //   - Eq fⱼ fⱼ for independent fields (type doesn't reference earlier fields)
        //   - HEq fⱼ fⱼ for dependent fields (type references earlier fields, e.g. Sigma.snd)
        //
        // The minor value is:
        //   fun f₁...fₖ (k : eq₁ → ... → eqₖ → P) => k (refl f₁) ... (refl fₖ)
        // where eqⱼ/reflⱼ use Eq/Eq.refl or HEq/HEq.refl matching noConfusionType.
        //
        // For zero-field constructors: fun (k : P) => k  (identity, type P → P)
        let field_sort_levels: Vec<Vec<Level>> = ind_type
            .constructors
            .iter()
            .map(|ctor| {
                if let Some(fb) = fallback_level {
                    self.compute_ctor_field_sort_levels_with_fallback(
                        &ctor.type_,
                        num_params,
                        &ctor.name,
                        fb,
                    )
                } else {
                    self.compute_ctor_field_sort_levels(&ctor.type_, num_params, &ctor.name)
                }
            })
            .collect::<Result<Vec<_>, EnvError>>()?;

        let minors: Vec<Expr> = ind_type
            .constructors
            .iter()
            .enumerate()
            .map(|(ctor_idx, ctor)| {
                let ctor_arity = count_pi_args(&ctor.type_);
                let num_fields = ctor_arity.saturating_sub(num_params) as usize;
                let sort_levels = &field_sort_levels[ctor_idx];

                // Extract field types from the constructor (skip params).
                // field_types[j] has BVars: BVar(0..j-1) = earlier fields, BVar(j..) = params.
                let field_types: Vec<Expr> = {
                    let mut types = Vec::new();
                    let mut cur = ctor.type_.clone();
                    for idx in 0..ctor_arity {
                        if let ExprKind::Pi(_, domain, body) = &cur.kind {
                            if idx >= num_params {
                                types.push((**domain).clone());
                            }
                            cur = (**body).clone();
                        }
                    }
                    types
                };

                if num_fields == 0 {
                    // Zero-field constructor: fun (k : P) => k
                    // The minor sits at body depth: h=BVar(0), b=BVar(1), a=BVar(2), P=BVar(3).
                    // noConfusionType P zero zero = P → P. A value of this type is fun k:P => k.
                    // k's domain is P = BVar(3).
                    Expr::lam(BinderInfo::Default, Expr::bvar(3), Expr::bvar(0))
                } else {
                    // Multi-field constructor:
                    //   fun f[0]...f[k-1] (k : Eq F₀ f₀ f₀ → ... → P) =>
                    //     k (@Eq.refl F₀ f₀) ... (@Eq.refl F_{k-1} f_{k-1})
                    //
                    // De Bruijn context (body depth where minors are built):
                    //   h=BVar(0), b=BVar(1), a=BVar(2), P=BVar(3), params at BVar(4)...
                    //
                    // After field lambdas f[0]..f[k-1] and k lambda:
                    //   k=BVar(0), f[k-1]=BVar(1), ..., f[0]=BVar(num_fields)
                    //   h=BVar(num_fields+1), b=BVar(num_fields+2), a=BVar(num_fields+3)
                    //   P=BVar(num_fields+4), params at BVar(num_fields+5)...

                    // Step 1: Build innermost body: k (refl f₀) ... (refl f_{k-1})
                    // For independent fields: @Eq.refl.{l} F_j f_j
                    // For dependent fields:   @HEq.refl.{l} F_j f_j
                    let mut body = Expr::bvar(0); // k
                    #[allow(clippy::needless_range_loop)] // j used for de Bruijn arithmetic
                    for j in 0..num_fields {
                        let level = sort_levels[j].clone();
                        if level.is_zero() {
                            continue; // Prop field — skip (proof irrelevance)
                        }
                        // f[j] at body-of-k depth = BVar(num_fields - j)
                        let f_ref = Expr::bvar((num_fields - j) as u32);
                        // Field type at body-of-k depth: compute at field j's lambda
                        // depth (extra_above=4 for h,b,a,P), then lift to body-of-k depth.
                        let ft_at_j =
                            self.lift_ctor_field_type(&field_types[j], j, num_params, 4, 0);
                        let ft_at_body_of_k = ft_at_j.lift((num_fields - j + 1) as u32);

                        let is_dep = Self::field_type_is_dependent(&field_types[j], j, 0);
                        let refl_app = if is_dep {
                            // @HEq.refl.{l} F_j f_j : @HEq.{l} F_j f_j F_j f_j
                            let heq_refl = Expr::const_(Name::from_string("HEq.refl"), vec![level]);
                            Expr::app(Expr::app(heq_refl, ft_at_body_of_k), f_ref)
                        } else {
                            // @Eq.refl.{l} F_j f_j : @Eq.{l} F_j f_j f_j
                            let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![level]);
                            Expr::app(Expr::app(eq_refl, ft_at_body_of_k), f_ref)
                        };
                        body = Expr::app(body, refl_app);
                    }

                    // Step 2: Build k's domain (the eq chain):
                    //   eq₀ → ... → eq_{k-1} → P
                    // where eq_j = Eq F_j f_j f_j (independent) or HEq F_j f_j F_j f_j (dependent)
                    // (non-Prop fields only)
                    //
                    // At k's depth (= num_fields from body):
                    //   f[k-1]=BVar(0), ..., f[0]=BVar(num_fields-1)
                    //   h=BVar(num_fields), b=BVar(num_fields+1), a=BVar(num_fields+2)
                    //   P=BVar(num_fields+3), params at BVar(num_fields+4)...
                    let mut k_domain = Expr::bvar((num_fields + 3) as u32); // P
                    for j in (0..num_fields).rev() {
                        let level = sort_levels[j].clone();
                        if level.is_zero() {
                            continue; // Prop field — not in chain
                        }
                        // f[j] at k depth = BVar(num_fields - 1 - j)
                        let f_at_k = Expr::bvar((num_fields - 1 - j) as u32);
                        // Field type at k depth: compute at field j's lambda depth,
                        // then lift to k depth.
                        let ft_at_j =
                            self.lift_ctor_field_type(&field_types[j], j, num_params, 4, 0);
                        let ft_at_k = ft_at_j.lift((num_fields - j) as u32);

                        let is_dep = Self::field_type_is_dependent(&field_types[j], j, 0);
                        let eq = if is_dep {
                            // Dependent field: @HEq.{l} F_j f_j F_j f_j (diagonal case)
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        Expr::app(
                                            Expr::const_(Name::from_string("HEq"), vec![level]),
                                            ft_at_k.clone(),
                                        ),
                                        f_at_k.clone(),
                                    ),
                                    ft_at_k,
                                ),
                                f_at_k,
                            )
                        } else {
                            // Independent field: @Eq.{l} F_j f_j f_j
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        Expr::const_(Name::from_string("Eq"), vec![level]),
                                        ft_at_k,
                                    ),
                                    f_at_k.clone(),
                                ),
                                f_at_k,
                            )
                        };
                        // Prepend: Pi(eq, shifted_chain)
                        k_domain = Expr::pi(BinderInfo::Default, eq, k_domain.lift(1));
                    }

                    // Step 3: Wrap k lambda
                    body = Expr::lam(BinderInfo::Default, k_domain, body);

                    // Step 4: Wrap field lambdas (inside-out, reverse iteration)
                    // For field j at depth j from body: use lift_ctor_field_type
                    // with extra_above=4 (h,b,a,P binders).
                    for j in (0..num_fields).rev() {
                        let ft = self.lift_ctor_field_type(&field_types[j], j, num_params, 4, 0);
                        body = Expr::lam(BinderInfo::Default, ft, body);
                    }

                    body
                }
            })
            .collect();

        let punit_u = Expr::const_(Name::from_string("PUnit"), vec![result_univ.clone()]);
        let punit_unit_u = Expr::const_(Name::from_string("PUnit.unit"), vec![result_univ.clone()]);
        let cases_on_name = Name::from_string(&format!("{ind_name}.casesOn"));
        let mut cases_levels = vec![Level::param(result_univ_name.clone())];
        cases_levels.extend(decl.level_params.iter().map(|p| Level::param(p.clone())));
        let cases_params: Vec<Expr> = (0..n).map(|i| Expr::bvar(n + 3 - i)).collect();
        let cases_app = self.apply_cases_on_with_restored_padding(
            decl,
            ind_name,
            &cases_on_name,
            &cases_levels,
            &cases_params,
            &cases_motive,
            &minors,
            &Expr::bvar(2),
            &punit_u,
            &punit_unit_u,
        )?;

        // Build Eq.ndrec application:
        //   @Eq.ndrec.{result_univ, ind_sort} {T params} {a} {ndrec_motive} cases_app {b} h
        // Eq.ndrec.{v, u}: v = motive universe, u = type universe
        let eq_ndrec_const = Expr::const_(
            Name::from_string("Eq.ndrec"),
            vec![result_univ.clone(), ind_sort_level.clone()],
        );

        let mut ndrec_app = eq_ndrec_const;
        // {α} = T params (implicit)
        ndrec_app = Expr::app(ndrec_app, build_ind_applied_at(0));
        // {a} (implicit)
        ndrec_app = Expr::app(ndrec_app, Expr::bvar(2));
        // {motive} (implicit)
        ndrec_app = Expr::app(ndrec_app, ndrec_motive);
        // base : motive a = cases_app
        ndrec_app = Expr::app(ndrec_app, cases_app);
        // {b} (implicit)
        ndrec_app = Expr::app(ndrec_app, Expr::bvar(1));
        // h : @Eq (T params) a b
        ndrec_app = Expr::app(ndrec_app, Expr::bvar(0));

        // Wrap value body in lambdas: fun {P} {a} {b} (h) => ndrec_app
        // Build ind_applied for lambda domains (same depths as the type binders).
        let mut val_ind_a = ind_const.clone();
        for i in 0..num_params {
            val_ind_a = Expr::app(val_ind_a, Expr::bvar(num_params - i));
        }
        let mut val_ind_b = ind_const.clone();
        for i in 0..num_params {
            val_ind_b = Expr::app(val_ind_b, Expr::bvar(num_params + 1 - i));
        }
        let mut val_ind_eq = ind_const.clone();
        for i in 0..num_params {
            val_ind_eq = Expr::app(val_ind_eq, Expr::bvar(num_params + 2 - i));
        }
        let val_eq_const = Expr::const_(Name::from_string("Eq"), vec![ind_sort_level.clone()]);
        let val_eq_ty = Expr::app(
            Expr::app(Expr::app(val_eq_const, val_ind_eq), Expr::bvar(1)),
            Expr::bvar(0),
        );

        let mut no_conf_val = Expr::lam(
            BinderInfo::Implicit,
            Expr::from_kind(ExprKind::Sort(result_univ)),
            Expr::lam(
                BinderInfo::Implicit,
                val_ind_a,
                Expr::lam(
                    BinderInfo::Implicit,
                    val_ind_b,
                    Expr::lam(BinderInfo::Default, val_eq_ty, ndrec_app),
                ),
            ),
        );

        // Wrap with parameter lambdas
        for (_bi, param_ty) in param_binders.iter().rev() {
            no_conf_val = Expr::lam(BinderInfo::Implicit, param_ty.clone(), no_conf_val);
        }

        Ok((no_conf_ty, no_conf_val, level_params))
    }

    /// Fix noConfusionType and noConfusion for inductives where these constants
    /// are missing values, have wrong reducibility, or retain blocking
    /// structural-only validation provenance. This handles:
    /// 1. Axiom stubs (no value) from .olean where the kernel couldn't generate
    ///    them during add_inductive due to missing same-module dependencies
    /// 2. Definitions with Regular(0) reducibility from .olean — noConfusionType
    ///    must be Reducible for the type checker to unfold it during WHNF
    /// 3. Kernel-generated pairs whose initial strict check ran before `Eq`
    ///    existed. Generation deliberately leaves those exact payloads marked
    ///    `StructuralOnly`; after equality is available this pass reconstructs
    ///    the canonical pair, rechecks both declarations from scratch, and
    ///    stamps neither unless both checks pass. Part of #3134.
    ///
    /// Returns the names of the `noConfusionType` / `noConfusion` constants this
    /// pass inserted into `self.constants` (1762/1772). Callers on the import path
    /// thread these into the per-load added-name set so the verify-batch
    /// new-constant scan can stay O(new) without missing these auto-generated
    /// constants (they are added here, *after* `register_converted_constants`, so
    /// they appear in no `LoadSummary` otherwise). A superset is harmless — the
    /// consumer dedups against the already-known set.
    pub fn regenerate_missing_no_confusion(&mut self) -> Vec<Name> {
        self.regenerate_missing_no_confusion_with_report()
            .repaired_names
    }

    /// Regenerate noConfusion pairs and retain block-level fail-closed
    /// diagnostics.
    ///
    /// A mutual block is repaired as one transaction. Every candidate is built
    /// before mutation; all old pair payloads and validation stamps are then
    /// snapshotted. `noConfusionType` declarations are checked with every pair
    /// name absent, provisionally installed, and only then are `noConfusion`
    /// declarations checked with every theorem name absent. A single failure
    /// restores every old constant and stamp exactly. Successful replacement is
    /// the only path that advances the environment generation.
    pub fn regenerate_missing_no_confusion_with_report(&mut self) -> NoConfusionRegenerationReport {
        let mut report = NoConfusionRegenerationReport::default();
        let mut seeds: Vec<Name> = self.inductives.keys().cloned().collect();
        seeds.sort();
        let mut visited = HashSet::with_capacity(seeds.len());

        for seed in seeds {
            if visited.contains(&seed) {
                continue;
            }

            let reconstructed = self.reconstruct_no_confusion_block(&seed);
            let decl = match reconstructed {
                Ok(decl) => decl,
                Err(diagnostic) => {
                    // `diagnostic.block` comes from metadata that just failed
                    // validation.  It is useful for reporting, but must not be
                    // allowed to mark unrelated seeds as visited: a corrupted
                    // all_names row could otherwise suppress regeneration of
                    // every valid block it happens to name.
                    visited.insert(seed);
                    report.diagnostics.push(diagnostic);
                    continue;
                }
            };
            let block: Vec<Name> = decl
                .types
                .iter()
                .map(|member| member.name.clone())
                .collect();
            visited.extend(block.iter().cloned());

            // Any damaged member makes the complete mutual block the target.
            // This prevents a singleton reconstruction from changing the
            // declaration context used for one sibling while retaining another.
            if !block
                .iter()
                .any(|member| self.no_confusion_pair_requires_regeneration(member))
            {
                continue;
            }

            if let Some(issue) = self.no_confusion_prerequisite_issue(&decl) {
                report
                    .diagnostics
                    .push(NoConfusionRegenerationDiagnostic { block, issue });
                continue;
            }

            let mut candidates = Vec::with_capacity(decl.types.len());
            let mut generation_issue = None;
            for member in &decl.types {
                match self.build_no_confusion_candidate(&member.name, &decl) {
                    Ok(candidate) => candidates.push(candidate),
                    Err(issue) => {
                        generation_issue = Some(issue);
                        break;
                    }
                }
            }
            if let Some(issue) = generation_issue {
                report
                    .diagnostics
                    .push(NoConfusionRegenerationDiagnostic { block, issue });
                continue;
            }

            match self.install_no_confusion_candidates_transactionally(&candidates, true) {
                Ok(repaired_names) => report.repaired_names.extend(repaired_names),
                Err(issue) => report
                    .diagnostics
                    .push(NoConfusionRegenerationDiagnostic { block, issue }),
            }
        }

        report
    }

    pub(super) fn build_no_confusion_candidate(
        &self,
        member: &Name,
        decl: &InductiveDecl,
    ) -> Result<NoConfusionCandidate, NoConfusionRegenerationIssue> {
        let member_type = decl
            .types
            .iter()
            .find(|candidate| &candidate.name == member)
            .ok_or_else(|| NoConfusionRegenerationIssue::GenerationFailed {
                member: member.clone(),
                detail: "member absent from reconstructed mutual declaration".to_owned(),
            })?;

        let fallback_level = {
            let mut current = member_type.type_.clone();
            for _ in 0..count_pi_args(&member_type.type_) {
                let ExprKind::Pi(_, _, body) = &current.kind else {
                    break;
                };
                current = (**body).clone();
            }
            match &current.kind {
                ExprKind::Sort(level) => Some(level.clone()),
                _ => None,
            }
        };

        let nct_result = self
            .build_no_confusion_type(member, decl)
            .or_else(|first_error| {
                fallback_level
                    .as_ref()
                    .map_or(Err(first_error), |fallback| {
                        self.build_no_confusion_type_with_fallback(member, decl, fallback)
                    })
            });
        let (nct_ty, nct_value, nct_levels) =
            nct_result.map_err(|error| NoConfusionRegenerationIssue::GenerationFailed {
                member: member.clone(),
                detail: format!("noConfusionType: {error}"),
            })?;

        let nc_result = self
            .build_no_confusion(member, decl)
            .or_else(|first_error| {
                fallback_level
                    .as_ref()
                    .map_or(Err(first_error), |fallback| {
                        self.build_no_confusion_with_fallback(member, decl, fallback)
                    })
            });
        let (nc_ty, nc_value, nc_levels) =
            nc_result.map_err(|error| NoConfusionRegenerationIssue::GenerationFailed {
                member: member.clone(),
                detail: format!("noConfusion: {error}"),
            })?;

        let nct_name = Name::from_string(&format!("{member}.noConfusionType"));
        let nc_name = Name::from_string(&format!("{member}.noConfusion"));
        Ok(NoConfusionCandidate {
            member: member.clone(),
            nct_name: nct_name.clone(),
            nc_name: nc_name.clone(),
            nct_decl: Declaration::Definition {
                name: nct_name.clone(),
                level_params: nct_levels.clone(),
                type_: nct_ty.clone(),
                value: nct_value.clone(),
                is_reducible: true,
            },
            nc_decl: Declaration::Definition {
                name: nc_name.clone(),
                level_params: nc_levels.clone(),
                type_: nc_ty.clone(),
                value: nc_value.clone(),
                is_reducible: true,
            },
            nct_const: ConstantInfo::new(nct_name, nct_levels, nct_ty, Some(nct_value), true),
            nc_const: ConstantInfo::new(nc_name, nc_levels, nc_ty, Some(nc_value), true),
        })
    }

    fn restore_no_confusion_snapshots(&mut self, snapshots: &[NoConfusionSnapshot]) {
        for snapshot in snapshots {
            self.constants.remove(&snapshot.name);
            self.declaration_verification.remove(&snapshot.name);
        }
        for snapshot in snapshots {
            if let Some(constant) = &snapshot.constant {
                self.constants
                    .insert(snapshot.name.clone(), constant.clone());
            }
            if let Some(verification) = snapshot.verification {
                self.declaration_verification
                    .insert(snapshot.name.clone(), verification);
            }
        }
    }

    pub(super) fn install_no_confusion_candidates_transactionally(
        &mut self,
        candidates: &[NoConfusionCandidate],
        bump_generation: bool,
    ) -> Result<Vec<Name>, NoConfusionRegenerationIssue> {
        let mut snapshots = Vec::with_capacity(candidates.len() * 2);
        for candidate in candidates {
            for name in [&candidate.nct_name, &candidate.nc_name] {
                snapshots.push(NoConfusionSnapshot {
                    name: name.clone(),
                    constant: self.constants.get(name).cloned(),
                    verification: self.declaration_verification(name),
                });
            }
        }

        // Eager removal is insufficient when the environment has a lazy
        // closure source: `get_const` would otherwise fall through and resolve
        // the old target payload from that source. Mask exactly the target
        // names for the duration of both validation phases while forwarding
        // every unrelated lazy dependency.
        let original_lazy_source = self.lazy_source.take();
        if let Some(source) = &original_lazy_source {
            self.lazy_source = Some(Arc::new(NoConfusionMaskedSource {
                inner: source.clone(),
                masked: snapshots
                    .iter()
                    .map(|snapshot| snapshot.name.clone())
                    .collect(),
            }));
        }

        // Phase 1: no candidate pair name may support its own validation.
        for snapshot in &snapshots {
            self.constants.remove(&snapshot.name);
            self.declaration_verification.remove(&snapshot.name);
        }
        for candidate in candidates {
            if let Err(error) = self.check_decl_readonly_strict(&candidate.nct_decl) {
                self.restore_no_confusion_snapshots(&snapshots);
                self.lazy_source = original_lazy_source;
                return Err(NoConfusionRegenerationIssue::KernelCheckFailed {
                    member: candidate.member.clone(),
                    detail: format!("noConfusionType: {error}"),
                });
            }
        }

        // Phase 2: checked type definitions may support noConfusion, but remain
        // blocking until every theorem in the block succeeds.
        for candidate in candidates {
            self.constants
                .insert(candidate.nct_name.clone(), candidate.nct_const.clone());
            self.declaration_verification.insert(
                candidate.nct_name.clone(),
                DeclarationVerification::StructuralOnly,
            );
        }
        for candidate in candidates {
            if let Err(error) = self.check_decl_readonly_strict(&candidate.nc_decl) {
                self.restore_no_confusion_snapshots(&snapshots);
                self.lazy_source = original_lazy_source;
                return Err(NoConfusionRegenerationIssue::KernelCheckFailed {
                    member: candidate.member.clone(),
                    detail: format!("noConfusion: {error}"),
                });
            }
        }

        let mut repaired_names = Vec::with_capacity(candidates.len() * 2);
        for candidate in candidates {
            self.constants
                .insert(candidate.nc_name.clone(), candidate.nc_const.clone());
            for name in [&candidate.nct_name, &candidate.nc_name] {
                self.declaration_verification
                    .insert(name.clone(), DeclarationVerification::FullKernelCheck);
                repaired_names.push(name.clone());
            }
        }
        self.lazy_source = original_lazy_source;
        if bump_generation {
            self.generation += 1;
        }
        Ok(repaired_names)
    }
}

/// Build a constant lambda over every Pi in `expected`.  `value` lives in the
/// surrounding context, so it is lifted once for each binder introduced.
fn constant_over_pi_telescope(expected: &Expr, value: &Expr) -> Expr {
    match expected.kind() {
        ExprKind::Pi(info, domain, body) => Expr::lam(
            *info,
            domain.as_ref().clone(),
            constant_over_pi_telescope(body, &value.lift(1)),
        ),
        _ => value.clone(),
    }
}

#[cfg(test)]
mod regeneration_tests {
    use super::*;
    use crate::expr::BinderInfo;
    use crate::inductive::InductiveDecl;
    use std::sync::Arc;

    fn even_odd_env() -> (Environment, Vec<Name>) {
        let mut env = Environment::new();
        env.init_punit()
            .expect("PUnit is required by noConfusionType");
        let even = Name::from_string("TxnEven");
        let odd = Name::from_string("TxnOdd");
        let even_ref = Expr::const_(even.clone(), vec![]);
        let odd_ref = Expr::const_(odd.clone(), vec![]);
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![
                InductiveType {
                    name: even.clone(),
                    type_: Expr::type_(),
                    constructors: vec![
                        Constructor {
                            name: Name::from_string("TxnEven.zero"),
                            type_: even_ref.clone(),
                        },
                        Constructor {
                            name: Name::from_string("TxnEven.succ_odd"),
                            type_: Expr::pi(BinderInfo::Default, odd_ref.clone(), even_ref.clone()),
                        },
                    ],
                },
                InductiveType {
                    name: odd.clone(),
                    type_: Expr::type_(),
                    constructors: vec![Constructor {
                        name: Name::from_string("TxnOdd.succ_even"),
                        type_: Expr::pi(BinderInfo::Default, even_ref, odd_ref),
                    }],
                },
            ],
        })
        .expect("declare transactional mutual fixture");
        (env, vec![even, odd])
    }

    fn pair_names(members: &[Name]) -> Vec<Name> {
        members
            .iter()
            .flat_map(|member| {
                [
                    Name::from_string(&format!("{member}.noConfusionType")),
                    Name::from_string(&format!("{member}.noConfusion")),
                ]
            })
            .collect()
    }

    fn assert_constant_exact(actual: &ConstantInfo, expected: &ConstantInfo) {
        assert_eq!(actual.name, expected.name);
        assert_eq!(actual.level_params, expected.level_params);
        assert_eq!(actual.type_, expected.type_);
        assert_eq!(actual.value, expected.value);
        assert_eq!(actual.is_reducible, expected.is_reducible);
        assert_eq!(actual.reducibility, expected.reducibility);
        assert_eq!(actual.kind, expected.kind);
    }

    fn restored_nested_decl() -> (InductiveDecl, Name) {
        let name = Name::from_string("RestoredNc");
        let ty = Expr::const_(name.clone(), vec![]);
        let list_ty = Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            ty.clone(),
        );
        (
            InductiveDecl {
                level_params: vec![],
                num_params: 0,
                types: vec![InductiveType {
                    name: name.clone(),
                    type_: Expr::type_(),
                    constructors: vec![
                        Constructor {
                            name: Name::from_string("RestoredNc.int"),
                            type_: ty.clone(),
                        },
                        Constructor {
                            name: Name::from_string("RestoredNc.vector"),
                            type_: Expr::pi(
                                BinderInfo::Default,
                                Expr::const_(Name::from_string("Nat"), vec![]),
                                ty.clone(),
                            ),
                        },
                        Constructor {
                            name: Name::from_string("RestoredNc.tuple"),
                            type_: Expr::pi(BinderInfo::Default, list_ty, ty),
                        },
                    ],
                }],
            },
            name,
        )
    }

    fn restored_nested_env() -> (Environment, Name) {
        let mut env = Environment::with_prelude();
        let (decl, name) = restored_nested_decl();
        env.add_inductive(decl)
            .expect("declare restored nested noConfusion fixture");
        (env, name)
    }

    fn restored_parameterized_nested_decl() -> (InductiveDecl, Name) {
        let name = Name::from_string("ParamRestoredNc");
        let ind = Expr::const_(name.clone(), vec![]);
        // Π (α : Type), Π (_ : α), Π (_ : List (ParamRestoredNc α)),
        //   ParamRestoredNc α
        let ctor_ty = Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(
                        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
                        Expr::app(ind.clone(), Expr::bvar(1)),
                    ),
                    Expr::app(ind, Expr::bvar(2)),
                ),
            ),
        );
        (
            InductiveDecl {
                level_params: vec![],
                num_params: 1,
                types: vec![InductiveType {
                    name: name.clone(),
                    type_: Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
                    constructors: vec![Constructor {
                        name: Name::from_string("ParamRestoredNc.node"),
                        type_: ctor_ty,
                    }],
                }],
            },
            name,
        )
    }

    fn collect_const_app_arities(expr: &Expr, target: &Name, out: &mut Vec<usize>) {
        let head = expr.get_app_fn();
        if matches!(head.kind(), ExprKind::Const(name, _) if name == target) {
            let args = expr.get_app_args();
            out.push(args.len());
            for arg in args {
                collect_const_app_arities(arg, target, out);
            }
            return;
        }
        match expr.kind() {
            ExprKind::App(f, a) => {
                collect_const_app_arities(f, target, out);
                collect_const_app_arities(a, target, out);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                collect_const_app_arities(ty, target, out);
                collect_const_app_arities(body, target, out);
            }
            ExprKind::Let(_, ty, value, body, _) => {
                collect_const_app_arities(ty, target, out);
                collect_const_app_arities(value, target, out);
                collect_const_app_arities(body, target, out);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                collect_const_app_arities(inner, target, out)
            }
            _ => {}
        }
    }

    #[test]
    fn restored_nested_no_confusion_uses_exact_registered_telescope() {
        let (env, member) = restored_nested_env();
        let cases_name = Name::from_string("RestoredNc.casesOn");
        let cases = env
            .get_recursor(&cases_name)
            .expect("restored casesOn metadata");
        assert_eq!(cases.arg_order, RecursorArgOrder::MajorAfterMotive);
        assert_eq!(cases.num_motives, 2, "primary plus restored List motive");
        assert_eq!(cases.num_minors, 5, "three primary plus nil/cons minors");
        assert!(
            env.get_recursor(&Name::from_string("RestoredNc.rec_1"))
                .is_some(),
            "restored companion recursor must supply the List rule metadata"
        );
        assert_eq!(
            env.get_inductive(&member)
                .expect("restored member")
                .all_names,
            vec![member.clone()],
            "temporary nested member must not leak into restored all_names"
        );

        let tc = TypeChecker::new(&env);
        for suffix in ["noConfusionType", "noConfusion"] {
            let generated = Name::from_string(&format!("{member}.{suffix}"));
            let info = env
                .get_const(&generated)
                .unwrap_or_else(|| panic!("{generated} must be generated"));
            let value = info
                .value
                .as_ref()
                .unwrap_or_else(|| panic!("{generated} must have a value"));
            let inferred = tc
                .infer_type(value)
                .unwrap_or_else(|error| panic!("{generated} value: {error}"));
            assert!(tc.is_def_eq(&inferred, &info.type_));
            assert_eq!(
                env.declaration_verification(&generated),
                Some(DeclarationVerification::FullKernelCheck)
            );

            let mut arities = Vec::new();
            collect_const_app_arities(value, &cases_name, &mut arities);
            assert!(
                !arities.is_empty(),
                "{generated} must eliminate with casesOn"
            );
            assert!(
                arities.iter().all(|arity| *arity == 8),
                "{generated} must apply 2 motives + major + 5 minors exactly, got {arities:?}"
            );
        }
    }

    #[test]
    fn parameterized_restored_nested_no_confusion_uses_exact_registered_telescope() {
        let mut env = Environment::with_prelude();
        let (decl, member) = restored_parameterized_nested_decl();
        env.add_inductive(decl)
            .expect("parameterized nested family must install atomically");

        let cases_name = Name::from_string("ParamRestoredNc.casesOn");
        let cases = env
            .get_recursor(&cases_name)
            .expect("restored parameterized casesOn metadata");
        assert_eq!(cases.arg_order, RecursorArgOrder::MajorAfterMotive);
        assert_eq!(cases.num_motives, 2, "primary plus restored List motive");
        assert_eq!(cases.num_minors, 3, "node plus nil/cons minors");

        let tc = TypeChecker::new(&env);
        for suffix in ["noConfusionType", "noConfusion"] {
            let generated = Name::from_string(&format!("{member}.{suffix}"));
            let info = env
                .get_const(&generated)
                .unwrap_or_else(|| panic!("{generated} must be generated"));
            let value = info
                .value
                .as_ref()
                .unwrap_or_else(|| panic!("{generated} must have a value"));
            let inferred = tc
                .infer_type(value)
                .unwrap_or_else(|error| panic!("{generated} value: {error}"));
            assert!(tc.is_def_eq(&inferred, &info.type_));
            assert_eq!(
                env.declaration_verification(&generated),
                Some(DeclarationVerification::FullKernelCheck)
            );

            let mut arities = Vec::new();
            collect_const_app_arities(value, &cases_name, &mut arities);
            assert!(
                !arities.is_empty(),
                "{generated} must eliminate with casesOn"
            );
            assert!(
                arities.iter().all(|arity| *arity == 7),
                "{generated} must apply param + 2 motives + major + 3 minors exactly, got {arities:?}"
            );
        }
    }

    #[test]
    fn restored_nested_malformed_minor_metadata_fails_with_diagnostic() {
        let (mut env, member) = restored_nested_env();
        for suffix in ["noConfusionType", "noConfusion"] {
            let name = Name::from_string(&format!("{member}.{suffix}"));
            env.constants.remove(&name);
            env.declaration_verification.remove(&name);
        }
        env.recursors
            .get_mut(&Name::from_string("RestoredNc.casesOn"))
            .expect("casesOn metadata")
            .num_minors += 1;

        let generation_before = env.generation();
        let report = env.regenerate_missing_no_confusion_with_report();
        assert!(report.repaired_names.is_empty());
        assert!(
            report.diagnostics.iter().any(|diagnostic| {
                diagnostic.block == vec![member.clone()]
                    && matches!(
                        &diagnostic.issue,
                        NoConfusionRegenerationIssue::GenerationFailed { member: failed, detail }
                            if failed == &member
                                && detail.contains("restored companion")
                                && detail.contains("RestoredNc.rec_2")
                    )
            }),
            "malformed restored metadata must be reported explicitly: {report:#?}"
        );
        assert_eq!(env.generation(), generation_before);
        for suffix in ["noConfusionType", "noConfusion"] {
            assert!(
                env.get_const(&Name::from_string(&format!("{member}.{suffix}")))
                    .is_none(),
                "failed block must remain transactionally absent"
            );
        }
    }

    #[test]
    fn restored_nested_occupied_no_confusion_target_rolls_back_complete_family() {
        for suffix in ["noConfusionType", "noConfusion"] {
            let mut env = Environment::with_prelude();
            let (decl, member) = restored_nested_decl();
            let occupied = Name::from_string(&format!("{member}.{suffix}"));
            env.add_decl(Declaration::Axiom {
                name: occupied.clone(),
                level_params: vec![],
                type_: Expr::prop(),
            })
            .expect("predeclare colliding target");
            let occupied_before = env.get_const(&occupied).expect("occupied target").clone();
            let verification_before = env.declaration_verification(&occupied);
            let generation_before = env.generation();

            let error = env
                .add_inductive(decl)
                .expect_err("occupied generated target must reject nested registration");
            assert!(
                matches!(
                    &error,
                    EnvError::Inductive(InductiveError::NestedRestoreInvariant(detail))
                        if detail.contains("already occupied") && detail.contains(&occupied.to_string())
                ),
                "occupied target must produce a precise invariant error: {error:?}"
            );
            assert_eq!(env.generation(), generation_before);
            assert!(env.get_inductive(&member).is_none());
            for leaked in [
                "RestoredNc.int",
                "RestoredNc.vector",
                "RestoredNc.tuple",
                "RestoredNc.rec",
                "RestoredNc.rec_1",
                "RestoredNc.casesOn",
            ] {
                let leaked = Name::from_string(leaked);
                assert!(
                    env.get_const(&leaked).is_none() && env.get_recursor(&leaked).is_none(),
                    "failed nested registration leaked {leaked}"
                );
            }
            assert_constant_exact(
                env.get_const(&occupied)
                    .expect("rollback must preserve occupied target"),
                &occupied_before,
            );
            assert_eq!(env.declaration_verification(&occupied), verification_before);
        }
    }

    #[test]
    fn restored_nested_occupied_companion_recursor_rolls_back_complete_family() {
        for core_only in [false, true] {
            let mut env = Environment::with_prelude();
            let (decl, member) = restored_nested_decl();
            let occupied = Name::from_string("RestoredNc.rec_1");
            env.add_decl(Declaration::Axiom {
                name: occupied.clone(),
                level_params: vec![],
                type_: Expr::prop(),
            })
            .expect("predeclare colliding companion recursor target");
            let occupied_before = env.get_const(&occupied).expect("occupied target").clone();
            let verification_before = env.declaration_verification(&occupied);
            let origin_before = env.get_constant_origin(&occupied).cloned();
            let generation_before = env.generation();

            let error = if core_only {
                env.add_inductive_core(decl)
            } else {
                env.add_inductive(decl)
            }
            .expect_err("occupied restored companion target must reject registration");
            assert!(
                matches!(&error, EnvError::DuplicateName(name) if name == &occupied),
                "restore collision must retain its precise diagnostic: {error:?}"
            );
            assert_eq!(env.generation(), generation_before);
            assert!(env.get_inductive(&member).is_none());
            for leaked in [
                "RestoredNc.int",
                "RestoredNc.vector",
                "RestoredNc.tuple",
                "RestoredNc.rec",
                "RestoredNc.casesOn",
                "RestoredNc.recOn",
                "RestoredNc.noConfusionType",
                "RestoredNc.noConfusion",
            ] {
                let leaked = Name::from_string(leaked);
                assert!(
                    env.get_const(&leaked).is_none()
                        && env.get_inductive(&leaked).is_none()
                        && env.get_constructor(&leaked).is_none()
                        && env.get_recursor(&leaked).is_none(),
                    "failed nested registration leaked {leaked} (core_only={core_only})"
                );
            }
            assert!(
                !env.constants
                    .keys()
                    .chain(env.inductives.keys())
                    .chain(env.constructors.keys())
                    .chain(env.recursors.keys())
                    .any(|name| name.to_string().starts_with("_nested.")),
                "failed restore must erase every transformed registration (core_only={core_only})"
            );
            assert_constant_exact(
                env.get_const(&occupied)
                    .expect("rollback must preserve occupied target"),
                &occupied_before,
            );
            assert_eq!(env.declaration_verification(&occupied), verification_before);
            assert_eq!(env.get_constant_origin(&occupied), origin_before.as_ref());
        }
    }

    #[test]
    fn restored_nested_malformed_motive_metadata_fails_with_diagnostic() {
        let (mut env, member) = restored_nested_env();
        for suffix in ["noConfusionType", "noConfusion"] {
            let name = Name::from_string(&format!("{member}.{suffix}"));
            env.constants.remove(&name);
            env.declaration_verification.remove(&name);
        }
        env.recursors
            .get_mut(&Name::from_string("RestoredNc.casesOn"))
            .expect("casesOn metadata")
            .num_motives = 0;

        let generation_before = env.generation();
        let report = env.regenerate_missing_no_confusion_with_report();
        assert!(report.repaired_names.is_empty());
        assert!(
            report.diagnostics.iter().any(|diagnostic| {
                diagnostic.block == vec![member.clone()]
                    && matches!(
                        &diagnostic.issue,
                        NoConfusionRegenerationIssue::GenerationFailed { member: failed, detail }
                            if failed == &member
                                && detail.contains("target position 0")
                                && detail.contains("motive count is 0")
                    )
            }),
            "malformed motive metadata must be reported explicitly: {report:#?}"
        );
        assert_eq!(env.generation(), generation_before);
        for suffix in ["noConfusionType", "noConfusion"] {
            assert!(
                env.get_const(&Name::from_string(&format!("{member}.{suffix}")))
                    .is_none(),
                "failed block must remain transactionally absent"
            );
        }
    }

    #[test]
    fn wrong_kind_and_reducibility_use_canonical_checked_block_transaction() {
        let (mut env, members) = even_odd_env();
        env.init_eq().expect("initialize equality and heal fixture");

        let sabotaged = Name::from_string("TxnEven.noConfusionType");
        let entry = env
            .constants
            .get_mut(&sabotaged)
            .expect("generated noConfusionType");
        entry.kind = ConstantKind::Theorem;
        entry.reducibility = Reducibility::Opaque;
        entry.is_reducible = false;

        let generation_before = env.generation();
        let report = env.regenerate_missing_no_confusion_with_report();
        assert_eq!(
            report.repaired_names,
            pair_names(&members),
            "one damaged member must regenerate the complete ordered block; diagnostics: {:#?}",
            report.diagnostics
        );
        assert_eq!(env.generation(), generation_before + 1);
        for name in pair_names(&members) {
            let constant = env.constants.get(&name).expect("canonical replacement");
            assert_eq!(constant.kind, ConstantKind::Definition);
            assert!(constant.is_reducible);
            assert_eq!(constant.reducibility, Reducibility::Reducible);
            assert_eq!(
                env.declaration_verification(&name),
                Some(DeclarationVerification::FullKernelCheck)
            );
        }
    }

    #[test]
    fn unknown_verification_provenance_repairs_the_complete_block() {
        let (mut env, members) = even_odd_env();
        env.init_eq().expect("initialize equality and heal fixture");
        let unstamped = Name::from_string("TxnOdd.noConfusion");
        env.declaration_verification.remove(&unstamped);

        let generation_before = env.generation();
        let report = env.regenerate_missing_no_confusion_with_report();
        assert_eq!(report.repaired_names, pair_names(&members));
        assert_eq!(env.generation(), generation_before + 1);
        for name in pair_names(&members) {
            assert_eq!(
                env.declaration_verification(&name),
                Some(DeclarationVerification::FullKernelCheck),
                "unknown provenance on one member must recheck the whole block"
            );
        }
    }

    #[test]
    fn invalid_all_names_cannot_suppress_an_unrelated_repair() {
        let (mut env, members) = even_odd_env();
        env.init_eq().expect("initialize equality and heal fixture");

        let independent = Name::from_string("ZIndependent");
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: independent.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("ZIndependent.mk"),
                    type_: Expr::const_(independent.clone(), vec![]),
                }],
            }],
        })
        .expect("declare independent repair target");
        let independent_nc = Name::from_string("ZIndependent.noConfusion");
        env.constants.remove(&independent_nc);
        env.declaration_verification.remove(&independent_nc);

        // Poison the lexicographically earlier block with an unrelated name.
        // A failed block's untrusted report list must not mark that unrelated
        // seed as visited.
        env.inductives
            .get_mut(&members[0])
            .expect("first mutual member")
            .all_names = vec![members[0].clone(), independent.clone()];

        let report = env.regenerate_missing_no_confusion_with_report();
        assert!(report.diagnostics.iter().any(|diagnostic| {
            matches!(
                diagnostic.issue,
                NoConfusionRegenerationIssue::InvalidBlockMetadata { .. }
            )
        }));
        assert!(report
            .repaired_names
            .contains(&Name::from_string("ZIndependent.noConfusionType")));
        assert!(report.repaired_names.contains(&independent_nc));
        assert_eq!(
            env.declaration_verification(&independent_nc),
            Some(DeclarationVerification::FullKernelCheck)
        );
    }

    #[test]
    fn failed_mutual_install_restores_every_payload_and_stamp_without_generation_bump() {
        let (mut env, members) = even_odd_env();
        env.init_eq().expect("initialize equality and heal fixture");
        let decl = env
            .reconstruct_no_confusion_block(&members[0])
            .expect("reconstruct complete mutual block");
        let candidates: Vec<_> = members
            .iter()
            .map(|member| {
                env.build_no_confusion_candidate(member, &decl)
                    .expect("build canonical candidate before dependency sabotage")
            })
            .collect();
        let names = pair_names(&members);
        let old: Vec<_> = names
            .iter()
            .map(|name| {
                (
                    name.clone(),
                    env.constants.get(name).expect("old pair member").clone(),
                    env.declaration_verification(name),
                )
            })
            .collect();

        // Make the already-built noConfusion theorem candidates fail their
        // fresh check after noConfusionType has been provisionally installed.
        // The transaction must restore both siblings, not merely the member
        // whose check observes the poisoned dependency.
        env.constants
            .get_mut(&Name::from_string("Eq.ndrec"))
            .expect("Eq.ndrec")
            .type_ = Expr::prop();
        let generation_before = env.generation();
        let error = env
            .install_no_confusion_candidates_transactionally(&candidates, true)
            .expect_err("poisoned Eq.ndrec must reject the transaction");
        assert!(matches!(
            error,
            NoConfusionRegenerationIssue::KernelCheckFailed { .. }
        ));
        assert_eq!(env.generation(), generation_before);
        for (name, expected_constant, expected_verification) in old {
            assert_constant_exact(
                env.constants.get(&name).expect("rolled-back pair member"),
                &expected_constant,
            );
            assert_eq!(env.declaration_verification(&name), expected_verification);
        }
    }

    #[test]
    fn indexed_block_is_excluded_initially_and_reported_without_mutation() {
        let mut env = Environment::new();
        env.init_nat().expect("initialize Nat");
        env.init_eq().expect("initialize Eq");
        let indexed = Name::from_string("UnsupportedIndexed");
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: indexed.clone(),
                type_: Expr::pi(BinderInfo::Default, nat, Expr::type_()),
                constructors: vec![Constructor {
                    name: Name::from_string("UnsupportedIndexed.zero"),
                    type_: Expr::app(
                        Expr::const_(indexed.clone(), vec![]),
                        Expr::const_(Name::from_string("Nat.zero"), vec![]),
                    ),
                }],
            }],
        })
        .expect("declare indexed fixture");
        for suffix in ["noConfusionType", "noConfusion"] {
            assert!(
                env.get_const(&Name::from_string(&format!("{indexed}.{suffix}")))
                    .is_none(),
                "unsupported indexed pairs must not be generated initially"
            );
        }

        let generation_before = env.generation();
        let report = env.regenerate_missing_no_confusion_with_report();
        assert!(report.diagnostics.iter().any(|diagnostic| {
            diagnostic.block == vec![indexed.clone()]
                && matches!(
                    &diagnostic.issue,
                    NoConfusionRegenerationIssue::Indexed { member }
                        if member == &indexed
                )
        }));
        assert_eq!(env.generation(), generation_before);
    }

    #[test]
    fn one_path_constructor_excludes_the_complete_mutual_block() {
        let plain = Name::from_string("MixedPlain");
        let hit = Name::from_string("MixedHit");
        let decl = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![
                InductiveType {
                    name: plain.clone(),
                    type_: Expr::type_(),
                    constructors: vec![Constructor {
                        name: Name::from_string("MixedPlain.mk"),
                        type_: Expr::const_(plain, vec![]),
                    }],
                },
                InductiveType {
                    name: hit.clone(),
                    type_: Expr::type_(),
                    constructors: vec![Constructor {
                        name: Name::from_string("MixedHit.loop"),
                        type_: Expr::from_kind(ExprKind::CubicalPath {
                            ty: Arc::new(Expr::type_()),
                            left: Arc::new(Expr::const_(hit.clone(), vec![])),
                            right: Arc::new(Expr::const_(hit.clone(), vec![])),
                        }),
                    }],
                },
            ],
        };
        assert_eq!(
            Environment::no_confusion_block_eligibility(&decl),
            Err(NoConfusionRegenerationIssue::HigherInductive { member: hit })
        );
    }

    #[test]
    fn inconsistent_mutual_order_fails_before_mutation() {
        let (mut env, members) = even_odd_env();
        env.init_eq().expect("initialize equality and heal fixture");
        let names = pair_names(&members);
        let old: Vec<_> = names
            .iter()
            .map(|name| {
                (
                    name.clone(),
                    env.constants.get(name).expect("old pair member").clone(),
                    env.declaration_verification(name),
                )
            })
            .collect();
        env.inductives
            .get_mut(&members[1])
            .expect("second mutual member")
            .all_names
            .reverse();

        let generation_before = env.generation();
        let report = env.regenerate_missing_no_confusion_with_report();
        assert!(report.diagnostics.iter().any(|diagnostic| {
            diagnostic.block == members
                && matches!(
                    diagnostic.issue,
                    NoConfusionRegenerationIssue::InvalidBlockMetadata { .. }
                )
        }));
        assert_eq!(env.generation(), generation_before);
        for (name, expected_constant, expected_verification) in old {
            assert_constant_exact(
                env.constants.get(&name).expect("unchanged pair member"),
                &expected_constant,
            );
            assert_eq!(env.declaration_verification(&name), expected_verification);
        }
    }
}
