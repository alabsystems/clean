// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Inductive, constructor, and recursor registration methods.
//!
//! Extracted from env/mod.rs for maintainability (see #307).
//! Contains register/extend methods for inductives, constructors, recursors,
//! and structure field management.

use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::inductive::{ConstructorVal, InductiveVal, RecursorArgOrder, RecursorRule, RecursorVal};
use crate::level::Level;
use crate::name::Name;
use crate::tc::{LocalContext, TypeChecker};
use std::collections::HashSet;
use std::sync::Arc;

use super::stub_upgrade_parallel::{SpeculativeVerdict, StubVerdict};
use super::types::{ConstantInfo, EnvError};
use super::Environment;

/// Open the next Pi binder in `cursor` as a fresh local, instantiate the
/// telescope body with that local, and return its expression.
fn open_recursor_local(
    cursor: &mut Expr,
    ctx: &mut LocalContext,
    label: &str,
) -> Result<Expr, String> {
    let (binder, domain, body) = match cursor.kind() {
        ExprKind::Pi(binder, domain, body) => (*binder, (**domain).clone(), (**body).clone()),
        _ => return Err(format!("telescope ended before {label}")),
    };
    let local = Expr::fvar(ctx.push(Name::from_string(label), domain, binder));
    *cursor = body.instantiate(&local);
    Ok(local)
}

/// Instantiate the next Pi binder in `cursor` with an already-built argument.
/// Returns the binder domain before instantiation for diagnostics/checking.
fn instantiate_recursor_arg(cursor: &mut Expr, arg: &Expr, label: &str) -> Result<Expr, String> {
    let (domain, body) = match cursor.kind() {
        ExprKind::Pi(_, domain, body) => ((**domain).clone(), (**body).clone()),
        _ => return Err(format!("telescope ended before {label}")),
    };
    *cursor = body.instantiate(arg);
    Ok(domain)
}

impl Environment {
    /// Clone the environment and remove any declarations shadowed by a read-only overlay.
    ///
    /// The clone preserves all other environment payloads (quotients, persistent
    /// extensions, reducibility metadata, registries, mode) while pruning the
    /// names the overlay intends to redefine. This keeps the shadowing logic in
    /// the kernel so downstream crates do not need to replay environment internals.
    pub(crate) fn clone_pruned_shadowing_overlay(&self, shadowed_names: &HashSet<Name>) -> Self {
        let mut overlay = self.clone();
        if shadowed_names.is_empty() {
            return overlay;
        }

        for name in shadowed_names {
            overlay.remove_resident_constant(name);
        }
        overlay
            .constant_origins
            .retain(|name, _| !shadowed_names.contains(name));
        overlay
            .declaration_verification
            .retain(|name, _| !shadowed_names.contains(name));
        overlay
            .inductives
            .retain(|name, _| !shadowed_names.contains(name));
        overlay
            .constructors
            .retain(|name, _| !shadowed_names.contains(name));
        overlay
            .recursors
            .retain(|name, _| !shadowed_names.contains(name));

        // Keep auxiliary registries consistent with the declaration tables above.
        overlay
            .structure_fields
            .retain(|name, _| !shadowed_names.contains(name));
        overlay
            .classes
            .retain(|name, _| !shadowed_names.contains(name));
        overlay.instances.retain(|class_name, infos| {
            if shadowed_names.contains(class_name) {
                return false;
            }
            infos.retain(|info| {
                !shadowed_names.contains(&info.name) && !shadowed_names.contains(&info.class_name)
            });
            !infos.is_empty()
        });
        overlay
            .instance_names
            .retain(|name| !shadowed_names.contains(name));
        overlay
            .instance_seqs
            .retain(|name, _| !shadowed_names.contains(name));
        overlay
            .param_names
            .retain(|name, _| !shadowed_names.contains(name));
        overlay
            .typed_param_names
            .retain(|name, _| !shadowed_names.contains(name));
        overlay
            .param_binder_infos
            .retain(|name, _| !shadowed_names.contains(name));
        overlay.generation += 1;

        overlay
    }

    /// Validate cross-table recursor metadata invariants.
    ///
    /// This checks consistency between:
    /// - `RecursorVal` binder metadata
    /// - `RecursorRule` field metadata
    /// - `ConstructorVal` arity metadata
    ///
    /// The checks mirror the assumptions used by iota and K reductions in
    /// `tc/mod.rs`, so metadata drift fails fast in tests/debug builds.
    pub(crate) fn validate_recursor_metadata(&self, name: &Name) -> Result<(), String> {
        let rec = self
            .get_recursor(name)
            .ok_or_else(|| format!("unknown recursor `{name}`"))?;
        if rec.name != *name {
            return Err(format!(
                "recursor registry key `{name}` contains packet `{}`",
                rec.name
            ));
        }
        rec.validate_metadata()?;
        if rec.num_motives == 0 {
            return Err(format!("{}: recursor declares no motives", rec.name));
        }

        let constant = self
            .get_const(name)
            .ok_or_else(|| format!("{}: missing constant-table entry", rec.name))?;
        if constant.name != *name
            || constant.kind != super::ConstantKind::Definition
            || constant.level_params != rec.level_params
            || constant.type_ != rec.type_
        {
            return Err(format!(
                "{}: constant/recursor kind, universes, or type disagree",
                rec.name
            ));
        }

        let major_inductive_name = rec.major_induct().ok_or_else(|| {
            format!(
                "{}: recursor type does not expose a constant-headed major premise",
                rec.name
            )
        })?;
        let ind = self.get_inductive(major_inductive_name).ok_or_else(|| {
            format!(
                "{}: missing inductive metadata for {}",
                rec.name, major_inductive_name
            )
        })?;

        // For mutual inductives, each per-type recursor has rules for only its
        // own constructors, but num_minors is the total across all types.
        // For non-mutual, rules.len() == num_minors == constructor_names.len().
        if rec.num_motives == 1 {
            // Non-mutual: rules count must match num_minors exactly
            if rec.rules.len() != rec.num_minors as usize {
                return Err(format!(
                    "{}: {} rules but num_minors={}",
                    rec.name,
                    rec.rules.len(),
                    rec.num_minors
                ));
            }
        } else {
            // Mutual: rules.len() <= num_minors (this type's ctors vs total)
            if rec.rules.len() > rec.num_minors as usize {
                return Err(format!(
                    "{}: {} rules exceeds num_minors={} (mutual inductive)",
                    rec.name,
                    rec.rules.len(),
                    rec.num_minors
                ));
            }
        }

        // Each recursor has one rule for every constructor of its MAJOR
        // inductive.  Ordinarily the major inductive equals `inductive_name`;
        // restored nested companions (`T.rec_N`) retain the family head in
        // `inductive_name` but eliminate a container such as `List`/`Array`.
        if rec.rules.len() != ind.constructor_names.len() {
            return Err(format!(
                "{}: {} rules but inductive {} has {} constructors",
                rec.name,
                rec.rules.len(),
                major_inductive_name,
                ind.constructor_names.len()
            ));
        }

        let expected_constructors: HashSet<&Name> = ind.constructor_names.iter().collect();
        let mut seen_constructors = HashSet::with_capacity(rec.rules.len());
        for (rule_idx, rule) in rec.rules.iter().enumerate() {
            if !seen_constructors.insert(&rule.constructor_name) {
                return Err(format!(
                    "{}: duplicate rule for constructor {}",
                    rec.name, rule.constructor_name
                ));
            }
            if !expected_constructors.contains(&rule.constructor_name) {
                return Err(format!(
                    "{}: rule {} references constructor {} outside major inductive {}",
                    rec.name, rule_idx, rule.constructor_name, major_inductive_name
                ));
            }
            let expected_constructor = &ind.constructor_names[rule_idx];
            if &rule.constructor_name != expected_constructor {
                return Err(format!(
                    "{}: rule {} names constructor {}, but canonical declaration order requires {}",
                    rec.name, rule_idx, rule.constructor_name, expected_constructor
                ));
            }

            let ctor = self
                .get_constructor(&rule.constructor_name)
                .ok_or_else(|| {
                    format!(
                        "{}: rule {} references unknown constructor {}",
                        rec.name, rule_idx, rule.constructor_name
                    )
                })?;

            // Rules are keyed to the major premise's constructors.  This is
            // deliberately not `rec.inductive_name` for restored `rec_N`.
            if &ctor.inductive_name != major_inductive_name {
                return Err(format!(
                    "{}: rule {} references constructor {} of {}, expected {}",
                    rec.name, rule_idx, ctor.name, ctor.inductive_name, major_inductive_name
                ));
            }

            // Iota slices the final `rule.num_fields` arguments from the
            // constructor application.  Constructor metadata already accounts
            // for fixed-index promotion, and unlike `rec.num_params` it remains
            // authoritative for container-major restored companions.
            if rule.num_fields != ctor.num_fields {
                return Err(format!(
                    "{}: rule for {} has num_fields={} but constructor metadata expects {}",
                    rec.name, rule.constructor_name, rule.num_fields, ctor.num_fields
                ));
            }
            if rule.recursive_fields.len() != ctor.num_fields as usize {
                return Err(format!(
                    "{}: rule for {} has {} recursive-field flags but constructor metadata expects {}",
                    rec.name,
                    rule.constructor_name,
                    rule.recursive_fields.len(),
                    ctor.num_fields
                ));
            }
        }

        if seen_constructors.len() != expected_constructors.len() {
            let missing = ind
                .constructor_names
                .iter()
                .find(|name| !seen_constructors.contains(name))
                .expect("different equal-sized constructor sets must have a missing member");
            return Err(format!(
                "{}: missing rule for constructor {}",
                rec.name, missing
            ));
        }

        Ok(())
    }

    /// Authenticate a recursor packet without mutating verification provenance.
    ///
    /// Imported recursors enter through trusted registration and therefore may
    /// not carry `DeclarationVerification::FullKernelCheck`. Consumers that
    /// treat their side-table data as executable reduction authority must still
    /// establish the complete invariant locally: registry/constant coherence,
    /// canonical constructor rule order, and subject reduction for every stored
    /// iota RHS. This read-only entry point centralizes that boundary so callers
    /// cannot accidentally reproduce only a subset of it.
    ///
    /// The operation is intentionally side-effect free. High-frequency callers
    /// should cache its result for the lifetime of their immutable environment
    /// borrow.
    pub fn authenticate_recursor_readonly(&self, name: &Name) -> Result<(), String> {
        self.validate_recursor_metadata(name)?;
        self.validate_recursor_rule_payloads(name)
    }

    /// Prove subject reduction for every iota rule carried by `rec`.
    ///
    /// For each constructor this builds a symbolic, well-typed saturated
    /// recursor application in a fresh local context.  The constructor's return
    /// indices are fed to the recursor, its constructor application is used as
    /// the major premise, and the kernel infers the expected result type.  We
    /// then beta-apply the exact stored rule RHS in the same canonical order as
    /// `try_iota_reduction` (params, motives, minors, fields), reapply the
    /// interval argument for HIT path constructors, and require the reduced
    /// payload to check against that expected type.
    ///
    /// This is intentionally independent of the recursor builder: a corrupted
    /// or mechanically restored RHS cannot earn `FullKernelCheck` merely because
    /// its surrounding recursor type is well formed.
    fn validate_recursor_rule_subject_reduction(
        &self,
        rec: &RecursorVal,
        rule_idx: usize,
        rule: &RecursorRule,
    ) -> Result<(), String> {
        if !rule.rhs.is_lam() {
            return Err(format!(
                "{}: rule {} for {} has a non-lambda RHS",
                rec.name, rule_idx, rule.constructor_name
            ));
        }

        let major_inductive_name = rec
            .major_induct()
            .cloned()
            .ok_or_else(|| format!("{}: cannot identify major inductive", rec.name))?;
        let major_inductive = self.get_inductive(&major_inductive_name).ok_or_else(|| {
            format!(
                "{}: missing major inductive {major_inductive_name}",
                rec.name
            )
        })?;
        if rec.num_indices != major_inductive.num_indices {
            return Err(format!(
                "{}: num_indices={} disagrees with major inductive {} num_indices={}",
                rec.name, rec.num_indices, major_inductive_name, major_inductive.num_indices
            ));
        }

        let ctor = self
            .get_constructor(&rule.constructor_name)
            .ok_or_else(|| {
                format!(
                    "{}: missing constructor {}",
                    rec.name, rule.constructor_name
                )
            })?;
        if ctor.num_params != major_inductive.num_params {
            return Err(format!(
                "{}: constructor {} num_params={} disagrees with major inductive {} num_params={}",
                rec.name,
                ctor.name,
                ctor.num_params,
                major_inductive_name,
                major_inductive.num_params
            ));
        }

        let rec_levels: Vec<Level> = rec
            .level_params
            .iter()
            .map(|name| Level::param(name.clone()))
            .collect();
        let mut rec_application = Expr::const_(rec.name.clone(), rec_levels.clone());
        let mut cursor = rec.type_.clone();
        let mut ctx = LocalContext::new();

        let mut params = Vec::with_capacity(rec.num_params as usize);
        for index in 0..rec.num_params {
            let arg = open_recursor_local(
                &mut cursor,
                &mut ctx,
                &format!("{}_rule_{rule_idx}_param_{index}", rec.name),
            )?;
            rec_application = Expr::app(rec_application, arg.clone());
            params.push(arg);
        }

        let mut motives = Vec::with_capacity(rec.num_motives as usize);
        for index in 0..rec.num_motives {
            let arg = open_recursor_local(
                &mut cursor,
                &mut ctx,
                &format!("{}_rule_{rule_idx}_motive_{index}", rec.name),
            )?;
            rec_application = Expr::app(rec_application, arg.clone());
            motives.push(arg);
        }

        let mut minors = Vec::with_capacity(rec.num_minors as usize);
        if rec.arg_order == RecursorArgOrder::MajorAfterMinors {
            for index in 0..rec.num_minors {
                let arg = open_recursor_local(
                    &mut cursor,
                    &mut ctx,
                    &format!("{}_rule_{rule_idx}_minor_{index}", rec.name),
                )?;
                rec_application = Expr::app(rec_application, arg.clone());
                minors.push(arg);
            }
        }

        // Preview the major domain after symbolic index locals solely to read
        // the major type's universe arguments and parameter spine.  Index
        // locals from the preview are discarded; the actual recursor receives
        // the constructor return indices below.
        let mut preview_cursor = cursor.clone();
        let mut preview_ctx = ctx.clone();
        for index in 0..rec.num_indices {
            let _ = open_recursor_local(
                &mut preview_cursor,
                &mut preview_ctx,
                &format!("{}_rule_{rule_idx}_preview_index_{index}", rec.name),
            )?;
        }
        let preview_major_domain = match preview_cursor.kind() {
            ExprKind::Pi(_, domain, _) => (**domain).clone(),
            _ => {
                return Err(format!(
                    "{}: telescope ended before rule {} major premise",
                    rec.name, rule_idx
                ))
            }
        };
        let (preview_major_name, major_levels) = match preview_major_domain.get_app_fn().kind() {
            ExprKind::Const(name, levels) => (name.clone(), levels.to_vec()),
            _ => {
                return Err(format!(
                    "{}: rule {} major premise is not constant-headed",
                    rec.name, rule_idx
                ))
            }
        };
        if preview_major_name != major_inductive_name {
            return Err(format!(
                "{}: rule {} major premise names {}, expected {}",
                rec.name, rule_idx, preview_major_name, major_inductive_name
            ));
        }
        if ctor.level_params != major_inductive.level_params {
            return Err(format!(
                "{}: constructor {} universe parameters disagree with major inductive {}",
                rec.name, ctor.name, major_inductive_name
            ));
        }
        if major_levels.len() != major_inductive.level_params.len() {
            return Err(format!(
                "{}: major inductive {} expects {} universe arguments, major premise supplies {}",
                rec.name,
                major_inductive_name,
                major_inductive.level_params.len(),
                major_levels.len()
            ));
        }
        let preview_major_args = preview_major_domain.get_app_args();
        let expected_major_args =
            major_inductive.num_params as usize + major_inductive.num_indices as usize;
        if preview_major_args.len() != expected_major_args {
            return Err(format!(
                "{}: rule {} major premise supplies {} inductive arguments, expected {}",
                rec.name,
                rule_idx,
                preview_major_args.len(),
                expected_major_args
            ));
        }
        let major_params: Vec<Expr> = preview_major_args
            .iter()
            .take(ctor.num_params as usize)
            .map(|arg| (*arg).clone())
            .collect();

        // Build the constructor major from the major inductive's own parameter
        // spine, not from `rec.num_params`.  The distinction is essential for
        // restored nested companions, whose family parameters and container
        // parameters are different telescopes.
        let mut ctor_application = Expr::const_(ctor.name.clone(), major_levels.clone());
        // In this environment's theory (`tc/level_profile.rs`, DECISIONS R150):
        // the checker below instantiates `ctor` at `major_levels` the same way.
        let mut ctor_cursor = self
            .instantiate_levels_in_theory(
                &ctor.name,
                &ctor.type_,
                &ctor.level_params,
                &major_levels,
            )
            .map_err(|error| format!("{}: rule {rule_idx}: {error:?}", rec.name))?;
        for (index, param) in major_params.iter().enumerate() {
            let _ = instantiate_recursor_arg(
                &mut ctor_cursor,
                param,
                &format!("constructor parameter {index}"),
            )?;
            ctor_application = Expr::app(ctor_application, param.clone());
        }

        let mut fields = Vec::with_capacity(rule.num_fields as usize);
        for index in 0..rule.num_fields {
            let field = open_recursor_local(
                &mut ctor_cursor,
                &mut ctx,
                &format!("{}_rule_{rule_idx}_field_{index}", rec.name),
            )?;
            ctor_application = Expr::app(ctor_application, field.clone());
            fields.push(field);
        }
        if matches!(ctor_cursor.kind(), ExprKind::Pi(..)) {
            return Err(format!(
                "{}: rule {} for {} leaves unapplied constructor fields",
                rec.name, rule_idx, ctor.name
            ));
        }

        let mut hit_path_arg = None;
        let (major, return_indices) = match ctor_cursor.kind() {
            ExprKind::CubicalPath { ty, .. } => {
                if rec.num_indices != 0 {
                    return Err(format!(
                        "{}: indexed HIT path rule {} is unsupported",
                        rec.name, rule_idx
                    ));
                }
                let ExprKind::Lam(_, interval_domain, line_body) = ty.kind() else {
                    return Err(format!(
                        "{}: HIT path constructor {} has a non-lambda type line",
                        rec.name, ctor.name
                    ));
                };
                if !matches!(interval_domain.kind(), ExprKind::CubicalInterval) {
                    return Err(format!(
                        "{}: HIT path constructor {} line is not interval-indexed",
                        rec.name, ctor.name
                    ));
                }
                let (line_name, line_levels) = match line_body.get_app_fn().kind() {
                    ExprKind::Const(name, levels) => (name, levels),
                    _ => {
                        return Err(format!(
                            "{}: HIT path constructor {} line is not constant-headed",
                            rec.name, ctor.name
                        ))
                    }
                };
                if line_name != &major_inductive_name
                    || line_levels.as_slice() != major_levels.as_slice()
                {
                    return Err(format!(
                        "{}: HIT path constructor {} line targets {} at levels {:?}, expected {} at {:?}",
                        rec.name,
                        ctor.name,
                        line_name,
                        line_levels,
                        major_inductive_name,
                        major_levels
                    ));
                }
                let line_args = line_body.get_app_args();
                if line_args.len() != expected_major_args
                    || !line_args
                        .iter()
                        .zip(&major_params)
                        .all(|(actual, expected)| *actual == expected)
                {
                    return Err(format!(
                        "{}: HIT path constructor {} line has a noncanonical major-inductive parameter spine",
                        rec.name, ctor.name
                    ));
                }
                let interval = Expr::from_kind(ExprKind::CubicalInterval);
                let interval_arg = Expr::fvar(ctx.push(
                    Name::from_string(&format!("{}_rule_{rule_idx}_interval", rec.name)),
                    interval,
                    BinderInfo::Default,
                ));
                let major = Expr::from_kind(ExprKind::CubicalPathApp {
                    path: Arc::new(ctor_application.clone()),
                    arg: Arc::new(interval_arg.clone()),
                });
                hit_path_arg = Some(interval_arg);
                (major, Vec::new())
            }
            _ => {
                let return_head = ctor_cursor.get_app_fn();
                let ExprKind::Const(return_name, return_levels) = return_head.kind() else {
                    return Err(format!(
                        "{}: constructor {} return is neither {} nor a cubical path",
                        rec.name, ctor.name, major_inductive_name
                    ));
                };
                if return_name != &major_inductive_name {
                    return Err(format!(
                        "{}: constructor {} returns {}, expected {}",
                        rec.name, ctor.name, return_name, major_inductive_name
                    ));
                }
                if return_levels.as_slice() != major_levels.as_slice() {
                    return Err(format!(
                        "{}: constructor {} returns {} at levels {:?}, but the major premise uses {:?}",
                        rec.name, ctor.name, major_inductive_name, return_levels, major_levels
                    ));
                }
                let return_args = ctor_cursor.get_app_args();
                let index_start = major_inductive.num_params as usize;
                let index_end = index_start + rec.num_indices as usize;
                if return_args.len() != index_end {
                    return Err(format!(
                        "{}: constructor {} return supplies {} inductive arguments, expected {}",
                        rec.name,
                        ctor.name,
                        return_args.len(),
                        index_end
                    ));
                }
                if !return_args[..index_start]
                    .iter()
                    .zip(&major_params)
                    .all(|(actual, expected)| *actual == expected)
                {
                    return Err(format!(
                        "{}: constructor {} return has a noncanonical major-inductive parameter spine",
                        rec.name, ctor.name
                    ));
                }
                let indices = return_args[index_start..index_end]
                    .iter()
                    .map(|arg| (*arg).clone())
                    .collect();
                (ctor_application.clone(), indices)
            }
        };

        for (index, return_index) in return_indices.iter().enumerate() {
            let _ = instantiate_recursor_arg(
                &mut cursor,
                return_index,
                &format!("recursor index {index}"),
            )?;
            rec_application = Expr::app(rec_application, return_index.clone());
        }
        let _major_domain = instantiate_recursor_arg(&mut cursor, &major, "major premise")?;
        rec_application = Expr::app(rec_application, major);

        if rec.arg_order == RecursorArgOrder::MajorAfterMotive {
            for index in 0..rec.num_minors {
                let arg = open_recursor_local(
                    &mut cursor,
                    &mut ctx,
                    &format!("{}_rule_{rule_idx}_minor_{index}", rec.name),
                )?;
                rec_application = Expr::app(rec_application, arg.clone());
                minors.push(arg);
            }
        }
        if matches!(cursor.kind(), ExprKind::Pi(..)) {
            return Err(format!(
                "{}: rule {} validation left recursor arguments unapplied",
                rec.name, rule_idx
            ));
        }

        let mut rhs_args =
            Vec::with_capacity(params.len() + motives.len() + minors.len() + fields.len());
        rhs_args.extend(params);
        rhs_args.extend(motives);
        rhs_args.extend(minors);
        rhs_args.extend(fields);
        // `rec_levels` is the identity, under which Clean's substitution keeps
        // every node (`Level::substitute_slice`), Lean's answer for shared
        // objects; Lean's construction would only add a sharing refusal to this
        // Clean-only check (DECISIONS R150).
        let rhs = rule
            .rhs
            .instantiate_level_params_direct(&rec.level_params, &rec_levels);
        let rhs_applied = Expr::apps(rhs, rhs_args);

        let mut tc = TypeChecker::with_context(self, ctx);
        tc.set_allow_unsafe(false);
        tc.set_allow_partial(false);
        tc.set_cumulative(self.cumulative);
        let expected = tc.infer_type_full(&rec_application).map_err(|error| {
            format!(
                "{}: symbolic application for rule {} ({}) failed kernel checking: {error:?}",
                rec.name, rule_idx, rule.constructor_name
            )
        })?;

        // The reducer beta-strips rule lambdas without checking their binder
        // annotations (notably Eq's repaired rule uses placeholder domains), so
        // validate the exact post-beta payload rather than the lambda telescope.
        let reduced_rhs = tc.whnf(&rhs_applied);
        let reduced_rhs = if let Some(interval_arg) = hit_path_arg {
            Expr::from_kind(ExprKind::CubicalPathApp {
                path: Arc::new(reduced_rhs),
                arg: Arc::new(interval_arg),
            })
        } else {
            reduced_rhs
        };
        tc.check_type(&reduced_rhs, &expected).map_err(|error| {
            format!(
                "{}: rule {} ({}) violates subject reduction: {error:?}",
                rec.name, rule_idx, rule.constructor_name
            )
        })
    }

    fn validate_recursor_rule_payloads(&self, name: &Name) -> Result<(), String> {
        let rec = self
            .get_recursor(name)
            .cloned()
            .ok_or_else(|| format!("unknown recursor `{name}`"))?;
        for (rule_idx, rule) in rec.rules.iter().enumerate() {
            self.validate_recursor_rule_subject_reduction(&rec, rule_idx, rule)?;
        }
        Ok(())
    }

    /// Validate the current constant/recursor payload through both the
    /// recursor-metadata invariants used by iota/K reduction and a fresh strict
    /// kernel declaration check, then record full verification provenance.
    ///
    /// Call this only for recursors generated or mechanically repaired by the
    /// Clean kernel. Imported/unchecked metadata must retain an unchecked or
    /// structural provenance marker instead.
    pub(crate) fn validate_and_stamp_recursor(&mut self, name: &Name) -> Result<(), EnvError> {
        self.validate_recursor_metadata(name).map_err(|detail| {
            EnvError::Inductive(crate::inductive::InductiveError::InvalidType(detail))
        })?;
        self.validate_recursor_rule_payloads(name)
            .map_err(|detail| {
                EnvError::Inductive(crate::inductive::InductiveError::InvalidType(detail))
            })?;
        let info =
            self.get_const(name)
                .cloned()
                .ok_or_else(|| EnvError::InitializationConflict {
                    name: name.clone(),
                    detail: "recursor validation lost its constant-table entry".to_string(),
                })?;
        let decl = match info.value {
            Some(value) => super::Declaration::Definition {
                name: info.name,
                level_params: info.level_params,
                type_: info.type_,
                value,
                is_reducible: info.is_reducible,
            },
            None => super::Declaration::Axiom {
                name: info.name,
                level_params: info.level_params,
                type_: info.type_,
            },
        };
        self.check_decl_readonly_strict(&decl)?;
        self.declaration_verification.insert(
            name.clone(),
            super::DeclarationVerification::FullKernelCheck,
        );
        Ok(())
    }

    /// Register a pre-validated inductive type.
    ///
    /// This is used when importing .olean files where the inductive has already
    /// been validated by the Lean compiler. No validation is performed.
    ///
    /// Also adds the inductive as a constant if not already present.
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub(crate) fn register_inductive(&mut self, ind_val: InductiveVal) {
        // Add as constant if not already present
        // Use entry API to avoid double hash lookup
        use hashbrown::hash_map::Entry;
        if let Entry::Vacant(e) = self.constants.entry(ind_val.name.clone()) {
            e.insert(ConstantInfo::new(
                ind_val.name.clone(),
                ind_val.level_params.clone(),
                ind_val.type_.clone(),
                None,
                false,
            ));
        }
        let name = ind_val.name.clone();
        self.inductives.insert(name.clone(), ind_val);
        self.declaration_verification
            .insert(name, super::DeclarationVerification::Unchecked);
        self.generation += 1;
    }

    /// Register a pre-validated inductive, skipping duplicate check.
    ///
    /// This is faster than `register_inductive` because it assumes the name
    /// does not already exist. Use only when loading trusted .olean files.
    #[inline]
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub(crate) fn register_inductive_unchecked(&mut self, ind_val: InductiveVal) {
        let ind_name = ind_val.name.clone();
        debug_assert!(
            !self.constants.contains_key(&ind_name),
            "register_inductive_unchecked duplicate constant: {}",
            ind_name
        );
        debug_assert!(
            !self.inductives.contains_key(&ind_name),
            "register_inductive_unchecked duplicate inductive: {}",
            ind_name
        );
        self.install_resident_constant(
            ind_name.clone(),
            ConstantInfo::new(
                ind_name.clone(),
                ind_val.level_params.clone(),
                ind_val.type_.clone(),
                None,
                false,
            ),
        );
        self.inductives.insert(ind_name.clone(), ind_val);
        self.declaration_verification
            .insert(ind_name, super::DeclarationVerification::Unchecked);
        self.generation += 1;
    }

    /// Register a pre-validated constructor.
    ///
    /// This is used when importing .olean files where the constructor has already
    /// been validated by the Lean compiler. No validation is performed.
    ///
    /// Also adds the constructor as a constant if not already present.
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub(crate) fn register_constructor(&mut self, ctor_val: ConstructorVal) {
        // Add as constant if not already present
        // Use entry API to avoid double hash lookup
        use hashbrown::hash_map::Entry;
        if let Entry::Vacant(e) = self.constants.entry(ctor_val.name.clone()) {
            e.insert(ConstantInfo::new(
                ctor_val.name.clone(),
                ctor_val.level_params.clone(),
                ctor_val.type_.clone(),
                None,
                false,
            ));
        }
        let name = ctor_val.name.clone();
        self.constructors.insert(name.clone(), ctor_val);
        self.declaration_verification
            .insert(name, super::DeclarationVerification::Unchecked);
        self.generation += 1;
    }

    /// Register a pre-validated constructor, skipping duplicate check.
    ///
    /// This is faster than `register_constructor` because it assumes the name
    /// does not already exist. Use only when loading trusted .olean files.
    #[inline]
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub(crate) fn register_constructor_unchecked(&mut self, ctor_val: ConstructorVal) {
        let ctor_name = ctor_val.name.clone();
        debug_assert!(
            !self.constants.contains_key(&ctor_name),
            "register_constructor_unchecked duplicate constant: {}",
            ctor_name
        );
        debug_assert!(
            !self.constructors.contains_key(&ctor_name),
            "register_constructor_unchecked duplicate constructor: {}",
            ctor_name
        );
        self.install_resident_constant(
            ctor_name.clone(),
            ConstantInfo::new(
                ctor_name.clone(),
                ctor_val.level_params.clone(),
                ctor_val.type_.clone(),
                None,
                false,
            ),
        );
        self.constructors.insert(ctor_name.clone(), ctor_val);
        self.declaration_verification
            .insert(ctor_name, super::DeclarationVerification::Unchecked);
        self.generation += 1;
    }

    /// Register a pre-validated recursor.
    ///
    /// This is used when importing .olean files where the recursor has already
    /// been validated by the Lean compiler. No validation is performed.
    ///
    /// Also adds the recursor as a constant if not already present.
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub(crate) fn register_recursor(&mut self, rec_val: RecursorVal) {
        // Add as constant if not already present
        // Use entry API to avoid double hash lookup
        use hashbrown::hash_map::Entry;
        if let Entry::Vacant(e) = self.constants.entry(rec_val.name.clone()) {
            e.insert(ConstantInfo::new(
                rec_val.name.clone(),
                rec_val.level_params.clone(),
                rec_val.type_.clone(),
                None,
                false,
            ));
        }
        let name = rec_val.name.clone();
        self.recursors.insert(name.clone(), rec_val);
        self.declaration_verification
            .insert(name, super::DeclarationVerification::Unchecked);
        self.generation += 1;
    }

    /// Register a pre-validated recursor, skipping duplicate check.
    ///
    /// This is faster than `register_recursor` because it assumes the name
    /// does not already exist. Use only when loading trusted .olean files.
    #[inline]
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub(crate) fn register_recursor_unchecked(&mut self, rec_val: RecursorVal) {
        let rec_name = rec_val.name.clone();
        debug_assert!(
            !self.constants.contains_key(&rec_name),
            "register_recursor_unchecked duplicate constant: {}",
            rec_name
        );
        debug_assert!(
            !self.recursors.contains_key(&rec_name),
            "register_recursor_unchecked duplicate recursor: {}",
            rec_name
        );
        self.install_resident_constant(
            rec_name.clone(),
            ConstantInfo::new(
                rec_name.clone(),
                rec_val.level_params.clone(),
                rec_val.type_.clone(),
                None,
                false,
            ),
        );
        self.recursors.insert(rec_name.clone(), rec_val);
        self.declaration_verification
            .insert(rec_name, super::DeclarationVerification::Unchecked);
        self.generation += 1;
    }

    /// Raw bulk-insert of constants (pure `HashMap::extend`, bumps generation).
    ///
    /// Shared implementation for both `extend_constants_unchecked` (the trusted
    /// bypass) and `extend_constants_checked` (the G4 kernel-checked lane, which
    /// inserts here then re-checks). Private on purpose: this is the un-gated
    /// primitive, so only the two accounted lanes above may call it.
    fn insert_constants_raw(&mut self, constants: impl Iterator<Item = ConstantInfo>) {
        let constants: Vec<_> = constants.collect();
        #[cfg(debug_assertions)]
        {
            let mut batch_names = hashbrown::HashSet::new();
            for constant in &constants {
                debug_assert!(
                    !self.constants.contains_key(&constant.name),
                    "insert_constants_raw duplicate constant: {}",
                    constant.name
                );
                debug_assert!(
                    batch_names.insert(constant.name.clone()),
                    "insert_constants_raw duplicate constant in batch: {}",
                    constant.name
                );
            }
        }
        let names: Vec<Name> = constants
            .iter()
            .map(|constant| constant.name.clone())
            .collect();
        self.extend_resident_constants(constants.into_iter().map(|c| (c.name.clone(), c)));
        for name in names {
            self.declaration_verification
                .insert(name, super::DeclarationVerification::Unchecked);
        }
        self.generation += 1;
    }

    /// Bulk register constants, skipping duplicate checks.
    ///
    /// This is more efficient than calling `add_decl_unchecked` in a loop
    /// because it uses `HashMap::extend()` for batch insertion.
    #[inline]
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub(crate) fn extend_constants_unchecked(
        &mut self,
        constants: impl Iterator<Item = ConstantInfo>,
    ) {
        self.insert_constants_raw(constants);
    }

    /// Bulk register constants WITH kernel re-checking (Pillar-1 gap G4).
    ///
    /// Unlike [`extend_constants_unchecked`](Self::extend_constants_unchecked),
    /// which admits records `add_decl` could never mint (e.g. a `kind:Axiom`
    /// record carrying a `Reducible` value, whose body the reducer δ-unfolds
    /// UNCHECKED), this runs two tiers of check per record:
    ///
    ///   1. **Structural (always, unconditional).**
    ///      [`validate_constant_info_structural`](Self::validate_constant_info_structural)
    ///      closes the exact "leaked fvar/mvar or out-of-scope `Level::Param`"
    ///      smuggle G4 names — with NO constant resolution, so it holds even for
    ///      records that reference not-yet-loaded dependencies. Any failure here
    ///      is fatal (fail-closed).
    ///
    ///   2. **Kernel type-check (dependency-tolerant).** `infer_sort(type_)` on
    ///      every record and `check_type(value, type_)` on every VALUE-bearing
    ///      record — the exact `add_decl` machinery, which closes the
    ///      `Function.Injective`-style unchecked-δ-unfoldable-body hole. Any
    ///      genuine type error (TypeMismatch, ExpectedSort, SortDepthExceeded, …)
    ///      is fatal. The SOLE tolerated outcome is `TypeError::UnknownConst`: an
    ///      overlay namespace legitimately references sibling/base constants that
    ///      are only present once the FULL certificate env is assembled (e.g.
    ///      `Topology.ProductTopology.prod_homeomorphism : … Topology.Homeomorphism`,
    ///      defined in a different init). An unresolved reference is a FORWARD /
    ///      EXTERNAL dependency, NOT a smuggle — rejecting it would break
    ///      legitimate incremental overlay loading. Such records are still fully
    ///      structurally checked (tier 1), and — when loaded into an env where the
    ///      dependency IS present — are re-typecheckable there.
    ///
    /// FORWARD/MUTUAL REFERENCES within the batch: the records are inserted FIRST
    /// (pure extend) and re-checked against the now-complete environment, so
    /// intra-batch references resolve.
    ///
    /// SOUNDNESS: this method only ADDS checks over `extend_constants_unchecked`
    /// (tier 1 unconditional, tier 2 whenever deps are present); it can reject an
    /// ill-formed/ill-typed record but never accepts anything the kernel rejects,
    /// and never rejects a legitimate external reference. It is the hardened lane
    /// for the one genuine trust-bearing production site (`generated_overlay.rs`
    /// `load_namespace_overlay`).
    ///
    /// # Errors
    /// Returns the first `(name, EnvError)` that fails the structural check or a
    /// non-`UnknownConst` kernel type-check. On error the records HAVE been
    /// inserted (the caller — a fresh overlay build — discards the env); this is
    /// the fail-closed outcome for a malformed overlay.
    pub(crate) fn extend_constants_checked(
        &mut self,
        constants: impl Iterator<Item = ConstantInfo>,
    ) -> Result<(), (Name, EnvError)> {
        use crate::tc::{TypeChecker, TypeError};

        // Phase 1: insert all records (pure extend) so forward/mutual references
        // among the batch resolve during the Phase-2 re-check. Uses the shared
        // raw primitive directly (NOT the unchecked bypass lane) — the kernel
        // re-check below is what makes this the CHECKED lane.
        let inserted: Vec<Name> = {
            let payload: Vec<ConstantInfo> = constants.collect();
            let names: Vec<Name> = payload.iter().map(|c| c.name.clone()).collect();
            self.insert_constants_raw(payload.into_iter());
            names
        };

        // A kernel type error is FATAL unless it is a bare `UnknownConst` (an
        // unresolved forward/external dependency, not a smuggle). Everything else
        // — leaked fvar (UnknownFVar), sort mismatch, type mismatch, depth blowup —
        // is a genuine well-formedness/typing failure and fails closed.
        fn is_tolerable(e: &TypeError) -> bool {
            matches!(e, TypeError::UnknownConst(_))
        }

        // Phase 2: re-check every inserted record against the now-complete env.
        for name in &inserted {
            let Some(info) = self.get_const(name).cloned() else {
                continue;
            };

            // Tier 1 — structural (unconditional, no const resolution). Closes the
            // fvar/mvar/level-scope smuggle even for records with external deps.
            self.validate_constant_info_structural(&info)
                .map_err(|e| (name.clone(), e))?;

            // Tier 2 — kernel type-check, tolerant of unresolved dependencies.
            let tc = TypeChecker::with_mode(self, self.mode());
            if let Err(e) = tc.infer_sort(&info.type_) {
                if !is_tolerable(&e) {
                    return Err((
                        name.clone(),
                        EnvError::TypeCheckFailed {
                            name: name.clone(),
                            source: e,
                        },
                    ));
                }
            }
            if let Some(value) = info.value.as_ref() {
                if let Err(e) = tc.check_type(value, &info.type_) {
                    if !is_tolerable(&e) {
                        return Err((
                            name.clone(),
                            EnvError::TypeCheckFailed {
                                name: name.clone(),
                                source: e,
                            },
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    /// Validate a `ConstantInfo` structurally without type checking.
    ///
    /// Performs the same O(1) structural checks as `add_decl_structural`:
    /// 1. No duplicate universe level parameters
    /// 2. No expression or level metavariables in type or value
    /// 3. No free variables (FVar) in type or value
    /// 4. All Level::Param references must be in the declared level_params
    ///
    /// Does NOT check for duplicate names (caller handles duplicate filtering).
    ///
    /// Returns `Ok(())` if valid, or the first structural error found.
    pub(crate) fn validate_constant_info_structural(
        &self,
        info: &ConstantInfo,
    ) -> Result<(), EnvError> {
        let name = &info.name;
        let level_params = &info.level_params;
        let type_ = &info.type_;
        let opt_value = info.value.as_ref();

        // Check 1: duplicate universe level parameters
        for (i, p) in level_params.iter().enumerate() {
            if level_params[..i].contains(p) {
                return Err(EnvError::DuplicateLevelParam {
                    name: name.clone(),
                    param: p.clone(),
                });
            }
        }

        // Check 2: no metavariables
        if type_.has_expr_mvar_quick() || type_.has_level_mvar_quick() {
            return Err(EnvError::ContainsMetavar { name: name.clone() });
        }
        // Check 3: no free variables
        if type_.has_fvar_quick() {
            return Err(EnvError::ContainsFreeVar {
                name: name.clone(),
                fvars: super::types::collect_fvar_ids_for_diagnostics(&[type_]),
            });
        }
        if let Some(value) = opt_value {
            if value.has_expr_mvar_quick() || value.has_level_mvar_quick() {
                return Err(EnvError::ContainsMetavar { name: name.clone() });
            }
            if value.has_fvar_quick() {
                return Err(EnvError::ContainsFreeVar {
                    name: name.clone(),
                    fvars: super::types::collect_fvar_ids_for_diagnostics(&[value]),
                });
            }
        }

        // Check 4: undefined level params
        if let Some(undef) = super::decl_add::find_undef_level_param(type_, level_params) {
            return Err(EnvError::UndefinedLevelParam {
                name: name.clone(),
                param: undef,
            });
        }
        if let Some(value) = opt_value {
            if let Some(undef) = super::decl_add::find_undef_level_param(value, level_params) {
                return Err(EnvError::UndefinedLevelParam {
                    name: name.clone(),
                    param: undef,
                });
            }
        }

        Ok(())
    }

    /// Bulk register constants with structural validation.
    ///
    /// Like `extend_constants_unchecked`, but runs O(1) structural integrity
    /// checks on each constant before insertion. Constants that fail validation
    /// are collected into the returned Vec rather than silently inserted.
    ///
    /// Checks performed per constant (same as `add_decl_structural`):
    /// 1. No duplicate universe level parameters
    /// 2. No metavariables in type or value
    /// 3. No free variables in type or value
    /// 4. All Level::Param references in scope
    ///
    /// Duplicate name checking is NOT performed here — callers are expected
    /// to pre-filter duplicates (as the existing import path already does).
    pub(crate) fn extend_constants_structural(
        &mut self,
        constants: impl Iterator<Item = ConstantInfo>,
    ) -> Vec<(Name, EnvError)> {
        let mut valid = Vec::new();
        let mut rejected = Vec::new();

        for info in constants {
            match self.validate_constant_info_structural(&info) {
                Ok(()) => valid.push(info),
                Err(e) => {
                    let name = info.name.clone();
                    rejected.push((name, e));
                }
            }
        }

        // Batch insert all valid constants. Structural validation is useful
        // evidence but is not a full kernel check, and it must overwrite any
        // stale stamp left by a same-name payload replacement.
        let valid_names: Vec<Name> = valid.iter().map(|info| info.name.clone()).collect();
        self.extend_resident_constants(valid.into_iter().map(|c| (c.name.clone(), c)));
        for name in valid_names {
            self.declaration_verification
                .insert(name, super::DeclarationVerification::StructuralOnly);
        }
        if rejected.is_empty() {
            // Only bump generation if we actually inserted something
            // (but always bump to match extend_constants_unchecked behavior)
        }
        self.generation += 1;

        rejected
    }

    /// Upgrade axiom stubs to definitions with values — UNCHECKED (test-only).
    ///
    /// DEMOTED 2026-08-24 (R1-STUB, census row `axiom-stub-upgrade`): every
    /// production caller now goes through
    /// [`upgrade_axiom_stubs_checked`](Self::upgrade_axiom_stubs_checked),
    /// which anchors the incoming record to the stub's type and kernel-checks
    /// the incoming value. This variant injects a δ-unfoldable VALUE with no
    /// check at all, so it is compiled only for test builds (the `test` cfg or
    /// the empty `test-fixtures` feature enabled by downstream
    /// dev-dependencies) — a production call no longer compiles.
    ///
    /// Original contract (#3134): when `.olean.private` provides the full
    /// definition for a constant that the base `.olean` exported as an axiom
    /// stub (Lean 4.29+ module system), replace the existing axiom (no value)
    /// with the definition (value, reducibility hints, etc.). Constants whose
    /// existing entry already has a value are left unchanged (not overwritten).
    #[cfg(any(test, feature = "test-fixtures"))]
    pub(crate) fn upgrade_axiom_stubs(
        &mut self,
        constants: impl Iterator<Item = ConstantInfo>,
    ) -> usize {
        let mut upgraded = 0usize;
        for ci in constants {
            if let Some(existing) = self.constants.get(&ci.name) {
                if existing.value.is_none() && ci.value.is_some() {
                    let name = ci.name.clone();
                    self.install_resident_constant(name.clone(), ci);
                    self.declaration_verification
                        .insert(name, super::DeclarationVerification::Unchecked);
                    upgraded += 1;
                }
            }
        }
        if upgraded > 0 {
            self.generation += 1;
        }
        upgraded
    }

    /// Upgrade axiom stubs to definitions with values, WITH kernel re-checking
    /// (R1-STUB, closing census row `axiom-stub-upgrade` per the G4
    /// checked-tier precedent [`extend_constants_checked`](Self::extend_constants_checked)).
    ///
    /// The production lane for the `.olean.private` stub-upgrade healing
    /// (#3134) and the mathverse per-constant demand-load. Unlike the retired
    /// unchecked door — which wholesale-replaced the resident entry, letting
    /// the reducer δ-unfold an arbitrary injected value — every record here
    /// must earn its swap:
    ///
    ///   1. **The stub must exist.** A record whose name has no resident entry
    ///      is refused ([`EnvError::UpgradeTargetMissing`]): an upgrade against
    ///      nothing has no type anchor.
    ///   2. **Structural tier (unconditional).**
    ///      [`validate_constant_info_structural`](Self::validate_constant_info_structural)
    ///      — no leaked fvar/mvar, no duplicate/out-of-scope `Level::Param`.
    ///   3. **Type anchor.** The incoming type must BE the stub's type,
    ///      compared alpha-insensitively on positional level params (same
    ///      arity; structural equality first, kernel `is_def_eq` fallback —
    ///      the same discipline as `upgrade_axiom_to_checked_decl`). Replacing
    ///      the entry must never change the constant's stated type
    ///      ([`EnvError::UpgradeTypeMismatch`]).
    ///   4. **Kernel type-check (dependency-tolerant, exactly G4).**
    ///      `infer_sort` on the incoming type and `check_type(value, type)` on
    ///      the incoming value — the `add_decl` machinery. The SOLE tolerated
    ///      outcome is `TypeError::UnknownConst`: a forward/external reference
    ///      legitimately unresolvable mid-load (the per-constant demand-load
    ///      assembles its closure incrementally), not a smuggle. Any other
    ///      type error refuses the record.
    ///
    /// A refused record REFUSES fail-closed: the stub stays exactly as it was,
    /// nothing registers, and the `(name, error)` pair is returned to the
    /// caller for loud accounting. Records that are silent no-ops under the
    /// original contract stay silent no-ops: an already-value-bearing resident
    /// is never overwritten, and a value-less incoming record (e.g. a
    /// policy-elided proof body) carries nothing to install.
    ///
    /// Successful swaps install the incoming `ConstantInfo` verbatim
    /// (preserving imported reducibility hints) and stamp it exactly as the G4
    /// checked lane stamps its records (`insert_constants_raw`'s conservative
    /// `Unchecked` — the `UnknownConst` tolerance means a record is not
    /// GUARANTEED fully checked, so the stamp never over-claims).
    ///
    /// Returns `(upgraded_count, refused_records)`.
    pub(crate) fn upgrade_axiom_stubs_checked(
        &mut self,
        constants: impl Iterator<Item = ConstantInfo>,
    ) -> (usize, Vec<(Name, EnvError)>) {
        let (upgraded, refused, _) = self.upgrade_axiom_stubs_checked_with_work(constants, true);
        (upgraded, refused)
    }

    pub(super) fn upgrade_axiom_stubs_checked_with_work(
        &mut self,
        constants: impl Iterator<Item = ConstantInfo>,
        reuse_refusals: bool,
    ) -> (
        usize,
        Vec<(Name, EnvError)>,
        super::stub_upgrade_parallel::StubUpgradeWork,
    ) {
        let constants: Vec<ConstantInfo> = constants.collect();
        // Every verdict below is `stub_upgrade_verdict` — the checks of steps
        // 1-4 — taken against the environment as it stands when the record
        // is installed or refused, or (for a batch large enough to fan out)
        // a speculative ACCEPT taken against the environment as it stood
        // before the batch. See `stub_upgrade_parallel` for why such an
        // accept is the same kernel check against a δ-sub-environment of the
        // one the record is installed into.
        let speculative =
            super::stub_upgrade_parallel::speculative_checks(self, &constants, reuse_refusals);
        let mut work = super::stub_upgrade_parallel::StubUpgradeWork {
            speculative_checks: speculative.checks,
            ..Default::default()
        };
        let mut speculative = speculative.verdicts.into_iter();
        let mut upgraded = 0usize;
        let mut rejected: Vec<(Name, EnvError)> = Vec::new();
        for ci in constants {
            let checked = speculative.next();
            let verdict = match self.stub_upgrade_precheck(&ci) {
                Some(early) => early,
                None => match checked {
                    Some(SpeculativeVerdict::Install) => StubVerdict::Install,
                    // No earlier swap: the complete worker check saw this
                    // exact environment, including every indirect dependency.
                    // After ANY swap, preserve the original in-order recheck.
                    Some(SpeculativeVerdict::Refuse(error)) if upgraded == 0 => {
                        work.reused_refusals += 1;
                        StubVerdict::Refuse(*error)
                    }
                    _ => {
                        work.sequential_checks += 1;
                        self.stub_upgrade_verdict(&ci)
                    }
                },
            };
            match verdict {
                StubVerdict::Skip => {}
                StubVerdict::Refuse(e) => rejected.push((ci.name.clone(), e)),
                StubVerdict::Install => {
                    // The swap: install the checked record; stamp per the G4 lane.
                    let name = ci.name.clone();
                    self.install_resident_constant(name.clone(), ci);
                    self.declaration_verification
                        .insert(name, super::DeclarationVerification::Unchecked);
                    upgraded += 1;
                }
            }
        }
        if upgraded > 0 {
            self.generation += 1;
        }
        (upgraded, rejected, work)
    }

    /// Steps 1 and the silent no-op lane of
    /// [`upgrade_axiom_stubs_checked`](Self::upgrade_axiom_stubs_checked):
    /// `Some` when the record is decided without a kernel check — refused for
    /// a missing stub, skipped when the resident already carries a value or
    /// the record carries none — and `None` when it needs steps 2-4.
    pub(super) fn stub_upgrade_precheck(&self, ci: &ConstantInfo) -> Option<StubVerdict> {
        // 1. The stub must exist.
        let Some(existing) = self.constants.get(&ci.name) else {
            return Some(StubVerdict::Refuse(EnvError::UpgradeTargetMissing {
                name: ci.name.clone(),
            }));
        };
        // Silent no-op lane (the original #3134 contract): never overwrite
        // a value-bearing resident; nothing to install without a value.
        if existing.value.is_some() || ci.value.is_none() {
            return Some(StubVerdict::Skip);
        }
        None
    }

    /// The whole per-record decision of
    /// [`upgrade_axiom_stubs_checked`](Self::upgrade_axiom_stubs_checked),
    /// read-only: steps 1-4 against `self` as it stands.
    pub(super) fn stub_upgrade_verdict(&self, ci: &ConstantInfo) -> StubVerdict {
        self.stub_upgrade_check(ci, false).0
    }

    /// Alongside the original verdict, report whether a refusal completed
    /// without a resource cutoff. This never changes the verdict itself.
    pub(super) fn stub_upgrade_check(
        &self,
        ci: &ConstantInfo,
        track_completion: bool,
    ) -> (StubVerdict, bool) {
        // Optional import diagnosis only: every checked verdict still follows
        // the same path, in the same order, with the same resource controls.
        static TRACE: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| {
            std::env::var("CLEAN_TRACE_STUB_UPGRADES").is_ok_and(|value| value == "1")
        });
        let started = if *TRACE {
            eprintln!(
                "checked-stub begin thread={:?} name={} completion_tracking={track_completion}",
                std::thread::current().id(),
                ci.name,
            );
            Some(std::time::Instant::now())
        } else {
            None
        };
        let complete = std::cell::Cell::new(track_completion);
        let verdict = self.stub_upgrade_verdict_inner(ci, &complete);
        if let Some(started) = started {
            let outcome = match &verdict {
                StubVerdict::Skip => "skip",
                StubVerdict::Install => "install",
                StubVerdict::Refuse(_) => "refuse",
            };
            eprintln!(
                "checked-stub end thread={:?} name={} outcome={outcome} elapsed_us={}",
                std::thread::current().id(),
                ci.name,
                started.elapsed().as_micros(),
            );
        }
        (verdict, complete.get())
    }

    fn stub_upgrade_verdict_inner(
        &self,
        ci: &ConstantInfo,
        complete: &std::cell::Cell<bool>,
    ) -> StubVerdict {
        use crate::tc::TypeError;

        // A kernel type error is FATAL unless it is a bare `UnknownConst` (an
        // unresolved forward/external dependency, not a smuggle) — the exact
        // G4 tolerance of `extend_constants_checked`.
        fn is_tolerable(e: &TypeError) -> bool {
            matches!(e, TypeError::UnknownConst(_))
        }

        if let Some(early) = self.stub_upgrade_precheck(ci) {
            return early;
        }
        let name = ci.name.clone();
        let Some(existing) = self.constants.get(&name) else {
            return StubVerdict::Refuse(EnvError::UpgradeTargetMissing { name });
        };

        // 3. Type anchor (arity first).
        if existing.level_params.len() != ci.level_params.len() {
            let detail = format!(
                "level-param arity {} differs from existing arity {}",
                ci.level_params.len(),
                existing.level_params.len()
            );
            return StubVerdict::Refuse(EnvError::UpgradeTypeMismatch { name, detail });
        }

        // 2. Structural tier.
        if let Err(e) = self.validate_constant_info_structural(ci) {
            return StubVerdict::Refuse(e);
        }

        // 3. (continued) Positional alpha-insensitive type identity.
        let incoming_type = if existing.level_params == ci.level_params {
            ci.type_.clone()
        } else {
            let renaming: Vec<Level> = existing
                .level_params
                .iter()
                .map(|n| Level::param(n.clone()))
                .collect();
            ci.type_
                .instantiate_level_params_direct(&ci.level_params, &renaming)
        };
        if existing.type_ != incoming_type {
            let tc = TypeChecker::with_mode(self, self.mode());
            if !tc.is_def_eq(&existing.type_, &incoming_type) {
                // This bool does not distinguish a completed inequality
                // from every conservative reduction cutoff. Keep the
                // original in-order recheck for type-anchor refusals.
                complete.set(false);
                return StubVerdict::Refuse(EnvError::UpgradeTypeMismatch {
                    name,
                    detail: "declared type is not definitionally equal to the \
                             existing value-free constant's type"
                        .to_string(),
                });
            }
        }

        // 4. Kernel type-check, `UnknownConst`-tolerant (G4). The stub
        // stays resident during the check — the same posture as G4's
        // insert-first batch re-check; a self-referencing value resolves
        // to the stub's (identical) type, so the check stays consistent,
        // and the conservative stamp claims nothing stronger.
        let tc = TypeChecker::with_mode(self, self.mode());
        if let Err(e) = tc.infer_sort(&ci.type_) {
            if !is_tolerable(&e) {
                if complete.get() {
                    complete.set(super::stub_upgrade_parallel::completed_type_refusal(
                        &tc, &e,
                    ));
                }
                return StubVerdict::Refuse(EnvError::TypeCheckFailed { name, source: e });
            }
        }
        if let Some(value) = ci.value.as_ref() {
            if let Err(e) = tc.check_type(value, &ci.type_) {
                if !is_tolerable(&e) {
                    if complete.get() {
                        complete.set(super::stub_upgrade_parallel::completed_type_refusal(
                            &tc, &e,
                        ));
                    }
                    return StubVerdict::Refuse(EnvError::TypeCheckFailed { name, source: e });
                }
            }
        }
        StubVerdict::Install
    }

    /// O(1) structural validation shared by the inductive-family structural
    /// tier (R1-IND) — the exact check set of
    /// [`validate_constant_info_structural`](Self::validate_constant_info_structural),
    /// adapted per payload type (the caller passes every expression the record
    /// carries: the type, plus each recursor rule's `rhs`, which participates
    /// in ι-reduction and is exactly where a leaked fvar/mvar would smuggle):
    /// 1. No duplicate universe level parameters
    /// 2. No expression or level metavariables in any carried expression
    /// 3. No free variables (FVar) in any carried expression
    /// 4. All `Level::Param` references in the declared `level_params`
    fn validate_family_record_structural(
        name: &Name,
        level_params: &[Name],
        exprs: &[&Expr],
    ) -> Result<(), EnvError> {
        // Check 1: duplicate universe level parameters
        for (i, p) in level_params.iter().enumerate() {
            if level_params[..i].contains(p) {
                return Err(EnvError::DuplicateLevelParam {
                    name: name.clone(),
                    param: p.clone(),
                });
            }
        }
        for &expr in exprs {
            // Check 2: no metavariables
            if expr.has_expr_mvar_quick() || expr.has_level_mvar_quick() {
                return Err(EnvError::ContainsMetavar { name: name.clone() });
            }
            // Check 3: no free variables
            if expr.has_fvar_quick() {
                return Err(EnvError::ContainsFreeVar {
                    name: name.clone(),
                    fvars: super::types::collect_fvar_ids_for_diagnostics(&[expr]),
                });
            }
            // Check 4: undefined level params
            if let Some(undef) = super::decl_add::find_undef_level_param(expr, level_params) {
                return Err(EnvError::UndefinedLevelParam {
                    name: name.clone(),
                    param: undef,
                });
            }
        }
        Ok(())
    }

    /// Raw bulk-insert of inductives (constants map + inductives map + stamp +
    /// generation bump). Shared implementation for `extend_inductives_unchecked`
    /// (the demoted test-only bypass) and `extend_inductives_structural` (the
    /// R1-IND structural tier, which validates each record first). Private on
    /// purpose: this is the un-gated primitive, so only the accounted lanes
    /// may call it.
    fn insert_inductives_raw(
        &mut self,
        inductives: Vec<InductiveVal>,
        verification: super::DeclarationVerification,
        caller: &'static str,
    ) {
        #[cfg(not(debug_assertions))]
        let _ = caller;
        #[cfg(debug_assertions)]
        {
            let mut batch_names = hashbrown::HashSet::new();
            for ind in &inductives {
                debug_assert!(
                    !self.constants.contains_key(&ind.name),
                    "{caller} duplicate constant: {}",
                    ind.name
                );
                debug_assert!(
                    !self.inductives.contains_key(&ind.name),
                    "{caller} duplicate inductive: {}",
                    ind.name
                );
                debug_assert!(
                    batch_names.insert(ind.name.clone()),
                    "{caller} duplicate inductive in batch: {}",
                    ind.name
                );
            }
        }
        // Add to constants map
        let names: Vec<Name> = inductives.iter().map(|ind| ind.name.clone()).collect();
        self.extend_resident_constants(inductives.iter().map(|ind| {
            (
                ind.name.clone(),
                ConstantInfo::new(
                    ind.name.clone(),
                    ind.level_params.clone(),
                    ind.type_.clone(),
                    None,
                    false,
                ),
            )
        }));
        // Add to inductives map
        self.inductives
            .extend(inductives.into_iter().map(|ind| (ind.name.clone(), ind)));
        for name in names {
            self.declaration_verification.insert(name, verification);
        }
        self.generation += 1;
    }

    /// Raw bulk-insert of constructors — see [`insert_inductives_raw`](Self::insert_inductives_raw).
    fn insert_constructors_raw(
        &mut self,
        constructors: Vec<ConstructorVal>,
        verification: super::DeclarationVerification,
        caller: &'static str,
    ) {
        #[cfg(not(debug_assertions))]
        let _ = caller;
        #[cfg(debug_assertions)]
        {
            let mut batch_names = hashbrown::HashSet::new();
            for ctor in &constructors {
                debug_assert!(
                    !self.constants.contains_key(&ctor.name),
                    "{caller} duplicate constant: {}",
                    ctor.name
                );
                debug_assert!(
                    !self.constructors.contains_key(&ctor.name),
                    "{caller} duplicate constructor: {}",
                    ctor.name
                );
                debug_assert!(
                    batch_names.insert(ctor.name.clone()),
                    "{caller} duplicate constructor in batch: {}",
                    ctor.name
                );
            }
        }
        // Add to constants map
        let names: Vec<Name> = constructors.iter().map(|ctor| ctor.name.clone()).collect();
        self.extend_resident_constants(constructors.iter().map(|ctor| {
            (
                ctor.name.clone(),
                ConstantInfo::new(
                    ctor.name.clone(),
                    ctor.level_params.clone(),
                    ctor.type_.clone(),
                    None,
                    false,
                ),
            )
        }));
        // Add to constructors map
        self.constructors.extend(
            constructors
                .into_iter()
                .map(|ctor| (ctor.name.clone(), ctor)),
        );
        for name in names {
            self.declaration_verification.insert(name, verification);
        }
        self.generation += 1;
    }

    /// Raw bulk-insert of recursors — see [`insert_inductives_raw`](Self::insert_inductives_raw).
    fn insert_recursors_raw(
        &mut self,
        recursors: Vec<RecursorVal>,
        verification: super::DeclarationVerification,
        caller: &'static str,
    ) {
        #[cfg(not(debug_assertions))]
        let _ = caller;
        #[cfg(debug_assertions)]
        {
            let mut batch_names = hashbrown::HashSet::new();
            for rec in &recursors {
                debug_assert!(
                    !self.constants.contains_key(&rec.name),
                    "{caller} duplicate constant: {}",
                    rec.name
                );
                debug_assert!(
                    !self.recursors.contains_key(&rec.name),
                    "{caller} duplicate recursor: {}",
                    rec.name
                );
                debug_assert!(
                    batch_names.insert(rec.name.clone()),
                    "{caller} duplicate recursor in batch: {}",
                    rec.name
                );
            }
        }
        // Add to constants map
        let names: Vec<Name> = recursors.iter().map(|rec| rec.name.clone()).collect();
        self.extend_resident_constants(recursors.iter().map(|rec| {
            (
                rec.name.clone(),
                ConstantInfo::new(
                    rec.name.clone(),
                    rec.level_params.clone(),
                    rec.type_.clone(),
                    None,
                    false,
                ),
            )
        }));
        // Add to recursors map
        self.recursors
            .extend(recursors.into_iter().map(|rec| (rec.name.clone(), rec)));
        for name in names {
            self.declaration_verification.insert(name, verification);
        }
        self.generation += 1;
    }

    /// Bulk register inductives, skipping duplicate checks — UNCHECKED (test-only).
    ///
    /// DEMOTED 2026-08-24 (R1-IND, census row `ind-meta-bulk`): every
    /// production caller now goes through
    /// [`extend_inductives_structural`](Self::extend_inductives_structural).
    /// This variant performs NO validation at all, so it is compiled only for
    /// test builds (the `test` cfg or the empty `test-fixtures` feature
    /// enabled by downstream dev-dependencies) — a production call no longer
    /// compiles.
    #[cfg(any(test, feature = "test-fixtures"))]
    #[inline]
    pub(crate) fn extend_inductives_unchecked(
        &mut self,
        inductives: impl Iterator<Item = InductiveVal>,
    ) {
        self.insert_inductives_raw(
            inductives.collect(),
            super::DeclarationVerification::Unchecked,
            "extend_inductives_unchecked",
        );
    }

    /// Bulk register inductives with structural validation (R1-IND).
    ///
    /// The structural tier for the `.olean` import's inductive-metadata leg,
    /// mirroring [`extend_constants_structural`](Self::extend_constants_structural):
    /// each record passes the same O(1) checks (no duplicate level params, no
    /// metavariables, no free variables, `Level::Param` scope) over every
    /// expression it carries before insertion; a failing record is diverted to
    /// the returned `Vec` and NEVER inserted (fail-closed refusal, named
    /// error). Inserted records are stamped `StructuralOnly`.
    ///
    /// Duplicate name checking is NOT performed here — callers pre-filter
    /// duplicates (as the import path already does). `num_indices` must be the
    /// type's arity minus `num_params` (`env/imported_family.rs`); the family
    /// itself (positivity, universes, constructor typing) is NOT re-checked.
    pub(crate) fn extend_inductives_structural(
        &mut self,
        inductives: impl Iterator<Item = InductiveVal>,
    ) -> Vec<(Name, EnvError)> {
        let mut valid = Vec::new();
        let mut rejected = Vec::new();
        for ind in inductives {
            // Derived arity metadata must be what the type determines
            // (env/imported_family.rs).
            match Self::validate_family_record_structural(
                &ind.name,
                &ind.level_params,
                &[&ind.type_],
            )
            .and_then(|()| self.check_imported_inductive(&ind))
            {
                Ok(()) => valid.push(ind),
                Err(e) => rejected.push((ind.name.clone(), e)),
            }
        }
        self.insert_inductives_raw(
            valid,
            super::DeclarationVerification::StructuralOnly,
            "extend_inductives_structural",
        );
        rejected
    }

    /// Bulk register constructors, skipping duplicate checks — UNCHECKED (test-only).
    ///
    /// DEMOTED 2026-08-24 (R1-IND, census row `ind-meta-bulk`): every
    /// production caller now goes through
    /// [`extend_constructors_structural`](Self::extend_constructors_structural).
    /// See [`extend_inductives_unchecked`](Self::extend_inductives_unchecked)
    /// for the gating rationale.
    #[cfg(any(test, feature = "test-fixtures"))]
    #[inline]
    pub(crate) fn extend_constructors_unchecked(
        &mut self,
        constructors: impl Iterator<Item = ConstructorVal>,
    ) {
        self.insert_constructors_raw(
            constructors.collect(),
            super::DeclarationVerification::Unchecked,
            "extend_constructors_unchecked",
        );
    }

    /// Bulk register constructors with structural validation (R1-IND) — see
    /// [`extend_inductives_structural`](Self::extend_inductives_structural).
    /// The owning inductive must already be resident, and the record's
    /// position, `num_params`, `num_fields` and universes must be the ones it
    /// and the constructor's type determine (`env/imported_family.rs`).
    pub(crate) fn extend_constructors_structural(
        &mut self,
        constructors: impl Iterator<Item = ConstructorVal>,
    ) -> Vec<(Name, EnvError)> {
        let mut valid = Vec::new();
        let mut rejected = Vec::new();
        for ctor in constructors {
            // Owner, position, num_params, num_fields and universes must be
            // what the resident inductive and the constructor's own type
            // determine (env/imported_family.rs).
            match Self::validate_family_record_structural(
                &ctor.name,
                &ctor.level_params,
                &[&ctor.type_],
            )
            .and_then(|()| self.check_imported_constructor(&ctor))
            {
                Ok(()) => valid.push(ctor),
                Err(e) => rejected.push((ctor.name.clone(), e)),
            }
        }
        self.insert_constructors_raw(
            valid,
            super::DeclarationVerification::StructuralOnly,
            "extend_constructors_structural",
        );
        rejected
    }

    /// Bulk register recursors, skipping duplicate checks — UNCHECKED (test-only).
    ///
    /// DEMOTED 2026-08-24 (R1-IND, census row `ind-meta-bulk`): every
    /// production caller now goes through
    /// [`extend_recursors_structural`](Self::extend_recursors_structural).
    /// See [`extend_inductives_unchecked`](Self::extend_inductives_unchecked)
    /// for the gating rationale.
    #[cfg(any(test, feature = "test-fixtures"))]
    #[inline]
    pub(crate) fn extend_recursors_unchecked(
        &mut self,
        recursors: impl Iterator<Item = RecursorVal>,
    ) {
        self.insert_recursors_raw(
            recursors.collect(),
            super::DeclarationVerification::Unchecked,
            "extend_recursors_unchecked",
        );
    }

    /// Bulk register recursors with structural validation (R1-IND) — see
    /// [`extend_inductives_structural`](Self::extend_inductives_structural).
    ///
    /// The validated expression set includes every rule's `rhs` alongside the
    /// recursor type: rule right-hand sides participate in ι-reduction, so a
    /// leaked fvar/mvar or out-of-scope level there is exactly the smuggle
    /// class the structural tier closes.
    ///
    /// Beyond scope checks, each record must EQUAL the recursor-table entry
    /// this kernel generates from the family already resident (its inductive
    /// and every constructor): type, universe arity, counts, `is_k`, argument
    /// order and every iota rule. A file's recursor is never reduction
    /// authority on its own — Lean's replay regenerates and compares the same
    /// way (`env/imported_family.rs`).
    pub(crate) fn extend_recursors_structural(
        &mut self,
        recursors: impl Iterator<Item = RecursorVal>,
    ) -> Vec<(Name, EnvError)> {
        let mut valid = Vec::new();
        let mut rejected = Vec::new();
        // A recursor must EQUAL the entry the kernel generates from its
        // resident family, as Lean's replay requires (env/imported_family.rs).
        let mut generated = super::imported_family::GeneratedRecursorCache::new();
        for rec in recursors {
            let mut exprs: Vec<&Expr> = Vec::with_capacity(1 + rec.rules.len());
            exprs.push(&rec.type_);
            exprs.extend(rec.rules.iter().map(|rule| &rule.rhs));
            let verdict =
                Self::validate_family_record_structural(&rec.name, &rec.level_params, &exprs);
            drop(exprs);
            let name = rec.name.clone();
            match verdict.and_then(|()| self.admit_imported_recursor(rec, &mut generated)) {
                Ok(admitted) => valid.push(admitted),
                Err(e) => rejected.push((name, e)),
            }
        }
        self.insert_recursors_raw(
            valid,
            super::DeclarationVerification::StructuralOnly,
            "extend_recursors_structural",
        );
        rejected
    }

    /// Register field names for a structure (single-constructor inductive).
    ///
    /// This allows elaboration to resolve named projections like `p.fst`.
    /// Field names must match the number of constructor fields (after parameters).
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn register_structure_fields(
        &mut self,
        struct_name: Name,
        field_names: Vec<Name>,
    ) -> Result<(), EnvError> {
        let ind = self
            .inductives
            .get(&struct_name)
            .ok_or_else(|| EnvError::UnknownInductive(struct_name.clone()))?;

        if ind.constructor_names.len() != 1 {
            return Err(EnvError::NotStructure(struct_name));
        }

        let ctor_name = &ind.constructor_names[0];
        let ctor = self.constructors.get(ctor_name).ok_or_else(|| {
            EnvError::UnknownInductive(struct_name.clone()) // should not happen if environment is consistent
        })?;

        let expected = ctor.num_fields;
        let actual = Self::usize_to_u32(field_names.len());
        if expected != actual {
            return Err(EnvError::InvalidFieldCount {
                struct_name,
                expected,
                actual,
            });
        }

        let mut seen = HashSet::new();
        for field in &field_names {
            if !seen.insert(field.clone()) {
                return Err(EnvError::DuplicateFieldName {
                    struct_name: ind.name.clone(),
                    field: field.clone(),
                });
            }
        }

        self.structure_fields.insert(ind.name.clone(), field_names);
        Ok(())
    }

    /// Get the field names for a registered structure
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn get_structure_field_names(&self, struct_name: &Name) -> Option<&[Name]> {
        self.structure_fields.get(struct_name).map(|v| v.as_slice())
    }

    /// Look up a field index by name for a registered structure.
    ///
    /// Returns the 0-based index of a field within a structure's field list.
    /// This is used for projection elaboration (e.g., `p.fst` → `Prod.fst p`).
    ///
    /// # Returns
    /// - `Some(index)` if `struct_name` is a registered structure and `field` is one of its fields
    /// - `None` if the structure is not registered or the field name is not found
    ///
    /// Structures must first be registered via [`Self::register_structure_fields`].
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    pub fn get_structure_field_index(&self, struct_name: &Name, field: &Name) -> Option<u32> {
        self.structure_fields.get(struct_name).and_then(|fields| {
            fields
                .iter()
                .position(|f| f == field)
                .map(Self::usize_to_u32)
        })
    }

    /// Register a default value for a structure field.
    ///
    /// This is an elaborator-only metadata channel: defaults are not consulted
    /// during type checking and do not affect the trusted kernel. They are
    /// stored here so that downstream elaboration (e.g. inheritance
    /// resolution) can read back the parent's default when building a child
    /// structure.
    ///
    /// The structure must already be registered via
    /// [`Self::register_structure_fields`]; otherwise this is a no-op store
    /// (the key is still inserted, mirroring the soft-storage model of
    /// other elaborator attribute maps).
    pub fn register_structure_field_default(
        &mut self,
        struct_name: Name,
        field: Name,
        default: Expr,
    ) {
        self.structure_field_defaults
            .entry(struct_name)
            .or_default()
            .insert(field, default);
    }

    /// Look up the default value for a structure field, if any.
    pub fn get_structure_field_default(&self, struct_name: &Name, field: &Name) -> Option<&Expr> {
        self.structure_field_defaults
            .get(struct_name)
            .and_then(|fields| fields.get(field))
    }

    /// Record the parent subobject fields of a structure declared with
    /// `extends`, as `(toParent_field_name, parent_struct_name)` pairs in
    /// constructor order.
    ///
    /// Elaborator-only metadata (mirrors Lean's `StructureFieldInfo.subobject?`
    /// in `src/Lean/Structure.lean`): it records which constructor fields are
    /// embedded parent structures, so anonymous-constructor flattening and
    /// structure-literal parent assembly can reconstruct the subobject. It is
    /// NOT consulted during type checking and does not affect the trusted
    /// kernel. Empty when a structure has no `extends` parents.
    pub fn register_structure_parents(&mut self, struct_name: Name, parents: Vec<(Name, Name)>) {
        if parents.is_empty() {
            return;
        }
        self.structure_parents.insert(struct_name, parents);
    }

    /// Look up the parent subobject fields of a structure, as
    /// `(toParent_field_name, parent_struct_name)` pairs in constructor order.
    /// Returns `None` for a structure with no recorded `extends` parents.
    pub fn get_structure_parents(&self, struct_name: &Name) -> Option<&[(Name, Name)]> {
        self.structure_parents
            .get(struct_name)
            .map(|v| v.as_slice())
    }
}
