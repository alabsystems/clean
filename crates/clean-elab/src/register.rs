// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Declaration registration and kernel check helpers.

use std::sync::atomic::{AtomicU64, Ordering};

use clean_kernel::env::TrustedEnvExt;
use clean_kernel::expr::UsedConstants;
use clean_kernel::name::Name;
use clean_parser::DeclModifiers;
use clean_parser::Visibility;

use crate::error::ElabError;
use crate::infer::ElabResult;
use crate::registration_warning::RegistrationWarning;

// =============================================================================
// Kernel check observability (#2198, #2207)
// =============================================================================

/// Counter for declarations that fail full kernel type checking. Kernel type
/// checking is mandatory and fail-closed, so this is bumped whenever a kernel
/// type check rejects a declaration.
pub(crate) static KERNEL_CHECK_FAILURE_COUNTER: AtomicU64 = AtomicU64::new(0);

thread_local! {
    /// Thread-scoped shadow of [`KERNEL_CHECK_FAILURE_COUNTER`], bumped at the
    /// same site and reset by the same reset.
    ///
    /// It exists because **the process-global counter cannot attribute a
    /// failure to a caller when callers run concurrently**, and a test IS a
    /// concurrent caller: libtest gives each `#[test]` its own thread and runs
    /// many at once. A test that resets the global and then asserts it is 0 is
    /// asserting something about the whole process, not about its own
    /// declaration, so any sibling that legitimately fails a kernel check in
    /// the same window fails it — a false RED with a true subject.
    ///
    /// That is not hypothetical: it was latent for as long as the counter has
    /// existed and began firing deterministically the moment the shared prelude
    /// template cut `clean-elab`'s `misc_04` shard from 419 s to 58 s, which
    /// packs far more concurrent elaboration into every such window.
    ///
    /// Production keeps reading the global — `clean check` counts failures for
    /// a whole run, across every declaration, which is exactly what a
    /// process-wide counter means — and serialises its readers with
    /// `check_file_lock()` / `check::global_lock()` for the same reason this
    /// shadow exists. Widening the thread-scoped view to those callers is a
    /// separate change with its own measurement; it is not made here.
    static KERNEL_CHECK_FAILURES_ON_THIS_THREAD: std::cell::Cell<u64> =
        const { std::cell::Cell::new(0) };
}

/// Get the current kernel check failure count.
///
/// Process-wide by design: this is the count for the whole run, not for one
/// caller. Do not use it as a per-test instrument — see
/// [`KERNEL_CHECK_FAILURES_ON_THIS_THREAD`].
pub fn kernel_check_failure_count() -> u64 {
    KERNEL_CHECK_FAILURE_COUNTER.load(Ordering::SeqCst)
}

/// Kernel check failures recorded **on the calling thread**.
///
/// The race-free instrument for a test: no sibling test can move it. It is
/// also what `clean lake build` reads per module: the builder elaborates
/// independent modules on concurrent threads, so a module's own delta is only
/// attributable through this thread-scoped view, never through the global.
pub fn kernel_check_failures_on_this_thread() -> u64 {
    KERNEL_CHECK_FAILURES_ON_THIS_THREAD.with(std::cell::Cell::get)
}

/// Reset the kernel check failure counter (for tests).
pub fn reset_kernel_check_counter() {
    KERNEL_CHECK_FAILURE_COUNTER.store(0, Ordering::SeqCst);
    KERNEL_CHECK_FAILURES_ON_THIS_THREAD.with(|c| c.set(0));
}

/// Returns true if the error is a type-check failure (not structural).
fn is_type_check_error(e: &clean_kernel::EnvError) -> bool {
    matches!(
        e,
        clean_kernel::EnvError::TypeCheckFailed { .. }
            | clean_kernel::EnvError::TheoremTypeNotProp { .. }
    )
}

fn map_kernel_check_error(error: &clean_kernel::EnvError) -> Option<ElabError> {
    match error {
        clean_kernel::EnvError::TypeCheckFailed { name, source } => {
            Some(ElabError::KernelCheckFailed {
                name: name.clone(),
                // Rendered with user-facing private names by the variant's
                // `Display` (G21).
                detail: source.to_string(),
            })
        }
        clean_kernel::EnvError::TheoremTypeNotProp { name, sort } => {
            Some(ElabError::KernelCheckFailed {
                name: name.clone(),
                detail: format!(
                    "type must be Prop, inferred sort {}",
                    crate::error_render::level(sort)
                ),
            })
        }
        _ => None,
    }
}

fn kernel_registration_failed(
    operation: impl Into<String>,
    error: clean_kernel::EnvError,
) -> ElabError {
    ElabError::KernelRegistrationFailed {
        operation: operation.into(),
        detail: error.to_string(),
    }
}

pub(crate) fn map_add_decl_error(
    operation: impl Into<String>,
    error: clean_kernel::EnvError,
) -> ElabError {
    map_kernel_check_error(&error).unwrap_or_else(|| kernel_registration_failed(operation, error))
}

/// Opt-in retry for inductive declarations the kernel rejected with
/// `NestedParamsContainLocals` (a nested occurrence whose parameter
/// instantiation captures constructor-locals — the shape Lean rejects and
/// Rocq accepts). When `clean.inductive.liftNestedLocals` is enabled, the
/// capturing occurrences are lifted into specialized aux mutual families and
/// the resulting block is re-submitted through the ordinary CHECKED
/// `add_inductive` path (the first, failed attempt rolled the environment
/// back, so the retry starts clean). Fail-closed: with the option off, on a
/// different kernel error, or when the lift itself declines, the original
/// kernel error surfaces.
fn retry_add_inductive_with_local_lift(
    env: &mut clean_kernel::Environment,
    decl: &clean_kernel::InductiveDecl,
    operation: &str,
    original: clean_kernel::EnvError,
) -> Result<(), ElabError> {
    use clean_kernel::{EnvError, InductiveError};

    let lift_enabled = match env.get_option("clean.inductive.liftNestedLocals") {
        Some(Some(v)) => v != "false",
        _ => false, // default: disabled (opt-in Clean extension)
    };
    if !lift_enabled
        || !matches!(
            original,
            EnvError::Inductive(InductiveError::NestedParamsContainLocals)
        )
    {
        return Err(kernel_registration_failed(operation, original));
    }
    let lifted = match env.lift_nested_locals(decl) {
        Ok(lifted) => lifted,
        Err(lift_error) => {
            return Err(ElabError::KernelRegistrationFailed {
                operation: operation.to_string(),
                detail: format!("{original} (nested-local lift declined: {lift_error})"),
            });
        }
    };
    let clean_kernel::LocalLift {
        decl: lifted_decl,
        families,
        ..
    } = lifted;
    // Snapshot for the fail-closed paths below: a round-trip-guard or bridge
    // failure is evidence of a synthesis bug and must leave no trace.
    let snapshot = env.clone();
    env.add_inductive(lifted_decl).map_err(|e| {
        kernel_registration_failed(format!("{operation} (after nested-local lift)"), e)
    })?;

    // Round-trip guard (always when the lift fired): the registered block
    // must be re-derivable from the synthesis records.
    if let Err(guard_error) = env.verify_local_lift_anchor(decl, &families) {
        *env = snapshot;
        return Err(ElabError::KernelRegistrationFailed {
            operation: format!("{operation} (lift round-trip guard)"),
            detail: guard_error.to_string(),
        });
    }

    // Bridge lemmas (rung P3): kernel-checked equivalences back to the
    // user's original spelling. Declared limitations skip additively; any
    // attempted-and-failed synthesis or registration rolls the retry back.
    match env.synthesize_local_lift_bridges(decl, &families) {
        Ok(clean_kernel::BridgeOutcome::OutOfScope { reason }) => {
            tracing::warn!("nested-local lift: bridges skipped for {operation}: {reason}");
            Ok(())
        }
        Ok(clean_kernel::BridgeOutcome::Bridges(bridge_decls)) => {
            for bridge in bridge_decls {
                let label = match &bridge {
                    clean_kernel::Declaration::Theorem { name, .. } => {
                        format!("nested-local lift bridge {name}")
                    }
                    _ => "nested-local lift bridge".to_string(),
                };
                if let Err(e) = add_decl_with_kernel_check(env, bridge, &label) {
                    *env = snapshot;
                    return Err(e);
                }
            }
            Ok(())
        }
        Ok(_) => {
            // Future BridgeOutcome variants (#[non_exhaustive]): treat as a
            // declared skip rather than failing a working lift.
            Ok(())
        }
        Err(synth_error) => {
            *env = snapshot;
            Err(ElabError::KernelRegistrationFailed {
                operation: format!("{operation} (bridge synthesis)"),
                detail: synth_error.to_string(),
            })
        }
    }
}

/// Opt-in deep-induction post-pass (rung P4): when
/// `clean.inductive.deepInduction` is enabled and a just-registered type is
/// nested, generate the elementwise `T.deep_ind` principle (plus the
/// container's `All` family) as kernel-checked declarations. Declared
/// limitations skip additively with a warning; synthesis invariant failures
/// or kernel rejections fail the declaration (fail-closed).
/// Post-pass for `deriving ContainerRel`: synthesize the `C.rel` FAMILY.
///
/// Same contract as [`generate_container_map_post_pass`] — opt-in only, loud on
/// decline, fail-closed on an unrecognized outcome. Differs in ONE way that
/// matters: `C.rel` is an inductive family, so it registers through
/// `add_inductive` (re-earning positivity, universes and constructor checks)
/// rather than `add_decl_with_kernel_check`.
fn generate_container_rel_post_pass(
    env: &mut clean_kernel::Environment,
    name: &Name,
    explicit: bool,
) -> Result<(), ElabError> {
    if !explicit {
        return Ok(());
    }
    match env.synthesize_container_rel(name) {
        Ok(clean_kernel::ContainerRelOutcome::OutOfScope { reason }) => {
            Err(ElabError::Unsupported {
                feature: format!("deriving ContainerRel for {name}: {reason}"),
            })
        }
        Ok(clean_kernel::ContainerRelOutcome::Decls { families }) => {
            for fam in families {
                env.add_inductive(fam).map_err(|e| {
                    kernel_registration_failed(format!("container rel family for {name}"), e)
                })?;
            }
            Ok(())
        }
        // `#[non_exhaustive]`: an unrecognized outcome must not be read as
        // success on a path that REGISTERS declarations.
        Ok(other) => Err(ElabError::Unsupported {
            feature: format!(
                "deriving ContainerRel for {name}: unrecognized synthesis outcome \
                 {other:?} — refusing rather than assuming success"
            ),
        }),
        Err(synth) => Err(ElabError::KernelRegistrationFailed {
            operation: format!("container rel for {name}"),
            detail: synth.to_string(),
        }),
    }
}

/// Post-pass for `deriving ContainerMap`: synthesize `C.map`.
///
/// Mirrors [`generate_deep_induction_post_pass`], including its loudness rule —
/// an EXPLICIT derive is never silently skipped, so a declined synthesis is an
/// error rather than a warning. The synthesized definition goes through the
/// ordinary CHECKED `add_decl_with_kernel_check`.
///
/// This is opt-in only: nothing runs without `deriving ContainerMap` on the
/// declaration. `synthesize_container_map` was previously reachable from tests
/// alone — real dead-code debt, since its sibling `synthesize_deep_induction`
/// has had a production caller here all along. This is that caller.
fn generate_container_map_post_pass(
    env: &mut clean_kernel::Environment,
    name: &Name,
    explicit: bool,
) -> Result<(), ElabError> {
    if !explicit {
        return Ok(());
    }
    match env.synthesize_container_map(name) {
        Ok(clean_kernel::ContainerMapOutcome::OutOfScope { reason }) => {
            Err(ElabError::Unsupported {
                feature: format!("deriving ContainerMap for {name}: {reason}"),
            })
        }
        Ok(clean_kernel::ContainerMapOutcome::Decls { definitions }) => {
            for def in definitions {
                let label = format!("container map for {name}");
                add_decl_with_kernel_check(env, def, &label)?;
            }
            Ok(())
        }
        // `ContainerMapOutcome` is `#[non_exhaustive]`. A future variant must not
        // be treated as success by default: this path REGISTERS declarations, so
        // "outcome I do not recognize" has to mean "register nothing and say so".
        // (The deep-induction sibling takes the opposite default, `Ok(_) => {}`;
        // that is the weaker choice and not worth copying.)
        Ok(other) => Err(ElabError::Unsupported {
            feature: format!(
                "deriving ContainerMap for {name}: unrecognized synthesis outcome \
                 {other:?} — refusing rather than assuming success"
            ),
        }),
        Err(synth) => Err(ElabError::KernelRegistrationFailed {
            operation: format!("container map for {name}"),
            detail: synth.to_string(),
        }),
    }
}

fn generate_deep_induction_post_pass(
    env: &mut clean_kernel::Environment,
    type_names: &[Name],
    explicit: bool,
) -> Result<(), ElabError> {
    let enabled = explicit
        || match env.get_option("clean.inductive.deepInduction") {
            Some(Some(v)) => v != "false",
            _ => false, // default: disabled (opt-in Clean extension)
        };
    if !enabled {
        return Ok(());
    }
    for name in type_names {
        let is_nested = env.get_inductive(name).is_some_and(|iv| iv.is_nested);
        if !is_nested {
            if explicit {
                return Err(ElabError::Unsupported {
                    feature: format!(
                        "deriving DeepInduction: {name} is not a nested inductive (v1)"
                    ),
                });
            }
            continue;
        }
        match env.synthesize_deep_induction(name) {
            Ok(clean_kernel::DeepIndOutcome::OutOfScope { reason }) => {
                if explicit {
                    // Explicit `deriving DeepInduction` is never silently
                    // skipped (design §Scope: loud on decline).
                    return Err(ElabError::Unsupported {
                        feature: format!("deriving DeepInduction for {name}: {reason}"),
                    });
                }
                tracing::warn!("deep induction skipped for {name}: {reason}");
            }
            Ok(clean_kernel::DeepIndOutcome::Decls {
                all_families,
                theorems,
            }) => {
                for fam in all_families {
                    env.add_inductive(fam).map_err(|e| {
                        kernel_registration_failed(
                            format!("deep-induction All family for {name}"),
                            e,
                        )
                    })?;
                }
                for thm in theorems {
                    let label = format!("deep induction for {name}");
                    add_decl_with_kernel_check(env, thm, &label)?;
                }
            }
            Ok(_) => {}
            Err(synth) => {
                return Err(ElabError::KernelRegistrationFailed {
                    operation: format!("deep induction for {name}"),
                    detail: synth.to_string(),
                });
            }
        }
    }
    Ok(())
}

/// Add a declaration with kernel type checking (#2198, #2207, #2454).
///
/// Kernel type checking is unconditional and fail-closed: this always runs
/// `add_decl` (full kernel type check), bumps `KERNEL_CHECK_FAILURE_COUNTER` on a
/// type-check failure, and returns the error without structurally registering a
/// rejected declaration.
fn add_decl_with_kernel_check(
    env: &mut clean_kernel::Environment,
    decl: clean_kernel::Declaration,
    label: &str,
) -> Result<(), ElabError> {
    let mut refs = std::collections::HashSet::new();
    use clean_kernel::expr::UsedConstants;
    match &decl {
        clean_kernel::Declaration::Definition { type_, value, .. }
        | clean_kernel::Declaration::Theorem { type_, value, .. }
        | clean_kernel::Declaration::Opaque { type_, value, .. } => {
            type_.used_constants_dag(UsedConstants::ConstantsOnly, &mut refs);
            value.used_constants_dag(UsedConstants::ConstantsOnly, &mut refs);
        }
        clean_kernel::Declaration::Axiom { type_, .. } => {
            type_.used_constants_dag(UsedConstants::ConstantsOnly, &mut refs);
        }
    }
    let roots = refs.into_iter().collect();
    let mut candidate = env.needs_bootstrap_stubs(&roots).then(|| env.clone());
    let target = candidate.as_mut().unwrap_or(&mut *env);
    prepare_bootstrap_stubs(target, &roots)?;
    match target.add_decl(decl) {
        Ok(()) => {
            if let Some(candidate) = candidate {
                *env = candidate;
            }
            Ok(())
        }
        Err(e) => {
            if is_type_check_error(&e) {
                KERNEL_CHECK_FAILURE_COUNTER.fetch_add(1, Ordering::SeqCst);
                KERNEL_CHECK_FAILURES_ON_THIS_THREAD.with(|c| c.set(c.get().saturating_add(1)));
            }
            tracing::warn!("add_decl failed for {label}: {e}");
            Err(map_add_decl_error(format!("add_decl {label}"), e))
        }
    }
}

fn map_derive_admission_error(error: crate::derive::DeriveError) -> ElabError {
    ElabError::Unsupported {
        feature: error.to_string(),
    }
}

/// Register and fully audit one generated instance. Automatic deriving is an
/// explicit source obligation: every admission or kernel failure propagates to
/// the parent declaration; no class has a best-effort escape hatch.
fn register_derived_instance(
    env: &mut clean_kernel::Environment,
    inst_decl: clean_kernel::Declaration,
    class_name: &Name,
    parent_name: &str,
    label: &str,
) -> Result<(), ElabError> {
    let (decl_name, type_, value) = match &inst_decl {
        clean_kernel::Declaration::Definition {
            name, type_, value, ..
        } => (name, type_, value),
        _ => {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "automatic deriving {class_name} returned a non-definition declaration"
                ),
            });
        }
    };
    let registered_name = decl_name.clone();
    crate::derive::admit_generated_instance_typed(
        env,
        class_name,
        parent_name,
        &registered_name,
        type_,
        value,
    )
    .map_err(map_derive_admission_error)?;

    add_decl_with_kernel_check(env, inst_decl, label)?;
    crate::derive::admit_registered_generated_instance_typed(
        env,
        class_name,
        parent_name,
        &registered_name,
    )
    .map_err(map_derive_admission_error)
}

/// Validate an elaborator-produced instance even when its declaration name
/// already exists and registration would otherwise take the metadata-only
/// path. Name collisions must not bypass the derive admission boundary.
fn admit_elaborated_derived_instance(
    env: &clean_kernel::Environment,
    parent_name: &str,
    inst: &crate::infer::DerivedInstance,
) -> Result<(), ElabError> {
    crate::derive::admit_generated_instance_typed(
        env,
        &inst.class_name,
        parent_name,
        &inst.name,
        &inst.ty,
        &inst.val,
    )
    .map_err(map_derive_admission_error)
}

/// Kernel-check a legitimate projection-backed parent instance even though its
/// public name is already occupied by the projection definition.  Validation
/// happens under a fresh private probe name in a cloned environment; only the
/// checked type/value are subsequently installed as instance metadata.
fn validate_projection_backed_instance(
    env: &clean_kernel::Environment,
    parent_name: &str,
    inst: &crate::infer::DerivedInstance,
) -> Result<(), ElabError> {
    let mut candidate = env.clone();
    let stem = inst.name.clone().str("_deriveAdmissionProbe");
    let mut probe_name = stem.clone();
    let mut suffix = 0_u32;
    while candidate.get_const(&probe_name).is_some() {
        suffix = suffix.checked_add(1).ok_or_else(|| {
            ElabError::InternalInvariant("derive admission probe namespace exhausted".to_owned())
        })?;
        probe_name = stem.clone().num(u64::from(suffix));
    }
    let probe_decl = clean_kernel::Declaration::Definition {
        name: probe_name.clone(),
        level_params: inst.level_params.clone(),
        type_: inst.ty.clone(),
        value: inst.val.clone(),
        is_reducible: true,
    };
    add_decl_with_kernel_check(
        &mut candidate,
        probe_decl,
        "projection-backed derived instance",
    )?;
    crate::derive::admit_registered_generated_instance_typed(
        &candidate,
        &inst.class_name,
        parent_name,
        &probe_name,
    )
    .map_err(map_derive_admission_error)
}

fn derived_name_collision(parent_name: &str, inst_name: &Name) -> ElabError {
    ElabError::KernelRegistrationFailed {
        operation: format!("register derived instance for {parent_name}"),
        detail: format!(
            "generated instance name `{inst_name}` collides with an existing declaration"
        ),
    }
}

/// Apply declaration modifiers (private, protected, noncomputable, partial, unsafe)
/// to the environment after a declaration has been registered.
fn apply_modifiers(env: &mut clean_kernel::Environment, name: &Name, modifiers: &DeclModifiers) {
    match modifiers.visibility {
        Visibility::Private => {
            env.mark_private(name.clone());
            // A mangled `_private.M.0.Foo.bar` has no `Foo` prefix, so the
            // prefix rule of `is_namespace` no longer sees `Foo`: register the
            // user-facing parent namespace, as Lean's implicit `namespace Foo`
            // does (`private theorem Foo.bar` then `open Foo` is accepted by
            // Lean 4.8.0; G21).
            if let Some(user) = crate::private_names::private_to_user_name(name) {
                let parent = crate::namespace::parent_name(&user);
                if !parent.is_anon() {
                    env.register_namespace(&parent);
                }
            }
        }
        Visibility::Protected => {
            env.mark_protected(name.clone());
        }
        Visibility::Public => {}
    }
    if modifiers.is_noncomputable {
        env.mark_noncomputable(name.clone());
    }
    if modifiers.is_partial {
        env.mark_partial(name.clone());
    }
    if modifiers.is_unsafe {
        env.mark_unsafe(name.clone());
    }
}

/// Register an elaboration result in the environment
///
/// Converts `ElabResult` variants to kernel declarations and adds them.
/// Kernel type checking is mandatory and fail-closed (#2454, matching the TLA+
/// spec): rejected declarations are never structurally registered.
pub(crate) fn register_elab_result(
    env: &mut clean_kernel::Environment,
    result: &ElabResult,
) -> Result<(), ElabError> {
    // Diagnostics do not change the enclosed declaration or its transaction.
    if let ElabResult::Diagnosed { result, .. } = result {
        return register_elab_result(env, result);
    }
    // Backstop for the source-level refusal (`check_not_reserved_kernel_name`):
    // no elaborated result — auxiliary `where` / `let rec` definitions,
    // constructors and projections included — registers a name reserved for a
    // kernel-owned axiom, structurally or by printed form. The kernel's own
    // declarations are installed by the prelude providers, never through here.
    if let Some(reserved) = leaf_own_names(result)
        .into_iter()
        .find(clean_kernel::is_reserved_ambient_axiom_name)
    {
        return Err(ElabError::ReservedKernelName {
            name: reserved.to_unambiguous_string(),
            printed: reserved.to_string(),
        });
    }
    let roots = bootstrap_roots(env, result);
    // Composite results perform several independently fallible environment
    // mutations (parent inductive, projections, generated instances, metadata,
    // or multiple leaves).  Commit them as one unit so a late failure cannot
    // leave a partially registered parent or prefix.
    if env.needs_bootstrap_stubs(&roots)
        || matches!(
            result,
            ElabResult::Structure { .. }
                | ElabResult::Inductive { .. }
                | ElabResult::MutualInductive { .. }
                | ElabResult::Multiple(_)
        )
    {
        let mut candidate = env.clone();
        prepare_bootstrap_stubs(&mut candidate, &roots)?;
        register_elab_result_in_place(&mut candidate, result)?;
        *env = candidate;
        return Ok(());
    }

    register_elab_result_in_place(env, result)
}

fn bootstrap_roots(
    env: &clean_kernel::Environment,
    result: &ElabResult,
) -> std::collections::BTreeSet<Name> {
    if let ElabResult::Diagnosed { result, .. } = result {
        return bootstrap_roots(env, result);
    }
    let mut roots = result.cited_roots(env);
    roots.extend(leaf_own_names(result));
    if let ElabResult::Multiple(results) = result {
        for result in results {
            roots.extend(bootstrap_roots(env, result));
        }
    }
    roots
}

fn prepare_bootstrap_stubs(
    env: &mut clean_kernel::Environment,
    roots: &std::collections::BTreeSet<Name>,
) -> Result<(), ElabError> {
    // Fixed bootstrap checks, not user proof search. The declaration's own
    // mandatory kernel check retains its original budget and refusal policy.
    clean_kernel::tc::with_declaration_budget_suspended(|| {
        env.init_requested_bootstrap_stubs(roots)
    })
    .map_err(|e| map_add_decl_error("requested bootstrap stub theory", e))
}

/// `clean lean`'s refusals for one leaf before it registers (docs/DECISIONS.md
/// R135, [`crate::lean_compile_checks`]): a safe leaf that uses an `unsafe`
/// constant (Lean's kernel safe context). These are actual admission refusals;
/// code-generation diagnostics are emitted after successful registration and
/// attribute application by `lean_compile_checks::diagnose_registered`.
fn safe_context_refusal(
    env: &clean_kernel::Environment,
    name: &Name,
    ty: &clean_kernel::Expr,
    value: Option<&clean_kernel::Expr>,
    modifiers: &DeclModifiers,
) -> Result<(), ElabError> {
    use crate::lean_compile_checks as checks;
    if !checks::front_door_active() {
        return Ok(());
    }
    if !modifiers.is_unsafe {
        if let Some(constant) = checks::unsafe_dependency(env, std::iter::once(ty).chain(value)) {
            return Err(ElabError::KernelCheckFailed {
                name: name.clone(),
                detail: checks::unsafe_message(&constant),
            });
        }
    }
    Ok(())
}

fn register_elab_result_in_place(
    env: &mut clean_kernel::Environment,
    result: &ElabResult,
) -> Result<(), ElabError> {
    use clean_kernel::Declaration;

    // An `opaque` the elaborator found inhabited only by `Nonempty` inside a
    // `noncomputable section` is marked, as Lean marks it (R134).
    for name in crate::lean_compile_checks::take_deferred_noncomputable_marks() {
        env.mark_noncomputable(name);
    }

    match result {
        ElabResult::Diagnosed { result, .. } => return register_elab_result_in_place(env, result),
        ElabResult::Definition {
            name,
            universe_params,
            ty,
            val,
            modifiers,
        } => {
            // Always use full kernel registration; rejected declarations are not
            // structurally registered. Part of #1301, #2198, #2207.
            //
            // In Lean 4, `abbrev` creates `ReducibilityHints.Abbreviation` (always
            // unfoldable), while `def` creates `ReducibilityHints.Regular(height)`.
            // `is_reducible: true` → `Reducibility::Reducible` (abbreviation)
            // `is_reducible: false` → `Reducibility::Regular(height)` (normal def)
            // Part of #3391.
            let is_reducible = modifiers.is_abbrev;
            // U2 rung-0b histogram: a surviving FRESH-minted level param
            // (`u_N` / `_u.N`) on a registering definition is an implicit
            // auto-generalization — the levelMVarToParam (rung 4) workload.
            if crate::u2_histogram::u2_hist_enabled() {
                for lp in universe_params {
                    let n = lp.to_string();
                    let is_fresh = n
                        .strip_prefix("u_")
                        .is_some_and(|rest| rest.chars().all(|c| c.is_ascii_digit()))
                        || n.starts_with("_u.");
                    if is_fresh {
                        crate::u2_histogram::u2_hist(
                            "generalized-fresh-param",
                            "register-def",
                            &format!("{name} keeps {n}"),
                        );
                    }
                }
            }
            safe_context_refusal(env, name, ty, Some(val), modifiers)?;
            let decl = Declaration::Definition {
                name: name.clone(),
                level_params: universe_params.clone(),
                type_: ty.clone(),
                value: val.clone(),
                is_reducible,
            };
            add_decl_with_kernel_check(env, decl, "Definition")?;
            apply_modifiers(env, name, modifiers);
        }
        ElabResult::Theorem {
            name,
            universe_params,
            ty,
            proof,
            modifiers,
        } => {
            // Always use full kernel registration; rejected declarations are not
            // structurally registered.
            // Part of #1301, #2198, #2207.
            safe_context_refusal(env, name, ty, Some(proof), modifiers)?;
            let decl = Declaration::Theorem {
                name: name.clone(),
                level_params: universe_params.clone(),
                type_: ty.clone(),
                value: proof.clone(),
            };
            add_decl_with_kernel_check(env, decl, "Theorem")?;
            apply_modifiers(env, name, modifiers);
        }
        ElabResult::Axiom {
            name,
            universe_params,
            ty,
            modifiers,
        } => {
            safe_context_refusal(env, name, ty, None, modifiers)?;
            let decl = Declaration::Axiom {
                name: name.clone(),
                level_params: universe_params.clone(),
                type_: ty.clone(),
            };
            add_decl_with_kernel_check(env, decl, "Axiom")?;
            apply_modifiers(env, name, modifiers);
        }
        // Opaque with body: register as Declaration::Opaque for kernel type check.
        // Opaque without body: register as Declaration::Axiom (kernel has no val-less
        // opaque form). Both paths use full kernel registration. Fixes #2552.
        ElabResult::Opaque {
            name,
            universe_params,
            ty,
            val,
            modifiers,
        } => {
            safe_context_refusal(env, name, ty, val.as_ref(), modifiers)?;
            if let Some(val) = val {
                let decl = Declaration::Opaque {
                    name: name.clone(),
                    level_params: universe_params.clone(),
                    type_: ty.clone(),
                    value: val.clone(),
                };
                add_decl_with_kernel_check(env, decl, "Opaque")?;
            } else {
                let decl = Declaration::Axiom {
                    name: name.clone(),
                    level_params: universe_params.clone(),
                    type_: ty.clone(),
                };
                add_decl_with_kernel_check(env, decl, "Axiom (opaque without body)")?;
            }
            crate::source_kind::record(env, name, clean_kernel::env::ConstantKind::Opaque);
            apply_modifiers(env, name, modifiers);
        }
        // Instance declarations need to be registered
        ElabResult::Instance {
            name,
            universe_params,
            class_name,
            ty,
            val,
            priority,
            modifiers,
            ..
        } => {
            // Always use full kernel registration; rejected declarations are not
            // structurally registered.
            // Part of #1301, #2198, #2207.
            safe_context_refusal(env, name, ty, Some(val), modifiers)?;
            let decl = Declaration::Definition {
                name: name.clone(),
                level_params: universe_params.clone(),
                type_: ty.clone(),
                value: val.clone(),
                is_reducible: true,
            };
            add_decl_with_kernel_check(env, decl, "Instance")?;

            // Register the instance in the kernel-side instance registry so
            // SUBSEQUENT declarations see it: each declaration's `ElabCtx`
            // rebuilds its `InstanceTable` from `env.classes()` +
            // `env.get_class_instances(..)` (`infer/elab_init.rs`), so an
            // instance that is only added as a `Definition` is invisible to
            // every later `C.f x` use site. Lean ground truth: `elabInstance`
            // applies the `instance` attribute, which calls `addInstance` into
            // the instance extension (lean4 `src/Lean/Meta/Instances.lean`).
            // `type_`/`value` are left `None` so resolution uses the registered
            // CONSTANT (correct binder infos, Lean-faithful `instFoo …` term
            // shape — see the #443 comment in `elab_init.rs`). B06.
            //
            // An instance of a reducible class ALIAS (`instance : DecidableLT
            // T`) is filed under the alias, which must then be a registered
            // class for the table rebuild to load its bucket
            // (`crate::instance_alias`; a no-op for an ordinary class).
            crate::instance_alias::register_alias_class(env, class_name);
            env.register_instance(clean_kernel::KernelInstanceInfo {
                name: name.clone(),
                class_name: class_name.clone(),
                priority: *priority,
                type_: None,
                value: None,
            });
            apply_modifiers(env, name, modifiers);
        }
        // Structure declarations - need proper registration
        // Fixes #163: structures weren't being registered, causing UnknownIdent errors
        ElabResult::Structure {
            name,
            universe_params,
            num_params,
            ty,
            ctor_name,
            ctor_ty,
            field_names,
            field_defaults,
            projections,
            projection_param_infos,
            parents,
            derived_instances,
            class_info,
            modifiers,
        } => {
            use clean_kernel::{Constructor, InductiveDecl, InductiveType, KernelInstanceInfo};

            // Ordinary registration never discharges existing declarations.
            // The closed builtin Fact transaction authenticates and completes
            // only its own newly created slots before calling this registrar.
            // Add as an inductive type
            let decl = InductiveDecl {
                level_params: universe_params.clone(),
                num_params: *num_params,
                types: vec![InductiveType {
                    name: name.clone(),
                    type_: ty.clone(),
                    constructors: vec![Constructor {
                        name: ctor_name.clone(),
                        type_: ctor_ty.clone(),
                    }],
                }],
            };
            env.add_inductive(decl)
                .map_err(|e| kernel_registration_failed("add_inductive Structure", e))?;

            // Register field names for projection resolution
            env.register_structure_fields(name.clone(), field_names.clone())
                .map_err(|e| kernel_registration_failed("register_structure_fields", e))?;

            // Named-argument binder row for the CONSTRUCTOR: the struct's
            // params (implicit in the ctor telescope) then the fields
            // (explicit), so `S.mk (A := T) (fst := x)` resolves by name —
            // the ctor-arm of `resolve_named_args` leaves param slots
            // unnamed, which failed LOUD before this row existed (U2 rung 2
            // follow-on to the B92 projection rows).
            let ctor_param_infos: Vec<(Name, clean_kernel::BinderInfo)> = projection_param_infos
                .iter()
                .take(projection_param_infos.len().saturating_sub(1))
                .map(|(n, _)| (n.name().clone(), clean_kernel::BinderInfo::Implicit))
                .chain(
                    field_names
                        .iter()
                        .map(|f| (f.clone(), clean_kernel::BinderInfo::Default)),
                )
                .collect();
            if !ctor_param_infos.is_empty() {
                env.set_typed_param_infos(ctor_name.clone(), ctor_param_infos);
            }

            // Register `extends` parent subobject metadata (elaborator-only):
            // `(toParent, Parent)` pairs so anonymous-constructor flattening and
            // structure-literal parent assembly can reconstruct the subobject.
            env.register_structure_parents(name.clone(), parents.clone());

            // Register in-file field defaults (`field : Type := value`) so a
            // structure literal that omits a defaulted field fills it with this
            // value (see `elab_struct_lit_inherit::field_default_value`). These are
            // elaborator-side metadata only — not consulted by type checking —
            // and every filled default is re-checked by the kernel when the
            // completed constructor application is elaborated.
            for (field, default_val) in field_defaults {
                env.register_structure_field_default(
                    name.clone(),
                    field.clone(),
                    default_val.clone(),
                );
            }

            // Add projection functions as definitions.  Part of #1301, #2198, #2207.
            for (proj_name, proj_ty, proj_val) in projections {
                let proj_decl = Declaration::Definition {
                    name: proj_name.clone(),
                    level_params: universe_params.clone(),
                    type_: proj_ty.clone(),
                    value: proj_val.clone(),
                    is_reducible: true,
                };
                add_decl_with_kernel_check(env, proj_decl, "projection")?;
                // Named-argument binder row (struct binders + `self`) so
                // `Struct.field (α := T)` resolves (B92). The names are the
                // structure's; the kinds are this projection's own telescope.
                // Lean's `mkProjections` infers each projection's implicit
                // parameters from that field's type (`Tg.tg : (α : Type) →
                // {β : Type} → [self : Tg α β] → β → Nat`), so the binders as
                // written are not the kinds, and a positional argument after
                // `(α := Int)` must skip the implicit `β`.
                if !projection_param_infos.is_empty() {
                    let mut telescope = proj_ty;
                    let row = projection_param_infos
                        .iter()
                        .map(|(n, written)| {
                            let info = match telescope.kind() {
                                clean_kernel::ExprKind::Pi(binder, _, body) => {
                                    telescope = body;
                                    binder.info
                                }
                                _ => *written,
                            };
                            (n.name().clone(), info)
                        })
                        .collect();
                    env.set_typed_param_infos(proj_name.clone(), row);
                }
            }

            if class_info.is_some() {
                crate::class_attribute::register_new_declaration(env, name)?;
            }

            // Register derived instances (including toParent instances from extends clause).
            // Full kernel registration; rejected declarations are not structurally
            // registered.
            // Part of #1301.
            for inst in derived_instances {
                let parent_name = name.to_string();
                admit_elaborated_derived_instance(env, &parent_name, inst)?;
                if env.get_const(&inst.name).is_some() {
                    // The sole legitimate collision is a generated `toParent`
                    // instance backed by the projection of the same name and
                    // class. Validate its metadata term independently under a
                    // probe name. Every other collision is an error; silently
                    // reusing an unrelated constant would bind instance
                    // metadata without kernel-checking the generated value.
                    // `parents` stores the UNQUALIFIED subobject field name
                    // (`toC1`), while the generated instance is qualified
                    // (`C2.toC1`) — qualify before comparing.
                    let projection_backed = parents.iter().any(|(projection, parent)| {
                        Name::append(name, &projection.to_string()) == inst.name
                            && parent == &inst.class_name
                    });
                    if !projection_backed {
                        return Err(derived_name_collision(&parent_name, &inst.name));
                    }
                    validate_projection_backed_instance(env, &parent_name, inst)?;
                } else {
                    // Use the instance's own level_params, NOT the struct's universe_params.
                    // Derive handlers generate fresh universe params (e.g., u_0) for
                    // universe-polymorphic constants they reference. These must be declared
                    // in the instance declaration.  Fixes #3393.
                    let inst_decl = Declaration::Definition {
                        name: inst.name.clone(),
                        level_params: inst.level_params.clone(),
                        type_: inst.ty.clone(),
                        value: inst.val.clone(),
                        is_reducible: true,
                    };
                    register_derived_instance(
                        env,
                        inst_decl,
                        &inst.class_name,
                        &parent_name,
                        "derived instance",
                    )?;
                }

                // Register the instance metadata with type/value for proper binder info (#443).
                // This is important for toParent instances which may share names with projections
                // but need different binder info (Implicit/InstImplicit vs Default).
                env.register_instance(KernelInstanceInfo {
                    name: inst.name.clone(),
                    class_name: inst.class_name.clone(),
                    priority: inst.priority,
                    type_: Some(inst.ty.clone()),
                    value: Some(inst.val.clone()),
                });
            }

            apply_modifiers(env, name, modifiers);
        }

        // Inductive declarations - need proper registration
        ElabResult::Inductive {
            name,
            universe_params,
            num_params,
            ty,
            constructors,
            derived_instances,
            wants_deep_induction,
            wants_container_map,
            wants_container_rel,
            modifiers,
        } => {
            use clean_kernel::{Constructor, InductiveDecl, InductiveType, KernelInstanceInfo};

            // Add as an inductive type
            let decl = InductiveDecl {
                level_params: universe_params.clone(),
                num_params: *num_params,
                types: vec![InductiveType {
                    name: name.clone(),
                    type_: ty.clone(),
                    constructors: constructors
                        .iter()
                        .map(|(n, t)| Constructor {
                            name: n.clone(),
                            type_: t.clone(),
                        })
                        .collect(),
                }],
            };
            if let Err(e) = env.add_inductive(decl.clone()) {
                retry_add_inductive_with_local_lift(env, &decl, "add_inductive Inductive", e)?;
            }
            generate_deep_induction_post_pass(
                env,
                std::slice::from_ref(name),
                *wants_deep_induction,
            )?;
            generate_container_map_post_pass(env, name, *wants_container_map)?;
            generate_container_rel_post_pass(env, name, *wants_container_rel)?;

            // Register derived instances with full kernel registration. Part of
            // #1301.
            for inst in derived_instances {
                let parent_name = name.to_string();
                admit_elaborated_derived_instance(env, &parent_name, inst)?;
                if env.get_const(&inst.name).is_some() {
                    return Err(derived_name_collision(&parent_name, &inst.name));
                } else {
                    // Use instance's own level_params — same fix as for structures.
                    // Fixes #3393.
                    let inst_decl = Declaration::Definition {
                        name: inst.name.clone(),
                        level_params: inst.level_params.clone(),
                        type_: inst.ty.clone(),
                        value: inst.val.clone(),
                        is_reducible: true,
                    };
                    register_derived_instance(
                        env,
                        inst_decl,
                        &inst.class_name,
                        &parent_name,
                        "inductive instance",
                    )?;
                }

                // Register with type/value for proper binder info (#443)
                env.register_instance(KernelInstanceInfo {
                    name: inst.name.clone(),
                    class_name: inst.class_name.clone(),
                    priority: inst.priority,
                    type_: Some(inst.ty.clone()),
                    value: Some(inst.val.clone()),
                });
            }

            apply_modifiers(env, name, modifiers);
        }

        // A mutual inductive family is registered in ONE `add_inductive` call so
        // the kernel resolves cross-references between the types and builds the
        // mutual recursors. The kernel re-checks positivity and every
        // constructor type; a rejected family surfaces as a real error here
        // rather than being silently dropped.
        ElabResult::MutualInductive {
            decl,
            derived_instances,
            modifiers,
        } => {
            if let Err(e) = env.add_inductive(decl.clone()) {
                retry_add_inductive_with_local_lift(env, decl, "add_inductive MutualInductive", e)?;
            }
            let member_names: Vec<Name> = decl.types.iter().map(|t| t.name.clone()).collect();
            generate_deep_induction_post_pass(env, &member_names, false)?;

            // Register derived instances through the same fail-closed path as
            // the single-inductive case.
            let parent_name = decl
                .types
                .iter()
                .map(|ind| ind.name.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            for inst in derived_instances {
                admit_elaborated_derived_instance(env, &parent_name, inst)?;
                if env.get_const(&inst.name).is_some() {
                    return Err(derived_name_collision(&parent_name, &inst.name));
                } else {
                    let inst_decl = Declaration::Definition {
                        name: inst.name.clone(),
                        level_params: inst.level_params.clone(),
                        type_: inst.ty.clone(),
                        value: inst.val.clone(),
                        is_reducible: true,
                    };
                    register_derived_instance(
                        env,
                        inst_decl,
                        &inst.class_name,
                        &parent_name,
                        "mutual inductive instance",
                    )?;
                }
                env.register_instance(clean_kernel::KernelInstanceInfo {
                    name: inst.name.clone(),
                    class_name: inst.class_name.clone(),
                    priority: inst.priority,
                    type_: Some(inst.ty.clone()),
                    value: Some(inst.val.clone()),
                });
            }

            // Apply modifiers to every type in the family.
            for ind_ty in &decl.types {
                apply_modifiers(env, &ind_ty.name, modifiers);
            }
        }

        ElabResult::Multiple(results) => {
            for inner in results {
                register_elab_result_in_place(env, inner)?;
            }
        }
        ElabResult::Command(_) => {}
        ElabResult::Skipped => {}
        // An `example` is fully elaborated and kernel-checked but NEVER
        // registered — Lean checks then discards it (lean4
        // `src/Lean/Elab/Declaration.lean`, `elabExample`). B02.
        ElabResult::Example { .. } => {}
        // A direct registration request must never turn a recorded failure into
        // success. Namespace/section elaboration reports these leaves without
        // re-registering its already-processed siblings; callers that do pass a
        // `Multiple` here get a transactional error, not a green result with a
        // hidden failed member.
        ElabResult::Failed { error, .. } => return Err((**error).clone()),
    }
    Ok(())
}

/// Extract and register parameter names from a surface declaration (#1230).
///
/// Stores binder names in the environment so that the elaborator can match
/// named arguments (e.g., `f(y := 1)`) to the correct parameter position.
pub(crate) fn register_param_names(
    env: &mut clean_kernel::Environment,
    decl: &clean_parser::SurfaceDecl,
    result: &ElabResult,
) {
    use clean_kernel::Name;

    // The value's own `∀` binder names, for named arguments on a head whose
    // type unfolds to it (`h (a₁ := x)` with `h : Injective f`).
    crate::value_binder_names::register_value_forall_binder_names(env, decl, result);

    if matches!(decl, clean_parser::SurfaceDecl::Alias { .. }) {
        let mut leaves = Vec::new();
        result.leaf_decls(&mut leaves);
        for leaf in leaves {
            let (name, value) = match leaf {
                ElabResult::Definition { name, val, .. } => (name, val),
                ElabResult::Theorem { name, proof, .. } => (name, proof),
                _ => continue,
            };
            let mut body = value;
            while let clean_kernel::ExprKind::Lam(_, _, inner) = body.kind() {
                body = inner;
            }
            let target_expr = if matches!(decl, clean_parser::SurfaceDecl::Alias { names, .. } if names.first().is_some_and(|(_, direction)| direction.is_some()))
            {
                let args = body.get_app_args();
                if args.len() != 3 {
                    continue;
                }
                args[2].get_app_fn()
            } else {
                body.get_app_fn()
            };
            let clean_kernel::ExprKind::Const(target, _) = target_expr.kind() else {
                continue;
            };
            let Some(names) = env
                .get_typed_param_names(target)
                .map(<[Name]>::to_vec)
                .or_else(|| {
                    env.get_param_names(target).map(|names| {
                        names
                            .iter()
                            .map(|name| Name::anon().str(name.as_str()))
                            .collect()
                    })
                })
            else {
                continue;
            };
            let Some(info) = env.get_const(target) else {
                continue;
            };
            let mut ty = info.type_.clone();
            let mut infos = Vec::new();
            for name in names {
                let clean_kernel::ExprKind::Pi(binder, _, body) = ty.kind() else {
                    break;
                };
                infos.push((name, binder.info));
                ty = body.as_ref().clone();
            }
            // The target's names and kinds, written for the ALIAS: through the
            // kernel's checked boundary, as a declared prefix of the alias's
            // own telescope, like the lifted helpers' (`decl_attributes`). An
            // alias whose own binders disagree gets no metadata, so a named
            // argument on it is refused rather than placed by another
            // declaration's kinds.
            if let Err(error) = env.add_checked_param_infos(name, infos, false) {
                tracing::debug!("alias `{name}`: parameter metadata not recorded: {error}");
            }
        }
        return;
    }

    let (_, binders) = match decl {
        clean_parser::SurfaceDecl::Def { name, binders, .. }
        | clean_parser::SurfaceDecl::Theorem { name, binders, .. }
        | clean_parser::SurfaceDecl::Axiom { name, binders, .. }
        | clean_parser::SurfaceDecl::Opaque { name, binders, .. } => (name, binders),
        _ => return,
    };

    if binders.is_empty() {
        return;
    }

    // B01 (GAP_SWEEP_2026-07-09): record binder KINDS alongside the names so
    // named-argument resolution can fill positional args into the remaining
    // *explicit* binders only (lean4 `src/Lean/Elab/App.lean`, `ElabAppArgs`).
    let infos: Vec<(Name, clean_kernel::BinderInfo)> = binders
        .iter()
        .map(|b| {
            (
                b.name.name().clone(),
                crate::infer::convert_binder_info(b.info),
            )
        })
        .collect();
    // Bind metadata to the declaration actually registered, including its exact
    // namespace qualification; the surface spelling is not a lookup key. A
    // declaration with lifted `where` / `let rec` helpers is the parent of
    // its result; the helpers' own names travel with the collected
    // attributes (`crate::decl_attributes`).
    let name = match result.primary_leaf() {
        Some(
            ElabResult::Definition { name, .. }
            | ElabResult::Theorem { name, .. }
            | ElabResult::Axiom { name, .. }
            | ElabResult::Opaque { name, .. },
        ) => name,
        _ => return,
    };
    env.set_typed_param_infos(name.clone(), infos);
}

/// Register an aesop rule from a parsed attribute
///
/// This should be called after a declaration with `@[aesop ...]` attribute
/// has been elaborated and added to the environment.
///
/// # Arguments
/// * `env` - The environment to register the rule in
/// * `name` - The name of the declaration (theorem/def) this rule applies to
/// * `attr` - The parsed aesop attribute
///
/// # Example
/// ```text
/// // After parsing: @[aesop safe apply] theorem my_intro : A -> B
/// let attr = AesopAttr { phase: AesopPhase::Safe, builder: AesopBuilder::Apply, priority: None, rule_sets: vec![] };
/// register_aesop_rule(&mut env, Name::from_string("my_intro"), &attr);
/// ```
pub fn register_aesop_rule(
    env: &mut clean_kernel::Environment,
    name: Name,
    attr: &clean_parser::AesopAttr,
) {
    use clean_kernel::{AesopRule, AesopRuleBuilder, AesopRulePhase};

    // Convert parser types to kernel types
    let phase = match attr.phase {
        clean_parser::AesopPhase::Safe => AesopRulePhase::Safe,
        clean_parser::AesopPhase::Unsafe => AesopRulePhase::Unsafe,
        clean_parser::AesopPhase::Norm => AesopRulePhase::Norm,
    };

    let builder = match attr.builder {
        clean_parser::AesopBuilder::Apply => AesopRuleBuilder::Apply,
        clean_parser::AesopBuilder::Cases => AesopRuleBuilder::Cases,
        clean_parser::AesopBuilder::Constructors => AesopRuleBuilder::Constructors,
        clean_parser::AesopBuilder::Destruct => AesopRuleBuilder::Destruct,
        clean_parser::AesopBuilder::Forward => AesopRuleBuilder::Forward,
        clean_parser::AesopBuilder::Simp => AesopRuleBuilder::Simp,
        clean_parser::AesopBuilder::Tactic => AesopRuleBuilder::Tactic,
        clean_parser::AesopBuilder::Unfold => AesopRuleBuilder::Unfold,
    };

    let index_mode = match attr.index_mode {
        clean_parser::AesopIndexMode::Target => clean_kernel::AesopIndexMode::Target,
        clean_parser::AesopIndexMode::Hyps => clean_kernel::AesopIndexMode::Hyps,
        clean_parser::AesopIndexMode::Unindexed => clean_kernel::AesopIndexMode::Unindexed,
    };

    // Default priority is 100 for safe/norm, use specified for unsafe
    let priority = attr.priority.unwrap_or(100);

    let builder_args = attr
        .builder_args
        .iter()
        .map(|s| Name::from_string(s))
        .collect();

    let rule = AesopRule {
        name,
        phase,
        builder,
        builder_args,
        priority,
        index_mode,
        transparency: clean_kernel::TransparencyMode::default(),
    };

    // If rule sets are specified, register to those sets; otherwise default set
    if attr.rule_sets.is_empty() {
        env.register_aesop_rule(rule);
    } else {
        // Register to each specified rule set
        for rule_set_name in &attr.rule_sets {
            let set_name = Name::from_string(rule_set_name);
            // Auto-declare the rule set if not already declared
            if !env.is_aesop_rule_set_declared(&set_name) {
                env.declare_aesop_rule_set(set_name.clone());
            }
            env.register_aesop_rule_to_set(&set_name, rule.clone());
        }
    }
}

/// Compute a registration warning for a just-registered declaration.
///
/// Uses `ElabResult::declaration_name()` to select the primary declaration,
/// then reads its trust debt from its own terms AND its constant closure (see
/// [`registration_warning_for_name`]).
/// Returns `None` for `Skipped` results or fully verified declarations.
pub(crate) fn registration_warning_for_result(
    env: &clean_kernel::Environment,
    result: &ElabResult,
) -> Option<RegistrationWarning> {
    let name = result.declaration_name()?;
    registration_warning_for_name(env, name)
}

/// The trust warning for ONE checked declaration leaf, as a checker that
/// credits leaves must read it.
///
/// A registered declaration is looked up by name. An `example` is never
/// registered (Lean checks then discards it), so it has no name to look up:
/// its warning is computed from its own elaborated type and value. Reading it
/// by name answered `None` for every `example`, so `clean project check`
/// credited `example : 1 = 2 := sorry` as a pass (round-22 verification).
///
/// CLOSURE-BASED: a leaf uses sorry iff `sorryAx` / `sorry` is in the constant
/// closure of the roots it cites ([`ElabResult::cited_roots`]) — in any
/// position, behind any alias or lemma. This builds a fresh closure memo per
/// call; a checker that asks for many leaves passes its run's memo to
/// [`registration_warning_for_leaf_in`] instead.
#[must_use]
pub fn registration_warning_for_leaf(
    env: &clean_kernel::Environment,
    leaf: &ElabResult,
) -> Option<RegistrationWarning> {
    let mut closure = clean_kernel::env::DomainAxiomClosure::new();
    registration_warning_for_leaf_in(&mut closure, env, leaf)
}

/// [`registration_warning_for_leaf`] with the caller's closure memo, so a run
/// that checks many leaves walks each constant's closure once.
#[must_use]
pub fn registration_warning_for_leaf_in(
    closure: &mut clean_kernel::env::DomainAxiomClosure,
    env: &clean_kernel::Environment,
    leaf: &ElabResult,
) -> Option<RegistrationWarning> {
    let (decl_name, own_names, mut summary) = match leaf {
        ElabResult::Example { ty, val, .. } => {
            let mut summary = clean_kernel::env::DeclarationTrustSummary::from_expr(ty);
            summary.merge(clean_kernel::env::DeclarationTrustSummary::from_expr(val));
            (Name::from_string("example"), Vec::new(), summary)
        }
        _ => {
            let name = leaf.declaration_name()?.clone();
            let mut own_names: Vec<Name> = Vec::new();
            let mut summary = clean_kernel::env::DeclarationTrustSummary::default();
            for own in leaf_own_names(leaf) {
                if let Some(info) = env.get_const(&own) {
                    summary.merge(info.trust_summary());
                }
                own_names.push(own);
            }
            (name, own_names, summary)
        }
    };
    let mut roots = leaf.cited_roots(env);
    roots.extend(
        own_names
            .iter()
            .filter(|own| env.get_const(own).is_some())
            .cloned(),
    );
    let mut markers = std::collections::BTreeSet::new();
    for root in &roots {
        markers.extend(closure.trust_markers_of_name(env, root));
    }
    let inherited = summary.absorb_closure_markers(markers.iter());
    let mut warning = RegistrationWarning::from_summary(decl_name, summary)?;
    if inherited {
        warning.via = inherited_via(closure, env, &roots, &own_names);
    }
    Some(warning)
}

/// The trust debt a leaf's OWN terms carry, without its constant closure.
///
/// Lean's `declaration uses 'sorry'` warning is this reading
/// (`Declaration.hasSorry` over the declaration's own expressions): `theorem t
/// := lemma1`, with `lemma1` a `sorry`, logs nothing for `t`. The checkers
/// read the closure ([`registration_warning_for_leaf_in`]) because a pass
/// that rests on a `sorry` anywhere is not a verification; `clean lean`,
/// which reproduces Lean's messages, reads this one.
#[must_use]
pub fn own_trust_summary(
    env: &clean_kernel::Environment,
    leaf: &ElabResult,
) -> clean_kernel::env::DeclarationTrustSummary {
    match leaf {
        ElabResult::Example { ty, val, .. } => {
            let mut summary = clean_kernel::env::DeclarationTrustSummary::from_expr(ty);
            summary.merge(clean_kernel::env::DeclarationTrustSummary::from_expr(val));
            summary
        }
        _ => {
            let mut summary = clean_kernel::env::DeclarationTrustSummary::default();
            for own in leaf_own_names(leaf) {
                if let Some(info) = env.get_const(&own) {
                    summary.merge(info.trust_summary());
                }
            }
            summary
        }
    }
}

/// The names a leaf itself registers (its own debt is read from these).
pub(crate) fn leaf_own_names(leaf: &ElabResult) -> Vec<Name> {
    match leaf {
        ElabResult::Diagnosed { result, .. } => leaf_own_names(result),
        ElabResult::Definition { name, .. }
        | ElabResult::Theorem { name, .. }
        | ElabResult::Axiom { name, .. }
        | ElabResult::Opaque { name, .. }
        | ElabResult::Instance { name, .. } => vec![name.clone()],
        ElabResult::Inductive {
            name, constructors, ..
        } => std::iter::once(name.clone())
            .chain(constructors.iter().map(|(ctor, _)| ctor.clone()))
            .collect(),
        ElabResult::MutualInductive { decl, .. } => decl
            .types
            .iter()
            .flat_map(|ty| {
                std::iter::once(ty.name.clone())
                    .chain(ty.constructors.iter().map(|ctor| ctor.name.clone()))
            })
            .collect(),
        ElabResult::Structure {
            name,
            ctor_name,
            projections,
            ..
        } => std::iter::once(name.clone())
            .chain(std::iter::once(ctor_name.clone()))
            .chain(projections.iter().map(|(proj, _, _)| proj.clone()))
            .collect(),
        ElabResult::Multiple(results) => results.iter().flat_map(leaf_own_names).collect(),
        _ => leaf.declaration_name().into_iter().cloned().collect(),
    }
}

/// The cited constants (other than the declaration's own names) whose closure
/// carries a trust marker — the "through" of an inherited warning.
fn inherited_via(
    closure: &mut clean_kernel::env::DomainAxiomClosure,
    env: &clean_kernel::Environment,
    roots: &std::collections::BTreeSet<Name>,
    own_names: &[Name],
) -> Vec<Name> {
    roots
        .iter()
        .filter(|root| !own_names.contains(root) && !clean_kernel::is_trust_marker(root))
        .filter(|root| !closure.trust_markers_of_name(env, root).is_empty())
        .cloned()
        .collect()
}

/// The DOMAIN axioms (neither foundational nor a trust marker) a checked
/// leaf's verdict rests on: the union of the closures of every root the leaf
/// cites ([`ElabResult::cited_roots`]), which includes the leaf's own
/// registered names — so an `axiom` leaf discloses itself, and an `example`
/// is reached through its terms. A checker that credits the leaf must
/// disclose a non-empty answer; the pass is assumption-bearing.
#[must_use]
pub fn leaf_domain_axioms(
    closure: &mut clean_kernel::env::DomainAxiomClosure,
    env: &clean_kernel::Environment,
    leaf: &ElabResult,
) -> std::collections::BTreeSet<Name> {
    let mut out = std::collections::BTreeSet::new();
    for root in leaf.cited_roots(env) {
        out.extend(closure.of_name(env, &root).iter().cloned());
    }
    out
}

/// Compute a registration (trust) warning for an already-registered declaration
/// identified by name.
///
/// This is the by-name counterpart to [`registration_warning_for_result`]. It is
/// used by `clean check` to surface per-declaration trust status for the leaf
/// declarations nested inside a `namespace`/`section` block (which elaborate to
/// a single [`ElabResult::Multiple`]), so that each inner declaration is counted
/// and reported individually rather than collapsed into one uncounted unit.
///
/// Returns `None` when the declaration is unknown or fully verified.
pub fn registration_warning_for_name(
    env: &clean_kernel::Environment,
    name: &Name,
) -> Option<RegistrationWarning> {
    let mut closure = clean_kernel::env::DomainAxiomClosure::new();
    registration_warning_for_name_in(&mut closure, env, name)
}

/// [`registration_warning_for_name`] with the caller's closure memo.
///
/// CLOSURE-BASED, as [`registration_warning_for_leaf_in`]: the declaration's
/// own terms (any occurrence of a marker, whatever its arguments) and every
/// trust marker in its constant closure.
fn registration_warning_for_name_in(
    closure: &mut clean_kernel::env::DomainAxiomClosure,
    env: &clean_kernel::Environment,
    name: &Name,
) -> Option<RegistrationWarning> {
    let info = env.get_const(name)?;
    let mut summary = info.trust_summary();
    let markers = closure.trust_markers_of_name(env, name);
    let inherited = summary.absorb_closure_markers(markers.iter());
    let mut warning = RegistrationWarning::from_summary(name.clone(), summary)?;
    if inherited {
        let mut refs = std::collections::HashSet::new();
        // DAG walks (G76): shared subterms are visited once.
        info.type_
            .used_constants_dag(UsedConstants::ConstantsOnly, &mut refs);
        if let Some(value) = &info.value {
            value.used_constants_dag(UsedConstants::ConstantsOnly, &mut refs);
        }
        let roots: std::collections::BTreeSet<Name> = refs.into_iter().collect();
        warning.via = inherited_via(closure, env, &roots, std::slice::from_ref(name));
    }
    Some(warning)
}

#[cfg(test)]
#[path = "register_alias_metadata_tests.rs"]
mod alias_metadata_tests;
