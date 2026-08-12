// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Declaration registration and kernel check helpers.

use std::sync::atomic::{AtomicU64, Ordering};

use clean_kernel::env::TrustedEnvExt;
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

/// Get the current kernel check failure count.
pub fn kernel_check_failure_count() -> u64 {
    KERNEL_CHECK_FAILURE_COUNTER.load(Ordering::SeqCst)
}

/// Reset the kernel check failure counter (for tests).
pub fn reset_kernel_check_counter() {
    KERNEL_CHECK_FAILURE_COUNTER.store(0, Ordering::SeqCst);
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
                detail: source.to_string(),
            })
        }
        clean_kernel::EnvError::TheoremTypeNotProp { name, sort } => {
            Some(ElabError::KernelCheckFailed {
                name: name.clone(),
                detail: format!("type must be Prop, inferred sort {sort:?}"),
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

fn map_add_decl_error(operation: impl Into<String>, error: clean_kernel::EnvError) -> ElabError {
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
    match env.add_decl(decl) {
        Ok(()) => Ok(()),
        Err(e) => {
            if is_type_check_error(&e) {
                KERNEL_CHECK_FAILURE_COUNTER.fetch_add(1, Ordering::SeqCst);
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
    crate::derive::admit_generated_instance(
        env,
        &class_name.to_string(),
        parent_name,
        &registered_name,
        type_,
        value,
    )
    .map_err(map_derive_admission_error)?;

    add_decl_with_kernel_check(env, inst_decl, label)?;
    crate::derive::admit_registered_generated_instance(
        env,
        &class_name.to_string(),
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
    crate::derive::admit_generated_instance(
        env,
        &inst.class_name.to_string(),
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
    let stem = format!("{}._deriveAdmissionProbe", inst.name);
    let mut probe_name = Name::from_string(&stem);
    let mut suffix = 0_u32;
    while candidate.get_const(&probe_name).is_some() {
        suffix = suffix.checked_add(1).ok_or_else(|| {
            ElabError::InternalInvariant("derive admission probe namespace exhausted".to_owned())
        })?;
        probe_name = Name::from_string(&format!("{stem}{suffix}"));
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
    crate::derive::admit_registered_generated_instance(
        &candidate,
        &inst.class_name.to_string(),
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
    // Composite results perform several independently fallible environment
    // mutations (parent inductive, projections, generated instances, metadata,
    // or multiple leaves).  Commit them as one unit so a late failure cannot
    // leave a partially registered parent or prefix.
    if matches!(
        result,
        ElabResult::Structure { .. }
            | ElabResult::Inductive { .. }
            | ElabResult::MutualInductive { .. }
            | ElabResult::Multiple(_)
    ) {
        let mut candidate = env.clone();
        register_elab_result_in_place(&mut candidate, result)?;
        *env = candidate;
        return Ok(());
    }

    register_elab_result_in_place(env, result)
}

fn register_elab_result_in_place(
    env: &mut clean_kernel::Environment,
    result: &ElabResult,
) -> Result<(), ElabError> {
    use clean_kernel::Declaration;

    match result {
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
            use clean_kernel::{
                Constructor, InductiveDecl, InductiveType, KernelClassInfo, KernelInstanceInfo,
            };

            // Discharge any prelude AXIOM stubs whose names this genuine source
            // structure is about to claim. The prelude seeds a few typeclass
            // carriers as opaque `Axiom` shims — e.g. Mathlib's `Fact` is hand-
            // rolled as `Fact : Prop → Prop`, `Fact.mk`, `Fact.out` (see
            // `algebra_substructures.rs::init_fact`). When `Mathlib/Logic/Basic`
            // re-declares the genuine `class Fact (p : Prop) : Prop where out : p`
            // from source, `add_inductive` below (and the projection registration
            // that follows) would collide with those shims — "Duplicate
            // declaration: Fact" — leaving the axiom stub in place so that
            // `Fact.elim`/`fact_iff`'s `h.1` projection fails with "index
            // projection on non-structure type" (the stub is an axiom, not a
            // projectable inductive). Discharging the value-less stubs first lets
            // the real, kernel-checked structure register in their place — the
            // same swap the `.olean` import path performs. `discharge_…` only ever
            // removes a bare value-less `Axiom` (never a real structure/def), so a
            // genuine redefinition still errors below; it is a no-op when no stub
            // is present. SOUNDNESS: the genuine structure that immediately
            // registers has definitionally the stub's type, and nothing declared
            // earlier in this file referenced the stub, so no prior term changes
            // meaning; the swap only removes a fabricated axiom (strictly more
            // accurate axiom accounting), matching the documented import-path
            // contract.
            let _ = env.discharge_axiom_stub_for_inductive_import(name);
            let _ = env.discharge_axiom_stub_for_inductive_import(ctor_name);
            for (proj_name, _, _) in projections {
                let _ = env.discharge_axiom_stub_for_inductive_import(proj_name);
            }

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
            let ctor_param_infos: Vec<(String, clean_kernel::BinderInfo)> = projection_param_infos
                .iter()
                .take(projection_param_infos.len().saturating_sub(1))
                .map(|(n, _)| (n.clone(), clean_kernel::BinderInfo::Implicit))
                .chain(
                    field_names
                        .iter()
                        .map(|f| (f.to_string(), clean_kernel::BinderInfo::Default)),
                )
                .collect();
            if !ctor_param_infos.is_empty() {
                env.set_param_infos(ctor_name.clone(), ctor_param_infos);
            }

            // Register `extends` parent subobject metadata (elaborator-only):
            // `(toParent, Parent)` pairs so anonymous-constructor flattening and
            // structure-literal parent assembly can reconstruct the subobject.
            env.register_structure_parents(name.clone(), parents.clone());

            // Register in-file field defaults (`field : Type := value`) so a
            // structure literal that omits a defaulted field fills it with this
            // value (see `elab_struct_lit::field_default_value`). These are
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
                // `Struct.field (α := T)` resolves (B92).
                if !projection_param_infos.is_empty() {
                    env.set_param_infos(proj_name.clone(), projection_param_infos.clone());
                }
            }

            // If this is a class declaration, register the class with the kernel
            if let Some(info) = class_info {
                env.register_class(KernelClassInfo {
                    name: name.clone(),
                    num_params: info.num_params,
                    out_params: info.out_params.clone(),
                    semi_out_params: info.semi_out_params.clone(),
                });
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
) {
    use clean_kernel::Name;

    let (name, binders) = match decl {
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
    let infos: Vec<(String, clean_kernel::BinderInfo)> = binders
        .iter()
        .map(|b| (b.name.clone(), crate::infer::convert_binder_info(b.info)))
        .collect();
    env.set_param_infos(Name::from_string(name), infos);
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
/// then queries `ConstantInfo::trust_summary()` from the environment.
/// Returns `None` for `Skipped` results or fully verified declarations.
pub(crate) fn registration_warning_for_result(
    env: &clean_kernel::Environment,
    result: &ElabResult,
) -> Option<RegistrationWarning> {
    let name = result.declaration_name()?;
    registration_warning_for_name(env, name)
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
    let info = env.get_const(name)?;
    RegistrationWarning::from_summary(name.clone(), info.trust_summary())
}
