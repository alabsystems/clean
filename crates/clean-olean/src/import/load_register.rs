// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Module registration: converting parsed constants into kernel Environment entries.
//!
//! Internal functions for registering inductives, constructors, recursors, and
//! other constants from `ParsedModule` into the kernel `Environment`.

use super::convert::{
    compute_recursive_fields_from_env, convert_parsed_constant, decl_to_constant_info,
    is_inductive_family_kind, ConvertedConstant,
};
use super::convert_direct::convert_load_constant;
use super::convert_expr_direct::RegionPtrCache;
use super::default_fn_binders::{
    record_default_fn_binders_from_parsed, record_default_fn_binders_from_region,
};
use super::load_parse::LoadModule;
use super::load_shadowing::{
    foreign_resident_provenance, refused_duplicates_loaded, refused_duplicates_parsed, ShadowedAt,
};
use super::{ExprInternCache, ImportError, LoadSummary, OleanImportPolicy, SkippedConstant};
use crate::module::typed_extensions::{
    legacy_display_extension_projection, TypedExtension, TypedExtensionEntry,
};
use crate::module::{
    ConstantKind, DefinitionSafety, ParsedExtensionEntryData, ParsedModule, LEAN_ALIAS_EXTENSION,
    LEAN_CLASS_EXTENSION, LEAN_INSTANCE_EXTENSION, LEAN_SIMP_EXTENSION,
};
use crate::payload::CleanPayload;
use clean_kernel::env::{
    attr_ext_idx, instance_ext_idx, register_persistent_ext, simp_ext_idx, AttrExtState,
    ConstantKind as KernelConstantKind, ConstantOrigin, EnvExtensionEntry, EnvExtensionEntryData,
    Environment, ExtensionIdx, InstanceExtState, KernelClassInfo, KernelInstanceInfo,
    PersistentExtEntry, PersistentExtState, ProofValueElision, Reducibility, SimpExtState,
    SimpPriority, TrustedEnvExt,
};
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::inductive::Constructor;
use clean_kernel::name::Name;
use hashbrown::{HashMap, HashSet};

mod deferred_recursors;
use deferred_recursors::RecursorStaging;
pub(crate) use deferred_recursors::{refresh_artifact_families, DeferredRecursors};

#[cfg(test)]
mod csimp_metadata_tests;
#[cfg(test)]
mod family_record_tests;
#[cfg(test)]
mod instance_metadata_tests;
#[cfg(test)]
mod large_elim_fixup_tests;
#[cfg(test)]
mod matcher_metadata_tests;
#[cfg(test)]
mod structure_projection_tests;

/// Preserve non-safe declaration authority after trusted `.olean` registration.
///
/// Lean excludes unsafe axioms, opaques, definitions, and inductive-family
/// declarations, plus partial definitions, from the trusted logical fragment.
/// A mark is applied only when the accepted declaration still has the exact
/// source kind. This prevents a failed `.olean.private` definition/opaque
/// upgrade from leaving authority on the surviving axiom stub, and prevents a
/// rejected family declaration from leaving a latent name-only mark.
fn apply_declaration_safety_marks(
    env: &mut Environment,
    marks: impl IntoIterator<Item = (Name, ConstantKind, DefinitionSafety)>,
) {
    for (name, kind, safety) in marks {
        let accepted = match kind {
            ConstantKind::Definition => env
                .get_const(&name)
                .is_some_and(|info| info.kind == KernelConstantKind::Definition),
            ConstantKind::Axiom => env
                .get_const(&name)
                .is_some_and(|info| info.kind == KernelConstantKind::Axiom),
            ConstantKind::Opaque => env
                .get_const(&name)
                .is_some_and(|info| info.kind == KernelConstantKind::Opaque),
            ConstantKind::Inductive => env.get_inductive(&name).is_some(),
            ConstantKind::Constructor => env.get_constructor(&name).is_some(),
            ConstantKind::Recursor => env.get_recursor(&name).is_some(),
            // TheoremVal and QuotVal have no declaration-safety field.
            ConstantKind::Theorem | ConstantKind::Quot => false,
        };
        if !accepted {
            continue;
        }
        match safety {
            DefinitionSafety::Unsafe => env.mark_unsafe(name),
            DefinitionSafety::Partial if kind == ConstantKind::Definition => {
                env.mark_partial(name);
            }
            // `partial` is not a valid state for the other declaration kinds.
            // Treat an internally-constructed impossible mark as unsafe rather
            // than granting ordinary safe authority.
            DefinitionSafety::Partial => env.mark_unsafe(name),
            DefinitionSafety::Safe => {}
        }
    }
}

/// Whether a declaration the `.olean` stores is one `Lean.Environment.replay`
/// never admits: `unsafe` or `partial` (`!ci.isUnsafe && !ci.isPartial`,
/// `src/lean/Lean/Replay.lean`). Recorded for the compiler artifacts the loader
/// skips (`LoadSummary::skipped_not_replayable`), so a replay can leave such a
/// skipped artifact out, as Lean's does, instead of refusing it: measured
/// 2026-09-25, `clean olean replay --fresh` over `Init.Prelude` otherwise
/// refused `Array.appendCore.loop._unsafe_rec`, an `unsafe` definition.
pub(super) fn stored_unsafe_or_partial(
    kind: &ConstantKind,
    safety: Option<DefinitionSafety>,
) -> bool {
    matches!(
        kind,
        ConstantKind::Definition | ConstantKind::Axiom | ConstantKind::Opaque
    ) && matches!(
        safety,
        Some(DefinitionSafety::Unsafe | DefinitionSafety::Partial)
    )
}

/// Record the stub completions the kernel refused at the checked upgrade
/// (R131) and, under a re-check lane's policy
/// ([`OleanImportPolicy::refusing_refused_completions`]), refuse the import by
/// the first one.
///
/// A refused completion of the artifact's OWN stub leaves the stub resident.
/// Lean reads the declaration with the refused value (`writeModule` stubs a
/// public theorem in the `.olean` and keeps the theorem in the
/// `.olean.private`), so the stub is not a declaration Lean reads, and trusting
/// it as an axiom accepted what the kernel refused: before R131 the sharded
/// worker counted such a stub as an accepted axiom and verified its user, and
/// verify-batch's full re-check passed both (review finding S1). Each is a
/// typed [`LoadSummary::refused_completions`] row, which a replay refuses by
/// name. A value for a stub another owner holds (the checker's own prelude) is
/// a skipped constant only, as before: the module's declaration of a name the
/// environment already holds. An `unsafe`/`partial` value is not a row either
/// (Lean's replay never admits it, `LoadSummary::skipped_not_replayable`).
fn record_refused_completions(
    env: &Environment,
    summary: &mut LoadSummary,
    artifact: &super::artifact_ledger::ArtifactKey,
    refused: Vec<(Name, clean_kernel::env::EnvError)>,
    unreplayable: &HashSet<&str>,
    policy: OleanImportPolicy,
) -> Result<(), ImportError> {
    let mut first: Option<(String, String)> = None;
    for (name, err) in refused {
        let label = name.to_string();
        let reason = err.to_string();
        if unreplayable.contains(label.as_str()) {
            summary.skipped_not_replayable.push(label.clone());
        } else if super::artifact_ledger::declared_by_this_artifact(env, &name, artifact) {
            if first.is_none() {
                first = Some((label.clone(), reason.clone()));
            }
            summary.refused_completions.push((name, reason.clone()));
        }
        summary.skipped_constants.push(SkippedConstant {
            name: label,
            reason: format!("axiom stub upgrade refused (kernel check): {reason}"),
        });
    }
    match first {
        Some((name, reason)) if policy.refuses_refused_completions() => {
            Err(ImportError::CompletionRefused {
                module: artifact
                    .clone()
                    .unwrap_or_else(|| "<unnamed module>".to_string()),
                name,
                reason,
            })
        }
        _ => Ok(()),
    }
}

/// Upgrade a part's `.olean.private` values over its axiom stubs, re-offering the
/// refused ones for as long as another upgrade succeeds.
///
/// [`TrustedEnvExt::upgrade_axiom_stubs_checked`] kernel-checks each value
/// against the environment AS IT STANDS, in the part's order, so a value whose
/// type reduces only through a sibling stub later in the same batch was refused
/// and left as a value-less stub. Measured 2026-09-25 by `clean olean replay
/// --fresh` over `Init.Prelude`: `Lean.Macro.State.noConfusion` was refused
/// (`Type mismatch … noConfusionType … (_private…Lean.Macro.State.mk l x x1)`),
/// so the loader kept a stub where Lean's replay checks the stored value.
/// Every attempt is the same checked upgrade; the fixpoint changes only the
/// ORDER in which values are offered, and terminates because each round that
/// continues upgrades at least one of them.
fn upgrade_stubs_to_fixpoint(
    env: &mut Environment,
    candidates: Vec<clean_kernel::env::ConstantInfo>,
) -> (usize, Vec<(Name, clean_kernel::env::EnvError)>) {
    let mut pending = candidates;
    let mut upgraded = 0usize;
    loop {
        let (round, refused) = env.upgrade_axiom_stubs_checked(pending.clone().into_iter());
        upgraded += round;
        if round == 0 || refused.is_empty() {
            return (upgraded, refused);
        }
        let refused_names: HashSet<Name> = refused.into_iter().map(|(name, _)| name).collect();
        pending.retain(|info| refused_names.contains(&info.name));
    }
}

/// A diagnostic name hint for compiler/code-generator auxiliaries.
///
/// Lean permits safe logical declarations with these same names. A name alone
/// is never authority to omit a `ConstantInfo` from import, custody, or replay.
/// Use [`is_nonreplayable_compiler_constant`] for the legacy parsed-record skip
/// policy; the direct loader applies the same independent stored-safety check.
/// IR-only declarations remain in the producer's separate IR/extra-name role.
pub fn is_compiler_ir_name(name: &str) -> bool {
    if is_compile_inductive_impl_artifact(name) {
        return true;
    }
    name.split('.').any(|component| {
        component == "_cstage1"
            || component == "_cstage2"
            || component == "_rarg"
            || component == "_unsafe_rec"
            || component.starts_with("_elambda")
            || component.starts_with("_lambda")
            || component.starts_with("_spec")
    })
}

/// Apply the diagnostic hint only to actual Name components. Quoted dots
/// never create namespace edges. This does not classify a kernel declaration.
pub(crate) fn is_typed_compiler_ir_name(name: &Name) -> bool {
    use clean_kernel::name::NameInner;
    let mut current = name;
    loop {
        match current.inner() {
            NameInner::Anon => break,
            NameInner::Str(parent, component) => {
                if matches!(
                    component.as_ref(),
                    "_cstage1" | "_cstage2" | "_rarg" | "_unsafe_rec"
                ) || component.starts_with("_elambda")
                    || component.starts_with("_lambda")
                    || component.starts_with("_spec")
                {
                    return true;
                }
                current = parent;
            }
            NameInner::Num(parent, _) => current = parent,
        }
    }
    // The existing special-case policy is textual. Only an exactly reversible
    // projection may reach it; the projection is not used for kernel lookup.
    let projected = name.to_string();
    Name::from_string(&projected) == *name && is_compile_inductive_impl_artifact(&projected)
}

/// Whether the parsed constant may keep the existing compiler-auxiliary skip.
///
/// Both conditions are required: a historical compiler-name hint AND the
/// record's own unsafe/partial flag. Lean's replay independently excludes the
/// latter. Safe or unknown-safety kernel records must be converted and checked,
/// including compiler-looking user definitions and malformed old artifacts.
/// This says nothing about native executability or dependency closure.
#[must_use]
pub fn is_nonreplayable_compiler_constant(constant: &crate::ParsedConstant) -> bool {
    is_compiler_ir_name(&constant.name)
        && stored_unsafe_or_partial(&constant.kind, constant.definition_safety)
}

/// Source roles established before any part registers. A payload owns the
/// names it declares; its Lean-format mirrors cannot supply original safety.
pub(super) struct ArtifactRecordRoles {
    pub(super) compiler_exclusions: HashSet<Name>,
    pub(super) payload_names: HashSet<Name>,
}

impl ArtifactRecordRoles {
    pub(super) fn from_parts(authoritative: &LoadModule, parts: &[&LoadModule]) -> Self {
        let payload_names: HashSet<Name> = parts
            .iter()
            .filter_map(|part| part.clean_payload.as_ref())
            .flat_map(|payload| payload.declared_names::<Vec<Name>>())
            .collect();
        let compiler_exclusions = authoritative
            .constants
            .iter()
            .filter(|constant| {
                !payload_names.contains(&constant.kernel_name)
                    && is_typed_compiler_ir_name(&constant.kernel_name)
                    && stored_unsafe_or_partial(&constant.kind, constant.definition_safety)
            })
            .map(|constant| constant.kernel_name.clone())
            .collect();
        Self {
            compiler_exclusions,
            payload_names,
        }
    }
}

/// Capture payload-owned declarations even when no Lean mirror exists, and
/// without borrowing safety from an intentionally shadowed mirror. The current
/// payload format carries no original declaration-safety metadata; None stays
/// an explicit unknown-safety census refusal, not Safe or NotReplayable.
fn payload_declarations(payload: Option<&CleanPayload>) -> Vec<(Name, Option<DefinitionSafety>)> {
    payload
        .into_iter()
        .flat_map(|payload| payload.declared_names::<Vec<Name>>())
        .map(|name| (name, None))
        .collect()
}

/// Legacy diagnostic hints for known Mathlib runtime implementation records.
/// These exact spellings do not authorize omitting a safe ConstantInfo; the
/// record-aware policy still requires independent unsafe/partial metadata.
fn is_compile_inductive_impl_artifact(name: &str) -> bool {
    const COMPILE_INDUCTIVE_PREFIX: &str = "_private.Mathlib.Util.CompileInductive.";

    name.strip_prefix(COMPILE_INDUCTIVE_PREFIX)
        .and_then(strip_private_index_segment)
        .is_some_and(|tail| {
            matches!(
                tail,
                "Float.mkImpl" | "Float.valImpl" | "Float.mk_eq" | "Float.val_eq"
            )
        })
}

/// Strip the leading `<digits>.` private-namespace index segment Lean inserts
/// after `_private.<module>.` (e.g. the `1.` in `_private.…CompileInductive.1.…`),
/// returning the remaining suffix. Returns `None` if there is no such segment.
fn strip_private_index_segment(rest: &str) -> Option<&str> {
    let (idx, tail) = rest.split_once('.')?;
    if !idx.is_empty() && idx.bytes().all(|b| b.is_ascii_digit()) {
        Some(tail)
    } else {
        None
    }
}

/// Whether an already-registered constant `name` is a value-free `Axiom`
/// carrier stub — the shape the import prelude uses for typeclass *carrier*
/// heads (`Membership`, …) it pre-registers so hand-rolled instances resolve
/// before any library loads — and neither a declaration of ANOTHER artifact
/// than the one loading (`artifact_ledger::declared_by_other_artifact`) nor
/// one of the kernel's quotient primitives (`Environment::get_quot`).
///
/// SOUNDNESS: a `true` result means the constant is an opaque, value-free
/// `Axiom` that no other module declared. Replacing it with the genuine
/// kernel-checked inductive of the same name (the only caller — and only when
/// the *incoming* constant is an `Inductive`) is a strict trust IMPROVEMENT: an
/// unchecked assumption is swapped for a checked declaration, removing a
/// phantom domain axiom from `axiom_deps`. It can never admit a new axiom.
/// Another module's axiom is a second declaration of the name, which Lean
/// refuses ("environment already contains"): the default policy refuses the
/// import for it before this is reached (rule 1 of `artifact_ledger`), and
/// under `OleanImportPolicy::with_replay_refusals`, which does not, the
/// incoming inductive must be recorded as a duplicate for the replay to refuse
/// — discharging the import's axiom instead let `ReplayForgedIndOverAx`'s
/// inductive replace it unrecorded, and `clean olean replay` admitted that
/// module's proof of `False`. The quotient primitives are value-free axioms
/// too, seeded by the kernel with no artifact behind them, so the artifact
/// test does not reach them: a module's `inductive Quot.ind` used to discharge
/// the kernel's `Quot.ind` under every policy, leaving its quotient reduction
/// rule behind a constant that is now an inductive, and recording nothing.
fn is_axiom_carrier_stub(
    env: &Environment,
    name: &Name,
    existing: &clean_kernel::env::ConstantInfo,
    artifact: &super::artifact_ledger::ArtifactKey,
) -> bool {
    matches!(existing.kind, clean_kernel::env::ConstantKind::Axiom)
        && existing.value.is_none()
        && env.get_quot(name).is_none()
        && super::artifact_ledger::declared_by_other_artifact(env, name, artifact).is_none()
}

/// Discharge the opaque prelude carrier stubs named in `names` so the genuine
/// imported inductives of the same name can register through the checked path.
///
/// Idempotent and conservative: [`Environment::discharge_axiom_stub_for_inductive_import`]
/// only removes a value-free `Axiom` that is not already backed by an inductive.
fn discharge_carrier_stubs(env: &mut Environment, names: &[Name]) {
    for name in names {
        let _ = env.discharge_axiom_stub_for_inductive_import(name);
    }
}

/// The module a Clean-payload or `.olean` origin names.
fn origin_module(origin: &ConstantOrigin) -> Option<&str> {
    match origin {
        ConstantOrigin::CleanPayload { module, .. } | ConstantOrigin::Olean { module, .. } => {
            module.as_deref()
        }
        ConstantOrigin::Kernel { .. } => None,
    }
}

/// Filter a payload slice, counting duplicates, and return non-duplicate items.
fn filter_payload_dups<T: Clone>(
    items: &[T],
    exists: impl Fn(&T) -> bool,
    duplicates: &mut usize,
) -> Vec<T> {
    items
        .iter()
        .filter(|item| {
            if exists(item) {
                *duplicates += 1;
                false
            } else {
                true
            }
        })
        .cloned()
        .collect()
}

/// Divert structural-tier rejections (R1-IND) into a `SkippedConstant` list and
/// return the origin names that were actually inserted, so refused records are
/// neither origin-tagged nor counted as added.
fn divert_structural_rejections(
    origin_names: Vec<Name>,
    rejected: Vec<(Name, clean_kernel::env::EnvError)>,
    skipped: &mut Vec<SkippedConstant>,
) -> Vec<Name> {
    if rejected.is_empty() {
        return origin_names;
    }
    let rejected_names: HashSet<Name> = rejected.iter().map(|(name, _)| name.clone()).collect();
    for (name, err) in rejected {
        skipped.push(SkippedConstant {
            name: name.to_string(),
            reason: format!("structural validation failed: {err}"),
        });
    }
    origin_names
        .into_iter()
        .filter(|name| !rejected_names.contains(name))
        .collect()
}

fn tag_inserted_constants(
    env: &mut Environment,
    origin: Option<&ConstantOrigin>,
    names: Vec<Name>,
    added_acc: &mut Vec<Name>,
) {
    // Single capture chokepoint: every registration path funnels its just-added
    // names through here, so accumulating them lets the verify-batch new-constant
    // scan stay O(new). Capture BEFORE `names` is moved into set_constant_origins.
    added_acc.extend(names.iter().cloned());
    if let Some(origin) = origin {
        env.set_constant_origins(names, origin.clone());
    }
}

/// The first record of `payload` whose name another imported ARTIFACT (an
/// `.olean` or a Clean payload of another module) already declared, other
/// than as the one duplicate Lean's import allows (see [`may_stand_beside`]),
/// and that module. Declarations of the checker's own base (native prelude,
/// kernel-checked) are not artifacts and are skipped by `filter_payload_dups`
/// as before. Which artifact declared a name is read from the artifact
/// ledger, not from the origin value: the same module met twice (its trust
/// raised by a re-check meanwhile, or one of its companion parts) is one
/// artifact.
fn contradicts_another_artifact(
    env: &Environment,
    payload: &CleanPayload,
    artifact: &super::artifact_ledger::ArtifactKey,
) -> Option<(Name, String)> {
    let first = |name: &Name| -> Option<String> {
        super::artifact_ledger::declared_by_other_artifact(env, name, artifact)
    };
    for c in &payload.constants {
        let Some(module) = first(&c.name) else {
            continue;
        };
        if !may_stand_beside(env, c) {
            return Some((c.name.clone(), module));
        }
    }
    // An inductive family, its constructors and recursors: never twice.
    let families = payload
        .inductives
        .iter()
        .map(|i| &i.name)
        .chain(payload.constructors.iter().map(|k| &k.name))
        .chain(payload.recursors.iter().map(|r| &r.name));
    for name in families {
        if let Some(module) = first(name) {
            return Some((name.clone(), module));
        }
    }
    None
}

/// Whether `incoming` may stand beside the declaration another artifact
/// already made under its name: only a theorem, or a value-free axiom, of the
/// very statement — same universe parameters, same type. Two proofs of one
/// statement are one theorem (proof irrelevance), and a value-free axiom of
/// it is its exported stub (Lean >= 4.29 writes a module's theorems as such
/// stubs into its public `.olean`; `dite.congr_simp` is realized in two
/// `Init` modules). That is the only duplicate Lean's import allows —
/// measured with `lean` v4.30.0-rc2: two theorems or axioms of one statement
/// import; two of different statements, two identical `def`s, `opaque`s, or
/// `axiom`s of a `Type` do not. (Two identical axioms of a `Type` stand here:
/// one assumption, not two meanings.) A definition, opaque, or inductive
/// family member never does.
fn may_stand_beside(env: &Environment, incoming: &clean_kernel::env::ConstantInfo) -> bool {
    fn bytes<T: serde::Serialize>(value: &T) -> Vec<u8> {
        bincode::serde::encode_to_vec(value, bincode::config::standard()).unwrap_or_default()
    }
    use clean_kernel::env::ConstantKind as K;
    let name = &incoming.name;
    let Some(existing) = env.get_const(name) else {
        return false;
    };
    if env.get_inductive(name).is_some()
        || env.get_constructor(name).is_some()
        || env.get_recursor(name).is_some()
    {
        return false;
    }
    let proof_like = |c: &clean_kernel::env::ConstantInfo| match c.kind {
        K::Theorem => true,
        K::Axiom => c.value.is_none(),
        K::Definition | K::Opaque => false,
    };
    proof_like(existing)
        && proof_like(incoming)
        && existing.level_params == incoming.level_params
        && bytes(&existing.type_) == bytes(&incoming.type_)
}

/// Quotient primitives are the kernel's, never the file's. Lean's kernel
/// handles a `quotInfo` record with `addDecl .quotDecl` and builds the four
/// types itself; here the kernel bundle is installed before the duplicate
/// filter, so the file's `Quot` records (and a same-module `Quot.sound`) are
/// dropped as duplicates instead of registering as axioms whose types the file
/// chose. The kernel's quotient reduction fires only on the kernel-built
/// primitives, so without this a bare-environment import would lose it.
///
/// Every quotient constant this call makes resident is recorded in `added`
/// (the summary's `added_names`, the verify-batch name census).
fn install_kernel_quotients(
    env: &mut Environment,
    module_declares_quot: bool,
    added: &mut Vec<Name>,
) {
    if !module_declares_quot {
        return;
    }
    let absent: Vec<Name> = clean_kernel::quot::init_quot_vals()
        .into_iter()
        .map(|val| val.name)
        .filter(|name| env.get_const(name).is_none())
        .collect();
    // SOUNDNESS: kernel-canonical builder (census row
    // `kernel-canonical-builders`, data/env_bypass_census.json): idempotent,
    // registers only the kernel's own quotient types, reads no file data.
    env.init_quot();
    added.extend(
        absent
            .into_iter()
            .filter(|name| env.get_const(name).is_some()),
    );
}

/// Merge a clean payload (serialized kernel objects) into the environment.
///
/// Returns (added_count, duplicate_count, structural_rejections), or
/// [`ImportError::InconsistentStructureTable`] for a payload whose structure
/// field table contradicts its own projections.
fn load_clean_payload(
    env: &mut Environment,
    payload: &CleanPayload,
    origin: Option<&ConstantOrigin>,
    artifact: &super::artifact_ledger::ArtifactKey,
    added_acc: &mut Vec<Name>,
    import_kinds: super::ImportKinds,
) -> Result<(usize, usize, Vec<SkippedConstant>), ImportError> {
    // HYBRID (Phase-1 zero-copy): under `InductiveFamiliesOnly` the payload's
    // definitional constants (`payload.constants`) are served lazily, so only the
    // inductive families below are registered eagerly from the payload.
    let inductive_families_only = matches!(import_kinds, super::ImportKinds::InductiveFamiliesOnly);
    // Refused before anything is registered: `filter_payload_dups` below only
    // compares with the environment, so two same-named records of ONE payload
    // were both inserted and the later won (module-trust round 28, Y5).
    if let Some((name, what)) = payload.duplicate_declaration() {
        return Err(ImportError::DuplicateDeclaration {
            name: name.to_string(),
            what,
        });
    }
    // A name another imported artifact already declared DIFFERENTLY: the
    // filter below would skip this record and keep the first silently, so
    // which definition a consumer sees would depend on import order
    // (measured: `V0.v := 1` carried by an unrelated module imported before
    // `V0` made `V0.v = 1` pass on `e3f696689` and `3f45fb7c6`). Lean
    // refuses every duplicate but a second proof (or axiom stub) of one
    // statement (`may_stand_beside`); the same module met twice is one
    // artifact and not compared (`artifact_ledger`).
    if let Some((name, first)) = contradicts_another_artifact(env, payload, artifact) {
        return Err(ImportError::ConflictingDeclaration {
            name: name.to_string(),
            first,
        });
    }
    // A record naming what an earlier part of this very artifact declared
    // (a payload carried by its `.olean.private`, say) must state it as that
    // part did; `filter_payload_dups` below used to drop it unread (rule 4 of
    // `artifact_ledger`; round 30: a `V0.olean.private` payload saying
    // `V0.v := 1` beside `V0.olean`'s `V0.v := 0` was ignored).
    for record in payload_part_records(payload) {
        let name = record.name().clone();
        if super::artifact_ledger::declared_by_this_artifact(env, &name, artifact) {
            super::artifact_ledger::check_same_artifact_record(
                env,
                artifact,
                &name,
                Some(&record),
            )?;
        }
    }
    for (struct_name, fields) in &payload.structure_fields {
        if super::artifact_ledger::declared_by_this_artifact(env, struct_name, artifact)
            && env
                .get_structure_field_names(struct_name)
                .is_some_and(|registered| registered != fields.as_slice())
        {
            return Err(ImportError::PartsDisagree {
                name: struct_name.to_string(),
                module: artifact
                    .clone()
                    .unwrap_or_else(|| "<unnamed module>".to_string()),
            });
        }
    }
    let mut added = 0usize;
    let mut duplicates = 0usize;
    let mut structural_rejections = Vec::new();

    // R1-IND (2026-08-24): the inductive-family legs go through the structural
    // tier (extend_*_structural — same O(1) checks as the constants leg below:
    // no dup level params, no metavariables, no free vars, Level::Param scope,
    // over every carried expression incl. recursor-rule rhs). A failing record
    // REFUSES structurally: diverted to `structural_rejections`, never inserted.
    let mut inductives = filter_payload_dups(
        &payload.inductives,
        |ind| env.get_inductive(&ind.name).is_some(),
        &mut duplicates,
    );
    let inductive_origin_names: Vec<_> = inductives.iter().map(|ind| ind.name.clone()).collect();
    let pre_validate_inductives = inductives.len();
    let rejected = env.extend_inductives_structural(inductives.drain(..));
    added += pre_validate_inductives - rejected.len();
    let inductive_origin_names =
        divert_structural_rejections(inductive_origin_names, rejected, &mut structural_rejections);
    tag_inserted_constants(env, origin, inductive_origin_names, added_acc);

    let mut constructors = filter_payload_dups(
        &payload.constructors,
        |c| env.get_constructor(&c.name).is_some(),
        &mut duplicates,
    );
    let constructor_origin_names: Vec<_> = constructors.iter().map(|c| c.name.clone()).collect();
    let pre_validate_constructors = constructors.len();
    let rejected = env.extend_constructors_structural(constructors.drain(..));
    added += pre_validate_constructors - rejected.len();
    let constructor_origin_names = divert_structural_rejections(
        constructor_origin_names,
        rejected,
        &mut structural_rejections,
    );
    tag_inserted_constants(env, origin, constructor_origin_names, added_acc);

    // HYBRID (Phase-1 zero-copy): skip the payload's definitional constants under
    // `InductiveFamiliesOnly`; they are served lazily. The inductive families
    // above and the structure-field metadata below still register eagerly.
    if !inductive_families_only {
        let mut constants = filter_payload_dups(
            &payload.constants,
            |c| env.get_const(&c.name).is_some(),
            &mut duplicates,
        );
        let pre_validate_count = constants.len();
        let constant_origin_names: Vec<_> = constants.iter().map(|c| c.name.clone()).collect();
        // SOUNDNESS: extend_constants_structural inserts WITHOUT kernel type-checking; it runs
        // only the O(1) structural checks (env/registration.rs: no dup level params, no
        // metavariables, no free vars, Level::Param scope) and diverts failures to `rejected`
        // below — so every INSERTED constant is closed, metavar-free, and level-scope-correct,
        // but NOT confirmed well-typed (no value:type / type-is-a-Sort check). SCOPE: since
        // R1-IND (2026-08-24) the payload.inductives/constructors/recursors legs above run the
        // SAME structural tier (extend_*_structural, incl. recursor-rule rhs), so the whole
        // payload is uniformly structurally checked. What is admitted here is ADMITTED-UNTRUSTED,
        // not trusted: it is tagged ConstantOrigin::CleanPayload (Unpinned, `needs_recheck`) and
        // there is no authenticity/hash check (OleanImportPolicy is admission-only), so a
        // tampered-but-structurally-valid trailer arrives with its type/value intact — measured
        // 2026-09-24 (reports/2026-09-24-module-trust.md: a rewritten type, a sorry proof, an
        // axiom, a dropped dependency and swapped recursor rules each let `clean check` and
        // `clean lake build` credit `(0 : Nat) = 1`). The re-check is the CONSUMER'S job: every
        // lane that prints a kernel verdict over a citation of these constants must first run
        // `recheck_closed::ImportedConeGate` over the citation's cone (`clean check`:
        // clean-cli/src/check_import_gate.rs; `clean lake build`: clean-lake/src/build.rs
        // `gate_module_closure`), which re-admits every one of them through the kernel.
        // Tracking: data/unchecked_decl_ratchet.json (extend_constants block, #4).
        let rejected = env.extend_constants_structural(constants.drain(..));
        added += pre_validate_count - rejected.len();
        if !constant_origin_names.is_empty() {
            let rejected_names: HashSet<_> =
                rejected.iter().map(|(name, _)| name.clone()).collect();
            let accepted_names = constant_origin_names
                .into_iter()
                .filter(|name| !rejected_names.contains(name))
                .collect();
            tag_inserted_constants(env, origin, accepted_names, added_acc);
        }
        for (name, err) in rejected {
            structural_rejections.push(SkippedConstant {
                name: name.to_string(),
                reason: format!("structural validation failed: {err}"),
            });
        }
    } // end `if !inductive_families_only` (HYBRID definitional-constant skip)

    // `protected` / `private` marks, for the payload's OWN declarations only
    // (a mark on another module's name would change what an importer's
    // identifiers resolve to).
    let own: std::collections::HashSet<&Name> = payload
        .constants
        .iter()
        .map(|c| &c.name)
        .chain(payload.inductives.iter().map(|i| &i.name))
        .chain(payload.constructors.iter().map(|c| &c.name))
        .chain(payload.recursors.iter().map(|r| &r.name))
        .collect();
    for name in &payload.protected_decls {
        if !own.contains(name) {
            return Err(ImportError::InconsistentDeclarationMark {
                name: name.to_string(),
                reason: "a `protected` mark names a declaration this module does not carry"
                    .to_string(),
            });
        }
        env.mark_protected(name.clone());
    }
    for name in &payload.private_decls {
        if !own.contains(name) {
            return Err(ImportError::InconsistentDeclarationMark {
                name: name.to_string(),
                reason: "a `private` mark names a declaration this module does not carry"
                    .to_string(),
            });
        }
        env.mark_private(name.clone());
    }
    // Recursors LAST, after the payload's constants: the kernel regenerates each
    // one from the resident family (env/imported_family.rs), and a Prop family's
    // elimination universe depends on its fields' sorts, which may name a
    // definition this payload carries.
    let mut recursors = filter_payload_dups(
        &payload.recursors,
        |r| env.get_recursor(&r.name).is_some(),
        &mut duplicates,
    );
    let recursor_origin_names: Vec<_> = recursors.iter().map(|r| r.name.clone()).collect();
    let pre_validate_recursors = recursors.len();
    let rejected = env.extend_recursors_structural(recursors.drain(..));
    added += pre_validate_recursors - rejected.len();
    let recursor_origin_names =
        divert_structural_rejections(recursor_origin_names, rejected, &mut structural_rejections);
    tag_inserted_constants(env, origin, recursor_origin_names, added_acc);

    for (struct_name, fields) in &payload.structure_fields {
        if env.get_structure_field_names(struct_name).is_some() {
            duplicates += 1;
            continue;
        }
        // The table is elaborator metadata the kernel never checks: `.x` on a
        // `P` elaborates to `Proj(P, i, _)` with `i` read from it. It is
        // registered only when it is the table the payload's own projections
        // define (`structure_table_contradiction`: each `P.f` must COMPUTE
        // field `i`). A table that is not gives `.x` a meaning the module's
        // declarations never gave it (module-trust round 27, M8f: a reversed
        // table made `(V0.P.mk 0 1).x = 1 := rfl` pass; round 28, Y1/Y2: the
        // same with the projections rewritten to recursor bodies, or removed).
        // Which side was rewritten cannot be told from here — dropping the
        // table would hand `.x` to a rewritten projection instead (M9) — so
        // the import is refused.
        if let Some(fault) =
            structure_table_contradiction(env, struct_name, fields, &[], inductive_families_only)
        {
            // The payload's own projections were registered above, so an
            // absent one is absent from the artifact.
            return Err(fault.into_import_error(struct_name));
        }
        if env
            .register_structure_fields(struct_name.clone(), fields.clone())
            .is_err()
        {
            duplicates += 1;
        } else {
            env.get_ext_state_mut::<StructureExtPending>(structure_ext_pending_idx())
                .payload_tables
                .insert(struct_name.clone());
        }
    }

    // What this part declares, for a later part of the artifact to be
    // compared with (rule 4).
    super::artifact_ledger::remember_part_records(env, artifact, payload_part_records(payload));
    let module = origin.and_then(origin_module);
    apply_payload_instance_entries(env, payload, module);
    apply_payload_compiler_attrs(env, payload, module);

    Ok((added, duplicates, structural_rejections))
}

/// A payload's declarations as the artifact ledger remembers them. A
/// payload carries no declaration safety, nor a recursor's mutual block or
/// nested count, so those read as absent.
fn payload_part_records(
    payload: &CleanPayload,
) -> impl Iterator<Item = super::artifact_ledger::PartRecord> + '_ {
    use super::artifact_ledger::PartRecord;
    payload
        .constants
        .iter()
        .map(|c| PartRecord::Constant {
            info: c.clone(),
            safety: None,
        })
        .chain(
            payload
                .inductives
                .iter()
                .map(|v| PartRecord::Inductive(v.clone(), None)),
        )
        .chain(
            payload
                .constructors
                .iter()
                .map(|v| PartRecord::Constructor(v.clone(), None)),
        )
        .chain(
            payload
                .recursors
                .iter()
                .map(|v| PartRecord::Recursor(v.clone(), Vec::new(), 0, None)),
        )
}

fn load_extension_entries(
    env: &mut Environment,
    module_idx: usize,
    extensions: &[TypedExtension],
) -> Result<(), ImportError> {
    for extension in extensions {
        if extension.extension_name.is_anon() {
            continue;
        }
        let extension_name = extension.extension_name.clone();
        env.register_persistent_extension(extension_name.clone());

        if extension.entries.is_empty() {
            continue;
        }

        if matches!(
            env.get_persistent_extension_module_entries(&extension_name, module_idx),
            Some(entries) if !entries.is_empty()
        ) {
            continue;
        }

        let mut converted = Vec::with_capacity(extension.entries.len());
        for entry in &extension.entries {
            // Only convert Named entries - RawScalar entries are opaque sentinel values
            // that don't have a name and are not used by the kernel.
            if let TypedExtensionEntry::Named { name, data } = entry {
                let data = match data {
                    ParsedExtensionEntryData::Scalar(value) => {
                        EnvExtensionEntryData::Scalar(*value)
                    }
                    ParsedExtensionEntryData::Object(bytes) => {
                        EnvExtensionEntryData::Object(bytes.clone())
                    }
                };

                converted.push(EnvExtensionEntry {
                    name: name.clone(),
                    data,
                });
            }
            // Skip RawScalar entries - they're preserved in ParsedModule for roundtrip
            // but don't represent environment extension entries with names.
        }

        env.add_persistent_extension_entries(&extension_name, module_idx, converted);
    }

    Ok(())
}

fn extension_accounting(extensions: &[TypedExtension]) -> Vec<super::ExtensionLoadAccounting> {
    extensions
        .iter()
        .map(|extension| super::ExtensionLoadAccounting {
            extension_name: extension.extension_name.clone(),
            source_rows: extension.source_rows,
            decoded_rows: extension
                .entries
                .iter()
                .filter(|entry| !matches!(entry, TypedExtensionEntry::Unmeasured { .. }))
                .count(),
            undecoded_rows: extension.undecoded_entries,
            undecoded_reasons: extension
                .entries
                .iter()
                .filter_map(|entry| match entry {
                    TypedExtensionEntry::Unmeasured { index, reason } => {
                        Some(format!("row {index}: {reason}"))
                    }
                    _ => None,
                })
                .collect(),
            unresolved_targets: 0,
        })
        .collect()
}

fn finish_extension_accounting(summary: &mut LoadSummary) -> Result<(), ImportError> {
    let total = summary
        .extension_accounting
        .iter()
        .try_fold(0_usize, |total, row| {
            total
                .checked_add(row.undecoded_rows)?
                .checked_add(row.unresolved_targets)
        })
        .ok_or_else(|| crate::OleanError::Region("extension diagnostic count overflow".into()))?;
    summary.extension_undecoded_entries = total;
    Ok(())
}

/// Register the DECODED real-Lean `@[instance]` entries of a module into the
/// kernel instance registry (#olean-env-ext-restore, increment 1).
///
/// Real Lean `.olean`s persist each `@[instance]` registration in
/// `Lean.Meta.instanceExtension` as a `ScopedEnvExtension.Entry InstanceEntry`
/// object. The binary reader decodes those into
/// [`TypedExtensionEntry::Instance`] (instance name, priority, attrKind,
/// scope); this bridge registers them through [`Environment::register_instance`]
/// with their REAL priority (Lean default 1000). Registration comes from
/// explicit source metadata, never from guessing which definition types look
/// like instances. A class-valued ordinary definition is not an instance.
///
/// Faithfulness rules (never fabricate, degrade inert):
/// - an entry whose constant is absent from the environment is skipped;
/// - the class is derived from the instance's own type conclusion head
///   (authoritative — the persisted entry does not carry the class name);
///   a non-`Const` head skips the entry;
/// - an unregistered class head is registered with its Π-arity as
///   `num_params` and empty out-params when no class metadata is available
///   (real out-params arrive through `Lean.classExtension`);
/// - `scoped instance` entries are registered like global ones for now:
///   Clean has no namespace-activation notion, so this preserves the status-quo
///   over-approximation rather than silently dropping them (`attr_kind` /
///   `scope_ns` are measured by the typed decoder and stay available on the
///   public `ParsedInstanceEntry` for a future increment; the typed record
///   carries neither until a registrar reads them).
///
/// **Already-registered names ADOPT Lean's priority.** Clean's hand-rolled
/// prelude registers many of these same instances with a GUESSED priority, and
/// first-registered-wins used to freeze that guess in place: `instOfNatNat`
/// (guessed 100, Lean 1000, `8d80c9d98`), `instLTNat` (guessed 100, Lean 1000,
/// ranked 30th of 43 `LT` candidates, `066a1173f`) and the B101 hetero bridges
/// (`28e7834a1`) were each dug out one at a time. This bridge now overwrites the
/// priority — and ONLY the priority — of an already-registered twin with the
/// value Lean serialized, via [`Environment::adopt_instance_priority`], so the
/// whole class is retired structurally instead of row by row. The hand-rolled
/// entry keeps its `class_name`/`type_`/`value` (the prelude sets those for
/// binder-info fidelity the persisted entry does not carry), and a name Lean
/// never registers keeps Clean's value untouched. Census + ratchet:
/// `data/prelude_instance_priority_census.json`,
/// `crates/clean-olean/tests/prelude_instance_priority_census.rs`.
///
/// SOUNDNESS: instance registrations are elaboration metadata — they steer
/// which candidate `resolve_instance` tries first; every synthesized term is
/// still kernel-checked by the caller. A wrong or extra entry can only cost
/// completeness/parity, never admit a false proof.
fn register_real_instance_entries(env: &mut Environment, extensions: &[TypedExtension]) {
    // Collect (name, priority, synthOrder) tuples first so nothing borrows
    // `extensions` while `env` is mutated.
    // Imported `scoped instance`s: remember the declaring namespace so the
    // elaborator can gate them on `open`, exactly as it gates source-declared
    // ones (see `ScopedInstanceState`). Recorded whether or not the instance
    // itself is registered below (a re-listed entry still carries its scope).
    let scoped: Vec<(Name, Name)> = extensions
        .iter()
        .filter(|ext| ext.extension_name == Name::interned(LEAN_INSTANCE_EXTENSION))
        .flat_map(|ext| ext.entries.iter())
        .filter_map(|entry| match entry {
            TypedExtensionEntry::Instance(inst) => inst
                .scope
                .as_ref()
                .map(|ns| (inst.instance_name.clone(), ns.clone())),
            _ => None,
        })
        .collect();
    if !scoped.is_empty() {
        let idx = scoped_instance_idx();
        let state = env.get_ext_state_mut::<ScopedInstanceState>(idx);
        for (inst, ns) in scoped {
            state.scope_of.insert(inst, ns);
        }
    }

    let decoded: Vec<(Name, u32, Vec<usize>)> = extensions
        .iter()
        .filter(|ext| ext.extension_name == Name::interned(LEAN_INSTANCE_EXTENSION))
        .flat_map(|ext| ext.entries.iter())
        .filter_map(|entry| match entry {
            TypedExtensionEntry::Instance(inst) => {
                // Binder indices always fit in usize on supported targets; a
                // (theoretical) overflowing index saturates and is then
                // ignored by the resolver's defensive mapping (out-of-range
                // indices match no binder), never mis-ordered.
                let synth_order = inst
                    .synth_order
                    .iter()
                    .map(|&i| usize::try_from(i).unwrap_or(usize::MAX))
                    .collect();
                Some((
                    inst.instance_name.clone(),
                    u32::try_from(inst.priority).unwrap_or(u32::MAX),
                    synth_order,
                ))
            }
            _ => None,
        })
        .collect();

    for (name, priority, synth_order) in decoded {
        // Already registered — by the hand-rolled prelude, by an earlier
        // module, or by a repeated/overlapping load (base + companion parts
        // re-list the same entries). ADOPT the serialized priority rather than
        // letting first-registered-wins freeze a guess: this is the structural
        // retirement of the `instOfNatNat`/`instLTNat` defect class. Adoption
        // is idempotent (re-listing the same entry re-writes the same value),
        // and every other field of the existing entry is left alone.
        if env.is_instance(&name) {
            env.adopt_instance_priority(&name, priority);
            continue;
        }
        let Some(class) = env
            .get_const(&name)
            .and_then(|c| instance_conclusion_class(&c.type_))
        else {
            continue; // constant skipped at import, or non-Const conclusion
        };
        if !env.is_class(&class) {
            let Some(num_params) = class_param_arity(env, &class) else {
                continue; // class constant absent: never fabricate metadata
            };
            env.register_class(KernelClassInfo {
                name: class.clone(),
                num_params,
                out_params: Vec::new(),
                semi_out_params: Vec::new(),
            });
        }
        env.set_instance_synth_order(name.clone(), synth_order);
        env.register_instance(KernelInstanceInfo {
            name,
            class_name: class,
            priority,
            type_: None,
            value: None,
        });
    }
}

/// Lean 4's default simp-lemma priority (`SimpTheorem.priority`'s default,
/// `eval_prio default` = 1000) — the numeric value [`SimpPriority::Default`]
/// also denotes, so decoded default-priority entries map onto the canonical
/// variant instead of a `Custom(1000)` twin.
const LEAN_DEFAULT_SIMP_PRIORITY: u64 = 1000;

/// Register the DECODED real-Lean `@[simp]` entries of a module into the
/// kernel simp-lemma registry (RC-B / T10: the typed `simpExtension` decoder).
///
/// Real Lean `.olean`s persist each `@[simp]` registration in
/// `Lean.Meta.simpExtension` as a `ScopedEnvExtension.Entry SimpEntry` object.
/// Before the typed decoder, every one of those entries was silently dropped
/// at parse (the layout does not match the generic `(Name × DataValue)` pair
/// heuristic), so bare `simp` under real imports saw only the hand-written
/// builtin rules — ~0.4% of upstream's `@[simp]` set. The binary reader now
/// decodes them into [`TypedExtensionEntry::Simp`] (origin name, priority,
/// post flag); this bridge registers each one through
/// [`Environment::register_simp_lemma`], which is exactly the registry the
/// simp tactic's `collect_registry_lemmas` reads.
///
/// Faithfulness rules (never fabricate, degrade loud):
/// - registration is BY NAME ONLY: the rewrite's statement is reconstructed at
///   simp-collection time from the imported constant's own kernel-checked
///   type (`clean_elab::tactic::simp::lemmas::collect_registry_lemmas`), never
///   from serialized bytes — so an entry whose constant is absent from the
///   environment (skipped at import) is NOT registered and is counted in the
///   returned unresolved tally, which the caller folds into
///   `LoadSummary::extension_undecoded_entries`;
/// - `thm`, `toUnfold`, and `toUnfoldThms` entries all register their
///   declaration name: Clean's unified registry model already routes
///   `Definition`-kind names to delta-unfolding
///   (`seed_unfold_defs_from_simp_defs`) and equality/iff-typed names to
///   rewriting, mirroring Lean's thm/toUnfold split;
/// - `scoped` entries are registered like global ones (Clean has no
///   namespace-activation notion; the status-quo over-approximation used for
///   instances — `scope_ns` stays on the parsed entry for a future increment);
/// - names already registered (an earlier module, a repeated/overlapping
///   load, or a prelude twin) are skipped — idempotent, first-writer-wins.
///
/// SOUNDNESS: simp registrations are elaboration metadata — they steer which
/// rewrites `simp` attempts; every rewrite proof is built from the registered
/// constant fetched from the environment and every closed goal is re-checked
/// by the kernel (`close_goal`). A wrong or extra entry can only cost
/// completeness/parity, never admit a false proof.
/// Register the DECODED real-Lean `export` aliases of a module.
///
/// Lean persists `export Ns (a b c)` in `Lean.aliasExtension` as `Name × Name`
/// pairs. Before the typed decoder those pairs hit the generic
/// `(Name × DataValue)` reader, which captured the TARGET as opaque bytes —
/// so `isTrue` / `isFalse` / `decide` (from `export Decidable …`) and
/// `eq_of_beq` (`export LawfulBEq …`) were unresolvable after `import Init`
/// even though their constants imported fine.
///
/// Faithfulness: an alias whose TARGET is absent from the environment is
/// counted as unresolved and NOT registered — an alias may never conjure a
/// constant. Registration is idempotent (first writer wins), matching the
/// simp bridge.
fn register_real_alias_entries(env: &mut Environment, extensions: &[TypedExtension]) -> usize {
    let decoded: Vec<(Name, Name)> = extensions
        .iter()
        .filter(|ext| ext.extension_name == Name::interned(LEAN_ALIAS_EXTENSION))
        .flat_map(|ext| ext.entries.iter())
        .filter_map(|entry| match entry {
            TypedExtensionEntry::Alias { alias, target } => Some((alias.clone(), target.clone())),
            _ => None,
        })
        .collect();

    let mut unresolved = 0usize;
    for (alias, target) in decoded {
        // Lean's alias table maps an alias to every target it was given
        // (`addAliasEntry`); a repeated entry is a no-op.
        if env.export_alias_targets(&alias).contains(&&target) {
            continue;
        }
        if env.get_const(&target).is_none() {
            unresolved += 1;
            continue;
        }
        env.register_export_alias(alias, target);
    }
    unresolved
}

/// Register the DECODED real-Lean compiler attributes of a module:
/// `Lean.Compiler.implementedByAttr` rows as `@[implemented_by]` bindings
/// `Lean.externAttr` rows as `@[extern]` bindings, and direct Names from
/// `Lean.noncomputableExt` as the existing code-generation exclusion, the registries source
/// elaboration fills (`clean_elab`'s `decl_attributes`), so the native audit
/// and `to_lcnf` see an imported binding exactly as they see a source one
/// (`docs/DECISIONS.md` R149). Before this, both were read for the IR census
/// only (`lean_ir::module_ir`) and an imported declaration's logical body
/// compiled where Lean runs another: `implSlow 1` printed `3` at exit 0 where
/// pinned Lean prints `2` (fixture family `implemented_by_import`).
///
/// A row binds the declaration THIS module added. When the loader kept a
/// resident declaration of that name instead (the builtin prelude's, or
/// another module's, `load_shadowing`), the row is about a declaration that
/// is not in the environment, so it is not registered: the resident
/// constant compiles as it does without the import (a runtime primitive the
/// native walk keeps as a shim stays one). A row whose declaration is absent
/// is counted in `unresolved_targets`. A binding's TARGET is registered
/// whatever holds it: the compiled lanes refuse by name a target that is
/// absent, `unsafe` or of another type when a program reaches it
/// (`clean_compiler::implemented_by`). First writer wins, as for every other
/// imported table.
///
/// A `@[macro_inline]` declaration's binding is not registered: Lean expands
/// its body at every call site (`late_binding::CompilerNames::macro_inline`).
/// Each binding registered for the module's own declaration is pushed to
/// `registered`, for `late_binding::record_late_bindings` to judge.
///
/// SOUNDNESS: kernel-irrelevant. Neither registry is read by type checking;
/// both change only which body compiled code runs, or refuse it.
fn register_real_compiler_attr_entries(
    env: &mut Environment,
    module: Option<&str>,
    extensions: &[TypedExtension],
    names: &super::late_binding::CompilerNames,
    registered: &mut Vec<(Name, Name)>,
) -> Result<usize, ImportError> {
    let mut unresolved = 0usize;
    for entry in extensions.iter().flat_map(|ext| ext.entries.iter()) {
        if let TypedExtensionEntry::CSimp {
            from,
            to,
            theorem,
            namespace,
        } = entry
        {
            let owner = module.map(Name::from_string).ok_or_else(|| {
                crate::OleanError::Region("CSimp metadata has no owning module".into())
            })?;
            let valid = env.get_const(theorem).is_some_and(|info| {
                clean_kernel::env::csimp::constant_replacement(&info.type_)
                    == Some((from.clone(), to.clone()))
            });
            if !valid || env.get_const(from).is_none() || env.get_const(to).is_none() {
                return Err(crate::OleanError::Region(format!(
                    "CSimp metadata for {theorem} disagrees with its registered equality or names an absent target"
                )).into());
            }
            if foreign_resident_provenance(env, theorem, module, false).is_some() {
                continue;
            }
            if !clean_kernel::env::csimp::import_rule(env, &owner, namespace.as_ref(), theorem) {
                return Err(crate::OleanError::Region(format!(
                    "invalid imported CSimp rule {theorem}"
                ))
                .into());
            }
            continue;
        }
        let (decl, attr) = match entry {
            TypedExtensionEntry::ImplementedBy { decl, target } => {
                if names.macro_inline(decl) == Some(true) {
                    tracing::debug!(
                        decl = %decl,
                        "imported `@[implemented_by]` of a `@[macro_inline]` declaration not \
                         registered: Lean expands its body at every call site"
                    );
                    continue;
                }
                (decl, ImportedCompilerAttr::ImplementedBy(target))
            }
            TypedExtensionEntry::Extern { decl, symbol } => {
                (decl, ImportedCompilerAttr::Extern(symbol))
            }
            TypedExtensionEntry::Noncomputable { decl } => {
                (decl, ImportedCompilerAttr::Noncomputable)
            }
            _ => continue,
        };
        match register_imported_compiler_attr(env, module, decl, attr) {
            Registration::Absent => unresolved += 1,
            Registration::Registered => {
                if let ImportedCompilerAttr::ImplementedBy(target) = attr {
                    registered.push((decl.clone(), target.clone()));
                }
            }
            Registration::NotRegistered => {}
        }
    }
    Ok(unresolved)
}

/// What [`register_imported_compiler_attr`] did with one binding.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Registration {
    /// The declaration is not in the environment.
    Absent,
    /// Registered for this module's own declaration.
    Registered,
    /// Not registered: the resident declaration is another's, or it was
    /// bound already (first writer wins).
    NotRegistered,
}

/// One imported compiler binding of a declaration.
#[derive(Clone, Copy)]
enum ImportedCompilerAttr<'a> {
    /// `@[implemented_by target]`.
    ImplementedBy(&'a Name),
    /// `@[extern]`, with the symbol (or entries) as the artifact spells it.
    Extern(&'a str),
    /// Source declaration excluded from Lean code generation.
    Noncomputable,
}

/// Register one imported compiler binding of `decl` under the rule of
/// [`register_real_compiler_attr_entries`], which a Clean payload's
/// bindings follow too (`apply_payload_compiler_attrs`): only for the
/// declaration `module` itself added, first writer wins.
fn register_imported_compiler_attr(
    env: &mut Environment,
    module: Option<&str>,
    decl: &Name,
    attr: ImportedCompilerAttr<'_>,
) -> Registration {
    if env.get_const(decl).is_none() {
        return Registration::Absent;
    }
    if let Some(held_by) = foreign_resident_provenance(env, decl, module, false) {
        tracing::debug!(
            decl = %decl,
            held_by = %held_by,
            "imported compiler attribute not registered: the resident declaration is not \
             this module's"
        );
        return Registration::NotRegistered;
    }
    match attr {
        ImportedCompilerAttr::ImplementedBy(target) => {
            if env.has_implemented_by(decl) {
                return Registration::NotRegistered;
            }
            env.register_implemented_by(decl.clone(), target.clone());
        }
        ImportedCompilerAttr::Extern(symbol) => {
            if env.is_extern(decl) {
                return Registration::NotRegistered;
            }
            env.register_extern(decl.clone(), symbol.to_owned());
        }
        ImportedCompilerAttr::Noncomputable => {
            if env.is_noncomputable(decl) {
                return Registration::NotRegistered;
            }
            env.mark_noncomputable(decl.clone());
        }
    }
    Registration::Registered
}

/// Register a Clean payload's `@[implemented_by]` / `@[extern]` bindings
/// (payload version 5), as [`register_real_compiler_attr_entries`] registers
/// a Lean-built module's rows. A binding whose declaration the payload did
/// not get into the environment is dropped: nothing can call it.
///
/// The payload's ORDER rows (the module's own constants a late `attribute
/// [implemented_by]` command of the module came too late for) join the
/// environment's order record, so every compiled lane refuses as it does for
/// the same command in a file it elaborates (`docs/DECISIONS.md` R149): before
/// they travelled, `lateCaller 1` printed `20` at exit 0 through a Clean-built
/// `.olean` where pinned Lean prints `30`. A row is kept whenever its
/// constant is in the environment, whoever holds it: refusing more is the
/// safe direction.
///
/// SOUNDNESS: kernel-irrelevant, as for the Lean rows.
fn apply_payload_compiler_attrs(
    env: &mut Environment,
    payload: &CleanPayload,
    module: Option<&str>,
) {
    clean_kernel::env::csimp::import_compilation_snapshot(env, &payload.csimp);
    for (name, exposed) in &payload.definition_exposure {
        if env.get_const(name).is_some()
            && foreign_resident_provenance(env, name, module, false).is_none()
        {
            clean_kernel::env::exposure::record(env, name.clone(), *exposed);
        }
    }
    for (decl, target) in &payload.implemented_by {
        register_imported_compiler_attr(
            env,
            module,
            decl,
            ImportedCompilerAttr::ImplementedBy(target),
        );
    }
    for (decl, symbol) in &payload.externs {
        register_imported_compiler_attr(env, module, decl, ImportedCompilerAttr::Extern(symbol));
    }
    let order: Vec<(Name, clean_kernel::env::CompiledBefore)> = payload
        .implemented_by_order
        .iter()
        .filter(|(referrer, _, _)| env.get_const(referrer).is_some())
        .map(|(referrer, rebound, via)| {
            (
                referrer.clone(),
                clean_kernel::env::CompiledBefore {
                    rebound: rebound.clone(),
                    via: via.clone(),
                },
            )
        })
        .collect();
    if !order.is_empty() {
        env.record_compiled_before(order);
    }
}

fn register_real_simp_entries(env: &mut Environment, extensions: &[TypedExtension]) -> usize {
    // Collect (name, priority) pairs first so nothing borrows `extensions`
    // while `env` is mutated.
    let decoded: Vec<(Name, u64)> = extensions
        .iter()
        .filter(|ext| ext.extension_name == Name::interned(LEAN_SIMP_EXTENSION))
        .flat_map(|ext| ext.entries.iter())
        .filter_map(|entry| match entry {
            TypedExtensionEntry::Simp(simp) => Some((simp.lemma_name.clone(), simp.priority)),
            _ => None,
        })
        .collect();

    let mut unresolved = 0usize;
    for (name, priority) in decoded {
        // Already registered — by an earlier module or a repeated/overlapping
        // load (base + companion parts re-list the same entries). Idempotent.
        if env.is_simp_lemma(&name) {
            continue;
        }
        // SOUNDNESS: a simp lemma is only usable if its statement comes from
        // the kernel-checked imported constant. A name with no environment
        // constant (skipped at import) is counted loudly, never registered.
        if env.get_const(&name).is_none() {
            unresolved += 1;
            continue;
        }
        let priority = if priority == LEAN_DEFAULT_SIMP_PRIORITY {
            SimpPriority::Default
        } else {
            SimpPriority::Custom(u32::try_from(priority).unwrap_or(u32::MAX))
        };
        env.register_simp_lemma(name, priority);
    }
    unresolved
}

/// Preserve the match compiler's explicit classification. Metadata never
/// supplies a body or authorizes a proof; the simplifier reduces the actual
/// registered definition and checks its result in the kernel.
fn register_real_matcher_entries(
    env: &mut Environment,
    module: Option<&str>,
    extensions: &[TypedExtension],
) -> Result<usize, ImportError> {
    let mut unresolved = 0;
    for entry in extensions.iter().flat_map(|extension| &extension.entries) {
        if let TypedExtensionEntry::Matcher { name, info } = entry {
            if env.get_const(name).is_none()
                || foreign_resident_provenance(env, name, module, false).is_some()
            {
                unresolved += 1;
                continue;
            }
            env.register_matcher_info(name.clone(), info.clone())
                .map_err(|reason| {
                    crate::OleanError::Region(format!(
                        "invalid matcher metadata for {name}: {reason}"
                    ))
                })?;
        }
    }
    Ok(unresolved)
}

/// Register the DECODED real-Lean type-class declarations of a module into the
/// kernel class registry with their real `outParams`
/// (#olean-env-ext-restore, lane-B increment 2).
///
/// Real Lean `.olean`s persist every `class` declaration in
/// `Lean.classExtension` as a `ClassEntry` (name + `outParams` + `outLevelParams`);
/// the binary reader decodes those into [`TypedExtensionEntry::Class`]. Two
/// things this bridge fixes over the pre-decoder state:
///
/// 1. **Instance-less classes now exist.** The former heuristic and the
///    increment-1 instance bridge only materialized a class as the *conclusion head of
///    some imported instance*, so a class with no imported instance (e.g.
///    `Membership` after `Init.Prelude`) was entirely absent — `is_class`
///    returned `false`. This bridge registers every persisted `ClassEntry`,
///    instance-bearing or not.
/// 2. **Real `outParams`.** Both the former heuristic and the increment-1 bridge
///    register classes with EMPTY `out_params`; the elaborator's two-phase
///    out-param unification (`resolve_instance`) therefore never fired for
///    imported classes. This bridge threads the decoded positions
///    (`Membership` ⟶ `[0]`, `GetElem` ⟶ `[2, 3]`, `HAdd` ⟶ `[2]`).
///
/// Runs BEFORE the class/instance bridges below so the real `outParams` win
/// first-writer registration (`register_class` overwrites, so a later empty
/// registration must not clobber this — the downstream bridges all gate on
/// `!is_class`, and this bridge itself does not overwrite an existing twin).
///
/// Faithfulness rules (never fabricate, degrade inert / loud):
/// - a class whose declaring constant is absent from the environment (skipped
///   at import) has no Π-arity to anchor `num_params` on, so it is skipped;
/// - a decoded `outParam` index that addresses past the class's parameter
///   telescope is a layout error: the class is NOT registered and the drift is
///   reported (rather than registering partially-correct metadata);
/// - a class already registered under this name (a hand-registered kernel twin,
///   or an earlier lane) is left untouched (**first-writer-wins**); its
///   `out_params` are compared against the decoded set and any DISAGREEMENT is
///   returned as a fidelity report — Clean's hand-authored metadata must match
///   the real Lean `.olean` (loud, never silent).
///
/// `outLevelParams` is decoded (`ParsedClassEntry::out_level_params`) but not
/// threaded here: `KernelClassInfo` has no out-level-param field and the
/// resolver does not consume it yet (Lean uses it only to normalize TC cache
/// keys). Parked for a later increment.
///
/// Returns the fidelity-report lines (empty when every twin agrees), which the
/// loader records in [`LoadSummary::class_out_param_mismatches`].
///
/// SOUNDNESS: class metadata is elaboration-only — `out_params` steers which
/// arguments `resolve_instance` treats as inferred-from-instance during
/// candidate unification; every synthesized term is still kernel re-checked by
/// the caller. Wrong or extra class metadata can only cost completeness/parity,
/// never admit a false proof.
fn register_real_class_entries(
    env: &mut Environment,
    extensions: &[TypedExtension],
) -> Vec<String> {
    // Collect (name, out_params) tuples first so nothing borrows `extensions`
    // while `env` is mutated.
    let decoded: Vec<(Name, Vec<usize>)> = extensions
        .iter()
        .filter(|ext| ext.extension_name == Name::interned(LEAN_CLASS_EXTENSION))
        .flat_map(|ext| ext.entries.iter())
        .filter_map(|entry| match entry {
            TypedExtensionEntry::Class(class) => {
                // Binder indices always fit in usize on supported targets; a
                // (theoretical) overflowing index saturates and is then
                // rejected by the arity check below, never mis-registered.
                let out_params = class
                    .out_params
                    .iter()
                    .map(|&i| usize::try_from(i).unwrap_or(usize::MAX))
                    .collect();
                Some((class.name.clone(), out_params))
            }
            _ => None,
        })
        .collect();

    let mut mismatches = Vec::new();
    for (class, out_params) in decoded {
        if let Some(existing) = env.get_class_info(&class) {
            // First-writer-wins: a hand-registered kernel twin (or an earlier
            // lane) already owns this class. Do NOT overwrite — but verify the
            // decoded out-params AGREE, and report any drift.
            let mut existing_out = existing.out_params.clone();
            existing_out.sort_unstable();
            let mut decoded_out = out_params;
            decoded_out.sort_unstable();
            if existing_out != decoded_out {
                mismatches.push(format!(
                    "class {class}: registered outParams {existing_out:?} disagree with \
                     Lean .olean classExtension outParams {decoded_out:?} (kept registered)"
                ));
            }
            continue;
        }
        // Not yet registered: derive num_params from the class constant's
        // Π-arity (faithful — never fabricate). A class whose declaring constant
        // was skipped at import has no arity to anchor the metadata on.
        let Some(num_params) = class_param_arity(env, &class) else {
            continue;
        };
        // out-param indices must address real parameters; a decode that points
        // past the telescope is a layout error — do not register partially
        // correct metadata, report the drift instead.
        if out_params.iter().any(|&i| i >= num_params) {
            mismatches.push(format!(
                "class {class}: decoded outParams {out_params:?} exceed parameter arity \
                 {num_params}; not registered"
            ));
            continue;
        }
        env.register_class(KernelClassInfo {
            name: class,
            num_params,
            out_params,
            semi_out_params: Vec::new(),
        });
    }
    mismatches
}

/// Bridge imported typeclass instances from the persistent extension into the
/// kernel instance registry.
///
/// `.olean` modules persist `@[instance]` registrations in the `instanceExtension`
/// persistent environment extension. [`load_extension_entries`] stores those as
/// opaque `EnvExtensionEntry` objects, but the elaborator's instance synthesis
/// reads the *kernel* registry via [`Environment::get_class_instances`] (see
/// `clean_elab::infer::init_instances_from_env`). Without this bridge, imported
/// instances are invisible to typeclass resolution.
///
/// This function folds the imported raw entries into the typed [`InstanceExtState`]
/// (decoding each instance's class name and priority faithfully — no fabrication),
/// then re-registers each entry via the existing [`Environment::register_instance`]
/// API so `get_class_instances()` returns them. Instances already present in the
/// kernel registry (e.g. natively registered, or re-encountered across module
/// loads / base+private `.olean` pairs) are skipped to avoid duplicates.
///
/// `type_`/`value` are left `None`: the persisted extension records only the
/// instance name, class, and priority. The elaborator reconstructs the instance
/// expression from `env.get_const(name)` when these are absent (see #443), so
/// the imported constant's own type/value are used — consistent with how natively
/// declared instances without overridden binders are handled.
/// Bridge imported typeclass instances from the persistent extension into the
/// kernel registry.
///
/// Only names explicitly present in the persistent instance extension are
/// candidates. Guessing registrations from definition types changes elaboration
/// semantics: ordinary class-valued definitions and even plain structures become
/// spurious instances/classes. An eventual kernel check does not justify that
/// change to the language's instance search.
fn register_instances_from_extension(env: &mut Environment) {
    let idx = instance_ext_idx();

    // Snapshot (name, priority, decoded-class) for every imported instance entry.
    // Collect into an owned Vec so the immutable borrow of the extension state is
    // released before re-borrowing `env` mutably for registration.
    let pending: Vec<(Name, u32, Name)> = match env.get_ext_state_or_init::<InstanceExtState>(idx) {
        Some(state) => state
            .all_instances()
            .map(|info| {
                (
                    info.instance_name.clone(),
                    info.priority,
                    info.class_name.clone(),
                )
            })
            .collect(),
        None => return,
    };

    for (name, priority, decoded_class) in pending {
        // Skip instances already present in the kernel registry to avoid
        // duplicate registration (idempotent across repeated/overlapping loads).
        if env.is_instance(&name) {
            continue;
        }
        // The class an instance belongs to is the head constant of its type's
        // conclusion (e.g. `{α} → [DecidableEq α] → DecidableEq (List α)` ⟶
        // `DecidableEq`). This is authoritative and — unlike the persisted
        // `class_name` — works for real Lean `.olean`s, whose `instanceExtension`
        // entries Clean cannot decode (the folded class is then anonymous; see
        // `InstanceExtEntry::from_env_entry`). Fall back to the decoded class.
        // Clean's explicit persistent metadata may precede its declaration.
        // Preserve that metadata-only registry contract without inventing a
        // declaration, value, or instance candidate from an unrelated type.
        let class = env
            .get_const(&name)
            .and_then(|constant| instance_conclusion_class(&constant.type_))
            .filter(|c| !c.is_anon())
            .unwrap_or(decoded_class);
        if class.is_anon() {
            continue;
        }
        env.register_instance(KernelInstanceInfo {
            name,
            class_name: class,
            priority,
            type_: None,
            value: None,
        });
    }
}

/// Retry explicitly imported instance records after their constants become
/// available. The historical policy name is retained for API compatibility;
/// an arbitrary class-valued definition is not evidence of an instance or class.
/// Unknown extension payloads remain unknown instead of triggering guesses.
pub(crate) fn finalize_global_instance_backfill(env: &mut Environment) {
    register_instances_from_extension(env);
}

/// The Π-arity of a class's type up to its `Sort` result — its `num_params` for
/// instance resolution. e.g. `DecidableEq : Sort u → Sort _` ⟶ `1`,
/// `LawfulBEq : (α) → [BEq α] → Prop` ⟶ `2`. Returns `None` if the type does not
/// end in a `Sort` (not a class).
fn class_param_arity(env: &Environment, class: &Name) -> Option<usize> {
    let mut t = &env.get_const(class)?.type_;
    let mut n = 0usize;
    while let ExprKind::Pi(_, _, body) = t.kind() {
        n += 1;
        t = body;
    }
    matches!(t.kind(), ExprKind::Sort(_)).then_some(n)
}

/// Derive the class an instance belongs to from its type: strip leading Π
/// binders to reach the conclusion, then return the head constant's name.
/// e.g. `{α} → [DecidableEq α] → DecidableEq (List α)` ⟶ `Some(DecidableEq)`.
fn instance_conclusion_class(ty: &Expr) -> Option<Name> {
    let mut conclusion = ty;
    while let ExprKind::Pi(_, _, body) = conclusion.kind() {
        conclusion = body;
    }
    match conclusion.get_app_fn().kind() {
        ExprKind::Const(name, _) => Some(name.clone()),
        _ => None,
    }
}

/// Bridge imported `@[simp]` lemmas from the persistent extension into the
/// kernel simp-lemma registry.
///
/// `.olean` modules persist `@[simp]` registrations in the `simpExtension`
/// persistent environment extension. [`load_extension_entries`] stores those as
/// opaque `EnvExtensionEntry` objects, but the `simp` tactic reads the *kernel*
/// registry via [`Environment::get_simp_lemmas`] / [`Environment::is_simp_lemma`].
/// Without this bridge, imported simp lemmas are invisible to `simp` — the exact
/// gap that [`register_instances_from_extension`] closed for typeclass instances.
///
/// This function folds the imported raw entries into the typed [`SimpExtState`]
/// (decoding each lemma's name and priority faithfully — no fabrication), then
/// re-registers each entry via the existing [`Environment::register_simp_lemma`]
/// API so `get_simp_lemmas()` returns them. Lemmas already present in the kernel
/// registry (e.g. re-encountered across module loads / base+private `.olean`
/// pairs) are skipped to avoid redundant re-registration (idempotent).
fn register_simp_lemmas_from_extension(env: &mut Environment) {
    let idx = simp_ext_idx();

    // Fold imported raw entries into the typed simp state, then snapshot the
    // (name, priority) pairs we need. We collect into an owned Vec so the
    // immutable borrow of the extension state is released before re-borrowing
    // `env` mutably for registration.
    let pending: Vec<(Name, SimpPriority)> = match env.get_ext_state_or_init::<SimpExtState>(idx) {
        Some(state) => state
            .iter()
            .map(|info| (info.name.clone(), info.priority))
            .collect(),
        None => return,
    };

    for (name, priority) in pending {
        // Skip lemmas already present in the kernel registry to avoid redundant
        // re-registration (idempotent across repeated/overlapping loads).
        if env.is_simp_lemma(&name) {
            continue;
        }
        env.register_simp_lemma(name, priority);
    }
}

/// Bridge imported reducibility attributes (`@[reducible]`, `@[semireducible]`,
/// `@[irreducible]`) from the persistent attribute extension into the kernel's
/// per-constant reducibility state.
///
/// `.olean` modules persist `@[reducible]`/`@[irreducible]` registrations in the
/// `attrExtension` persistent environment extension. [`load_extension_entries`]
/// stores those as opaque `EnvExtensionEntry` objects, but the kernel reducer
/// (delta-reduction / [`Environment::get_reducibility`]) and the elaborator's
/// transparency logic read the *typed* [`Reducibility`] recorded on each
/// `ConstantInfo`. Without this bridge, an imported `@[reducible]` definition is
/// treated as the default `Regular(0)` (semireducible) and an imported
/// `@[irreducible]` definition is still unfolded — the exact gap that
/// [`register_instances_from_extension`] / [`register_simp_lemmas_from_extension`]
/// closed for instances and simp lemmas.
///
/// This function folds the imported raw entries into the typed [`AttrExtState`]
/// (via [`Environment::get_ext_state_or_init`], which decodes each
/// `(decl_name, attr_name, priority)` faithfully — no fabrication), then maps the
/// recognized reducibility attribute names onto the kernel [`Reducibility`] levels
/// exactly as the elaborator's `@[reducible]`/`@[semireducible]`/`@[irreducible]`
/// command handlers do, applying them through the existing
/// [`TrustedEnvExt::set_reducibility`] API. Attributes whose target constant is not
/// (yet) present in the environment are skipped — `set_reducibility` reports this
/// by returning `false`, so re-application is naturally idempotent: setting the
/// same level twice is a no-op-equivalent overwrite.
///
/// Non-reducibility attributes (`@[simp]`, `@[instance]`, `@[inline]`,
/// `@[class]`, …) are intentionally left to their own dedicated bridges or to the
/// elaborator's in-memory attribute manager; this function only materializes the
/// attributes the kernel itself acts on (delta-reduction transparency).
fn register_attributes_from_extension(env: &mut Environment) {
    let idx = attr_ext_idx();

    // Fold imported raw entries into the typed attribute state, then snapshot the
    // (decl_name, reducibility) pairs we need. We collect into an owned Vec so the
    // immutable borrow of the extension state is released before re-borrowing `env`
    // mutably for registration. Only the reducibility attribute names the kernel
    // reducer acts on are materialized; the inverted `decls_by_attr` index makes
    // this a direct lookup per recognized attribute.
    let pending: Vec<(Name, Reducibility)> = match env.get_ext_state_or_init::<AttrExtState>(idx) {
        Some(state) => REDUCIBILITY_ATTRS
            .iter()
            .flat_map(|&(attr_name, reducibility)| {
                let attr = Name::interned(attr_name);
                state
                    .get_decls_with_attr(&attr)
                    .iter()
                    .map(move |decl_name| (decl_name.clone(), reducibility))
            })
            .collect(),
        None => return,
    };

    for (decl_name, reducibility) in pending {
        // `set_reducibility` returns false when the target constant is absent;
        // we simply skip those (faithful: we never fabricate a constant).
        env.set_reducibility(&decl_name, reducibility);
    }
}

/// The persisted attribute names the kernel reducer acts on, paired with the
/// [`Reducibility`] level each one sets — mirroring the elaborator's
/// `@[reducible]`/`@[semireducible]`/`@[irreducible]` command handlers.
///
/// Other attribute names (`@[simp]`, `@[instance]`, `@[inline]`, `@[class]`, …)
/// are intentionally absent: they are handled by their own dedicated bridges or
/// the elaborator's in-memory attribute manager, and do not affect kernel
/// delta-reduction transparency.
const REDUCIBILITY_ATTRS: [(&str, Reducibility); 3] = [
    ("reducible", Reducibility::Reducible),
    ("semireducible", Reducibility::SEMIREDUCIBLE),
    ("irreducible", Reducibility::Irreducible),
];

/// The persisted attribute name marking a declaration as a typeclass.
///
/// In Lean 4, `@[class]` is recorded in the same general-purpose `attrExtension`
/// persistent store as `@[simp]`/`@[instance]`/`@[reducible]`, keyed by this
/// attribute name. See `clean_elab::attribute_ext2::valid_decl_kinds` (`"class"`
/// applies to `Structure`/`Inductive`).
const CLASS_ATTR: &str = "class";

/// Bridge imported `@[class]` attributes from the persistent attribute extension
/// into the kernel's typeclass registry.
///
/// A `.olean` declares a typeclass by attaching `@[class]` to a structure or
/// inductive; that registration is persisted in the `attrExtension` extension
/// keyed by the attribute name `"class"`. [`load_extension_entries`] stores those
/// as opaque `EnvExtensionEntry` objects, and [`register_attributes_from_extension`]
/// deliberately ignores the `"class"` entries (it only materializes the
/// reducibility attributes the kernel reducer acts on). Without this bridge, an
/// imported `@[class]` structure is registered as an *ordinary inductive*, so
/// [`Environment::is_class`] returns `false` and the elaborator's instance
/// synthesis never treats it as a typeclass — typeclass resolution fails for every
/// imported class (e.g. Mathlib's `Group`/`AddGroup`). This is the exact gap that
/// [`register_instances_from_extension`] / [`register_simp_lemmas_from_extension`]
/// closed for instances and simp lemmas.
///
/// This function folds the imported raw entries into the typed [`AttrExtState`]
/// (via [`Environment::get_ext_state_or_init`], which decodes each
/// `(decl_name, attr_name, priority)` faithfully — no fabrication), looks up every
/// declaration carrying the `"class"` attribute, and registers it as a typeclass
/// through the existing [`Environment::register_class`] API. The class's
/// `num_params` is read from the already-registered inductive
/// ([`Environment::get_inductive`]) — exactly the value the elaborator's
/// structure/class command supplies (the count of the class's parameters). Output
/// and semi-output parameter indices are not persisted in the `attrExtension`
/// entry, so they are left empty, matching how the elaborator's `structure`
/// command registers a plain `class` without an explicit `outParam`/`semiOutParam`
/// annotation (`clean_elab::structure_cmd`).
///
/// Declarations whose `@[class]` target is not (yet) a registered inductive are
/// skipped — the `.olean` may carry the attribute without the corresponding
/// inductive having been loaded, and we never fabricate class metadata. Classes
/// already present in the kernel registry (re-encountered across module loads or
/// base+private `.olean` pairs) are skipped so repeated loads are idempotent.
fn register_classes_from_extension(env: &mut Environment) {
    let idx = attr_ext_idx();

    // Fold imported raw entries into the typed attribute state, then snapshot the
    // declaration names carrying `@[class]`. We collect into an owned Vec so the
    // immutable borrow of the extension state is released before re-borrowing `env`
    // (immutably for the inductive lookup, mutably for registration).
    let class_decls: Vec<Name> = match env.get_ext_state_or_init::<AttrExtState>(idx) {
        Some(state) => state
            .get_decls_with_attr(&Name::interned(CLASS_ATTR))
            .to_vec(),
        None => return,
    };

    for class_name in class_decls {
        // Skip classes already present in the kernel registry to avoid redundant
        // re-registration (idempotent across repeated/overlapping loads).
        if env.is_class(&class_name) {
            continue;
        }
        // Read `num_params` from the imported inductive faithfully. If the
        // inductive is absent, skip — we never fabricate class metadata.
        let Some(num_params) = env
            .get_inductive(&class_name)
            .map(|ind| ind.num_params as usize)
        else {
            continue;
        };
        env.register_class(KernelClassInfo {
            name: class_name,
            num_params,
            out_params: Vec::new(),
            semi_out_params: Vec::new(),
        });
    }
}

/// Why an imported structure-field table is not the one the environment's
/// own declarations define; `None` when it is.
///
/// The table is elaborator metadata the kernel never sees: `.x` on an `S`
/// elaborates to `Proj(S, i, _)` and `{ x := …, y := … }` to `S.mk` with the
/// position `i` read from it. So it is not believed as read. Clean's kernel
/// terms carry no binder names, so the admitted inductive alone cannot name
/// its fields; what names field `f` is the projection constant `S.f`, and what
/// fixes its position is what `S.f` COMPUTES: applied to the parameters and
/// `S.mk params a₀ … aₙ₋₁` (fresh locals typed by the constructor's own
/// telescope), its value must reduce, by the kernel's `whnf`, to exactly the
/// local `aᵢ` for the table's index `i`. A table is registered only when every
/// field passes (module-trust round 28: the round-27 rule read the projection's
/// BODY SHAPE, `λ*. Proj(S, j, _)`, and skipped any other — a reversed table
/// with the projections rewritten to equivalent recursor bodies (Y1), or with
/// both projections removed (Y2), made `(V0.P.mk 0 1).x = 1` pass).
///
/// Refused: a field with no projection constant, a projection with no
/// definition, one that does not reduce to a single field of the constructor,
/// one that reduces to another field than the table says, a count the
/// constructor does not have, and a non-atomic field name. Not evidence either
/// way (skipped): a projection absent under a lazy closure load
/// (`lazy_definitions`, where definitions are served later by a
/// `ConstantSource`), a value-free projection the table places at a
/// PROPOSITION field (a proof, which cannot change what a statement means),
/// and a value-free projection the checker's own native prelude declares.
///
/// This makes the table the one the artifact's own declarations define. It
/// does not make those declarations faithful to a source: a projection and
/// table rewritten together are a different, consistent module, which only
/// source binding or the disclosure can speak to (`reports/2026-09-24-module-trust.md`).
/// Why [`structure_table_contradiction`] does not register a table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum TableFault {
    /// Kernel computation stopped before it could authenticate the table.
    Resource(String),
    /// Not decidable YET: a field's projection is not in the environment (a
    /// module's `.olean.private` companion, where Lean keeps a private
    /// field's projection, is loaded after the module itself), or a
    /// value-free projection's field type mentions what is not loaded.
    Absent(String),
    /// A field's projection computes ANOTHER field than the table says.
    Computes(String),
    /// The projections define no table, or another one for another reason
    /// (count, constructor, a data field with no definition, …).
    Contradiction(String),
}

impl TableFault {
    pub(crate) fn reason(&self) -> &str {
        match self {
            Self::Resource(r) | Self::Absent(r) | Self::Computes(r) | Self::Contradiction(r) => r,
        }
    }

    fn into_import_error(self, structure: &Name) -> ImportError {
        match self {
            Self::Resource(reason) => ImportError::ResourceLimit {
                operation: format!("structure-field validation for {structure}"),
                reason,
            },
            fault => ImportError::InconsistentStructureTable {
                structure: structure.to_string(),
                reason: fault.to_string(),
            },
        }
    }
}

fn table_resource_fault(tc: &clean_kernel::TypeChecker<'_>) -> Option<TableFault> {
    if !tc.heartbeat_spent() {
        return None;
    }
    let reason = if clean_kernel::tc::declaration_budget_exhausted() {
        format!(
            "declaration budget exhausted ({} kernel operations)",
            clean_kernel::tc::declaration_budget_limit()
        )
    } else {
        format!(
            "kernel heartbeat budget ({}) or caller deadline exhausted",
            tc.heartbeat_limit()
        )
    };
    Some(TableFault::Resource(reason))
}

impl std::fmt::Display for TableFault {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.reason())
    }
}

pub(crate) fn structure_table_contradiction(
    env: &Environment,
    struct_name: &Name,
    fields: &[Name],
    proj_fns: &[(Name, Name)],
    lazy_definitions: bool,
) -> Option<TableFault> {
    let ind = env.get_inductive(struct_name)?;
    let [ctor_name] = ind.constructor_names.as_slice() else {
        return Some(TableFault::Contradiction(format!(
            "`{struct_name}` has {} constructors, not one",
            ind.constructor_names.len()
        )));
    };
    let Some(ctor) = env.get_constructor(ctor_name) else {
        return Some(TableFault::Contradiction(format!(
            "the constructor `{ctor_name}` is not in the closure"
        )));
    };
    let num_params = ctor.num_params as usize;
    let num_fields = ctor.num_fields as usize;
    if fields.len() != num_fields {
        return Some(TableFault::Contradiction(format!(
            "the table has {} fields, the constructor `{ctor_name}` {num_fields}",
            fields.len()
        )));
    }
    // `S : Π params, Prop`: its fields that have projections are proofs.
    let prop_structure = {
        let mut ty = &ind.type_;
        while let ExprKind::Pi(_, _, body) = ty.kind() {
            ty = body;
        }
        ind.num_indices == 0 && matches!(ty.kind(), ExprKind::Sort(l) if l.is_zero())
    };
    let tc = clean_kernel::TypeChecker::new(env);
    // Fresh locals for the parameters and fields, typed by the constructor's
    // own telescope.
    let mut ty = ctor.type_.clone();
    let mut locals = Vec::with_capacity(num_params + num_fields);
    let mut field_types = Vec::with_capacity(num_fields);
    for k in 0..num_params + num_fields {
        let ExprKind::Pi(binder, domain, body) = ty.kind() else {
            return Some(TableFault::Contradiction(format!(
                "the constructor `{ctor_name}`'s type has fewer than {} binders",
                num_params + num_fields
            )));
        };
        if k >= num_params {
            field_types.push((**domain).clone());
        }
        let local = tc.push_binder_local(Name::anon(), (**domain).clone(), *binder);
        ty = body.instantiate(&Expr::fvar(local));
        locals.push(local);
    }
    let levels: Vec<clean_kernel::Level> = ind
        .level_params
        .iter()
        .cloned()
        .map(clean_kernel::Level::param)
        .collect();
    let constructed = Expr::apps(
        Expr::const_(ctor_name.clone(), levels),
        locals.iter().map(|l| Expr::fvar(*l)),
    );
    let params: Vec<Expr> = locals[..num_params]
        .iter()
        .map(|l| Expr::fvar(*l))
        .collect();
    if let Some(fault) = table_resource_fault(&tc) {
        return Some(fault);
    }
    for (i, field) in fields.iter().enumerate() {
        let proj_name = match field.inner() {
            clean_kernel::name::NameInner::Str(parent, component) if parent.is_anon() => {
                struct_name.clone().str(component.as_ref())
            }
            clean_kernel::name::NameInner::Num(parent, component) if parent.is_anon() => {
                struct_name.clone().num(*component)
            }
            _ => {
                return Some(TableFault::Contradiction(format!(
                    "field `{field}` is not an atomic name"
                )))
            }
        };
        // Lean's own `StructureFieldInfo.projFn` names the projection when it
        // is not `S.f` literally: a private field's is `_private.<mod>.<n>.S.f`
        // (measured: `Lean.Macro.State.expandedMacroDecls`, pinned v4.30 Init),
        // and a hygienic structure's carries its macro scopes after the field
        // (`…RpcEncodablePacket.id._@.Lean.Widget.Types…`, measured in `Lean`).
        // Only a `projFn` that is `S.f` up to those two decorations stands in
        // for it: one naming any other constant cannot move a field.
        let (proj_name, proj) = match env.get_const(&proj_name) {
            Some(proj) => (proj_name, Some(proj)),
            None => match proj_fns
                .iter()
                .find(|(f, p)| f == field && names_field_projection(p, struct_name, field))
            {
                Some((_, alias)) => (alias.clone(), env.get_const(alias)),
                None => (proj_name, None),
            },
        };
        let Some(proj) = proj else {
            if lazy_definitions {
                continue;
            }
            return Some(TableFault::Absent(format!(
                "field `{field}` has no projection constant `{proj_name}` in the closure"
            )));
        };
        let Some(value) = proj.value.as_ref() else {
            let imported = matches!(
                env.get_constant_origin(&proj_name),
                Some(ConstantOrigin::Olean { .. } | ConstantOrigin::CleanPayload { .. })
            );
            if !imported {
                // The kernel's native prelude declares some projections
                // (`MonadExcept.throw`, measured on the pinned v4.30 Init)
                // without a value; an artifact's copy of the same name is
                // not loaded over it. The checker's own base, not artifact
                // evidence either way.
                continue;
            }
            // A proof field's projection is exported without its value: Lean's
            // public `.olean` carries theorems as value-free declarations
            // (measured: `Std.Irrefl.irrefl`, an `Axiom` here, pinned v4.30),
            // and bounded-memory loading elides proof values. Which PROOF a
            // proof field's name reaches cannot change what a statement means,
            // so such a field is not checked — but only where the table puts
            // it at a proposition: every data position is claimed by a
            // projection that computes it.
            if prop_structure {
                continue; // every field of a `Prop` structure that has a projection is a proof
            }
            let inferred = tc.infer_type(&field_types[i]).map(|sort| tc.whnf(&sort));
            if let Some(fault) = table_resource_fault(&tc) {
                return Some(fault);
            }
            match inferred {
                Ok(sort) if matches!(sort.kind(), ExprKind::Sort(l) if l.is_zero()) => continue,
                Ok(_) => {}
                // The field's type mentions what is not loaded yet (a module
                // loaded on its own, or before its dependencies): undecided
                // until the closure ends, where it is refused.
                Err(_) => {
                    return Some(TableFault::Absent(format!(
                        "whether field `{field}` (index {i}), whose projection `{proj_name}` has \
                         no definition, is a proof cannot be decided in this environment"
                    )));
                }
            }
            return Some(TableFault::Contradiction(format!(
                "the projection `{proj_name}` of field `{field}` has no definition ({:?}), and \
                 the table puts it at data field {i}",
                proj.kind
            )));
        };
        let applied = Expr::apps(
            value.clone(),
            params
                .iter()
                .cloned()
                .chain(std::iter::once(constructed.clone())),
        );
        let reduced = tc.whnf(&applied);
        if let Some(fault) = table_resource_fault(&tc) {
            return Some(fault);
        }
        let position = match reduced.kind() {
            ExprKind::FVar(id) => locals[num_params..].iter().position(|l| l == id),
            _ => None,
        };
        match position {
            Some(j) if j == i => {}
            Some(j) => {
                return Some(TableFault::Computes(format!(
                    "field `{field}` is at index {i} in the table, but the projection \
                     `{proj_name}` computes field {j} of `{ctor_name}`"
                )));
            }
            None => {
                return Some(TableFault::Contradiction(format!(
                    "the projection `{proj_name}` of field `{field}` does not compute a field \
                     of `{ctor_name}`"
                )));
            }
        }
    }
    None
}

/// A name with Lean's two decorations removed: a `_private.<module>.<n>.`
/// prefix (a private declaration) and a `._@.…` macro-scope suffix (a
/// hygienic one).
fn undecorated(name: &str) -> &str {
    let mut name = name;
    if let Some(rest) = name.strip_prefix("_private.") {
        // `<module components>.<n>.<name>`: the first all-digit component
        // ends the prefix.
        let mut offset = 0;
        for component in rest.split('.') {
            offset += component.len() + 1;
            if !component.is_empty() && component.bytes().all(|b| b.is_ascii_digit()) {
                name = rest.get(offset..).unwrap_or("");
                break;
            }
        }
    }
    name.split_once("._@.").map_or(name, |(base, _)| base)
}

/// `proj_fn` is the projection of field `field` of `struct_name`: it is
/// `struct_name.field` once both are undecorated ([`undecorated`]).
fn names_field_projection(proj_fn: &Name, struct_name: &Name, field: &Name) -> bool {
    let proj_fn = proj_fn.to_string();
    let struct_name = struct_name.to_string();
    let wanted = format!("{}.{field}", undecorated(&struct_name));
    undecorated(&proj_fn) == wanted
}

/// If `expr` is a projection-function body — `λ params. Proj(S, i, self)`
/// (optionally under transparent `MData`) — return the projected structure name
/// `S` and the 0-based field index `i`. Returns `None` for anything else.
///
/// This is the same value-shape [`super::convert::is_projection_fn_body`]
/// detects, but it recovers the target `(S, i)` rather than a bare bool. It
/// only NOMINATES a recovered table; the table is registered only when
/// [`structure_table_contradiction`] finds nothing.
pub(super) fn projection_fn_target(expr: &Expr) -> Option<(Name, u32)> {
    let mut e = expr;
    loop {
        match e.kind() {
            ExprKind::Lam(_, _, body) => e = body,
            ExprKind::MData(_, inner) => e = inner,
            ExprKind::Proj(struct_name, idx, _) => return Some((struct_name.clone(), *idx)),
            _ => return None,
        }
    }
}

/// The declaring namespace of every IMPORTED `scoped instance`, keyed by the
/// instance's name — Lean's `ScopedEnvExtension.Entry.scoped ns entry` with
/// `attrKind = scoped` in `Lean.Meta.instanceExtension`.
///
/// The kernel registry holds such an instance exactly like a global one (the
/// pre-2026-09-10 over-approximation `register_real_instance_entries`
/// documents), and the elaborator already knows how to gate a scoped
/// instance on `open`/namespace entry for SOURCE-declared ones
/// (`ElabCtx::instance_visible` over `scoped_instances`); what was missing is
/// the bridge for imported ones. Measured on the pinned Mathlib:
/// `example (α : Type) [LE α] : LT α := inferInstance` FAILS in Lean and
/// PASSED in Clean through `Classical.Order.instOrd` (a `scoped instance`)
/// plus `ltOfOrd`, which then handed `Pi.preorder` an `LT` whose `lt` is a
/// `compare` and broke its `by intros; rfl` autoParam. In-process state,
/// never exported.
#[derive(Clone, Debug, Default)]
pub struct ScopedInstanceState {
    /// instance name → declaring namespace, for every instance whose only
    /// entries are `scoped` (an instance that also has a global entry is in
    /// every state, and is not listed): it is in a state only once its
    /// namespace is activated there.
    pub scope_of: std::collections::HashMap<Name, Name>,
    /// Lean's `ScopedEnvExtension.StateStack.scopedEntries` for the instance
    /// extension, as (namespace, instance, priority) in the order the entries
    /// were added — imported modules first, in import order, then the
    /// current module's. `activateScoped ns` adds `ns`'s entries to the
    /// state in exactly this order (`ScopedEnvExtension.lean`). Filled by
    /// source elaboration (`scoped instance`, `attribute [scoped
    /// instance]`); an `.olean`-imported scoped instance is listed in
    /// `scope_of` only, at its registered priority.
    pub entries: Vec<(Name, Name, u32)>,
    /// The modules whose Clean-payload instance entries are already applied
    /// ([`apply_payload_instance_entries`]). Lean imports each module once;
    /// an environment that loads one module's closure through several calls
    /// (`clean lake build` loads each direct import's closure in turn) must
    /// not replay a shared module's entries again after a later module's.
    pub applied_payload_modules: std::collections::HashSet<String>,
}

/// Whether instance `name` has a GLOBAL entry in the environment's instance
/// table — the replay of every imported module's global entries that an
/// importer starts from: a registered instance whose entries are not all
/// `local` (never exported) or all `scoped` (in no state until activated).
#[must_use]
pub fn has_global_instance_entry(env: &Environment, name: &Name) -> bool {
    env.is_instance(name)
        && !env.is_local_instance(name)
        && !env
            .get_ext_state::<ScopedInstanceState>(scoped_instance_idx())
            .is_some_and(|state| state.scope_of.contains_key(name))
}

/// Lean's `addInstanceEntry` of a GLOBAL entry for the registered instance
/// `name` into the environment's global instance table
/// (`Lean/Meta/Instances.lean`, `DiscrTree.insertVal`): IN PLACE with
/// `priority` when the table holds it, pushed as the newest otherwise — it
/// then has a global entry, and is no longer only local or only scoped.
pub fn add_global_instance_entry(env: &mut Environment, name: &Name, priority: u32) {
    if has_global_instance_entry(env, name) {
        env.set_instance_priority_in_place(name, priority);
        return;
    }
    env.push_instance_as_newest(name, priority);
    env.unmark_local_instance(name);
    env.get_ext_state_mut::<ScopedInstanceState>(scoped_instance_idx())
        .scope_of
        .remove(name);
}

/// Replay a Clean payload's class, instance, alias and namespace entries
/// (payload version 3 and later) into `env`, as Lean's import replays the module's
/// exported extension entries: classes registered; each global instance
/// entry added to the global table ([`add_global_instance_entry`], a fresh
/// registration for an instance the environment does not know); each scoped
/// entry appended to `scopedEntries` (a fresh scoped-only registration for a
/// new instance); aliases and namespaces registered. A module's entries are
/// applied once per environment (`module`, when known).
fn apply_payload_instance_entries(
    env: &mut Environment,
    payload: &CleanPayload,
    module: Option<&str>,
) {
    if let Some(module) = module {
        let state = env.get_ext_state_mut::<ScopedInstanceState>(scoped_instance_idx());
        if !state.applied_payload_modules.insert(module.to_string()) {
            return;
        }
    }
    for class in &payload.classes {
        if !env.is_class(&class.name) {
            env.register_class(class.clone());
        }
    }
    for info in &payload.global_instances {
        if env.get_const(&info.name).is_none() {
            // An entry never conjures a constant.
            continue;
        }
        if env.is_instance(&info.name) {
            add_global_instance_entry(env, &info.name, info.priority);
        } else {
            env.register_instance(info.clone());
        }
    }
    for (ns, info) in &payload.scoped_instances {
        if env.get_const(&info.name).is_none() {
            continue;
        }
        if !env.is_instance(&info.name) {
            env.register_instance(info.clone());
            env.get_ext_state_mut::<ScopedInstanceState>(scoped_instance_idx())
                .scope_of
                .insert(info.name.clone(), ns.clone());
        }
        env.get_ext_state_mut::<ScopedInstanceState>(scoped_instance_idx())
            .entries
            .push((ns.clone(), info.name.clone(), info.priority));
    }
    for (alias, target) in &payload.export_aliases {
        if env.get_const(target).is_some() {
            env.register_export_alias(alias.clone(), target.clone());
        }
    }
    for ns in &payload.namespaces {
        env.register_namespace(ns);
    }
}

/// Placeholder entry type: the state is filled by the loader directly and
/// carries no persisted entries.
#[derive(Clone, Debug)]
pub struct ScopedInstanceEntry {
    pub instance: Name,
    pub namespace: Name,
}

impl PersistentExtEntry for ScopedInstanceEntry {
    fn to_env_entry(&self) -> EnvExtensionEntry {
        EnvExtensionEntry {
            name: self.instance.clone(),
            data: EnvExtensionEntryData::Scalar(0),
        }
    }

    fn from_env_entry(_entry: &EnvExtensionEntry) -> Option<Self> {
        None
    }
}

impl PersistentExtState for ScopedInstanceState {
    type Entry = ScopedInstanceEntry;

    fn add_entry(&mut self, entry: &Self::Entry) {
        self.scope_of
            .insert(entry.instance.clone(), entry.namespace.clone());
    }

    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        Vec::new()
    }
}

static SCOPED_INSTANCE_IDX: std::sync::OnceLock<ExtensionIdx> = std::sync::OnceLock::new();

/// The extension index of [`ScopedInstanceState`]; the elaborator reads it
/// through `Environment::get_ext_state`.
pub fn scoped_instance_idx() -> ExtensionIdx {
    *SCOPED_INSTANCE_IDX.get_or_init(|| {
        register_persistent_ext::<ScopedInstanceState>(Name::from_string(
            "Clean.olean.scopedInstances",
        ))
    })
}

/// One decoded `Lean.structureExt` entry whose structure was NOT yet
/// materialized when its module's extensions were registered.
///
/// The zero-copy import path serves a module's constants LAZILY, so at the
/// per-module registration point `env.get_inductive(struct)` can be `None`
/// for the very structure the entry describes — the same reason the
/// projection-derived recovery moved to an end-of-closure pass (see the note
/// at `load.rs` above `register_structure_fields_from_projections`). The
/// entry is parked here and retried once the whole closure is present.
#[derive(Clone, Debug)]
pub(crate) struct PendingStructureMeta {
    pub(crate) struct_name: Name,
    pub(crate) field_names: Vec<Name>,
    /// `(fieldName, projFn)` as Lean's `StructureFieldInfo` records them.
    pub(crate) field_proj_fns: Vec<(Name, Name)>,
    pub(crate) parents: Vec<(Name, Name)>,
}

impl PersistentExtEntry for PendingStructureMeta {
    fn to_env_entry(&self) -> EnvExtensionEntry {
        // In-process only: never exported, never imported from an olean.
        EnvExtensionEntry {
            name: self.struct_name.clone(),
            data: EnvExtensionEntryData::Scalar(0),
        }
    }

    fn from_env_entry(_entry: &EnvExtensionEntry) -> Option<Self> {
        None
    }
}

/// The per-environment parking lot for [`PendingStructureMeta`].
#[derive(Clone, Debug, Default)]
pub(crate) struct StructureExtPending {
    pub(crate) pending: Vec<PendingStructureMeta>,
    /// Structures whose field table a Clean PAYLOAD registered. A decoded
    /// `structureExt` table for one of these comes from the same artifact
    /// (its Lean region), so a disagreement between the two is a rewritten
    /// artifact. A table registered by anything else — the kernel's native
    /// prelude, above all — may legitimately differ from a Lean version's
    /// (`String`, `Array` under v4.30: measured), and is not compared.
    pub(crate) payload_tables: HashSet<Name>,
    /// Structures whose table a decoded `structureExt` entry or the
    /// projection-recovery pass registered (each checked against the
    /// projections when registered). A later decoded table that differs is a
    /// contradiction, exactly as for [`Self::payload_tables`].
    pub(crate) derived_tables: HashSet<Name>,
    /// Some module of this closure was loaded with its definitions left to a
    /// lazy `ConstantSource` ([`super::ImportKinds::InductiveFamiliesOnly`]),
    /// so a projection absent from the environment is not evidence that the
    /// artifact lacks it.
    pub(crate) lazy_definitions: bool,
}

/// Record that a module of this closure is being loaded under `kinds`.
fn note_import_kinds(env: &mut Environment, kinds: super::ImportKinds) {
    if matches!(kinds, super::ImportKinds::InductiveFamiliesOnly) {
        env.get_ext_state_mut::<StructureExtPending>(structure_ext_pending_idx())
            .lazy_definitions = true;
    }
}

pub(super) fn lazy_definitions(env: &mut Environment) -> bool {
    env.get_ext_state_mut::<StructureExtPending>(structure_ext_pending_idx())
        .lazy_definitions
}

impl PersistentExtState for StructureExtPending {
    type Entry = PendingStructureMeta;

    fn add_entry(&mut self, entry: &Self::Entry) {
        self.pending.push(entry.clone());
    }

    fn export_entries(&self) -> Vec<EnvExtensionEntry> {
        Vec::new()
    }
}

static STRUCTURE_EXT_PENDING_IDX: std::sync::OnceLock<ExtensionIdx> = std::sync::OnceLock::new();

fn structure_ext_pending_idx() -> ExtensionIdx {
    *STRUCTURE_EXT_PENDING_IDX.get_or_init(|| {
        register_persistent_ext::<StructureExtPending>(Name::from_string(
            "Clean.olean.structureExtPending",
        ))
    })
}

/// Try to register one decoded structure's metadata; `Ok(false)` when its
/// inductive is not (yet) in the environment, and
/// [`ImportError::InconsistentStructureTable`] when its field table
/// contradicts the environment's projections (the payload leg's rule).
fn try_register_structure_meta(
    env: &mut Environment,
    meta: &PendingStructureMeta,
    closure_end: bool,
) -> Result<bool, ImportError> {
    if env.get_inductive(&meta.struct_name).is_none() {
        return Ok(false);
    }
    let lazy = lazy_definitions(env);
    if env.get_structure_field_names(&meta.struct_name).is_some() {
        tracing::debug!(
            structure = %meta.struct_name,
            "structureExt: field table already present (projection-derived or earlier load); decoded table not applied"
        );
        // A table an artifact registered — a Clean payload's, a decoded
        // one, or one recovered from the projections — and a decoded
        // `structureExt` table that disagree: one of them was rewritten, and
        // nothing says which. Round 28: a decoded table parked until the
        // closure end met the table the projection pass had registered
        // meanwhile and was dropped silently, where `e3f696689` refused it.
        // (A table the kernel's native prelude registered is not compared;
        // see `StructureExtPending::payload_tables`.)
        let from_payload = {
            let state = env.get_ext_state_mut::<StructureExtPending>(structure_ext_pending_idx());
            state.payload_tables.contains(&meta.struct_name)
                || state.derived_tables.contains(&meta.struct_name)
        };
        let present = env
            .get_structure_field_names(&meta.struct_name)
            .unwrap_or_default();
        let differs = present != meta.field_names.as_slice();
        // A table that differs from one registered by the checker's own
        // prelude or by source elaboration is not applied, so what it says
        // is not believed; it is still refused when the artifact's own
        // projections compute other fields than it names (the round-27 rule,
        // kept: `e3f696689` refused a Lean-built `W.olean` whose decoded
        // table was reversed while `W.P` already had its source's table).
        // A count or constructor mismatch alone is version skew with the
        // native prelude (`String`, `Array` under v4.30) and is not refused.
        if differs && !from_payload {
            if let Some(fault) = structure_table_contradiction(
                env,
                &meta.struct_name,
                &meta.field_names,
                &meta.field_proj_fns,
                lazy,
            ) {
                if matches!(fault, TableFault::Computes(_) | TableFault::Resource(_)) {
                    return Err(fault.into_import_error(&meta.struct_name));
                }
            }
        }
        if from_payload && differs {
            return Err(ImportError::InconsistentStructureTable {
                structure: meta.struct_name.to_string(),
                reason: format!(
                    "the decoded `structureExt` table {:?} differs from the table already \
                     registered {:?}",
                    meta.field_names
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>(),
                    present.iter().map(ToString::to_string).collect::<Vec<_>>()
                ),
            });
        }
    }
    if env.get_structure_field_names(&meta.struct_name).is_none() {
        // Same rule as the payload leg (`load_clean_payload`): a decoded
        // table is registered only when it is the one the closure's own
        // projections define. (A decoded table for a structure that already
        // has one is not applied, so it is only compared, above.)
        match structure_table_contradiction(
            env,
            &meta.struct_name,
            &meta.field_names,
            &meta.field_proj_fns,
            lazy,
        ) {
            None => {}
            // Not loaded YET (a private projection lives in the module's
            // `.olean.private`, loaded after it): parked, and decided at the
            // end of the closure, where absent means absent.
            Some(TableFault::Absent(_)) if !closure_end => return Ok(false),
            Some(fault) => {
                return Err(fault.into_import_error(&meta.struct_name));
            }
        }
        // The kernel validates the count against the constructor and rejects
        // duplicates; a rejected table is simply absent, exactly as before
        // this pass, never mis-registered — but LOUDLY, because a structure
        // whose `fieldNames` disagree with its own constructor is a loader
        // defect (a field dropped or fused), not a property of the olean.
        if let Err(e) =
            env.register_structure_fields(meta.struct_name.clone(), meta.field_names.clone())
        {
            tracing::warn!(
                structure = %meta.struct_name,
                error = %e,
                "structureExt field table rejected by the kernel"
            );
        }
        if env.get_structure_field_names(&meta.struct_name).is_some() {
            env.get_ext_state_mut::<StructureExtPending>(structure_ext_pending_idx())
                .derived_tables
                .insert(meta.struct_name.clone());
        }
    }
    if env.get_structure_parents(&meta.struct_name).is_none() {
        env.register_structure_parents(meta.struct_name.clone(), meta.parents.clone());
    }
    Ok(true)
}

/// Retry every parked [`PendingStructureMeta`] now that the import closure is
/// materialized. Called once per closure load, before the projection-derived
/// recovery, so a decoded table wins over a recovered one. An entry whose
/// structure is still absent describes a structure this load never brought
/// in and is dropped.
pub(crate) fn flush_pending_structure_metadata(env: &mut Environment) -> Result<(), ImportError> {
    let idx = structure_ext_pending_idx();
    let pending = std::mem::take(&mut env.get_ext_state_mut::<StructureExtPending>(idx).pending);
    if pending.is_empty() {
        return Ok(());
    }
    let mut applied = 0usize;
    let mut absent = 0usize;
    for meta in &pending {
        if try_register_structure_meta(env, meta, true)? {
            applied += 1;
        } else {
            absent += 1;
        }
    }
    tracing::info!(
        applied,
        absent,
        "structureExt: flushed parked structure metadata at closure end"
    );
    Ok(())
}

/// Register imported structures' field tables and `extends` parents from the
/// DECODED `Lean.structureExt` entries of this module.
///
/// This is the metadata Lean's own structure-instance elaborator reads
/// (`Lean/Structure.lean`: `getStructureFields`, `getStructureParentInfo`,
/// `findField?`) and that an imported structure NEVER had in Clean: with no
/// field table, `struct_field_index` fell back to decompiling the projection
/// constant `S.<field>` (absent for an inherited field, so `le := …` on a
/// `LinearOrder` was `Unknown structure field`), and with no parents
/// `rewrite_parent_subobject_construction` returned `None` for every import.
/// Measured 2026-09-10 on `Mathlib/Order/Basic.lean`: `Pi.preorder`,
/// `Prod.instPreorder`, `LinearOrder.ofSubsingleton`,
/// `Function.Injective.preorder` and their downstream all stopped here.
///
/// Faithful, never fabricated: only a structure whose inductive is loaded is
/// touched; the field table is the entry's own `fieldNames` and the kernel
/// still refuses a list whose length differs from the constructor's field
/// count; a parent is recorded only when Lean marks it `subobject` (a diamond
/// resolved by copying has its fields flattened into the child, which the
/// field table already reflects). The `toParent` slot name is the last
/// component of the parent's projection function, which is how Lean names it.
/// SOUNDNESS: search/elaboration metadata only; every term built from it is
/// kernel-re-checked.
fn register_structures_from_extension(
    env: &mut Environment,
    extensions: &[TypedExtension],
) -> Result<(), ImportError> {
    let decoded: Vec<PendingStructureMeta> = extensions
        .iter()
        .filter(|ext| crate::module::is_structure_extension_name(&ext.extension_name.to_string()))
        .flat_map(|ext| ext.entries.iter())
        .filter_map(|entry| match entry {
            TypedExtensionEntry::Structure(s) => {
                let parents = s
                    .parents
                    .iter()
                    .filter(|p| p.subobject)
                    .filter_map(|p| {
                        let to_field = p.proj_fn.last_component()?;
                        Some((Name::from_string(&to_field), p.struct_name.clone()))
                    })
                    .collect();
                Some(PendingStructureMeta {
                    struct_name: s.struct_name.clone(),
                    field_names: s.field_names.clone(),
                    field_proj_fns: s.field_proj_fns.clone(),
                    parents,
                })
            }
            _ => None,
        })
        .collect();
    let idx = structure_ext_pending_idx();
    for meta in decoded {
        // Register now when the structure is already present (the eager
        // path); otherwise park it for `flush_pending_structure_metadata`
        // at the end of the closure (the zero-copy path serves this module's
        // own inductives lazily — see `PendingStructureMeta`).
        if !try_register_structure_meta(env, &meta, false)? {
            env.get_ext_state_mut::<StructureExtPending>(idx)
                .pending
                .push(meta);
        }
    }
    Ok(())
}

/// Recover structure field-name metadata for single-constructor structures /
/// classes from their already-loaded PROJECTION FUNCTIONS.
///
/// HISTORY: until 2026-09-10 this was the ONLY source of an imported
/// structure's field table — Lean's `structureExt` was not decoded — so an
/// imported structure/class (`Monoid`, `MulOneClass`, `Semigroup`, …) landed
/// in the kernel with NO field-name table
/// ([`Environment::get_structure_field_names`] → `None`) unless every one of
/// its direct projections was visible here, and the consumer of that table —
/// clean-auto's typeclass-projection law lane
/// (`collect_instance_projection_laws`, guarded on `field_names.is_some()`) —
/// skipped every imported class. The decoded extension
/// ([`register_structures_from_extension`] + [`flush_pending_structure_metadata`])
/// now supplies the table AND the `extends` parents straight from Lean's own
/// `fieldNames`/`parentInfo`; this pass remains as the fallback for a
/// structure whose entry did not decode, and is idempotent over the decoded
/// ones (it skips a structure that already has a table).
///
/// The field names are recovered FAITHFULLY, never fabricated. For a structure
/// `S`, Lean emits exactly one projection constant per direct field, named
/// `S.<field>`, whose value is `fun params (self : S ..) => self.<i>` — i.e.
/// `λ*. Proj(S, i, _)`. We scan the loaded constants, and for every constant
/// whose value has that shape AND whose name is literally `S.<field>` (prefix ==
/// the projected structure — this rejects any unrelated helper that merely
/// projects `S`), record `(i, <field>)`. When the recovered indices form a
/// contiguous `0..k` set we register them, in `Proj`-index order, via
/// [`Environment::register_structure_fields`].
///
/// SOUNDNESS: the field table is SEARCH metadata, never part of the TCB.
/// `register_structure_fields` independently rejects any list whose length ≠ the
/// constructor's field count (and any duplicate name), so an incomplete set (a
/// projection served lazily, say) is skipped rather than mis-registered. Field
/// names are read verbatim from real projection constants, and their order is
/// the authoritative `Proj` index, so `Expr::proj(S, i, inst)` selects the
/// intended field. Even a hypothetically wrong table only mis-guides the search
/// lane; the kernel re-check (`infer_type` + `is_def_eq`) it feeds remains the
/// sole soundness gate, so no unsound proof can be admitted.
pub(crate) fn register_structure_fields_from_projections(env: &mut Environment) {
    // struct_name -> (proj_index -> field_name). Owned so the immutable
    // `constants()` borrow is released before the mutable registration pass.
    let mut fields_by_struct: HashMap<Name, HashMap<u32, Name>> = HashMap::new();
    for c in env.constants() {
        // Field projections carry a `λ*. Proj(S, i, _)` body. DATA-field
        // projections (`Monoid.toSemigroup`, `Mul.mul`) are emitted as
        // `Definition`s; PROP-field projections (`Monoid.mul_one`,
        // `Semigroup.mul_assoc`, `MulOneClass.one_mul`, … — the class *axioms*)
        // are emitted as `Theorem`s but carry the SAME projection body. BOTH
        // kinds must be scanned: real Mathlib `Monoid` has 4 of its 7 fields as
        // Theorem-kind law projections (indices 2/3/5/6), so scanning
        // `Definition`s alone recovers only the data fields {0,1,4} — a
        // non-contiguous set that the `0..k` check below rejects, leaving the
        // whole class with NO field table (the exact gap this pass closes).
        // `Axiom`/`Opaque` never carry a value, so they are excluded by the
        // `c.value` check just below regardless.
        if !matches!(
            c.kind,
            clean_kernel::env::ConstantKind::Definition | clean_kernel::env::ConstantKind::Theorem
        ) {
            continue;
        }
        let Some(value) = c.value.as_ref() else {
            continue;
        };
        let Some((struct_name, idx)) = projection_fn_target(value) else {
            continue;
        };
        let field = match c.name.inner() {
            clean_kernel::name::NameInner::Str(parent, component) if **parent == struct_name => {
                Name::anon().str(component.as_ref())
            }
            clean_kernel::name::NameInner::Num(parent, component) if **parent == struct_name => {
                Name::anon().num(*component)
            }
            _ => continue,
        };
        // Keep only the CANONICAL projection `S.<field>` (prefix == projected
        // structure). This is exactly Lean's projection naming and rules out an
        // unrelated `Foo.bar := fun s => s.i` that happens to project `S`.
        fields_by_struct
            .entry(struct_name)
            .or_default()
            .insert(idx, field);
    }

    // Second pass: pick the single-constructor inductives whose recovered
    // projections form a contiguous `0..k` set and are not already registered.
    let mut to_register: Vec<(Name, Vec<Name>)> = Vec::new();
    for (struct_name, idx_map) in fields_by_struct {
        if env.get_structure_field_names(&struct_name).is_some() {
            continue; // kernel-native structure or an earlier load already did it
        }
        let Some(ind) = env.get_inductive(&struct_name) else {
            continue;
        };
        if ind.constructor_names.len() != 1 {
            continue; // structures are single-constructor inductives
        }
        // Require every index in `0..k` so the vector position == the Proj index.
        // A gap means a projection was not recovered; skip rather than mis-order.
        let Ok(k) = u32::try_from(idx_map.len()) else {
            continue;
        };
        let mut ordered = Vec::with_capacity(idx_map.len());
        let mut contiguous = true;
        for i in 0..k {
            match idx_map.get(&i) {
                Some(name) => ordered.push(name.clone()),
                None => {
                    contiguous = false;
                    break;
                }
            }
        }
        if contiguous {
            to_register.push((struct_name, ordered));
        }
    }

    // Final pass: register. A table recovered from projection BODY SHAPES is
    // only a nomination (`λ s. Proj(S, 0, S.mk s.1 s.0)` has the shape of
    // field 0 and computes field 1): it is registered only when every
    // projection computes the field it names. A table that does not is left
    // out — there is no table here to contradict, only none to believe.
    // `register_structure_fields` re-validates count == constructor field
    // count and uniqueness; on mismatch it errors and we skip.
    let lazy = lazy_definitions(env);
    for (struct_name, fields) in to_register {
        register_recovered_structure_table(env, struct_name, fields, lazy);
    }
}

/// The final decision on ONE projection-recovered field table, shared by the
/// whole-environment scan above and the per-module incremental scan
/// (`projection_scan::register_touched_structure_fields`), so the two cannot
/// disagree on what is believed: a table is registered only when
/// [`structure_table_contradiction`] finds nothing, and a registered table is
/// recorded as derived. Returns whether it was registered.
pub(super) fn register_recovered_structure_table(
    env: &mut Environment,
    struct_name: Name,
    fields: Vec<Name>,
    lazy: bool,
) -> bool {
    if let Some(fault) = structure_table_contradiction(env, &struct_name, &fields, &[], lazy) {
        tracing::warn!(
            structure = %struct_name,
            reason = %fault,
            "projection-recovered structure field table not registered"
        );
        return false;
    }
    if env
        .register_structure_fields(struct_name.clone(), fields)
        .is_ok()
    {
        env.get_ext_state_mut::<StructureExtPending>(structure_ext_pending_idx())
            .derived_tables
            .insert(struct_name);
        return true;
    }
    false
}

/// Load a parsed module into the environment.
///
/// Uses two-pass loading to ensure inductives are registered before recursors.
/// This is necessary because recursors need to look up inductive info to correctly
/// determine which constructor fields are recursive.
///
/// # REQUIRES
/// - `env` is a valid Environment
/// - `module` is a successfully parsed `ParsedModule`
///
/// # ENSURES
/// - Constants are loaded in order: inductives -> constructors -> recursors -> others
/// - Duplicates (constants already in env) are counted but not overwritten
/// - `summary.added_constants + summary.duplicate_constants` equals total valid constants
/// - Skipped constants are recorded with their failure reason
///
/// # Lean world
///
/// A `ParsedModule` carries no header, so this family never checks which
/// Lean world wrote the part (docs/DECISIONS.md R81): a caller admits every
/// part it parsed into a [`crate::LeanWorldScope`] first.
pub fn load_parsed_module(
    env: &mut Environment,
    module: &ParsedModule,
    module_name: Option<String>,
) -> Result<LoadSummary, ImportError> {
    load_parsed_module_with_import_policy(env, module, module_name, OleanImportPolicy::default())
}

/// Load a parsed module using an explicit persistent-extension module index.
///
/// `persistent_extension_module_idx` is part of the caller's deterministic
/// module ordering. It must be unique for every distinct parsed module (or
/// module part) loaded into `env`. Replaying the same module at the same index
/// is idempotent. Callers loading more than one module should prefer this API:
/// the compatibility [`load_parsed_module`] API derives its index from the
/// module's direct-import count, which is not a unique module identity.
pub fn load_parsed_module_at_index(
    env: &mut Environment,
    module: &ParsedModule,
    module_name: Option<String>,
    persistent_extension_module_idx: usize,
) -> Result<LoadSummary, ImportError> {
    load_parsed_module_at_index_with_import_policy(
        env,
        module,
        module_name,
        persistent_extension_module_idx,
        OleanImportPolicy::default(),
    )
}

/// Load a parsed module into the environment using an explicit import policy.
///
/// Strict policies are enforced before payload or constant registration, so a
/// rejected unpinned module leaves the environment unchanged by this loader.
pub fn load_parsed_module_with_import_policy(
    env: &mut Environment,
    module: &ParsedModule,
    module_name: Option<String>,
    policy: OleanImportPolicy,
) -> Result<LoadSummary, ImportError> {
    let mut intern_cache = ExprInternCache::default();
    load_parsed_module_with_cache_and_policy(env, module, module_name, &mut intern_cache, policy)
}

/// Load a parsed module using an explicit persistent-extension module index
/// and import policy.
///
/// The index has the same uniqueness and replay requirements as
/// [`load_parsed_module_at_index`]. Import policy validation runs before any
/// environment mutation.
pub fn load_parsed_module_at_index_with_import_policy(
    env: &mut Environment,
    module: &ParsedModule,
    module_name: Option<String>,
    persistent_extension_module_idx: usize,
    policy: OleanImportPolicy,
) -> Result<LoadSummary, ImportError> {
    let mut intern_cache = ExprInternCache::default();
    load_parsed_module_with_cache_and_policy_at_index(
        env,
        module,
        module_name,
        &mut intern_cache,
        policy,
        persistent_extension_module_idx,
    )
}

/// Internal: load a parsed module using an externally-owned intern cache.
///
/// When the cache already contains entries from prior modules, expressions
/// shared across modules (e.g. `Nat`, `Prop`, `BVar(0)`) are deduplicated
/// across the entire dependency graph, not just within a single module (#2383).
pub(super) fn load_parsed_module_with_cache_and_policy(
    env: &mut Environment,
    module: &ParsedModule,
    module_name: Option<String>,
    intern_cache: &mut ExprInternCache,
    policy: OleanImportPolicy,
) -> Result<LoadSummary, ImportError> {
    // Compatibility path: historical callers used direct-import count as the
    // persistent-extension slot. Multi-module callers that need collision-free
    // slots use `load_parsed_module_at_index[_with_import_policy]` instead.
    let persistent_extension_module_idx = module.imports.len();
    load_parsed_module_with_cache_and_policy_at_index(
        env,
        module,
        module_name,
        intern_cache,
        policy,
        persistent_extension_module_idx,
    )
}

fn load_parsed_module_with_cache_and_policy_at_index(
    env: &mut Environment,
    module: &ParsedModule,
    module_name: Option<String>,
    intern_cache: &mut ExprInternCache,
    policy: OleanImportPolicy,
    persistent_extension_module_idx: usize,
) -> Result<LoadSummary, ImportError> {
    super::clean_payload_requirement::check_parsed_module(env, module, module_name.as_deref())?;
    policy.check_parsed_module(module, module_name.as_deref())?;
    // This compatibility API has display-only Lean record names. Do not let
    // a quoted/numeric payload identity miss ownership checks through reparsing.
    if let Some(payload) = module.clean_payload.as_ref() {
        if let Some(name) = payload
            .declared_names::<Vec<Name>>()
            .into_iter()
            .find(|name| Name::from_string(&name.to_string()) != *name)
        {
            return Err(ImportError::LossyParsedPayloadName {
                name: name.to_string(),
                identity: name,
            });
        }
    }
    super::projection_scan::begin_module(env);
    note_import_kinds(env, policy.import_kinds());
    // One artifact per parsed module (this path loads no companion parts).
    let artifact = module_name.clone();
    super::artifact_ledger::bind_part(env, &module_name, &artifact)?;
    // Rule 4 for the tables Clean reads. This path loads the parts a caller
    // hands it, one call each, in level order (`parse_module_parts`), and
    // takes every part's entries; it holds them to Lean's cumulative levels,
    // so the last part — the one a consumer that is not a `module` reads —
    // states every entry any part states.
    let extension_rows = legacy_display_extension_projection(&module.entries);
    super::artifact_ledger::check_part_entries(env, &artifact, true, &extension_rows)?;
    // One name, one declaration — for the Lean-built records too, checked
    // before anything of the module is registered (round 29: N2r, N3, N3p).
    // A record the module's own Clean payload also declares is shadowed by
    // the payload's (loaded first; the payload leg compares it): the
    // Lean-format record Clean writes beside its payload is not what loads,
    // and is not always the same term (measured: `K1Lib.t : 1 = 1` read back
    // from it as `0 = 0`).
    let payload_names: HashSet<Name> = module
        .clean_payload
        .as_ref()
        .map(CleanPayload::declared_names)
        .unwrap_or_default();
    let others = super::artifact_ledger::check_lean_records(
        env,
        module
            .constants
            .iter()
            .enumerate()
            .filter(|(_, c)| !c.name.is_empty())
            .map(|(i, c)| (i, Name::interned(&c.name)))
            .filter(|(_, n)| !payload_names.contains(n)),
        &artifact,
    )?;
    refuse_other_declarations(env, policy, others, |i| {
        let c = &module.constants[i];
        (
            Name::interned(&c.name),
            convert_parsed_constant(c, intern_cache, policy.proof_elision()),
        )
    })?;
    let olean_origin = ConstantOrigin::olean_import(module_name.clone());
    let payload_origin = ConstantOrigin::clean_payload(module_name.clone());

    let mut summary = LoadSummary {
        module_name,
        imports: module
            .imports
            .iter()
            .map(|i| i.module_name.clone())
            .collect(),
        ..LoadSummary::empty()
    };

    if let Some(owner) = summary.module_name.as_deref() {
        clean_kernel::env::csimp::record_imported_module(
            env,
            Name::from_string(owner),
            summary
                .imports
                .iter()
                .map(|import| Name::from_string(import))
                .collect(),
        );
    }

    let payload_const_count = module
        .clean_payload
        .as_ref()
        .map_or(0, CleanPayload::total_constants);

    let constant_count = module.constants.len();
    env.reserve_capacity(constant_count + payload_const_count);

    // Load clean payload definitions first if present.
    if let Some(payload) = module.clean_payload.as_ref() {
        let (added, duplicates, rejected) = load_clean_payload(
            env,
            payload,
            Some(&payload_origin),
            &artifact,
            &mut summary.added_names,
            policy.import_kinds(),
        )?;
        summary.added_constants += added;
        summary.duplicate_constants += duplicates;
        summary.skipped_constants.extend(rejected);
    }

    install_kernel_quotients(
        env,
        module
            .constants
            .iter()
            .any(|c| matches!(c.kind, ConstantKind::Quot)),
        &mut summary.added_names,
    );
    let mut duplicate_filtered = 0usize;
    let mut cstage_skipped: Vec<SkippedConstant> = Vec::new();
    let mut cstage_not_replayable: Vec<String> = Vec::new();
    let mut upgrade_indices: Vec<usize> = Vec::new();
    let mut discharge_stub_names: Vec<Name> = Vec::new();
    let mut same_artifact_indices: Vec<usize> = Vec::new();
    let mut shadowed: Vec<ShadowedAt> = Vec::new();
    let summary_module = summary.module_name.clone();
    let mut stored_declarations = super::StoredDeclarationPart {
        artifact: artifact.clone(),
        part: summary.module_name.clone(),
        declarations: payload_declarations(module.clean_payload.as_ref()),
        pending_restatements: Vec::new(),
        certified_restatements: Vec::new(),
        completed_theorems: Vec::new(),
    };
    let constants: Vec<_> = module
        .constants
        .iter()
        .enumerate()
        .filter(|(_i, c)| !c.name.is_empty() || c.type_.is_some())
        .filter(|(_i, c)| {
            // Spelling alone cannot remove a safe kernel ConstantInfo.
            if !payload_names.contains(&Name::interned(&c.name))
                && is_nonreplayable_compiler_constant(c)
            {
                cstage_not_replayable.push(c.name.clone());
                cstage_skipped.push(SkippedConstant {
                    name: c.name.clone(),
                    reason: "compiler/code-generator artifact (not kernel-checkable)".to_string(),
                });
                return false;
            }
            true
        })
        // Capture at the existing logical-declaration boundary, before
        // conversion/duplicate handling. Only independently non-replayable
        // auxiliaries were excluded above.
        .inspect(|(_, c)| {
            let safety = stored_constant_safety(
                &c.kind,
                parsed_constant_safety(c),
                c.inductive_val.is_some(),
                c.constructor_val.is_some(),
                c.recursor_val.is_some(),
            );
            let name = Name::interned(&c.name);
            if !payload_names.contains(&name) {
                stored_declarations.declarations.push((name, safety));
            }
        })
        .filter(|(i, c)| {
            let name = Name::interned(&c.name);
            let exists_as_const = env.get_const(&name);
            let exists_other = env.get_inductive(&name).is_some()
                || env.get_constructor(&name).is_some()
                || env.get_recursor(&name).is_some();
            // Rule 4 of `artifact_ledger`, as on the direct path: this call's
            // module met before under the same name.
            let completes_stub = !exists_other
                && exists_as_const.is_some_and(|e| e.value.is_none())
                && c.value.is_some();
            if (exists_other || exists_as_const.is_some())
                && !completes_stub
                && !payload_names.contains(&name)
                && super::artifact_ledger::declared_by_this_artifact(env, &name, &artifact)
            {
                same_artifact_indices.push(*i);
            }
            let mut note_shadow = |name: &Name| {
                if let Some(held_by) = foreign_resident_provenance(
                    env,
                    name,
                    summary_module.as_deref(),
                    matches!(c.kind, ConstantKind::Quot),
                ) {
                    shadowed.push((*i, name.clone(), held_by));
                }
            };
            // A kernel-only or replay load fills another module's value-less
            // constant only where Lean's import would merge the two, a theorem
            // subsuming a safe axiom (`OleanImportPolicy::confines_stub_upgrade`);
            // anything else is a duplicate. No load fills a quotient primitive:
            // the kernel seeds Lean's canonical quotient, a name no artifact
            // declares, so rule 1 never sees its redeclaration, and a module's
            // `def Quot := fun {α} _ => α` at `Quot`'s own type passed the
            // checked upgrade under the default policy (measured 2026-09-29:
            // `stamp-verified --parallel` stamped `ReplayForgedQuotDef`'s
            // `quot_def_false : False`; `leanchecker`: already declared 'Quot').
            let upgradable = |name: &Name, resident: &clean_kernel::env::ConstantInfo| {
                env.get_quot(name).is_none()
                    && (!policy.confines_stub_upgrade()
                        || foreign_resident_provenance(env, name, summary_module.as_deref(), false)
                            .is_none()
                        || (matches!(c.kind, ConstantKind::Theorem)
                            && resident.kind == KernelConstantKind::Axiom
                            && !env.is_unsafe(name)))
            };
            if exists_other {
                note_shadow(&name);
                duplicate_filtered += 1;
                return false;
            }
            if let Some(existing) = exists_as_const {
                // Faithful carrier import: the genuine Lean class (an `Inductive`)
                // collides with a prelude `Axiom` carrier stub (e.g. `Membership`).
                // Discharge the opaque stub and let the real inductive register
                // through the checked path so it stops being counted as a phantom
                // domain axiom. SOUNDNESS: see
                // `Environment::discharge_axiom_stub_for_inductive_import`.
                if matches!(c.kind, ConstantKind::Inductive)
                    && existing.value.is_none()
                    && is_axiom_carrier_stub(env, &name, existing, &artifact)
                {
                    discharge_stub_names.push(name);
                    return true;
                }
                // Axiom upgrade: .olean.private provides value for base .olean's
                // axiom stub (Lean 4.29+ module system). Part of #3134.
                if existing.value.is_none() && c.value.is_some() && upgradable(&name, existing) {
                    upgrade_indices.push(*i);
                    return false;
                }
                note_shadow(&name);
                duplicate_filtered += 1;
                return false;
            }
            true
        })
        .map(|(_i, c)| c)
        .collect();
    summary.stored_declarations = Some(stored_declarations);
    // Elaborator-side binder-name tables; a kernel-only load reads none.
    if !policy.kernel_only() {
        // See `default_fn_binders`: the same table, off the parsed values.
        record_default_fn_binders_from_parsed(env, &module.constants);
        // See `type_binder_names`: named arguments bind by the type's binder names.
        super::type_binder_names::record_type_binder_names_from_parsed(env, &module.constants);
        // See `value_binder_names`: a local whose type unfolds to a `∀` binds named
        // arguments by the names in the definition's value.
        super::value_binder_names::record_value_binder_names_from_parsed(env, &module.constants);
    }
    let safety_marks: Vec<_> = constants
        .iter()
        .copied()
        .chain(upgrade_indices.iter().map(|&i| &module.constants[i]))
        .filter_map(|c| {
            parsed_constant_safety(c)
                .map(|safety| (Name::interned(&c.name), c.kind.clone(), safety))
        })
        .collect();

    summary.duplicate_constants += duplicate_filtered;
    summary.skipped_constants.extend(cstage_skipped);
    summary.skipped_not_replayable.extend(cstage_not_replayable);
    let (refused_duplicates, restated, pending) = refused_duplicates_parsed(env, module, shadowed);
    if let Some(part) = summary.stored_declarations.as_mut() {
        part.pending_restatements = pending;
    }
    summary.shadowed_declarations.extend(refused_duplicates);
    summary.restated_declarations.extend(restated);

    // Discharge the opaque prelude carrier stubs whose genuine inductive is about
    // to register (collected above). Done here, after the immutable borrow of
    // `env` in the dedup filter has ended.
    discharge_carrier_stubs(env, &discharge_stub_names);

    // Convert constants sequentially with the shared intern cache so that
    // identical sub-expressions across different constants — and across
    // modules when called from recursive loaders — share the same Arc<Expr>
    // allocation (#2383).
    let cache_size_before: u64 = intern_cache.total_entries;
    let inductive_families_only = policy.inductive_families_only();
    // Rule 4 of `artifact_ledger` (see the direct path).
    for &i in &same_artifact_indices {
        let c = &module.constants[i];
        if inductive_families_only && !is_inductive_family_kind(&c.kind) {
            continue;
        }
        let converted = convert_parsed_constant(c, intern_cache, policy.proof_elision());
        let incoming = part_record(&converted, parsed_constant_safety(c));
        super::artifact_ledger::check_same_artifact_record(
            env,
            &artifact,
            &Name::interned(&c.name),
            incoming.as_ref(),
        )?;
    }
    let constants: Vec<_> = constants
        .into_iter()
        // HYBRID (Phase-1 zero-copy): under `InductiveFamiliesOnly` the definitional
        // kinds are served by the lazy `ShardConstantSource`; never build their owned
        // `Arc<Expr>` (the memory win). `convert_parsed_constant` only ever maps these
        // to the `Other` bucket, which `register_converted_constants` already drops, so
        // filtering here removes pure waste — the registered SET is unchanged.
        .filter(|c| !inductive_families_only || is_inductive_family_kind(&c.kind))
        .collect();
    let converted: Vec<ConvertedConstant> = constants
        .iter()
        .map(|c| convert_parsed_constant(c, intern_cache, policy.proof_elision()))
        .collect();
    let records: Vec<_> = constants
        .iter()
        .zip(&converted)
        .filter_map(|(c, cc)| part_record(cc, parsed_constant_safety(c)))
        .collect();
    super::artifact_ledger::remember_part_records(env, &artifact, records);

    // Registration logic shared with the LoadModule direct path.
    register_converted_constants(
        env,
        converted,
        intern_cache,
        &mut summary,
        cache_size_before,
        Some(&olean_origin),
        policy.proof_elision(),
        policy.import_kinds(),
        None,
    );

    // Upgrade axiom stubs with definitions from .olean.private (#3134).
    // HYBRID (Phase-1 zero-copy): the axiom-stub upgrade restores `Definition`
    // VALUES (a definitional kind). Under `InductiveFamiliesOnly` the definitional
    // kinds are served lazily, so eagerly upgrading them here would defeat the
    // memory win and double-register a name the lazy source already covers — skip.
    let mut upgraded_names: Vec<Name> = Vec::new();
    if !upgrade_indices.is_empty() && !policy.inductive_families_only() {
        // #3134 axiom-stub upgrade: CONVERT with NO elision (the conversion itself
        // must produce a real value, never a `Sort 0` placeholder — `convert_*`'s
        // own elision nulls in-place and would leak that placeholder through the
        // upgrade). We then apply the policy elision POST-conversion, on the fully
        // built `ConstantInfo`, exactly mirroring Pass-4 below. This is required
        // for v4.30+ stdlib where most Init bodies (Opaque/Theorem proof values)
        // arrive through `.olean.private` and would otherwise re-inflate here —
        // defeating the preload memory bound. SOUNDNESS is identical to Pass-4:
        // TYPES are retained (the upgraded constant still type-checks references),
        // only the VALUE of a policy-selected kind is dropped, and `OpaqueOnly`
        // remains verdict-preserving (the kernel never δ-unfolds an `Opaque`).
        let upgrade_converted: Vec<ConvertedConstant> = upgrade_indices
            .iter()
            .map(|&i| {
                convert_parsed_constant(&module.constants[i], intern_cache, ProofValueElision::None)
            })
            .collect();
        let mut upgrade_others = Vec::new();
        for cc in upgrade_converted {
            match cc {
                ConvertedConstant::Other(_name, Ok((decl, hints)), _stats) => {
                    let mut info = decl_to_constant_info(decl, hints);
                    // Under R142's invariant the value is checked whole first and
                    // elided after the upgrade installs it (below).
                    if info.value.is_some()
                        && policy.proof_elision().elides(info.kind)
                        && !policy.checks_authoritative_values()
                    {
                        info.value = None;
                    }
                    upgrade_others.push(info);
                }
                ConvertedConstant::Other(name, Err(e), _stats) => {
                    summary.skipped_constants.push(SkippedConstant {
                        name,
                        reason: format!("axiom upgrade failed: {e}"),
                    });
                }
                _ => {} // inductives/constructors/recursors not expected in upgrade path
            }
        }
        // R1-STUB (2026-08-24): the checked tier — the stub must exist, the
        // incoming type must kernel-match the stub's type, and the incoming
        // value must check_type against it (UnknownConst-tolerant, G4). A
        // refused record leaves the stub in place FAIL-CLOSED and is recorded
        // loudly below; nothing ever registers unchecked.
        // Rule 4 at the upgrade too: the completion is the declaration the
        // earlier part's stub stated — the same universe parameters and type,
        // as read — or the parts disagree (round 31: a private part whose
        // record of a public stub stated another type left the stub standing
        // with the public part's type while `lean` reads the private one).
        for info in &upgrade_others {
            super::artifact_ledger::check_stub_completion(env, &artifact, info)?;
        }
        let completing = upgrade_others.clone();
        upgraded_names.extend(upgrade_others.iter().map(|c| c.name.clone()));
        let (upgraded, refused) = upgrade_stubs_to_fixpoint(env, upgrade_others);
        summary.added_constants += upgraded;
        // R142: the values were checked whole; the policy's elision drops the
        // installed ones now, so an eliding re-check load never trusts a stub
        // whose completion it did not check.
        if policy.checks_authoritative_values() {
            let refused_names: HashSet<&Name> = refused.iter().map(|(n, _)| n).collect();
            let installed: Vec<&Name> = completing
                .iter()
                .map(|c| &c.name)
                .filter(|n| !refused_names.contains(n))
                .collect();
            let _ = env.forget_proof_values_for(installed, policy.proof_elision());
        }
        let safety_of: HashMap<Name, Option<DefinitionSafety>> = upgrade_indices
            .iter()
            .map(|&i| {
                let c = &module.constants[i];
                (Name::interned(&c.name), parsed_constant_safety(c))
            })
            .collect();
        remember_completed_stubs(env, &artifact, completing, &refused, &safety_of);
        // An `unsafe`/`partial` value the check refused (Lean's safe context
        // refuses an `unsafe` body's `unsafeCast`) is one Lean's replay never
        // admits either (`LoadSummary::skipped_not_replayable`).
        let unreplayable: HashSet<&str> = upgrade_indices
            .iter()
            .map(|&i| &module.constants[i])
            .filter(|c| stored_unsafe_or_partial(&c.kind, c.definition_safety))
            .map(|c| c.name.as_str())
            .collect();
        record_refused_completions(env, &mut summary, &artifact, refused, &unreplayable, policy)?;
    }

    // Everything this module registered, for the projection-scan index.
    super::projection_scan::note_touched(
        env,
        summary
            .added_names
            .iter()
            .chain(&upgraded_names)
            .chain(&discharge_stub_names),
    );

    apply_declaration_safety_marks(env, safety_marks);
    // Closed over its imports, and no declaration depends on itself (round
    // 29, C1/C4) — decided before anything can unfold what this part added;
    // left to the caller's replay under `OleanImportPolicy::with_replay_refusals`
    // (both), and `with_module_replay_refusals` (the cycle only).
    if policy.refuses_forward_references() {
        let upgraded: Vec<Name> = upgrade_indices
            .iter()
            .map(|&i| Name::interned(&module.constants[i].name))
            .collect();
        super::artifact_ledger::check_part_references(
            env,
            &artifact,
            &summary.added_names,
            &upgraded,
            policy.refuses_definitional_cycles(),
        )?;
    }

    // Extension entries feed the elaborator's tables; a kernel-only load
    // (`OleanImportPolicy::with_kernel_only`) reads none of them.
    if !extension_rows.is_empty() && !policy.kernel_only() {
        summary.extension_accounting = extension_accounting(&extension_rows);
        load_extension_entries(env, persistent_extension_module_idx, &extension_rows)?;
        // Register the DECODED real-Lean type-class declarations (`ClassEntry`)
        // FIRST — before every other class/instance bridge — so classes with no
        // imported instance (e.g. `Membership`) exist at all, and out-param
        // classes carry their REAL `outParams` (`GetElem` ⟶ [2,3]) that the
        // downstream empty-out-param registrations must not clobber
        // (first-writer-wins; #olean-env-ext-restore lane-B increment 2).
        summary
            .class_out_param_mismatches
            .extend(register_real_class_entries(env, &extension_rows));
        // Register imported `@[class]` structures/inductives as typeclasses
        // FIRST, before bridging instances: the elaborator's instance synthesis
        // (`init_instances_from_env`) only surfaces instances of *registered*
        // classes, so the target class must exist before its instances are
        // associated with it. Otherwise typeclass resolution fails for every
        // imported class (e.g. Group/Semiring) (#olean-class-before-instance-order).
        register_classes_from_extension(env);
        // Register the DECODED real-Lean `@[instance]` entries with their real
        // priorities BEFORE the persistent-state bridge below, so decoded
        // source registrations supply the real priority
        // (#olean-env-ext-restore).
        register_real_instance_entries(env, &extension_rows);
        // Recover structure/class field-name tables from the loaded projection
        // functions for any structure whose `structureExt` entry did not
        // decode (#olean-structure-field-names); the decoded entries above
        // win first.
        // Register the DECODED real-Lean `Lean.structureExt` entries FIRST:
        // the field-name table straight from Lean's own `fieldNames`, and the
        // `extends` parents (subobject `toParent` slots) that an imported
        // structure never had before — the metadata the structure-instance
        // elaborator needs to route `le := …` on a `LinearOrder` into
        // `toPartialOrder`. The projection-derived pass below is kept as the
        // fallback for a structure whose entry did not decode.
        register_structures_from_extension(env, &extension_rows)?;
        // The whole-environment `register_structure_fields_from_projections`,
        // proportional to what this module touched (see `projection_scan`).
        super::projection_scan::register_touched_structure_fields(env);
        // Re-register imported typeclass instances into the kernel registry so
        // the elaborator's instance synthesis can see them (#instance-import).
        // Only explicitly persisted registrations are candidates. No global
        // definition-type scan may manufacture missing metadata.
        register_instances_from_extension(env);
        // Register the DECODED real-Lean `@[simp]` entries
        // (`Lean.Meta.simpExtension`) into the kernel simp registry, counting
        // origins whose constant is absent LOUDLY in the summary (RC-B/T10).
        for (extension, counts) in extension_rows.iter().zip(&mut summary.extension_accounting) {
            counts.unresolved_targets =
                register_real_simp_entries(env, std::slice::from_ref(extension));
            counts.unresolved_targets += register_real_matcher_entries(
                env,
                summary.module_name.as_deref(),
                std::slice::from_ref(extension),
            )?;
        }
        // The legacy projection carries display-string rows only, never a
        // typed compiler-attribute row; a binding it did register could not
        // be judged, so it is recorded as late (`late_binding`).
        let mut registered = Vec::new();
        for (extension, counts) in extension_rows.iter().zip(&mut summary.extension_accounting) {
            counts.unresolved_targets +=
                register_real_alias_entries(env, std::slice::from_ref(extension));
            counts.unresolved_targets += register_real_compiler_attr_entries(
                env,
                summary.module_name.as_deref(),
                std::slice::from_ref(extension),
                &super::late_binding::CompilerNames::unknown(),
                &mut registered,
            )?;
        }
        env.record_compiled_before(
            registered
                .into_iter()
                .map(|(decl, _)| {
                    (
                        decl.clone(),
                        clean_kernel::env::CompiledBefore {
                            rebound: decl.clone(),
                            via: decl,
                        },
                    )
                })
                .collect(),
        );
        finish_extension_accounting(&mut summary)?;
        // Re-register imported `@[simp]` lemmas into the kernel registry so the
        // simp tactic can use them (#simp-import).
        register_simp_lemmas_from_extension(env);
        // Materialize imported reducibility attributes (`@[reducible]`,
        // `@[irreducible]`, `@[semireducible]`) into the kernel's per-constant
        // reducibility state so delta-reduction transparency is faithful
        // (#attr-import).
        register_attributes_from_extension(env);
    }

    super::projection_scan::end_module(env);
    Ok(summary)
}

/// One PART of the module `artifact` (see [`load_module_part_direct`]).
#[cfg(test)]
pub(crate) fn load_part_direct_with_cache(
    env: &mut Environment,
    module: &LoadModule,
    label: Option<String>,
    artifact: Option<String>,
    intern_cache: &mut ExprInternCache,
) -> Result<LoadSummary, ImportError> {
    load_module_part_direct(
        env,
        module,
        label,
        artifact,
        intern_cache,
        OleanImportPolicy::default(),
        PartEntries::Read,
        None,
        &ArtifactRecordRoles::from_parts(module, &[module]),
    )
}

/// Load a `LoadModule` into the environment using direct binary-to-Expr conversion (#2428).
///
/// This is the fast path: expressions are converted directly from binary data
/// to kernel `Expr` without materializing intermediate `ParsedExpr` trees.
#[cfg(test)]
pub(crate) fn load_module_direct_with_cache(
    env: &mut Environment,
    module: &LoadModule,
    module_name: Option<String>,
    intern_cache: &mut ExprInternCache,
) -> Result<LoadSummary, ImportError> {
    load_module_direct_with_cache_and_policy(
        env,
        module,
        module_name,
        intern_cache,
        OleanImportPolicy::default(),
    )
}

pub(crate) fn load_module_direct_with_cache_and_policy(
    env: &mut Environment,
    module: &LoadModule,
    module_name: Option<String>,
    intern_cache: &mut ExprInternCache,
    policy: OleanImportPolicy,
) -> Result<LoadSummary, ImportError> {
    let artifact = module_name.clone();
    load_module_part_direct(
        env,
        module,
        module_name,
        artifact,
        intern_cache,
        policy,
        PartEntries::Read,
        None,
        &ArtifactRecordRoles::from_parts(module, &[module]),
    )
}

/// Whether a part's elaborator tables are the ones its artifact is read
/// through (see [`load_module_part_direct`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PartEntries {
    /// The part a consumer that is not a `module` reads: its entries are
    /// registered.
    Read,
    /// Another part: its entries are compared with the read part's (rule 4
    /// of `artifact_ledger`) and counted, never registered.
    Compared,
}

/// [`load_module_direct_with_cache_and_policy`] for one PART of the module
/// `artifact`: its `.olean`, or a `.olean.server` / `.olean.private`
/// companion loaded under the label `module_name`. `entries` says whether
/// this part's elaborator tables are the ones the artifact is read through
/// (registered) or another part's (compared, not registered): `lean`
/// imports a module-system artifact's `.olean.private` entries into a
/// consumer that is not a `module`, and nothing of its other parts
/// (`Environment.lean`, `finalizeImport`: `setImportedEntries` over
/// `mainModule?`).
#[allow(clippy::too_many_arguments)]
pub(crate) fn load_module_part_direct(
    env: &mut Environment,
    module: &LoadModule,
    module_name: Option<String>,
    artifact: super::artifact_ledger::ArtifactKey,
    intern_cache: &mut ExprInternCache,
    policy: OleanImportPolicy,
    entries: PartEntries,
    deferred: Option<(&mut DeferredRecursors, usize)>,
    record_roles: &ArtifactRecordRoles,
) -> Result<LoadSummary, ImportError> {
    // One environment, one Lean world (R38, R81): every loader of a
    // `LoadModule` registers through here, so a part of a refused or second
    // world stops before anything of it reaches `env`. `load_parsed_module*`
    // does not (a `ParsedModule` has no header); its callers hold a
    // `LeanWorldScope` over the parts they parsed.
    super::clean_payload_requirement::check_load_module(env, module, module_name.as_deref())?;
    super::world_gate::admit_part(env, module_name.as_deref(), &module.bytes)?;
    policy.check_load_module(module, module_name.as_deref())?;
    super::projection_scan::begin_module(env);
    note_import_kinds(env, policy.import_kinds());
    super::artifact_ledger::bind_part(env, &module_name, &artifact)?;
    // One name, one declaration — for the Lean-built records too, checked
    // before anything of the part is registered (round 29: N2r, N3, N3p).
    // A record the module's own Clean payload also declares is shadowed by
    // the payload's (loaded first; the payload leg compares it): the
    // Lean-format record Clean writes beside its payload is not what loads,
    // and is not always the same term (measured: `K1Lib.t : 1 = 1` read back
    // from it as `0 = 0`).
    let payload_names: HashSet<Name> = module
        .clean_payload
        .as_ref()
        .map(CleanPayload::declared_names)
        .unwrap_or_default();
    let others = super::artifact_ledger::check_lean_records(
        env,
        module
            .constants
            .iter()
            .enumerate()
            .map(|(i, c)| (i, c.kernel_name.clone()))
            .filter(|(_, n)| !payload_names.contains(n)),
        &artifact,
    )?;
    if !others.is_empty() {
        let region = module.region();
        let mut memo = RegionPtrCache::for_region();
        refuse_other_declarations(env, policy, others, |i| {
            let c = &module.constants[i];
            (
                c.kernel_name.clone(),
                convert_load_constant(c, &region, intern_cache, &mut memo, policy.proof_elision()),
            )
        })?;
    }
    let mod_idx = module.imports.len();
    let olean_origin = ConstantOrigin::olean_import(module_name.clone());
    let payload_origin = ConstantOrigin::clean_payload(module_name.clone());

    let mut summary = LoadSummary {
        module_name,
        imports: module
            .imports
            .iter()
            .map(|i| i.module_name.clone())
            .collect(),
        ..LoadSummary::empty()
    };

    if let Some(owner) = summary.module_name.as_deref() {
        clean_kernel::env::csimp::record_imported_module(
            env,
            Name::from_string(owner),
            summary
                .imports
                .iter()
                .map(|import| Name::from_string(import))
                .collect(),
        );
    }

    let payload_const_count = module
        .clean_payload
        .as_ref()
        .map_or(0, CleanPayload::total_constants);

    let constant_count = module.constants.len();
    env.reserve_capacity(constant_count + payload_const_count);

    // Load clean payload definitions first if present.
    if let Some(payload) = module.clean_payload.as_ref() {
        let (added, duplicates, rejected) = load_clean_payload(
            env,
            payload,
            Some(&payload_origin),
            &artifact,
            &mut summary.added_names,
            policy.import_kinds(),
        )?;
        summary.added_constants += added;
        summary.duplicate_constants += duplicates;
        summary.skipped_constants.extend(rejected);
    }

    install_kernel_quotients(
        env,
        module
            .constants
            .iter()
            .any(|c| matches!(c.kind, ConstantKind::Quot)),
        &mut summary.added_names,
    );
    let mut duplicate_filtered = 0usize;
    let mut cstage_skipped: Vec<SkippedConstant> = Vec::new();
    let mut cstage_not_replayable: Vec<String> = Vec::new();
    let mut upgrade_indices: Vec<usize> = Vec::new();
    let mut discharge_stub_names: Vec<Name> = Vec::new();
    let mut same_artifact_indices: Vec<usize> = Vec::new();
    let mut shadowed: Vec<ShadowedAt> = Vec::new();
    let summary_module = summary.module_name.clone();
    let mut stored_declarations = super::StoredDeclarationPart {
        artifact: artifact.clone(),
        part: summary.module_name.clone(),
        declarations: payload_declarations(module.clean_payload.as_ref()),
        pending_restatements: Vec::new(),
        certified_restatements: Vec::new(),
        completed_theorems: Vec::new(),
    };
    let constants: Vec<_> = module
        .constants
        .iter()
        .enumerate()
        .filter(|(_i, c)| !c.name.is_empty() || c.type_ptr != 0)
        .filter(|(_i, c)| {
            // These are kernel ConstantInfos, not the separate IR-only table.
            // Retain safe/unknown-safety records regardless of their names.
            if record_roles.compiler_exclusions.contains(&c.kernel_name) {
                cstage_not_replayable.push(c.name.clone());
                cstage_skipped.push(SkippedConstant {
                    name: c.name.clone(),
                    reason: "compiler/code-generator artifact (not kernel-checkable)".to_string(),
                });
                return false;
            }
            true
        })
        // Capture at the existing logical-declaration boundary, before
        // conversion/duplicate handling. Only independently non-replayable
        // auxiliaries were excluded above.
        .inspect(|(_, c)| {
            let safety = stored_constant_safety(
                &c.kind,
                load_constant_safety(c),
                c.inductive_val.is_some(),
                c.constructor_val.is_some(),
                c.recursor_val.is_some(),
            );
            if !record_roles.payload_names.contains(&c.kernel_name) {
                stored_declarations
                    .declarations
                    .push((c.kernel_name.clone(), safety));
            }
        })
        .filter(|(i, c)| {
            let name = c.kernel_name.clone();
            // Check if this constant already exists in any registration table
            let exists_as_const = env.get_const(&name);
            let exists_other = env.get_inductive(&name).is_some()
                || env.get_constructor(&name).is_some()
                || env.get_recursor(&name).is_some();
            // An earlier part of this very artifact holds the name: this
            // record must say what that part said (rule 4 of
            // `artifact_ledger`), unless it completes that part's value-free
            // stub (the upgrade below, kernel re-checked) — which only a
            // module-system artifact's later part does: `Lean.addDecl` exports
            // a public theorem as an axiom of its type, while every importer
            // reads a non-module artifact's `.olean` alone, so a companion of
            // one completing its stub states another declaration (R131). The
            // names this part's own payload declares are the payload's (see
            // above).
            let own_stub_completable = |name: &Name| {
                module.is_module
                    || !super::artifact_ledger::declared_by_this_artifact(env, name, &artifact)
            };
            let completes_stub = !exists_other
                && exists_as_const.is_some_and(|e| e.value.is_none())
                && c.value_ptr != 0
                && own_stub_completable(&name);
            if (exists_other || exists_as_const.is_some())
                && !completes_stub
                && !payload_names.contains(&name)
                && super::artifact_ledger::declared_by_this_artifact(env, &name, &artifact)
            {
                same_artifact_indices.push(*i);
            }
            let mut note_shadow = |name: &Name| {
                if let Some(held_by) = foreign_resident_provenance(
                    env,
                    name,
                    summary_module.as_deref(),
                    matches!(c.kind, ConstantKind::Quot),
                ) {
                    shadowed.push((*i, name.clone(), held_by));
                }
            };
            // A kernel-only or replay load fills another module's value-less
            // constant only where Lean's import would merge the two, a theorem
            // subsuming a safe axiom (`OleanImportPolicy::confines_stub_upgrade`);
            // anything else is a duplicate. No load fills a quotient primitive:
            // the kernel seeds Lean's canonical quotient, a name no artifact
            // declares, so rule 1 never sees its redeclaration, and a module's
            // `def Quot := fun {α} _ => α` at `Quot`'s own type passed the
            // checked upgrade under the default policy (measured 2026-09-29:
            // `stamp-verified --parallel` stamped `ReplayForgedQuotDef`'s
            // `quot_def_false : False`; `leanchecker`: already declared 'Quot').
            let upgradable = |name: &Name, resident: &clean_kernel::env::ConstantInfo| {
                env.get_quot(name).is_none()
                    && (!policy.confines_stub_upgrade()
                        || foreign_resident_provenance(env, name, summary_module.as_deref(), false)
                            .is_none()
                        || (matches!(c.kind, ConstantKind::Theorem)
                            && resident.kind == KernelConstantKind::Axiom
                            && !env.is_unsafe(name)))
            };
            if exists_other {
                note_shadow(&name);
                duplicate_filtered += 1;
                return false;
            }
            if let Some(existing) = exists_as_const {
                // Faithful carrier import: the genuine Lean class (an `Inductive`)
                // collides with a prelude `Axiom` carrier stub (e.g. `Membership`).
                // Discharge the opaque stub and let the real inductive register.
                // SOUNDNESS: see
                // `Environment::discharge_axiom_stub_for_inductive_import`.
                if matches!(c.kind, ConstantKind::Inductive)
                    && existing.value.is_none()
                    && is_axiom_carrier_stub(env, &name, existing, &artifact)
                {
                    discharge_stub_names.push(name);
                    return true;
                }
                // Axiom upgrade: .olean.private provides value for base .olean's
                // axiom stub (Lean 4.29+ module system). Part of #3134.
                if existing.value.is_none()
                    && c.value_ptr != 0
                    && upgradable(&name, existing)
                    && own_stub_completable(&name)
                {
                    upgrade_indices.push(*i);
                    return false; // handle separately via upgrade path
                }
                note_shadow(&name);
                duplicate_filtered += 1;
                return false;
            }
            true
        })
        .map(|(_i, c)| c)
        .collect();
    summary.stored_declarations = Some(stored_declarations);
    let safety_marks: Vec<_> = constants
        .iter()
        .copied()
        .chain(upgrade_indices.iter().map(|&i| &module.constants[i]))
        .filter_map(|c| {
            load_constant_safety(c).map(|safety| (c.kernel_name.clone(), c.kind.clone(), safety))
        })
        .collect();

    summary.duplicate_constants += duplicate_filtered;
    summary.skipped_constants.extend(cstage_skipped);
    summary.skipped_not_replayable.extend(cstage_not_replayable);
    let (refused_duplicates, restated, pending) = refused_duplicates_loaded(env, module, shadowed);
    if let Some(part) = summary.stored_declarations.as_mut() {
        part.pending_restatements = pending;
    }
    summary.shadowed_declarations.extend(refused_duplicates);
    summary.restated_declarations.extend(restated);

    // Discharge the opaque prelude carrier stubs whose genuine inductive is about
    // to register (collected above), after the immutable borrow of `env` ends.
    discharge_carrier_stubs(env, &discharge_stub_names);

    // Reconstruct the compacted region from the owned bytes
    let region = module.region();

    // Binder NAMES of every `<Struct>.<field>._default` in the module, read
    // off the raw value before the kernel conversion drops them — see
    // `default_fn_binders`. Independent of the import policy's kinds: the
    // value is in the region whether or not the definition is served lazily.
    // A kernel-only load (`OleanImportPolicy::with_kernel_only`) records none
    // of the three elaborator-side binder tables.
    if !policy.kernel_only() {
        record_default_fn_binders_from_region(
            env,
            &region,
            module
                .constants
                .iter()
                .map(|c| (c.name.as_str(), &c.kind, c.value_ptr)),
        )?;
        // Binder NAMES of every constant's TYPE, for named arguments — see
        // `type_binder_names`.
        super::type_binder_names::record_type_binder_names_from_region(
            env,
            &region,
            module
                .constants
                .iter()
                .map(|c| (c.name.as_str(), c.type_ptr)),
        )?;
        // `∀` binder NAMES under each definition's value, for named arguments on a
        // head whose type unfolds to it — see `value_binder_names`.
        super::value_binder_names::record_value_binder_names_from_region(
            env,
            &region,
            module
                .constants
                .iter()
                .map(|c| (c.name.as_str(), &c.kind, c.value_ptr)),
        )?;
    }

    // Region-scoped memo for the direct converter (#import-dag-memo). Created
    // WITH `region` and dropped with it, which is what keeps its pointer keys
    // meaningful — see `RegionPtrCache`. It is shared by the main conversion
    // below and the `.olean.private` axiom-stub upgrade further down, both of
    // which read THIS region, so a type reachable from both is decoded once.
    let mut ptr_memo = RegionPtrCache::for_region();

    // Convert constants using direct binary-to-Expr path
    let cache_size_before: u64 = intern_cache.total_entries;
    let inductive_families_only = policy.inductive_families_only();

    // Rule 4 of `artifact_ledger`: a record naming what an earlier part of
    // this artifact declared must state it as that part did. It used to be
    // dropped unread, so the parts of one module could disagree and the
    // first loaded won (X1: `D.olean` said `D.e := 1`, the `D.olean.private`
    // `lean` reads said `D.e := 0`, and `D.e = 1` passed). Under
    // `InductiveFamiliesOnly` the definitional kinds are neither converted
    // nor registered here (served lazily), so only the families compare.
    // The very bytes loaded before for this artifact (met again, e.g.
    // `Init` re-read by a second load into one environment) state nothing
    // new; their records were compared at the first load. For a
    // companion part the bytes are the combined region it is read in.
    let met_before = super::artifact_ledger::part_met_before(
        env,
        &artifact,
        *blake3::hash(&module.bytes).as_bytes(),
    );
    if met_before {
        // Its records were compared when these bytes were first loaded. What
        // it states in THIS load still counts: a value-free record of a name
        // the environment holds with a value is a stub a later part of this
        // load must complete (rule 4, one rule for every load).
        // Under `InductiveFamiliesOnly` definitions are served lazily and not
        // compared here (see below).
        let definitional = |c: &&super::load_parse::LoadConstant| {
            !inductive_families_only && !is_inductive_family_kind(&c.kind)
        };
        let restated: Vec<&super::load_parse::LoadConstant> = same_artifact_indices
            .iter()
            .map(|&i| &module.constants[i])
            .filter(definitional)
            .collect();
        super::artifact_ledger::note_met_before_part(
            env,
            &artifact,
            module.is_module,
            restated
                .iter()
                .filter(|c| c.value_ptr == 0)
                .map(|c| c.kernel_name.clone()),
            restated
                .iter()
                .filter(|c| c.value_ptr != 0)
                .map(|c| c.kernel_name.clone()),
        )?;
    }
    for &i in &same_artifact_indices {
        let c = &module.constants[i];
        if met_before || (inductive_families_only && !is_inductive_family_kind(&c.kind)) {
            continue;
        }
        super::deadline::poll()?;
        let converted = convert_load_constant(
            c,
            &region,
            intern_cache,
            &mut ptr_memo,
            policy.proof_elision(),
        );
        let incoming = part_record(&converted, load_constant_safety(c));
        super::artifact_ledger::check_same_artifact_record(
            env,
            &artifact,
            &c.kernel_name,
            incoming.as_ref(),
        )?;
    }

    let constants: Vec<_> = constants
        .into_iter()
        // HYBRID (Phase-1 zero-copy): under `InductiveFamiliesOnly` the definitional
        // kinds are served by the lazy `ShardConstantSource`; never build their owned
        // `Arc<Expr>` (the memory win). See the ParsedModule path for the soundness note.
        .filter(|c| !inductive_families_only || is_inductive_family_kind(&c.kind))
        .collect();
    // The caller's deadline is polled before each conversion: a load past it
    // stops here (`super::deadline`), with nothing of this part registered.
    let converted: Vec<ConvertedConstant> = constants
        .iter()
        .map(|c| {
            super::deadline::poll()?;
            Ok(convert_load_constant(
                c,
                &region,
                intern_cache,
                &mut ptr_memo,
                policy.proof_elision(),
            ))
        })
        .collect::<Result<_, ImportError>>()?;
    // What this part declares, as read — for a later part of the artifact
    // to be compared with (rule 4).
    let records: Vec<_> = constants
        .iter()
        .zip(&converted)
        .filter_map(|(c, cc)| part_record(cc, load_constant_safety(c)))
        .collect();
    let staged_records: HashMap<_, _> = if deferred.is_some() {
        let ordinals: HashMap<_, _> = module
            .constants
            .iter()
            .enumerate()
            .map(|(i, constant)| (&constant.kernel_name, i))
            .collect();
        records
            .iter()
            .filter_map(|record| match record {
                super::artifact_ledger::PartRecord::Recursor(rec, ..) => {
                    Some((rec.name.clone(), (ordinals[&rec.name], record.clone())))
                }
                _ => None,
            })
            .collect()
    } else {
        HashMap::new()
    };
    super::artifact_ledger::remember_part_records(env, &artifact, records);

    // Registration logic is identical to the ParsedModule path
    register_converted_constants(
        env,
        converted,
        intern_cache,
        &mut summary,
        cache_size_before,
        Some(&olean_origin),
        policy.proof_elision(),
        policy.import_kinds(),
        deferred.map(|(queue, summary_ordinal)| RecursorStaging {
            queue,
            summary_ordinal,
            records: &staged_records,
        }),
    );

    // Upgrade axiom stubs with definitions from .olean.private (#3134).
    // When Lean 4.29+ exports definitions as axiom stubs in the base .olean,
    // the full definitions (with values) are in .olean.private. Replace the
    // stubs so the type checker can unfold these definitions.
    // HYBRID (Phase-1 zero-copy): the upgrade restores `Definition` VALUES, a
    // definitional kind served lazily under `InductiveFamiliesOnly`; skip it then
    // so the lazy source remains the single owner of the definitional kinds.
    let mut upgraded_names: Vec<Name> = Vec::new();
    if !upgrade_indices.is_empty() && !policy.inductive_families_only() {
        // #3134 axiom-stub upgrade: CONVERT with NO elision (the conversion must
        // produce a real value, never a `Sort 0` placeholder), then apply the
        // policy elision POST-conversion on the built `ConstantInfo`, mirroring
        // Pass-4 and the ParsedModule path. Required for v4.30+ stdlib where Init
        // proof bodies arrive via `.olean.private` and would otherwise re-inflate
        // here. SOUNDNESS: types retained; only policy-selected VALUEs dropped.
        let upgrade_converted: Vec<ConvertedConstant> = upgrade_indices
            .iter()
            .map(|&i| {
                super::deadline::poll()?;
                Ok(convert_load_constant(
                    &module.constants[i],
                    &region,
                    intern_cache,
                    &mut ptr_memo,
                    ProofValueElision::None,
                ))
            })
            .collect::<Result<_, ImportError>>()?;
        let mut upgrade_others = Vec::new();
        for cc in upgrade_converted {
            match cc {
                ConvertedConstant::Other(_name, Ok((decl, hints)), _stats) => {
                    let mut info = decl_to_constant_info(decl, hints);
                    // Under R142's invariant the value is checked whole first and
                    // elided after the upgrade installs it (below).
                    if info.value.is_some()
                        && policy.proof_elision().elides(info.kind)
                        && !policy.checks_authoritative_values()
                    {
                        info.value = None;
                    }
                    upgrade_others.push(info);
                }
                ConvertedConstant::Other(name, Err(e), _stats) => {
                    summary.skipped_constants.push(SkippedConstant {
                        name,
                        reason: format!("axiom upgrade failed: {e}"),
                    });
                }
                _ => {} // inductives/constructors/recursors not expected in upgrade path
            }
        }
        // R1-STUB (2026-08-24): the checked tier — the stub must exist, the
        // incoming type must kernel-match the stub's type, and the incoming
        // value must check_type against it (UnknownConst-tolerant, G4). A
        // refused record leaves the stub in place FAIL-CLOSED and is recorded
        // loudly below; nothing ever registers unchecked.
        let completing = upgrade_others.clone();
        upgraded_names.extend(upgrade_others.iter().map(|c| c.name.clone()));
        let (upgraded, refused) = upgrade_stubs_to_fixpoint(env, upgrade_others);
        summary.added_constants += upgraded;
        // R142: the values were checked whole; the policy's elision drops the
        // installed ones now, so an eliding re-check load never trusts a stub
        // whose completion it did not check.
        if policy.checks_authoritative_values() {
            let refused_names: HashSet<&Name> = refused.iter().map(|(n, _)| n).collect();
            let installed: Vec<&Name> = completing
                .iter()
                .map(|c| &c.name)
                .filter(|n| !refused_names.contains(n))
                .collect();
            let _ = env.forget_proof_values_for(installed, policy.proof_elision());
        }
        let safety_of: HashMap<Name, Option<DefinitionSafety>> = upgrade_indices
            .iter()
            .map(|&i| {
                let c = &module.constants[i];
                (c.kernel_name.clone(), load_constant_safety(c))
            })
            .collect();
        remember_completed_stubs(env, &artifact, completing, &refused, &safety_of);
        // An `unsafe`/`partial` value the check refused (Lean's safe context
        // refuses an `unsafe` body's `unsafeCast`) is one Lean's replay never
        // admits either (`LoadSummary::skipped_not_replayable`).
        let unreplayable: HashSet<&str> = upgrade_indices
            .iter()
            .map(|&i| &module.constants[i])
            .filter(|c| stored_unsafe_or_partial(&c.kind, c.definition_safety))
            .map(|c| c.name.as_str())
            .collect();
        record_refused_completions(env, &mut summary, &artifact, refused, &unreplayable, policy)?;
    }

    // Everything this module registered, for the projection-scan index.
    super::projection_scan::note_touched(
        env,
        summary
            .added_names
            .iter()
            .chain(&upgraded_names)
            .chain(&discharge_stub_names),
    );

    apply_declaration_safety_marks(env, safety_marks);
    // Closed over its imports, and no declaration depends on itself (round
    // 29, C1/C4) — decided before anything can unfold what this part added;
    // left to the caller's replay under `OleanImportPolicy::with_replay_refusals`
    // (both), and `with_module_replay_refusals` (the cycle only).
    if policy.refuses_forward_references() {
        let upgraded: Vec<Name> = upgrade_indices
            .iter()
            .map(|&i| module.constants[i].kernel_name.clone())
            .collect();
        super::artifact_ledger::check_part_references(
            env,
            &artifact,
            &summary.added_names,
            &upgraded,
            policy.refuses_definitional_cycles(),
        )?;
    }

    if !module.entries.is_empty() && !policy.kernel_only() {
        summary.extension_accounting = extension_accounting(&module.entries);
    }
    // Only the part the artifact is read through registers its tables; the
    // artifact loader compared the others with it before any part loaded
    // (`artifact_ledger::check_artifact_entries`).
    if !module.entries.is_empty() && entries == PartEntries::Read {
        load_extension_entries(env, mod_idx, &module.entries)?;
        // Register the DECODED real-Lean type-class declarations (`ClassEntry`)
        // FIRST — before every other class/instance bridge — so classes with no
        // imported instance (e.g. `Membership`) exist at all, and out-param
        // classes carry their REAL `outParams` (`GetElem` ⟶ [2,3]) that the
        // downstream empty-out-param registrations must not clobber
        // (first-writer-wins; #olean-env-ext-restore lane-B increment 2).
        summary
            .class_out_param_mismatches
            .extend(register_real_class_entries(env, &module.entries));
        // Register imported `@[class]` structures/inductives as typeclasses
        // FIRST, before bridging instances: the elaborator's instance synthesis
        // (`init_instances_from_env`) only surfaces instances of *registered*
        // classes, so the target class must exist before its instances are
        // associated with it. Otherwise typeclass resolution fails for every
        // imported class (e.g. Group/Semiring) (#olean-class-before-instance-order).
        register_classes_from_extension(env);
        // Register the DECODED real-Lean `@[instance]` entries with their real
        // priorities BEFORE the persistent-state bridge below, so decoded
        // source registrations supply the real priority
        // (#olean-env-ext-restore).
        register_real_instance_entries(env, &module.entries);
        // Recover structure/class field-name tables from the loaded projection
        // functions for any structure whose `structureExt` entry did not
        // decode (#olean-structure-field-names); the decoded entries above
        // win first.
        // Register the DECODED real-Lean `Lean.structureExt` entries FIRST:
        // the field-name table straight from Lean's own `fieldNames`, and the
        // `extends` parents (subobject `toParent` slots) that an imported
        // structure never had before — the metadata the structure-instance
        // elaborator needs to route `le := …` on a `LinearOrder` into
        // `toPartialOrder`. The projection-derived pass below is kept as the
        // fallback for a structure whose entry did not decode.
        register_structures_from_extension(env, &module.entries)?;
        // The whole-environment `register_structure_fields_from_projections`,
        // proportional to what this module touched (see `projection_scan`).
        super::projection_scan::register_touched_structure_fields(env);
        // Re-register imported typeclass instances into the kernel registry so
        // the elaborator's instance synthesis can see them (#instance-import).
        // Only explicitly persisted registrations are candidates. No global
        // definition-type scan may manufacture missing metadata.
        register_instances_from_extension(env);
        // Register the DECODED real-Lean `@[simp]` entries
        // (`Lean.Meta.simpExtension`) into the kernel simp registry, counting
        // origins whose constant is absent LOUDLY in the summary (RC-B/T10).
        for (extension, counts) in module.entries.iter().zip(&mut summary.extension_accounting) {
            counts.unresolved_targets =
                register_real_simp_entries(env, std::slice::from_ref(extension));
            counts.unresolved_targets += register_real_matcher_entries(
                env,
                summary.module_name.as_deref(),
                std::slice::from_ref(extension),
            )?;
        }
        // The part's compiler tables, read for the late-binding judgement
        // (`late_binding`): which declarations Lean compiled, and how each
        // may be inlined.
        let compiler_names = super::late_binding::CompilerNames::of(&module.entries);
        let mut registered = Vec::new();
        for (extension, counts) in module.entries.iter().zip(&mut summary.extension_accounting) {
            counts.unresolved_targets +=
                register_real_alias_entries(env, std::slice::from_ref(extension));
            counts.unresolved_targets += register_real_compiler_attr_entries(
                env,
                summary.module_name.as_deref(),
                std::slice::from_ref(extension),
                &compiler_names,
                &mut registered,
            )?;
        }
        super::late_binding::record_late_bindings(
            env,
            summary.module_name.as_deref(),
            module,
            &compiler_names,
            &registered,
        );
        finish_extension_accounting(&mut summary)?;
        // Re-register imported `@[simp]` lemmas into the kernel registry so the
        // simp tactic can use them (#simp-import).
        register_simp_lemmas_from_extension(env);
        // Materialize imported reducibility attributes (`@[reducible]`,
        // `@[irreducible]`, `@[semireducible]`) into the kernel's per-constant
        // reducibility state so delta-reduction transparency is faithful
        // (#attr-import).
        register_attributes_from_extension(env);
    } else if !module.entries.is_empty() {
        finish_extension_accounting(&mut summary)?;
    }

    super::projection_scan::end_module(env);
    Ok(summary)
}

/// Preserve unknown safety for missing kind-specific headers; do not infer
/// safety from a loader-created environment declaration or a future kind.
fn stored_constant_safety(
    kind: &ConstantKind,
    safety: Option<DefinitionSafety>,
    inductive: bool,
    constructor: bool,
    recursor: bool,
) -> Option<DefinitionSafety> {
    match kind {
        ConstantKind::Definition | ConstantKind::Axiom | ConstantKind::Opaque => safety,
        ConstantKind::Theorem | ConstantKind::Quot => Some(DefinitionSafety::Safe),
        ConstantKind::Inductive => inductive.then_some(safety.unwrap_or(DefinitionSafety::Safe)),
        ConstantKind::Constructor => {
            constructor.then_some(safety.unwrap_or(DefinitionSafety::Safe))
        }
        ConstantKind::Recursor => recursor.then_some(safety.unwrap_or(DefinitionSafety::Safe)),
    }
}

/// The declaration safety a Lean-built record gives itself (`None`: safe,
/// or a kind that carries none).
pub(super) fn load_constant_safety(
    c: &super::load_parse::LoadConstant,
) -> Option<DefinitionSafety> {
    match c.kind {
        ConstantKind::Definition | ConstantKind::Axiom | ConstantKind::Opaque => {
            c.definition_safety
        }
        ConstantKind::Inductive => c
            .inductive_val
            .as_ref()
            .and_then(|v| v.is_unsafe.then_some(DefinitionSafety::Unsafe)),
        ConstantKind::Constructor => c
            .constructor_val
            .as_ref()
            .and_then(|v| v.is_unsafe.then_some(DefinitionSafety::Unsafe)),
        ConstantKind::Recursor => c
            .recursor_val
            .as_ref()
            .and_then(|v| v.is_unsafe.then_some(DefinitionSafety::Unsafe)),
        ConstantKind::Theorem | ConstantKind::Quot => None,
    }
}

/// Rule 4 of `artifact_ledger`: a stub a part completed now reads as the
/// completing part states it (a refused completion leaves the stub, and
/// what the ledger remembers of it, as it was).
fn remember_completed_stubs(
    env: &mut Environment,
    artifact: &super::artifact_ledger::ArtifactKey,
    completing: Vec<clean_kernel::env::ConstantInfo>,
    refused: &[(Name, clean_kernel::env::EnvError)],
    safety_of: &HashMap<Name, Option<DefinitionSafety>>,
) {
    let refused: HashSet<&Name> = refused.iter().map(|(n, _)| n).collect();
    let completed: Vec<_> = completing
        .into_iter()
        .filter(|info| !refused.contains(&info.name))
        .map(|info| super::artifact_ledger::PartRecord::Constant {
            safety: safety_of.get(&info.name).copied().flatten(),
            info,
        })
        .collect();
    super::artifact_ledger::remember_part_records(env, artifact, completed);
}

/// [`load_constant_safety`] for a record of the `ParsedModule` path.
fn parsed_constant_safety(c: &crate::module::ParsedConstant) -> Option<DefinitionSafety> {
    match c.kind {
        ConstantKind::Definition | ConstantKind::Axiom | ConstantKind::Opaque => {
            c.definition_safety
        }
        ConstantKind::Inductive => c
            .inductive_val
            .as_ref()
            .and_then(|v| v.is_unsafe.then_some(DefinitionSafety::Unsafe)),
        ConstantKind::Constructor => c
            .constructor_val
            .as_ref()
            .and_then(|v| v.is_unsafe.then_some(DefinitionSafety::Unsafe)),
        ConstantKind::Recursor => c
            .recursor_val
            .as_ref()
            .and_then(|v| v.is_unsafe.then_some(DefinitionSafety::Unsafe)),
        ConstantKind::Theorem | ConstantKind::Quot => None,
    }
}

/// A converted record as the ledger remembers it; `None` if it did not
/// convert.
pub(super) fn part_record(
    converted: &ConvertedConstant,
    safety: Option<DefinitionSafety>,
) -> Option<super::artifact_ledger::PartRecord> {
    use super::artifact_ledger::PartRecord;
    Some(match converted {
        ConvertedConstant::Inductive(_, Ok(v), _) => PartRecord::Inductive(v.clone(), safety),
        ConvertedConstant::Constructor(_, Ok(v), _) => PartRecord::Constructor(v.clone(), safety),
        ConvertedConstant::Recursor(_, Ok((v, all, nested)), _) => {
            PartRecord::Recursor(v.clone(), all.clone(), *nested, safety)
        }
        ConvertedConstant::Other(_, Ok((decl, hints)), _) => PartRecord::Constant {
            info: decl_to_constant_info(decl.clone(), *hints),
            safety,
        },
        _ => return None,
    })
}

/// Whether a converted Lean-built record may stand beside the declaration
/// another artifact already made under its name ([`may_stand_beside`]); a
/// family member, or a record that did not convert, never.
fn same_declaration(env: &Environment, converted: ConvertedConstant) -> bool {
    match converted {
        ConvertedConstant::Other(_, Ok((decl, hints)), _) => {
            may_stand_beside(env, &decl_to_constant_info(decl, hints))
        }
        _ => false,
    }
}

/// Refuse the first of `others` (`(index, first module)` from
/// `artifact_ledger::check_lean_records`) that is not the declaration the
/// environment already holds.
///
/// Under [`OleanImportPolicy::with_replay_refusals`] (and
/// `with_module_replay_refusals`) nothing is refused here:
/// the registration filter keeps the resident declaration and records the
/// later one in `LoadSummary::shadowed_declarations` (or, for a restatement
/// Lean's import merges, `restated_declarations`), and the replay refuses it
/// by name, at the layer Lean does.
fn refuse_other_declarations(
    env: &Environment,
    policy: OleanImportPolicy,
    others: Vec<(usize, String)>,
    mut convert: impl FnMut(usize) -> (Name, ConvertedConstant),
) -> Result<(), ImportError> {
    if policy.leaves_conflicts_to_replay() {
        return Ok(());
    }
    for (index, first) in others {
        let (name, converted) = convert(index);
        if !same_declaration(env, converted) {
            return Err(ImportError::ConflictingDeclaration {
                name: name.to_string(),
                first,
            });
        }
    }
    Ok(())
}

/// The `.olean` loader's structural tier, for declarations another front end
/// has already converted to kernel types: the NDJSON reader (`crate::ndjson`)
/// registers an export's declarations here, through the same passes, the same
/// structural checks and the same safety marks as a Lean-built `.olean`, so
/// both front doors hand the replay the same tier. It adds no registration
/// path: every insertion is [`register_converted_constants`]'s.
pub(crate) fn register_front_end_constants(
    env: &mut Environment,
    converted: Vec<ConvertedConstant>,
    safety_marks: Vec<(Name, ConstantKind, DefinitionSafety)>,
) -> LoadSummary {
    let intern_cache = ExprInternCache::default();
    let mut summary = LoadSummary::empty();
    register_converted_constants(
        env,
        converted,
        &intern_cache,
        &mut summary,
        0,
        None,
        ProofValueElision::None,
        super::ImportKinds::All,
        None,
    );
    apply_declaration_safety_marks(env, safety_marks);
    summary
}

/// Common registration logic for converted constants.
///
/// Used by both the `ParsedModule` path and the `LoadModule` direct path.
fn register_converted_constants(
    env: &mut Environment,
    converted: Vec<ConvertedConstant>,
    intern_cache: &ExprInternCache,
    summary: &mut LoadSummary,
    cache_size_before: u64,
    origin: Option<&ConstantOrigin>,
    proof_elision: ProofValueElision,
    import_kinds: super::ImportKinds,
    mut staging: Option<RecursorStaging<'_>>,
) {
    // HYBRID (Phase-1 zero-copy): under `InductiveFamiliesOnly`, the definitional
    // kinds (Definition/Theorem/Axiom/Opaque — the `Other` bucket) are served by
    // a lazy `ConstantSource`, so they are NOT registered eagerly here. The
    // inductive families (Inductive/Constructor/Recursor) still register — they
    // cannot be served lazily (the shard format can't carry recursor rules).
    let inductive_families_only = matches!(import_kinds, super::ImportKinds::InductiveFamiliesOnly);
    // Pre-size category Vecs from empirical Init/Std ratios:
    // ~10% inductives, ~20% constructors, ~15% recursors, ~55% other.
    let n = converted.len();
    let mut ok_inductives = Vec::with_capacity(n / 8);
    let mut ok_constructors = Vec::with_capacity(n / 4);
    let mut recursors = Vec::with_capacity(n / 6);
    let mut ok_others = Vec::with_capacity(n / 2);

    for converted_const in converted {
        match converted_const {
            ConvertedConstant::Inductive(name, result, stats) => {
                summary.expr_sharing.merge(&stats);
                match result {
                    Ok(ind_val) => ok_inductives.push(ind_val),
                    Err(e) => summary.skipped_constants.push(SkippedConstant {
                        name,
                        reason: e.to_string(),
                    }),
                }
            }
            ConvertedConstant::Constructor(name, result, stats) => {
                summary.expr_sharing.merge(&stats);
                match result {
                    Ok(ctor_val) => ok_constructors.push(ctor_val),
                    Err(e) => summary.skipped_constants.push(SkippedConstant {
                        name,
                        reason: e.to_string(),
                    }),
                }
            }
            ConvertedConstant::Recursor(name, result, stats) => {
                summary.expr_sharing.merge(&stats);
                recursors.push((name, result));
            }
            ConvertedConstant::Other(name, result, stats) => {
                summary.expr_sharing.merge(&stats);
                match result {
                    Ok((decl, hints)) => ok_others.push((decl, hints)),
                    Err(e) => summary.skipped_constants.push(SkippedConstant {
                        name,
                        reason: e.to_string(),
                    }),
                }
            }
        }
    }

    summary.expr_sharing.unique_exprs = intern_cache.total_entries - cache_size_before;

    // `is_large_elim` is decided after passes 1-2 below, in place: see
    // `Environment::recompute_imported_large_elim`. The constructor lists it
    // decides on are taken here, before pass 2 consumes the constructors —
    // every converted constructor, as the per-module staging clone this
    // replaced was given (P1_IMPORT, 2026-09-26: that clone of the WHOLE
    // environment per module was 71-74% of steady-state import samples).
    let mut ctor_map: HashMap<Name, Vec<Constructor>> = HashMap::new();
    if !ok_inductives.is_empty() {
        for ctor in &ok_constructors {
            ctor_map
                .entry(ctor.inductive_name.clone())
                .or_default()
                .push(Constructor {
                    name: ctor.name.clone(),
                    type_: ctor.type_.clone(),
                });
        }
    }

    // Pass 1: Bulk register inductives.
    // R1-IND (2026-08-24): passes 1-3 run the structural tier
    // (extend_*_structural — the same O(1) checks as Pass 4's constants leg,
    // incl. every recursor-rule rhs). A failing record REFUSES structurally:
    // diverted to summary.skipped_constants, never inserted.
    let inductive_origin_names: Vec<_> = ok_inductives.iter().map(|ind| ind.name.clone()).collect();
    let pre_validate_inductives = ok_inductives.len();
    let rejected = env.extend_inductives_structural(ok_inductives.into_iter());
    summary.added_constants += pre_validate_inductives - rejected.len();
    let inductive_origin_names = divert_structural_rejections(
        inductive_origin_names,
        rejected,
        &mut summary.skipped_constants,
    );
    let accepted_inductives = inductive_origin_names.clone();
    tag_inserted_constants(
        env,
        origin,
        inductive_origin_names,
        &mut summary.added_names,
    );

    // Pass 2: Bulk register constructors
    let constructor_origin_names: Vec<_> = ok_constructors
        .iter()
        .map(|ctor| ctor.name.clone())
        .collect();
    let pre_validate_constructors = ok_constructors.len();
    let rejected = env.extend_constructors_structural(ok_constructors.into_iter());
    summary.added_constants += pre_validate_constructors - rejected.len();
    let constructor_origin_names = divert_structural_rejections(
        constructor_origin_names,
        rejected,
        &mut summary.skipped_constants,
    );
    tag_inserted_constants(
        env,
        origin,
        constructor_origin_names,
        &mut summary.added_names,
    );

    // Pass 4: Bulk register other constants with structural validation.
    // Validates each constant for duplicate level params, metavariables,
    // free variables, and level param scope before insertion. Part of #3233.
    //
    // HYBRID (Phase-1 zero-copy): the `Other` bucket is exactly the lazily-
    // servable definitional kinds (Definition/Theorem/Axiom/Opaque). Under
    // `InductiveFamiliesOnly` they are owned by the lazy `ConstantSource`, so
    // skip eager registration entirely (no constants stored, no names tagged).
    // SOUNDNESS: every such name resolves through `get_const`'s lazy fallback to
    // the same `ConstantInfo`, so no verdict changes — the inductive families
    // registered above resolve their definitional deps through that fallback.
    if !inductive_families_only {
        let others: Vec<_> = ok_others
            .into_iter()
            .map(|(decl, hints)| decl_to_constant_info(decl, hints))
            .map(|mut info| {
                // BOUNDED MEMORY (WS3): drop never-unfolded proof VALUES here, before
                // the constant is stored, so the proof-term Expr DAG is freed as each
                // module loads — capping PEAK resident memory. TYPES and Definition
                // values are always kept (references type-check; definitions unfold).
                // SOUNDNESS: `OpaqueOnly` is verdict-preserving (the kernel never
                // δ-unfolds an `Opaque` value); broader policies are the caller's
                // explicit, gate-validated choice. Only ever set on trusted imports.
                if info.value.is_some() && proof_elision.elides(info.kind) {
                    info.value = None;
                }
                info
            })
            .collect();
        let pre_validate_count = others.len();
        let other_origin_names: Vec<_> = others.iter().map(|info| info.name.clone()).collect();
        // SOUNDNESS: structural validation (above) is NOT kernel type-checking — a
        // structurally-clean constant whose stored type disagrees with its value, or that
        // references a nonexistent constant, still passes. Bypassing per-decl type-checking is
        // acceptable only under Clean's declared .olean trust posture (CLAUDE.md: "full
        // validation must be explicit"): the trust anchor is that the upstream Lean 4 kernel
        // type-checked these decls before serialization. NOTE: "upstream-checked" means
        // well-typed relative to the module's admitted axioms — NOT axiom-free or sorry-free.
        // Imported constants are stored Unverified; a caller wanting Clean's kernel to discharge
        // that trust must run the opt-in typecheck_constants_full (clean-olean/src/verify_batch_full.rs).
        // Residual trust: upstream checking + faithful deserialization/conversion (a conversion
        // bug yields a structurally-valid-but-wrong constant the structural checks can't catch).
        // Tracking: data/unchecked_decl_ratchet.json (extend_constants block, #4).
        let rejected = env.extend_constants_structural(others.into_iter());
        summary.added_constants += pre_validate_count - rejected.len();
        if !other_origin_names.is_empty() {
            let rejected_names: HashSet<_> =
                rejected.iter().map(|(name, _)| name.clone()).collect();
            let accepted_names = other_origin_names
                .into_iter()
                .filter(|name| !rejected_names.contains(name))
                .collect();
            tag_inserted_constants(env, origin, accepted_names, &mut summary.added_names);
        }
        for (name, err) in rejected {
            summary.skipped_constants.push(SkippedConstant {
                name: name.to_string(),
                reason: format!("structural validation failed: {err}"),
            });
        }
    }

    // Own definitions can occur in constructor field types. Decide their
    // sorts after those definitions register, before any recursor is admitted.
    if !accepted_inductives.is_empty() {
        env.recompute_imported_large_elim(accepted_inductives.into_iter().map(|name| {
            let ctors = ctor_map.remove(&name).unwrap_or_default();
            (name, ctors)
        }));
    }

    // Pass 3 (runs LAST): Bulk register recursors.
    // After the module's definitional constants (pass 4), because the kernel
    // now REGENERATES each recursor from the resident family and compares
    // (env/imported_family.rs): deciding whether a Prop family may eliminate
    // into every universe infers its fields' sorts, and a field type may name
    // a definition declared later in this same module.
    // Compute recursive fields first (needs env lookups for constructors),
    // then batch-insert all recursors in one extend call to avoid per-recursor
    // generation increments. Part of #3133.
    {
        let mut ok_recursors = Vec::with_capacity(recursors.len());
        for (name, result) in recursors {
            match result {
                Ok((mut rec_val, mutual_inductives, param_count)) => {
                    rec_val.rules = rec_val
                        .rules
                        .into_iter()
                        .map(|mut rule| {
                            rule.recursive_fields = compute_recursive_fields_from_env(
                                env,
                                &rule.constructor_name,
                                &mutual_inductives,
                                param_count,
                                rule.num_fields,
                            );
                            rule
                        })
                        .collect();
                    ok_recursors.push(rec_val);
                }
                Err(e) => summary.skipped_constants.push(SkippedConstant {
                    name,
                    reason: e.to_string(),
                }),
            }
        }
        let recursor_origin_names: Vec<_> =
            ok_recursors.iter().map(|rec| rec.name.clone()).collect();
        let pre_validate_recursors = ok_recursors.len();
        let rejected = env.extend_recursors_structural(ok_recursors.into_iter());
        summary.added_constants += pre_validate_recursors - rejected.len();
        let rejected_names: HashSet<_> = rejected.iter().map(|(name, _)| name.clone()).collect();
        for (name, error) in rejected {
            // Preserve every successful early admission. Only an actual strict
            // rejection in a provably incomplete private context can wait.
            let staged = staging.as_mut().is_some_and(|staging| {
                staging
                    .records
                    .get(&name)
                    .is_some_and(|(source_ordinal, record)| {
                        staging.queue.stage(
                            env,
                            staging.summary_ordinal,
                            summary,
                            *source_ordinal,
                            record,
                            &error,
                        )
                    })
            });
            if !staged {
                summary.skipped_constants.push(SkippedConstant {
                    name: name.to_string(),
                    reason: format!("structural validation failed: {error}"),
                });
            }
        }
        tag_inserted_constants(
            env,
            origin,
            recursor_origin_names
                .into_iter()
                .filter(|name| !rejected_names.contains(name))
                .collect(),
            &mut summary.added_names,
        );
    }
}

#[cfg(test)]
mod definition_safety_registration_tests {
    use super::apply_declaration_safety_marks;
    use crate::module::{ConstantKind as ModuleConstantKind, DefinitionSafety};
    use clean_kernel::env::{ConstantInfo, ConstantKind, Environment, Reducibility, TrustedEnvExt};
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    fn seed(env: &mut Environment, name: &str) -> Name {
        let name = Name::from_string(name);
        env.extend_constants_unchecked(std::iter::once(ConstantInfo::new(
            name.clone(),
            vec![],
            Expr::type_(),
            Some(Expr::prop()),
            false,
        )));
        name
    }

    fn seed_kind(env: &mut Environment, name: &str, kind: ConstantKind) -> Name {
        let name = Name::from_string(name);
        let value = (kind != ConstantKind::Axiom).then_some(Expr::prop());
        env.extend_constants_unchecked(std::iter::once(ConstantInfo::new_with_reducibility(
            name.clone(),
            vec![],
            Expr::type_(),
            value,
            Reducibility::Opaque,
            kind,
        )));
        name
    }

    #[test]
    fn unsafe_and_partial_are_both_preserved_as_non_safe_authority() {
        let mut env = Environment::new();
        let unsafe_name = seed(&mut env, "Test.ImportedUnsafe");
        let partial_name = seed(&mut env, "Test.ImportedPartial");
        let safe_name = seed(&mut env, "Test.ImportedSafe");

        apply_declaration_safety_marks(
            &mut env,
            [
                (
                    unsafe_name.clone(),
                    ModuleConstantKind::Definition,
                    DefinitionSafety::Unsafe,
                ),
                (
                    partial_name.clone(),
                    ModuleConstantKind::Definition,
                    DefinitionSafety::Partial,
                ),
                (
                    safe_name.clone(),
                    ModuleConstantKind::Definition,
                    DefinitionSafety::Safe,
                ),
            ],
        );

        assert!(env.is_unsafe(&unsafe_name));
        assert!(!env.is_partial(&unsafe_name));
        assert!(env.is_partial(&partial_name));
        assert!(!env.is_unsafe(&partial_name));
        assert!(!env.is_unsafe(&safe_name));
        assert!(!env.is_partial(&safe_name));
    }

    #[test]
    fn rejected_or_absent_constant_does_not_leave_a_latent_mark() {
        let mut env = Environment::new();
        let absent = Name::from_string("Test.AbsentPartial");
        apply_declaration_safety_marks(
            &mut env,
            [(
                absent.clone(),
                ModuleConstantKind::Definition,
                DefinitionSafety::Partial,
            )],
        );
        assert!(!env.is_partial(&absent));

        let axiom_stub = Name::from_string("Test.RejectedPrivateUpgrade");
        env.extend_constants_unchecked(std::iter::once(ConstantInfo::new_with_reducibility(
            axiom_stub.clone(),
            vec![],
            Expr::type_(),
            None,
            Reducibility::Opaque,
            ConstantKind::Axiom,
        )));
        apply_declaration_safety_marks(
            &mut env,
            [(
                axiom_stub.clone(),
                ModuleConstantKind::Definition,
                DefinitionSafety::Partial,
            )],
        );
        assert!(
            !env.is_partial(&axiom_stub),
            "a rejected private upgrade must not mark the surviving axiom stub"
        );
    }

    #[test]
    fn axiom_and_opaque_marks_require_and_preserve_exact_kernel_kinds() {
        let mut env = Environment::new();
        let axiom = seed_kind(&mut env, "Test.UnsafeAxiom", ConstantKind::Axiom);
        let opaque = seed_kind(&mut env, "Test.UnsafeOpaque", ConstantKind::Opaque);

        apply_declaration_safety_marks(
            &mut env,
            [
                (
                    axiom.clone(),
                    ModuleConstantKind::Axiom,
                    DefinitionSafety::Unsafe,
                ),
                (
                    opaque.clone(),
                    ModuleConstantKind::Opaque,
                    DefinitionSafety::Unsafe,
                ),
            ],
        );
        assert!(env.is_unsafe(&axiom));
        assert!(env.is_unsafe(&opaque));

        let mismatched_axiom = seed_kind(&mut env, "Test.MismatchedAxiom", ConstantKind::Axiom);
        let mismatched_opaque = seed_kind(&mut env, "Test.MismatchedOpaque", ConstantKind::Opaque);
        apply_declaration_safety_marks(
            &mut env,
            [
                (
                    mismatched_axiom.clone(),
                    ModuleConstantKind::Opaque,
                    DefinitionSafety::Unsafe,
                ),
                (
                    mismatched_opaque.clone(),
                    ModuleConstantKind::Axiom,
                    DefinitionSafety::Unsafe,
                ),
            ],
        );
        assert!(!env.is_unsafe(&mismatched_axiom));
        assert!(!env.is_unsafe(&mismatched_opaque));
    }
}

#[cfg(test)]
mod compiler_ir_filter_tests {
    use super::is_compiler_ir_name;

    #[test]
    fn test_is_compiler_ir_name_matches_codegen_artifacts() {
        // Compiler IR stages and lambda-lifting / specialization artifacts.
        assert!(is_compiler_ir_name("Nat.bitwise._cstage2"));
        assert!(is_compiler_ir_name("instHAdd._rarg._cstage2"));
        assert!(is_compiler_ir_name("Equiv.Set.rangeInl._elambda_1"));
        assert!(is_compiler_ir_name("Bifunctor.mapEquiv._elambda_2"));
        assert!(is_compiler_ir_name("Foo._lambda_3"));
        assert!(is_compiler_ir_name("List.foldr._rarg"));
        assert!(is_compiler_ir_name("Foo.bar._spec_1"));
        assert!(is_compiler_ir_name("Acc.rec._unsafe_rec"));
    }

    #[test]
    fn test_is_compiler_ir_name_preserves_logical_declarations() {
        // Genuine, logically-referenced declarations must NOT be skipped —
        // including match-equation compiler defs and hygiene-mangled names.
        assert!(!is_compiler_ir_name("Nat.add"));
        assert!(!is_compiler_ir_name("Equiv.Set.rangeInl"));
        assert!(!is_compiler_ir_name("Mathlib.Logic.Basic._auxLemma.3"));
        assert!(!is_compiler_ir_name("Foo.match_1"));
        assert!(!is_compiler_ir_name("List.map"));
        assert!(!is_compiler_ir_name("Function.Injective.comp"));
        // Substring-but-not-a-component must not match (component-scoped).
        assert!(!is_compiler_ir_name("My_cstage1Thing"));
    }

    #[test]
    fn test_is_compiler_ir_name_matches_compile_inductive_float_artifacts() {
        // The genuinely-failing, unreferenced Float runtime-impl / spec artifacts
        // the CompileInductive tooling module emits.
        assert!(is_compiler_ir_name(
            "_private.Mathlib.Util.CompileInductive.1.Float.mkImpl"
        ));
        assert!(is_compiler_ir_name(
            "_private.Mathlib.Util.CompileInductive.1.Float.valImpl"
        ));
        assert!(is_compiler_ir_name(
            "_private.Mathlib.Util.CompileInductive.1.Float.mk_eq"
        ));
        assert!(is_compiler_ir_name(
            "_private.Mathlib.Util.CompileInductive.1.Float.val_eq"
        ));
    }

    #[test]
    fn test_is_compiler_ir_name_preserves_compile_inductive_genuine_helpers() {
        // CRITICAL GUARD: genuine, kernel-verified helpers of these tooling
        // modules — and their public API — must STAY imported.
        // - Filtering the whole `_private.…CompileInductive.` namespace regressed
        //   `compileDefn` (it references `addAndCompile'`).
        assert!(!is_compiler_ir_name(
            "_private.Mathlib.Util.CompileInductive.1.Mathlib.Util.addAndCompile'"
        ));
        assert!(!is_compiler_ir_name("Mathlib.Util.compileDefn"));
        assert!(!is_compiler_ir_name("Mathlib.Util.compileInductiveOnly"));
        // - The MemoFix impl artifacts are NOT filtered: the genuine KV
        //   `memoFixImpl` references `memoFixImplObj`, so filtering it would
        //   regress `memoFixImpl` to "Unknown constant".
        assert!(!is_compiler_ir_name(
            "_private.Mathlib.Util.MemoFix.1.memoFixImpl"
        ));
        assert!(!is_compiler_ir_name(
            "_private.Mathlib.Util.MemoFix.1.memoFixImplObj"
        ));
        assert!(!is_compiler_ir_name(
            "_private.Mathlib.Util.MemoFix.1.ObjectMap"
        ));
        // - The macro-scope `_@.…CompileInductive._hyg` recursor copies are NOT
        //   filtered — byte-identical copies of already-verified recursors that
        //   mostly kernel-verify; removing them would lower the honest KV rate.
        assert!(!is_compiler_ir_name(
            "List.rec._@.Mathlib.Util.CompileInductive._hyg.6481"
        ));
        assert!(!is_compiler_ir_name(
            "And.rec._@.Mathlib.Util.CompileInductive._hyg.6567"
        ));
        // A `_private` decl of a DIFFERENT module is genuine math — not matched.
        assert!(!is_compiler_ir_name(
            "_private.Mathlib.Algebra.Group.Basic.1.someRealLemma"
        ));
        // Same artifact suffix but wrong module — not matched.
        assert!(!is_compiler_ir_name(
            "_private.Mathlib.Other.Module.1.Float.mkImpl"
        ));
    }
}

#[cfg(test)]
mod structure_field_projection_tests {
    use super::{
        projection_fn_target, register_structure_fields_from_projections,
        structure_table_contradiction, try_register_structure_meta, PendingStructureMeta,
    };
    use clean_kernel::env::{ConstantInfo, Environment, TrustedEnvExt};
    use clean_kernel::expr::{BinderInfo, Expr};
    use clean_kernel::inductive::{ConstructorVal, InductiveVal};
    use clean_kernel::name::Name;

    /// A projection-function value: `fun (self : S) => self.idx`.
    fn projection_value(struct_name: &Name, idx: u32) -> Expr {
        Expr::lam(
            BinderInfo::Default,
            Expr::const_(struct_name.clone(), clean_kernel::expr::LevelVec::new()),
            Expr::proj(struct_name.clone(), idx, Expr::bvar(0)),
        )
    }

    /// Register a single-constructor inductive `name` (a structure/class shape)
    /// with `num_fields` fields, plus one projection-function constant
    /// `name.<field>` per `(idx, field)` in `projections`.
    fn seed_structure(
        env: &mut Environment,
        name: &Name,
        num_fields: u32,
        projections: &[(u32, &str)],
    ) {
        let field_types = vec![Expr::type_(); num_fields as usize];
        seed_structure_typed(env, name, &field_types, projections);
    }

    /// `S.mk : T₀ → … → Tₙ₋₁ → S` (no parameters): a real telescope, so
    /// `structure_table_contradiction` can compute each projection on it.
    fn seed_structure_typed(
        env: &mut Environment,
        name: &Name,
        field_types: &[Expr],
        projections: &[(u32, &str)],
    ) {
        let num_fields = u32::try_from(field_types.len()).expect("few fields");
        let ctor_name = Name::append(name, "mk");
        let mut ctor_type = Expr::const_(name.clone(), clean_kernel::expr::LevelVec::new());
        for ty in field_types.iter().rev() {
            ctor_type = Expr::pi(BinderInfo::Default, ty.clone(), ctor_type);
        }
        env.extend_inductives_unchecked(std::iter::once(InductiveVal {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::type_(),
            num_params: 0,
            num_indices: 0,
            all_names: vec![name.clone()],
            constructor_names: vec![ctor_name.clone()],
            is_recursive: false,
            is_reflexive: false,
            is_large_elim: true,
            is_nested: false,
        }));
        env.extend_constructors_unchecked(std::iter::once(ConstructorVal {
            name: ctor_name,
            inductive_name: name.clone(),
            level_params: vec![],
            type_: ctor_type,
            num_params: 0,
            num_fields,
            constructor_idx: 0,
        }));
        let consts: Vec<ConstantInfo> = projections
            .iter()
            .map(|(idx, field)| {
                ConstantInfo::new(
                    Name::append(name, field),
                    vec![],
                    Expr::type_(),
                    Some(projection_value(name, *idx)),
                    true,
                )
            })
            .collect();
        env.extend_constants_unchecked(consts.into_iter());
    }

    fn meta(structure: &Name, fields: &[&str]) -> PendingStructureMeta {
        PendingStructureMeta {
            struct_name: structure.clone(),
            field_names: fields.iter().map(|f| Name::from_string(f)).collect(),
            field_proj_fns: vec![],
            parents: vec![],
        }
    }

    // Module-trust round 27 (M8f/M9): a decoded structure-field table is
    // elaborator metadata; one that contradicts the projections loaded with
    // it, or a table already registered, refuses the import instead of
    // silently choosing either side.

    #[test]
    fn a_table_agreeing_with_its_projections_is_registered() {
        let s = Name::from_string("RT27.P");
        let mut env = Environment::new();
        seed_structure(&mut env, &s, 2, &[(0, "x"), (1, "y")]);
        assert_eq!(
            structure_table_contradiction(
                &env,
                &s,
                &[Name::from_string("x"), Name::from_string("y")],
                &[],
                false
            ),
            None
        );
        assert!(matches!(
            try_register_structure_meta(&mut env, &meta(&s, &["x", "y"]), true),
            Ok(true)
        ));
        assert_eq!(
            env.get_structure_field_names(&s).map(<[Name]>::to_vec),
            Some(vec![Name::from_string("x"), Name::from_string("y")])
        );
        // Re-registering the SAME table is not a contradiction.
        assert!(matches!(
            try_register_structure_meta(&mut env, &meta(&s, &["x", "y"]), true),
            Ok(true)
        ));
    }

    #[test]
    fn a_table_contradicting_its_projections_is_refused() {
        let s = Name::from_string("RT27.P");
        let mut env = Environment::new();
        seed_structure(&mut env, &s, 2, &[(0, "x"), (1, "y")]);
        let refused = try_register_structure_meta(&mut env, &meta(&s, &["y", "x"]), true);
        assert!(
            matches!(
                refused,
                Err(crate::ImportError::InconsistentStructureTable { .. })
            ),
            "{refused:?}"
        );
        assert!(
            env.get_structure_field_names(&s).is_none(),
            "nothing registered"
        );
    }

    #[test]
    fn a_region_table_disagreeing_with_its_payload_table_is_refused() {
        // No projections loaded (a lazily served closure): the only evidence
        // is the table the artifact's Clean payload registered, and the
        // decoded region table of the same artifact contradicts it.
        let s = Name::from_string("RT27.Q");
        let mut env = Environment::new();
        seed_structure(&mut env, &s, 2, &[]);
        env.register_structure_fields(
            s.clone(),
            vec![Name::from_string("x"), Name::from_string("y")],
        )
        .expect("first table");
        env.get_ext_state_mut::<super::StructureExtPending>(super::structure_ext_pending_idx())
            .payload_tables
            .insert(s.clone());
        let refused = try_register_structure_meta(&mut env, &meta(&s, &["y", "x"]), true);
        assert!(
            matches!(
                refused,
                Err(crate::ImportError::InconsistentStructureTable { .. })
            ),
            "{refused:?}"
        );
    }

    #[test]
    fn a_region_table_differing_from_a_native_table_is_not_a_contradiction() {
        // The kernel's native prelude registers its own table for a structure
        // a Lean version defines differently (measured: `String`, `Array`
        // under v4.30). That is version skew, not a rewritten artifact: the
        // decoded table is simply not applied, as before round 27.
        let s = Name::from_string("RT27.N");
        let mut env = Environment::new();
        seed_structure(&mut env, &s, 1, &[]);
        env.register_structure_fields(s.clone(), vec![Name::from_string("data")])
            .expect("native table");
        assert!(matches!(
            try_register_structure_meta(&mut env, &meta(&s, &["toList"]), true),
            Ok(true)
        ));
        assert_eq!(
            env.get_structure_field_names(&s).map(<[Name]>::to_vec),
            Some(vec![Name::from_string("data")])
        );
    }

    #[test]
    fn test_projection_fn_target_recovers_struct_and_index() {
        let s = Name::from_string("TestMonoid");
        let body = projection_value(&s, 2);
        assert_eq!(projection_fn_target(&body), Some((s, 2)));
        // A non-projection body yields None.
        assert_eq!(projection_fn_target(&Expr::type_()), None);
    }

    #[test]
    fn typed_projection_suffix_preserves_quoted_and_numeric_components() {
        // Deliberately assumed metadata: no fresh admission is claimed here.
        let structure = Name::anon().str("S.part");
        let mut env = Environment::new();
        seed_structure(&mut env, &structure, 3, &[]);
        let fields = [
            Name::anon().str("field.dot"),
            Name::anon().str("07"),
            Name::anon().num(7),
        ];
        let names = [
            structure.clone().str("field.dot"),
            structure.clone().str("07"),
            structure.clone().num(7),
        ];
        for (index, name) in names.into_iter().enumerate() {
            env.extend_constants_unchecked(std::iter::once(ConstantInfo::new(
                name,
                vec![],
                Expr::type_(),
                Some(projection_value(&structure, index as u32)),
                true,
            )));
        }
        register_structure_fields_from_projections(&mut env);
        assert_eq!(
            env.get_structure_field_names(&structure),
            Some(fields.as_slice())
        );
    }

    #[test]
    fn display_equal_projection_parent_does_not_retarget_structure() {
        let structure = Name::anon().str("S.part");
        let mut env = Environment::new();
        seed_structure(&mut env, &structure, 1, &[]);
        let wrong_parent = Name::anon().str("S").str("part");
        assert_eq!(structure.to_string(), wrong_parent.to_string());
        assert_ne!(structure, wrong_parent);
        env.extend_constants_unchecked(std::iter::once(ConstantInfo::new(
            wrong_parent.str("field"),
            vec![],
            Expr::type_(),
            Some(projection_value(&structure, 0)),
            true,
        )));
        register_structure_fields_from_projections(&mut env);
        assert!(env.get_structure_field_names(&structure).is_none());
    }

    #[test]
    fn test_field_names_populated_in_projection_index_order() {
        // A Monoid-shaped class: three DIRECT fields. Seed the projection
        // constants in SCRAMBLED order so the test proves ordering comes from
        // the Proj index, not insertion order.
        let monoid = Name::from_string("TestMonoid");
        let mut env = Environment::new();
        seed_structure(
            &mut env,
            &monoid,
            3,
            &[(2, "mul_one"), (0, "mul"), (1, "one")],
        );
        assert!(
            env.get_structure_field_names(&monoid).is_none(),
            "precondition: no field table before the projection pass (the gap)"
        );

        register_structure_fields_from_projections(&mut env);

        let fields = env
            .get_structure_field_names(&monoid)
            .expect("field names should now be populated for the Monoid-shaped class");
        let got: Vec<String> = fields.iter().map(Name::to_string).collect();
        // Ordered by projection index 0,1,2 — so Proj(TestMonoid, i, inst)
        // selects the intended field.
        assert_eq!(got, vec!["mul", "one", "mul_one"]);
    }

    #[test]
    fn test_incomplete_projection_set_leaves_field_names_none() {
        // The constructor has 3 fields but only 2 projections were recovered
        // (e.g. one served lazily). register_structure_fields' count check
        // rejects the mismatch, so no partial/wrong table is stored.
        let monoid = Name::from_string("TestMonoidPartial");
        let mut env = Environment::new();
        seed_structure(&mut env, &monoid, 3, &[(0, "mul"), (1, "one")]);

        register_structure_fields_from_projections(&mut env);

        assert!(
            env.get_structure_field_names(&monoid).is_none(),
            "an incomplete projection set must not register a partial field table"
        );
    }

    #[test]
    fn test_non_canonical_projection_is_ignored() {
        // A helper `Other.helper := fun s => s.0` that projects TestMonoid but is
        // NOT named `TestMonoid.<field>` must not contribute a field. With no
        // canonical projections, the field table stays None.
        let monoid = Name::from_string("TestMonoidNoProj");
        let mut env = Environment::new();
        seed_structure(&mut env, &monoid, 1, &[]);
        let other = Name::from_string("Other.helper");
        env.extend_constants_unchecked(std::iter::once(ConstantInfo::new(
            other,
            vec![],
            Expr::type_(),
            Some(projection_value(&monoid, 0)),
            true,
        )));

        register_structure_fields_from_projections(&mut env);

        assert!(
            env.get_structure_field_names(&monoid).is_none(),
            "a non-`S.<field>` projection must not populate S's field table"
        );
    }

    #[test]
    fn test_theorem_kind_prop_field_projections_are_recovered() {
        // Real Mathlib regression: a structure's PROP-field (class-axiom)
        // projections — `Monoid.mul_one`, `Semigroup.mul_assoc`, … — are emitted
        // as `Theorem`-kind constants, while its DATA-field projections
        // (`toSemigroup`, `npow`, …) are `Definition`s. Both carry the SAME
        // `λ*. Proj(S, i, _)` body. If only `Definition`s were scanned the
        // recovered index set would be the data fields alone — non-contiguous —
        // and NO field table would register (the exact real-Monoid gap: it has 4
        // of 7 fields as Theorem-kind law projections). Here fields 1 and 3 are
        // Theorem-kind law projections interleaved with Definition data fields 0
        // and 2; the pass must recover all four.
        use clean_kernel::env::ConstantKind;

        let s = Name::from_string("TestMonoidMixed");
        let mut env = Environment::new();
        // Inductive + 4-field constructor, NO projections seeded here.
        seed_structure(&mut env, &s, 4, &[]);

        // Seed the 4 projections with REALISTIC kinds: data=Definition,
        // law=Theorem. Insertion order scrambled to prove index-ordering.
        let seeds: [(u32, &str, ConstantKind); 4] = [
            (3, "mul_one", ConstantKind::Theorem),        // law
            (0, "toSemigroup", ConstantKind::Definition), // data
            (2, "npow", ConstantKind::Definition),        // data
            (1, "mul_assoc", ConstantKind::Theorem),      // law
        ];
        let consts: Vec<ConstantInfo> = seeds
            .iter()
            .map(|(idx, field, kind)| {
                let mut ci = ConstantInfo::new(
                    Name::append(&s, field),
                    vec![],
                    Expr::type_(),
                    Some(projection_value(&s, *idx)),
                    true,
                );
                ci.kind = *kind;
                ci
            })
            .collect();
        env.extend_constants_unchecked(consts.into_iter());

        register_structure_fields_from_projections(&mut env);

        let fields = env
            .get_structure_field_names(&s)
            .expect("Theorem-kind law projections must be recovered alongside Definition ones");
        let got: Vec<String> = fields.iter().map(Name::to_string).collect();
        assert_eq!(
            got,
            vec!["toSemigroup", "mul_assoc", "npow", "mul_one"],
            "fields ordered by Proj index, mixing Definition (0,2) and Theorem (1,3) kinds"
        );
    }

    // Module-trust round 28 (Y1/Y2): the table is the one the projections
    // COMPUTE, not the one their body shapes suggest.

    fn s_const(s: &Name) -> Expr {
        Expr::const_(s.clone(), clean_kernel::expr::LevelVec::new())
    }

    /// `fun (self : S) => (fun t => t.idx) self`: computes field `idx`, and
    /// is not `λ*. Proj(S, idx, _)`-shaped (Y1's recursor bodies were not).
    fn indirect_projection(s: &Name, idx: u32) -> Expr {
        let inner = Expr::lam(
            BinderInfo::Default,
            s_const(s),
            Expr::proj(s.clone(), idx, Expr::bvar(0)),
        );
        Expr::lam(
            BinderInfo::Default,
            s_const(s),
            Expr::app(inner, Expr::bvar(0)),
        )
    }

    fn add_projection(env: &mut Environment, s: &Name, field: &str, value: Expr) {
        env.extend_constants_unchecked(std::iter::once(ConstantInfo::new(
            Name::append(s, field),
            vec![],
            Expr::type_(),
            Some(value),
            true,
        )));
    }

    fn refused(r: &Result<bool, crate::ImportError>) -> bool {
        matches!(
            r,
            Err(crate::ImportError::InconsistentStructureTable { .. })
        )
    }

    #[test]
    fn a_reversed_table_over_projections_that_are_not_proj_shaped_is_refused() {
        let s = Name::from_string("RT28.Y1");
        let mut env = Environment::new();
        seed_structure(&mut env, &s, 2, &[]);
        add_projection(&mut env, &s, "x", indirect_projection(&s, 0));
        add_projection(&mut env, &s, "y", indirect_projection(&s, 1));
        assert_eq!(projection_fn_target(&indirect_projection(&s, 0)), None);
        let r = try_register_structure_meta(&mut env, &meta(&s, &["y", "x"]), true);
        assert!(refused(&r), "{r:?}");
        assert!(env.get_structure_field_names(&s).is_none());
        // Control: the honest table over the same projections registers.
        let r = try_register_structure_meta(&mut env, &meta(&s, &["x", "y"]), true);
        assert!(matches!(r, Ok(true)), "{r:?}");
    }

    #[test]
    fn a_table_whose_projections_are_missing_is_refused_unless_they_are_served_lazily() {
        let s = Name::from_string("RT28.Y2");
        let mut env = Environment::new();
        seed_structure(&mut env, &s, 2, &[]);
        let fields = [Name::from_string("y"), Name::from_string("x")];
        assert!(structure_table_contradiction(&env, &s, &fields, &[], false)
            .is_some_and(|why| matches!(why, super::TableFault::Absent(_))));
        let r = try_register_structure_meta(&mut env, &meta(&s, &["y", "x"]), true);
        assert!(refused(&r), "{r:?}");
        // Under a lazy closure load, absence is not evidence.
        assert_eq!(
            structure_table_contradiction(&env, &s, &fields, &[], true),
            None
        );
    }

    #[test]
    fn a_projection_shaped_like_one_field_that_computes_another_is_found_out() {
        // `x := fun s => (S.mk s.1 s.0).0` has the shape of field 0 and
        // computes field 1.
        let s = Name::from_string("RT28.Shape");
        let mut env = Environment::new();
        seed_structure(&mut env, &s, 2, &[(1, "y")]);
        let swapped = Expr::apps(
            Expr::const_(Name::append(&s, "mk"), clean_kernel::expr::LevelVec::new()),
            [
                Expr::proj(s.clone(), 1, Expr::bvar(0)),
                Expr::proj(s.clone(), 0, Expr::bvar(0)),
            ],
        );
        let x = Expr::lam(
            BinderInfo::Default,
            s_const(&s),
            Expr::proj(s.clone(), 0, swapped),
        );
        assert_eq!(projection_fn_target(&x), Some((s.clone(), 0)));
        add_projection(&mut env, &s, "x", x);
        let r = try_register_structure_meta(&mut env, &meta(&s, &["x", "y"]), true);
        assert!(refused(&r), "{r:?}");
        // The shape-based recovery pass nominates [x, y] and must not
        // register it either.
        register_structure_fields_from_projections(&mut env);
        assert!(env.get_structure_field_names(&s).is_none());
    }

    #[test]
    fn a_projection_that_is_an_axiom_does_not_name_a_field() {
        let s = Name::from_string("RT28.Ax");
        let mut env = Environment::new();
        seed_structure(&mut env, &s, 1, &[]);
        let mut ax = ConstantInfo::new(Name::append(&s, "x"), vec![], Expr::type_(), None, true);
        ax.kind = clean_kernel::env::ConstantKind::Axiom;
        env.extend_constants_unchecked(std::iter::once(ax));
        // Control: a value-free projection the checker's own base declares
        // (no import origin) is not artifact evidence.
        let r = try_register_structure_meta(&mut env, &meta(&s, &["x"]), true);
        assert!(matches!(r, Ok(true)), "{r:?}");
        // The same, loaded from an artifact, names no field.
        let s = Name::from_string("RT28.Ax2");
        seed_structure(&mut env, &s, 1, &[]);
        let mut ax = ConstantInfo::new(Name::append(&s, "x"), vec![], Expr::type_(), None, true);
        ax.kind = clean_kernel::env::ConstantKind::Axiom;
        env.extend_constants_unchecked(std::iter::once(ax));
        env.set_constant_origins(
            vec![Name::append(&s, "x")],
            clean_kernel::env::ConstantOrigin::clean_payload(Some("RT28".to_string())),
        );
        let r = try_register_structure_meta(&mut env, &meta(&s, &["x"]), true);
        assert!(refused(&r), "{r:?}");
    }

    #[test]
    fn a_private_field_is_read_through_its_private_projection_and_only_that() {
        // Lean names a `private` field's projection `_private.<mod>.<n>.S.f`
        // (measured: `Lean.Macro.State.expandedMacroDecls`, pinned v4.30).
        let s = Name::from_string("RT28.Priv");
        let mut env = Environment::new();
        seed_structure(&mut env, &s, 2, &[(0, "x")]);
        let private_y = Name::from_string("_private.RT28.Mod.0.RT28.Priv.y");
        env.extend_constants_unchecked(std::iter::once(ConstantInfo::new(
            private_y.clone(),
            vec![],
            Expr::type_(),
            Some(projection_value(&s, 1)),
            true,
        )));
        let mut m = meta(&s, &["x", "y"]);
        m.field_proj_fns = vec![
            (Name::from_string("x"), Name::append(&s, "x")),
            (Name::from_string("y"), private_y.clone()),
        ];
        let r = try_register_structure_meta(&mut env, &m, true);
        assert!(matches!(r, Ok(true)), "{r:?}");
        // A `projFn` that is not a private alias of `S.f` cannot stand in
        // for it: reversed table, `projFn`s pointed at each other.
        let t = Name::from_string("RT28.Retarget");
        let mut env = Environment::new();
        seed_structure(&mut env, &t, 2, &[(0, "x")]);
        let mut m = meta(&t, &["y", "x"]);
        m.field_proj_fns = vec![
            (Name::from_string("y"), Name::append(&t, "x")),
            (Name::from_string("x"), Name::append(&t, "x")),
        ];
        let r = try_register_structure_meta(&mut env, &m, true);
        assert!(refused(&r), "{r:?}");
        let y = Name::from_string("y");
        assert!(super::names_field_projection(&private_y, &s, &y));
        assert!(!super::names_field_projection(
            &Name::append(&t, "x"),
            &t,
            &y
        ));
        // A private prefix with no counter is not Lean's shape.
        assert!(!super::names_field_projection(
            &Name::from_string("_private.RT28.Priv.y"),
            &s,
            &y
        ));
        // A hygienic structure's projection carries the scopes after the field.
        let hyg = Name::from_string("RT28.H._@.RT28.Mod._hyg.1");
        let id = Name::from_string("id");
        assert!(super::names_field_projection(
            &Name::from_string("RT28.H.id._@.RT28.Mod._hyg.1"),
            &hyg,
            &id
        ));
        assert!(!super::names_field_projection(
            &Name::from_string("RT28.H.other._@.RT28.Mod._hyg.1"),
            &hyg,
            &id
        ));
    }

    #[test]
    fn a_projection_not_loaded_yet_parks_the_table_until_the_closure_ends() {
        let s = Name::from_string("RT28.Late");
        let mut env = Environment::new();
        seed_structure(&mut env, &s, 2, &[(0, "x")]);
        // Mid-closure: `y`'s projection may still arrive (a private
        // companion part) — parked, not refused and not registered.
        let r = try_register_structure_meta(&mut env, &meta(&s, &["x", "y"]), false);
        assert!(matches!(r, Ok(false)), "{r:?}");
        assert!(env.get_structure_field_names(&s).is_none());
        // Closure end, still absent: refused.
        let r = try_register_structure_meta(&mut env, &meta(&s, &["x", "y"]), true);
        assert!(refused(&r), "{r:?}");
        // Arrived: registered.
        env.extend_constants_unchecked(std::iter::once(ConstantInfo::new(
            Name::append(&s, "y"),
            vec![],
            Expr::type_(),
            Some(projection_value(&s, 1)),
            true,
        )));
        let r = try_register_structure_meta(&mut env, &meta(&s, &["x", "y"]), true);
        assert!(matches!(r, Ok(true)), "{r:?}");
        // A contradiction is refused mid-closure too.
        let t = Name::from_string("RT28.LateBad");
        seed_structure(&mut env, &t, 2, &[(0, "x"), (1, "y")]);
        let r = try_register_structure_meta(&mut env, &meta(&t, &["y", "x"]), false);
        assert!(refused(&r), "{r:?}");
    }

    #[test]
    fn a_value_free_projection_is_accepted_only_at_a_proof_field() {
        // `S.mk : Type → (∀ p : Prop, p) → S`: field 1 is a proof.
        let s = Name::from_string("RT28.Prf");
        let proof_ty = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
        let mut env = Environment::new();
        seed_structure_typed(&mut env, &s, &[Expr::type_(), proof_ty], &[(0, "x")]);
        let mut h = ConstantInfo::new(Name::append(&s, "h"), vec![], Expr::type_(), None, true);
        h.kind = clean_kernel::env::ConstantKind::Axiom;
        env.extend_constants_unchecked(std::iter::once(h));
        env.set_constant_origins(
            vec![Name::append(&s, "h"), Name::append(&s, "x")],
            clean_kernel::env::ConstantOrigin::olean_import(Some("RT28".to_string())),
        );
        // Honest [x, h]: `h` is value-free (Lean exports theorems so) and
        // sits at the proof field.
        let r = try_register_structure_meta(&mut env, &meta(&s, &["x", "h"]), true);
        assert!(matches!(r, Ok(true)), "{r:?}");
        // Reversed [h, x]: `x` computes field 0, not 1.
        let t = Name::from_string("RT28.Prf2");
        let proof_ty = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
        seed_structure_typed(&mut env, &t, &[Expr::type_(), proof_ty], &[(0, "x")]);
        let mut h = ConstantInfo::new(Name::append(&t, "h"), vec![], Expr::type_(), None, true);
        h.kind = clean_kernel::env::ConstantKind::Axiom;
        env.extend_constants_unchecked(std::iter::once(h));
        env.set_constant_origins(
            vec![Name::append(&t, "h")],
            clean_kernel::env::ConstantOrigin::olean_import(Some("RT28".to_string())),
        );
        let r = try_register_structure_meta(&mut env, &meta(&t, &["h", "x"]), true);
        assert!(refused(&r), "{r:?}");
    }

    #[test]
    fn a_parked_decoded_table_is_compared_with_the_recovered_one() {
        // Measured with a Lean-built `W.olean` whose `structureExt` field
        // table was reversed in the region: the decoded table was parked
        // (its inductive not yet registered), the projection pass then
        // registered the honest table, and the parked one was dropped
        // silently where `e3f696689` refused the import.
        let s = Name::from_string("RT28.Park");
        let mut env = Environment::new();
        let r = try_register_structure_meta(&mut env, &meta(&s, &["y", "x"]), false);
        assert!(matches!(r, Ok(false)), "{r:?}");
        seed_structure(&mut env, &s, 2, &[(0, "x"), (1, "y")]);
        register_structure_fields_from_projections(&mut env);
        assert!(env.get_structure_field_names(&s).is_some());
        let r = try_register_structure_meta(&mut env, &meta(&s, &["y", "x"]), true);
        assert!(refused(&r), "{r:?}");
        // The honest decoded table agrees with the recovered one.
        let r = try_register_structure_meta(&mut env, &meta(&s, &["x", "y"]), true);
        assert!(matches!(r, Ok(true)), "{r:?}");
    }

    #[test]
    fn a_decoded_table_its_projections_contradict_is_refused_beside_any_table() {
        // `W.P` already has a table (its source was elaborated, or the native
        // prelude declared it); the artifact's decoded table is reversed and
        // its own projections compute the honest fields. Refused, as on
        // `e3f696689` (measured with a Lean-built `W.olean`).
        let s = Name::from_string("RT28.Beside");
        let mut env = Environment::new();
        seed_structure(&mut env, &s, 2, &[(0, "x"), (1, "y")]);
        env.register_structure_fields(
            s.clone(),
            vec![Name::from_string("x"), Name::from_string("y")],
        )
        .expect("source table");
        let r = try_register_structure_meta(&mut env, &meta(&s, &["y", "x"]), true);
        assert!(refused(&r), "{r:?}");
    }
}

/// Rule 4 of `artifact_ledger` on the payload leg: a Clean payload carried by
/// a later part of an artifact (its `.olean.private`, say) that re-declares
/// what an earlier part's payload declared. Measured on `f4af8f11a`: a
/// `V0.olean.private` payload saying `V0.v := 1` beside `V0.olean`'s
/// `V0.v := 0` was dropped unread (`filter_payload_dups`).
#[cfg(test)]
mod part_agreement_tests {
    use super::load_clean_payload;
    use crate::import::artifact_ledger::bind_part;
    use crate::import::{ImportError, ImportKinds};
    use crate::payload::CleanPayload;
    use clean_kernel::env::{ConstantInfo, ConstantOrigin, Environment, TrustedEnvExt};
    use clean_kernel::expr::{Expr, LevelVec};
    use clean_kernel::name::Name;

    fn payload(value: u64) -> CleanPayload {
        CleanPayload {
            constants: vec![ConstantInfo::new(
                Name::from_string("V0.v"),
                vec![],
                Expr::const_(Name::from_string("Nat"), LevelVec::new()),
                Some(Expr::nat_lit(value)),
                false,
            )],
            ..CleanPayload::default()
        }
    }

    fn load_part(
        env: &mut Environment,
        label: &str,
        part: &CleanPayload,
    ) -> Result<(), ImportError> {
        let label = Some(label.to_string());
        let artifact = Some("V0".to_string());
        bind_part(env, &label, &artifact)?;
        let mut added = Vec::new();
        load_clean_payload(
            env,
            part,
            Some(&ConstantOrigin::clean_payload(label)),
            &artifact,
            &mut added,
            ImportKinds::All,
        )
        .map(|_| ())
    }

    /// A payload's compiler bindings (version 5, `docs/DECISIONS.md` R149)
    /// register for the payload's own declarations, never for a resident
    /// declaration the loader kept instead of one the payload names.
    #[test]
    fn test_payload_compiler_bindings_register_for_its_own_declarations_only() {
        let name = |s: &str| Name::from_string(s);
        let mut env = Environment::with_prelude();
        let mut part = payload(0);
        part.implemented_by = vec![
            (name("V0.v"), name("V0.w")),
            (name("Nat.add"), name("V0.v")),
        ];
        part.externs = vec![
            (name("V0.v"), "clean_v0_symbol".to_owned()),
            (name("Nat.mul"), "clean_mul_symbol".to_owned()),
        ];
        load_part(&mut env, "V0", &part).expect("V0's payload");
        assert_eq!(env.get_implemented_by(&name("V0.v")), Some(&name("V0.w")));
        assert_eq!(
            env.get_extern(&name("V0.v")).map(String::as_str),
            Some("clean_v0_symbol")
        );
        assert_ne!(
            env.get_implemented_by(&name("Nat.add")),
            Some(&name("V0.v"))
        );
        assert_ne!(
            env.get_extern(&name("Nat.mul")).map(String::as_str),
            Some("clean_mul_symbol")
        );
    }

    #[test]
    fn noncomputable_import_tags_only_its_own_resident_declaration() {
        use super::{register_imported_compiler_attr, ImportedCompilerAttr, Registration};
        let n = |s: &str| Name::from_string(s);
        let mut env = Environment::with_prelude();
        load_part(&mut env, "V0", &payload(0)).unwrap();
        assert!(matches!(
            register_imported_compiler_attr(
                &mut env,
                Some("V0"),
                &n("V0.v"),
                ImportedCompilerAttr::Noncomputable
            ),
            Registration::Registered
        ));
        assert!(env.is_noncomputable(&n("V0.v")));
        assert!(matches!(
            register_imported_compiler_attr(
                &mut env,
                Some("V0"),
                &n("Nat.add"),
                ImportedCompilerAttr::Noncomputable
            ),
            Registration::NotRegistered
        ));
        assert!(!env.is_noncomputable(&n("Nat.add")));
        assert!(matches!(
            register_imported_compiler_attr(
                &mut env,
                Some("V0"),
                &n("Absent"),
                ImportedCompilerAttr::Noncomputable
            ),
            Registration::Absent
        ));
    }

    #[test]
    fn a_companion_payload_stating_a_declaration_differently_is_refused() {
        let mut env = Environment::with_prelude();
        load_part(&mut env, "V0", &payload(0)).expect("V0.olean's payload");
        let err = load_part(&mut env, "V0._private", &payload(1))
            .expect_err("V0.olean.private's payload says V0.v := 1");
        assert!(matches!(err, ImportError::PartsDisagree { .. }), "{err}");

        // Control: the same declaration in both parts.
        let mut env = Environment::with_prelude();
        load_part(&mut env, "V0", &payload(0)).expect("V0.olean's payload");
        load_part(&mut env, "V0._private", &payload(0)).expect("the parts agree");
    }

    #[test]
    fn a_companion_payload_stating_a_structure_table_differently_is_refused() {
        use clean_kernel::expr::BinderInfo;
        use clean_kernel::inductive::{ConstructorVal, InductiveVal};
        let s = Name::from_string("V0.P");
        let mk = Name::from_string("V0.P.mk");
        let nat = Expr::const_(Name::from_string("Nat"), LevelVec::new());
        let p = Expr::const_(s.clone(), LevelVec::new());
        let mut env = Environment::with_prelude();
        // `structure V0.P where x : Nat; y : Nat`, declared by the artifact
        // V0 (its base part), with projections `x` (field 0) and `y` (1).
        env.extend_inductives_unchecked(std::iter::once(InductiveVal {
            name: s.clone(),
            level_params: vec![],
            type_: Expr::type_(),
            num_params: 0,
            num_indices: 0,
            all_names: vec![s.clone()],
            constructor_names: vec![mk.clone()],
            is_recursive: false,
            is_reflexive: false,
            is_large_elim: true,
            is_nested: false,
        }));
        env.extend_constructors_unchecked(std::iter::once(ConstructorVal {
            name: mk.clone(),
            inductive_name: s.clone(),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                nat.clone(),
                Expr::pi(BinderInfo::Default, nat.clone(), p.clone()),
            ),
            num_params: 0,
            num_fields: 2,
            constructor_idx: 0,
        }));
        let projections = [("V0.P.x", 0), ("V0.P.y", 1)].map(|(f, i)| {
            ConstantInfo::new(
                Name::from_string(f),
                vec![],
                Expr::pi(BinderInfo::Default, p.clone(), nat.clone()),
                Some(Expr::lam(
                    BinderInfo::Default,
                    p.clone(),
                    Expr::proj(s.clone(), i, Expr::bvar(0)),
                )),
                true,
            )
        });
        env.extend_constants_unchecked(projections.into_iter());
        env.set_constant_origins(
            [
                s.clone(),
                mk,
                Name::from_string("V0.P.x"),
                Name::from_string("V0.P.y"),
            ],
            ConstantOrigin::clean_payload(Some("V0".into())),
        );
        let table = |fields: [&str; 2]| CleanPayload {
            structure_fields: vec![(
                s.clone(),
                fields.iter().map(|f| Name::from_string(f)).collect(),
            )],
            ..CleanPayload::default()
        };
        load_part(&mut env, "V0", &table(["x", "y"])).expect("V0.olean's table");
        assert!(env.get_structure_field_names(&s).is_some(), "registered");
        // Control: the same table again.
        load_part(&mut env, "V0._server", &table(["x", "y"])).expect("the parts agree");
        let err = load_part(&mut env, "V0._private", &table(["y", "x"]))
            .expect_err("the private part's table is reversed");
        assert!(matches!(err, ImportError::PartsDisagree { .. }), "{err}");
    }
}
