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
use super::load_parse::LoadModule;
use super::{ExprInternCache, ImportError, LoadSummary, OleanImportPolicy, SkippedConstant};
use crate::module::{
    ConstantKind, DefinitionSafety, ParsedExtension, ParsedExtensionEntry,
    ParsedExtensionEntryData, ParsedModule, LEAN_CLASS_EXTENSION, LEAN_INSTANCE_EXTENSION,
};
use crate::payload::CleanPayload;
use clean_kernel::env::{
    attr_ext_idx, instance_ext_idx, simp_ext_idx, AttrExtState, ConstantOrigin, EnvExtensionEntry,
    EnvExtensionEntryData, Environment, InstanceExtState, KernelClassInfo, KernelInstanceInfo,
    ProofValueElision, Reducibility, SimpExtState, SimpPriority, TrustedEnvExt,
};
use clean_kernel::expr::{BinderInfo, Expr, ExprKind};
use clean_kernel::inductive::{allows_large_elim, Constructor};
use clean_kernel::name::Name;
use hashbrown::{HashMap, HashSet};

/// Detect Lean compiler / code-generator auxiliary declarations that are not
/// kernel-checkable logical declarations.
///
/// SOUNDNESS: every name matched here is a code-generator / lambda-lifting
/// artifact, never referenced by any logical term, and never type-checked by
/// Lean's own kernel:
/// - `_cstage1` / `_cstage2`: compiled IR stages. Their stored types are written
///   in Lean's erased compiler type system and reference the runtime
///   pseudo-types `_obj` / `_neutral`, which are never declared — importing them
///   makes every check trip on `UnknownConst(_obj)`.
/// - `_elambda_N` / `_lambda_N`: lambda-lifted closures from the old code
///   generator. In the exported `.olean` they are stored as `AxiomVal` with an
///   EMPTY `levelParams` list but a universe-polymorphic type, so they cannot be
///   re-typechecked as standalone constants (`UndefinedLevelParam`). They are
///   referenced only through `@[implemented_by]` / `csimp` compiler metadata,
///   never by a logical term (verified: parent defs' values contain no
///   `_elambda` reference).
/// - `_rarg`: the restricted-argument specialization of a code-generated def.
/// - `_spec` / `_spec_N`: compiler specializations.
/// - `_unsafe_rec`: the unsafe recursor used only by compiled code.
///
/// Excluding these at import drops no logical declaration and keeps the
/// KernelVerified accounting honest (skipped, not failed). NOTE: the match-equation
/// compiler's `Foo.match_N` and hygiene-mangled `_hyg` names are deliberately NOT
/// matched here — they are genuine, logically-referenced declarations.
///
/// Additionally skips the specific Mathlib `CompileInductive` / `MemoFix`
/// runtime-impl artifacts identified by [`is_compile_inductive_impl_artifact`].
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

/// Whether `name` is one of the specific private `Float` runtime-impl /
/// equation-spec artifacts the Mathlib `CompileInductive` TOOLING module emits:
/// `Float.{mkImpl,valImpl,mk_eq,val_eq}`.
///
/// These reference the erased spec type `FloatSpec.float`, which is NOT
/// reconstructable from a type-only import — Lean's own kernel re-checks them at
/// definition time with the real `rfl` bodies a type-only import does not carry.
/// They previously surfaced as masked-fallback "Eq vs Eq" / "Pi vs Pi" rows
/// (measured `Nat vs FloatSpec.float`, a genuinely non-closeable mismatch —
/// accepting it would be UNSOUND). Skipping them is denominator bookkeeping
/// (skip-not-fail); zero constants registered, zero axioms admitted, no kernel
/// path touched.
///
/// SOUNDNESS / CRITICAL GUARD — why this is scoped to EXACT artifact suffixes:
///
/// - NOT the whole `_private.Mathlib.Util.CompileInductive.` namespace: that
///   broader scope would also drop GENUINE, kernel-verified helpers — e.g.
///   `_private.…CompileInductive.1.Mathlib.Util.addAndCompile'`, which the PUBLIC
///   `Mathlib.Util.compileDefn` references; filtering it regresses `compileDefn`
///   to "Unknown constant".
///
/// - The `MemoFix` artifacts are deliberately NOT matched: although
///   `memoFixImplObj` / `ObjectMap` are themselves unreconstructable, the genuine
///   KERNEL-VERIFIED `_private.…MemoFix.1.memoFixImpl` references `memoFixImplObj`
///   — filtering it would regress `memoFixImpl` to "Unknown constant". Likewise
///   the `_@.…CompileInductive._hyg` macro-scope recursor copies are NOT matched
///   (they are byte-identical copies of already-verified recursors that mostly
///   kernel-verify; removing them would LOWER the honest KV rate).
///
/// All of the above was empirically validated against the Util subtree: every
/// name matched here is a genuinely-failing artifact with NO genuine dependent.
/// The `Lean.Export.*` / `Mathlib.Tactic.Superscript` rows are genuine structures
/// (a separate reconstruction bug, out of scope) and are NOT matched.
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

/// Whether an already-registered constant is a value-free `Axiom` carrier stub
/// — the shape the import prelude uses for typeclass *carrier* heads
/// (`Membership`, …) it pre-registers so hand-rolled instances resolve before
/// any library loads.
///
/// SOUNDNESS: a `true` result means the constant is an opaque, value-free
/// `Axiom`. Replacing it with the genuine kernel-checked inductive of the same
/// name (the only caller — and only when the *incoming* constant is an
/// `Inductive`) is a strict trust IMPROVEMENT: an unchecked assumption is
/// swapped for a checked declaration, removing a phantom domain axiom from
/// `axiom_deps`. It can never admit a new axiom.
fn is_axiom_carrier_stub(existing: &clean_kernel::env::ConstantInfo) -> bool {
    matches!(existing.kind, clean_kernel::env::ConstantKind::Axiom) && existing.value.is_none()
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

/// Merge a clean payload (serialized kernel objects) into the environment.
///
/// Returns (added_count, duplicate_count, structural_rejections).
fn load_clean_payload(
    env: &mut Environment,
    payload: &CleanPayload,
    origin: Option<&ConstantOrigin>,
    added_acc: &mut Vec<Name>,
    import_kinds: super::ImportKinds,
) -> (usize, usize, Vec<SkippedConstant>) {
    // HYBRID (Phase-1 zero-copy): under `InductiveFamiliesOnly` the payload's
    // definitional constants (`payload.constants`) are served lazily, so only the
    // inductive families below are registered eagerly from the payload.
    let inductive_families_only = matches!(import_kinds, super::ImportKinds::InductiveFamiliesOnly);
    let mut added = 0usize;
    let mut duplicates = 0usize;
    let mut structural_rejections = Vec::new();

    let mut inductives = filter_payload_dups(
        &payload.inductives,
        |ind| env.get_inductive(&ind.name).is_some(),
        &mut duplicates,
    );
    let inductive_origin_names: Vec<_> = inductives.iter().map(|ind| ind.name.clone()).collect();
    added += inductives.len();
    env.extend_inductives_unchecked(inductives.drain(..));
    tag_inserted_constants(env, origin, inductive_origin_names, added_acc);

    let mut constructors = filter_payload_dups(
        &payload.constructors,
        |c| env.get_constructor(&c.name).is_some(),
        &mut duplicates,
    );
    let constructor_origin_names: Vec<_> = constructors.iter().map(|c| c.name.clone()).collect();
    added += constructors.len();
    env.extend_constructors_unchecked(constructors.drain(..));
    tag_inserted_constants(env, origin, constructor_origin_names, added_acc);

    let mut recursors = filter_payload_dups(
        &payload.recursors,
        |r| env.get_recursor(&r.name).is_some(),
        &mut duplicates,
    );
    let recursor_origin_names: Vec<_> = recursors.iter().map(|r| r.name.clone()).collect();
    added += recursors.len();
    env.extend_recursors_unchecked(recursors.drain(..));
    tag_inserted_constants(env, origin, recursor_origin_names, added_acc);

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
        // but NOT confirmed well-typed (no value:type / type-is-a-Sort check). SCOPE: covers
        // payload.constants only; payload.inductives/constructors/recursors above are registered
        // via extend_*_unchecked (no structural check at all). Why tolerated: a CleanPayload is
        // Clean's own re-serialization of kernel ConstantInfos already type-checked on export (a
        // definition-reuse cache), tagged ConstantOrigin::CleanPayload (Unpinned) in the trust
        // ledger. Residual trust: no authenticity/hash check (OleanImportPolicy is admission-only),
        // so a tampered-but-structurally-valid trailer is admitted with its type/value intact.
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

    for (struct_name, fields) in &payload.structure_fields {
        if env.get_structure_field_names(struct_name).is_some() {
            duplicates += 1;
            continue;
        }
        if env
            .register_structure_fields(struct_name.clone(), fields.clone())
            .is_err()
        {
            duplicates += 1;
        }
    }

    (added, duplicates, structural_rejections)
}

fn load_extension_entries(
    env: &mut Environment,
    module_idx: usize,
    extensions: &[ParsedExtension],
) -> Result<(), ImportError> {
    for extension in extensions {
        if extension.extension_name.is_empty() {
            continue;
        }
        let extension_name = Name::interned(&extension.extension_name);
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
            if let ParsedExtensionEntry::Named { name, data } = entry {
                let data = match data {
                    ParsedExtensionEntryData::Scalar(value) => {
                        EnvExtensionEntryData::Scalar(*value)
                    }
                    ParsedExtensionEntryData::Object(bytes) => {
                        EnvExtensionEntryData::Object(bytes.clone())
                    }
                };

                converted.push(EnvExtensionEntry {
                    name: Name::interned(name),
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

/// Register the DECODED real-Lean `@[instance]` entries of a module into the
/// kernel instance registry (#olean-env-ext-restore, increment 1).
///
/// Real Lean `.olean`s persist each `@[instance]` registration in
/// `Lean.Meta.instanceExtension` as a `ScopedEnvExtension.Entry InstanceEntry`
/// object. The binary reader decodes those into
/// [`ParsedExtensionEntry::Instance`] (instance name, priority, attrKind,
/// scope); this bridge registers them through [`Environment::register_instance`]
/// with their REAL priority (Lean default 1000) — unlike the shape heuristic
/// [`register_class_typed_definitions_as_instances`], which fabricates
/// `DEFAULT_INSTANCE_PRIORITY` (100) for everything it registers. Running this
/// bridge FIRST therefore (a) guarantees every persisted `@[instance]` is in
/// the table even where the heuristic's shape filter would drop it, and
/// (b) ranks real instances above heuristic backfill in
/// `resolve_instance`'s priority-first candidate order — the Lean-faithful
/// preference — while the heuristic (which skips already-registered names)
/// continues to backfill, so no candidate that resolved before is lost.
///
/// Faithfulness rules (never fabricate, degrade inert):
/// - an entry whose constant is absent from the environment is skipped;
/// - the class is derived from the instance's own type conclusion head
///   (authoritative — the persisted entry does not carry the class name);
///   a non-`Const` head skips the entry;
/// - an unregistered class head is registered with its Π-arity as
///   `num_params` and empty out-params, exactly as the heuristic does today
///   (real out-params arrive with the `Lean.classExtension` increment);
/// - `scoped instance` entries are registered like global ones for now:
///   Clean has no namespace-activation notion and the shape heuristic
///   already surfaces them today, so this preserves the status-quo
///   over-approximation rather than silently dropping them (`attr_kind` /
///   `scope_ns` stay available on the parsed entry for a future increment).
///
/// SOUNDNESS: instance registrations are elaboration metadata — they steer
/// which candidate `resolve_instance` tries first; every synthesized term is
/// still kernel-checked by the caller. A wrong or extra entry can only cost
/// completeness/parity, never admit a false proof.
fn register_real_instance_entries(env: &mut Environment, extensions: &[ParsedExtension]) {
    // Collect (name, priority, synthOrder) tuples first so nothing borrows
    // `extensions` while `env` is mutated.
    let decoded: Vec<(Name, u32, Vec<usize>)> = extensions
        .iter()
        .filter(|ext| ext.extension_name == LEAN_INSTANCE_EXTENSION)
        .flat_map(|ext| ext.entries.iter())
        .filter_map(|entry| match entry {
            ParsedExtensionEntry::Instance(inst) => {
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
                    Name::interned(&inst.instance_name),
                    u32::try_from(inst.priority).unwrap_or(u32::MAX),
                    synth_order,
                ))
            }
            _ => None,
        })
        .collect();

    for (name, priority, synth_order) in decoded {
        // Idempotent across repeated/overlapping loads (base + companion
        // parts re-list the same entries) and first-writer-wins vs the
        // heuristic backfill, which runs after this bridge.
        if env.is_instance(&name) {
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

/// Register the DECODED real-Lean type-class declarations of a module into the
/// kernel class registry with their real `outParams`
/// (#olean-env-ext-restore, lane-B increment 2).
///
/// Real Lean `.olean`s persist every `class` declaration in
/// `Lean.classExtension` as a `ClassEntry` (name + `outParams` + `outLevelParams`);
/// the binary reader decodes those into [`ParsedExtensionEntry::Class`]. Two
/// things this bridge fixes over the pre-decoder state:
///
/// 1. **Instance-less classes now exist.** The heuristic
///    ([`register_class_typed_definitions_as_instances`]) and the increment-1
///    instance bridge only ever materialize a class as the *conclusion head of
///    some imported instance*, so a class with no imported instance (e.g.
///    `Membership` after `Init.Prelude`) was entirely absent — `is_class`
///    returned `false`. This bridge registers every persisted `ClassEntry`,
///    instance-bearing or not.
/// 2. **Real `outParams`.** Both the heuristic and the increment-1 bridge
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
    extensions: &[ParsedExtension],
) -> Vec<String> {
    // Collect (name, out_params) tuples first so nothing borrows `extensions`
    // while `env` is mutated.
    let decoded: Vec<(Name, Vec<usize>)> = extensions
        .iter()
        .filter(|ext| ext.extension_name == LEAN_CLASS_EXTENSION)
        .flat_map(|ext| ext.entries.iter())
        .filter_map(|entry| match entry {
            ParsedExtensionEntry::Class(class) => {
                // Binder indices always fit in usize on supported targets; a
                // (theoretical) overflowing index saturates and is then
                // rejected by the arity check below, never mis-registered.
                let out_params = class
                    .out_params
                    .iter()
                    .map(|&i| usize::try_from(i).unwrap_or(usize::MAX))
                    .collect();
                Some((Name::interned(&class.name), out_params))
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
        let class = env
            .get_const(&name)
            .and_then(|c| instance_conclusion_class(&c.type_))
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

    // Heuristic fallback for real Lean `.olean`s whose `instanceExtension` Clean
    // cannot parse (the entries carry Lean's `InstanceEntry` layout, so the names
    // never reach the typed state above): register every imported DEFINITION
    // whose type's conclusion head is an already-registered class. Structurally
    // that is exactly what a typeclass instance is, so this surfaces the stdlib
    // `@[instance]`s (e.g. `instDecidableEqList`, `List.hasDecEq`) for resolution.
    // SOUNDNESS: only consts with a real `value` are considered (axiom / `sorry`
    // stubs are excluded, so no unsound instance can be synthesized), and every
    // resolved proof term is re-checked by the kernel in `close_goal`; an extra
    // candidate can only cost completeness, never admit a false proof. It can
    // over-register a non-`@[instance]` class-typed def, which is harmless.
    register_class_typed_definitions_as_instances(env);
}

/// See `register_instances_from_extension`: register imported DEFINITIONS whose
/// type concludes in a registered class as instances of that class. Skips axiom
/// stubs (no `value`) and already-registered instances.
fn register_class_typed_definitions_as_instances(env: &mut Environment) {
    // Collect (name, class) first so the immutable `constants()` borrow is
    // released before the mutable `register_instance` calls.
    // Instances are `Definition`s OR `Theorem`s: a `Prop`-valued class such as
    // `LawfulBEq`/`DecidableEq`-lawfulness has THEOREM-kind instances (they are
    // proofs), and excluding them breaks every downstream instance that defers to
    // them — e.g. `List.instDecidableMemOfLawfulBEq` needs `[LawfulBEq α]`, so
    // without LawfulBEq instances `a ∈ l` decidability never resolves. We must
    // NOT widen to `!= Axiom`: `Axiom` is excluded (Clean's `sorry`/skipped-const
    // stubs). NOTE: the kind filter alone does NOT exclude `Constructor`s /
    // `Inductive`s / `Recursor`s — `ConstantKind` cannot represent them, so their
    // imported `ConstantInfo` mirrors default to `Definition`; the per-kind
    // registry checks inside the filter below handle those. Imported decls may
    // carry no `value` (served lazily by the zero-copy import path), so we must
    // NOT filter on `value`.
    use clean_kernel::env::ConstantKind;
    // Enumerate OWNED constants AND the names served lazily by the zero-copy
    // `ConstantSource`: `env.constants()` walks only owned constants, but most
    // imported stdlib decls (including instances like
    // `List.instDecidableMemOfLawfulBEq`) are served lazily and are absent from
    // it — so scanning `constants()` alone silently misses them. `get_const`
    // materializes each on demand (and applies the serve gate → `None` for
    // unverified shards, which we skip).
    let mut all_names: Vec<Name> = env.constants().map(|c| c.name.clone()).collect();
    all_names.extend(env.lazy_source_names());
    all_names.sort_by_cached_key(|a| a.to_string());
    all_names.dedup();
    let candidates: Vec<(Name, Name)> = all_names
        .into_iter()
        .filter_map(|name| {
            let c = env.get_const(&name)?;
            if !matches!(c.kind, ConstantKind::Definition | ConstantKind::Theorem) {
                return None;
            }
            // The `ConstantKind` filter above cannot exclude imported
            // constructors / recursors / inductives on its own:
            // `ConstantKind` has no variants for them, so the `.olean` import
            // registers their `ConstantInfo` mirror with the DEFAULT kind
            // (`Definition` — see `register_constructor` /
            // `register_recursor`). That let `Decidable.isFalse {p} (h : ¬p) :
            // Decidable p` into the instance table, where it matched EVERY
            // `Decidable _` goal and leaked its un-synthesizable `¬p` proof
            // binder as an unassigned metavariable (kernel: "Declaration
            // contains free variables" — the trust-ir bridge blocker on the
            // guarded `semIntBinOp` arms). Constructors are never instances in
            // Lean unless explicitly `@[instance]`-attributed (which lean-core
            // never does for constructors), so consult the authoritative
            // per-kind registries directly.
            if env.get_constructor(&name).is_some()
                || env.get_recursor(&name).is_some()
                || env.get_inductive(&name).is_some()
            {
                return None;
            }
            valid_instance_class(&c.type_).map(|class| (name, class))
        })
        .collect();

    // Pass 1: register each instance's conclusion-head class (e.g. `BEq`,
    // `LawfulBEq`, `Fintype`) that names a const but isn't a registered class
    // yet, so `resolve_instance` will both consult its instances and discharge
    // OTHER instances' deferred `[BEq α]`/… arguments (real Lean `.olean`s carry
    // these in Lean's `classExtension`, which Clean can't decode — same gap as
    // the instances). `num_params` is the Π-arity of the class's type up to its
    // `Sort` result; out-params are left empty (correct for the decidability /
    // `BEq` family; at most a minor completeness cost for out-param classes).
    let mut head_classes: Vec<Name> = candidates.iter().map(|(_, c)| c.clone()).collect();
    head_classes.sort_by_cached_key(|a| a.to_string());
    head_classes.dedup();
    for class in head_classes {
        if env.is_class(&class) {
            continue;
        }
        if let Some(num_params) = class_param_arity(env, &class) {
            env.register_class(KernelClassInfo {
                name: class,
                num_params,
                out_params: Vec::new(),
                semi_out_params: Vec::new(),
            });
        }
    }

    // Pass 2: register the instances now that their classes exist.
    for (name, class) in candidates {
        if env.is_class(&class) && !env.is_instance(&name) {
            env.register_instance(KernelInstanceInfo {
                name,
                class_name: class,
                priority: clean_kernel::env::DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        }
    }
}

/// Like `instance_conclusion_class`, but ALSO validates that the const can serve
/// as a resolvable instance. The danger case is a binder that resolution can
/// neither UNIFY (it does not occur in the conclusion) nor SYNTHESIZE (its type
/// is not a class) — a genuine explicit HYPOTHESIS, e.g. `Decidable.isTrue
/// {p}(h:p):Decidable p`, whose proof `h : p` is absent from `Decidable p`.
/// Registering such a const lets resolution pick it for any goal of the class and
/// leave `h` an unassigned metavariable (a `Decidable.isTrue` that fails kernel
/// checking). We reject a `Default` binder that is BOTH absent from the
/// conclusion AND has a non-`Const`-headed type (i.e. a local prop `h : p`, head
/// `BVar p`). We KEEP binders whose type head is a `Const`: those are class/type
/// arguments (`[BEq α]`, `[LawfulBEq α]`, `[DecidableEq α]`) that resolution
/// discharges recursively — without this, every typeclass-constrained instance
/// (e.g. `List.instDecidableMemOfLawfulBEq`) is wrongly dropped. A wrongly-kept
/// non-class `Const` arg (e.g. `h : ¬p` — `Not`-headed, so it passes this
/// filter) fails resolution later: `resolve_instance`'s candidate-hygiene check
/// rejects any candidate whose binder metavariables end the search undetermined
/// (no false-accept; the kernel re-checks every proof). Genuine instances like
/// `List.decidableMem {α}[BEq α](a)(l):Decidable (a∈l)` are kept (a, l appear;
/// `[BEq α]` is Const).
fn valid_instance_class(ty: &Expr) -> Option<Name> {
    let mut binders: Vec<(BinderInfo, Expr)> = Vec::new();
    let mut conclusion = ty;
    while let ExprKind::Pi(bd, bty, body) = conclusion.kind() {
        binders.push((bd.info, (**bty).clone()));
        conclusion = body;
    }
    let class = match conclusion.get_app_fn().kind() {
        ExprKind::Const(name, _) => name.clone(),
        _ => return None,
    };
    // Binder at outermost position `p` of `n` is `BVar(n-1-p)` in the conclusion.
    let n = binders.len();
    for (p, (info, bty)) in binders.iter().enumerate() {
        if *info == BinderInfo::Default
            && !mentions_bvar(conclusion, (n - 1 - p) as u32)
            && !matches!(bty.get_app_fn().kind(), ExprKind::Const(..))
        {
            return None;
        }
    }
    Some(class)
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

/// True if `expr` references the de-Bruijn binder at outer index `target`
/// (0 = innermost binder of the enclosing telescope); indices shift by the
/// number of binders entered within `expr`.
fn mentions_bvar(expr: &Expr, target: u32) -> bool {
    match expr.kind() {
        ExprKind::BVar(idx) => *idx == target,
        ExprKind::App(f, a) => mentions_bvar(f, target) || mentions_bvar(a, target),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            mentions_bvar(ty, target) || mentions_bvar(body, target + 1)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            mentions_bvar(ty, target)
                || mentions_bvar(val, target)
                || mentions_bvar(body, target + 1)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => mentions_bvar(inner, target),
        _ => false,
    }
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

/// If `expr` is a projection-function body — `λ params. Proj(S, i, self)`
/// (optionally under transparent `MData`) — return the projected structure name
/// `S` and the 0-based field index `i`. Returns `None` for anything else.
///
/// This is the same value-shape [`super::convert::is_projection_fn_body`]
/// detects, but it recovers the target `(S, i)` rather than a bare bool.
fn projection_fn_target(expr: &Expr) -> Option<(Name, u32)> {
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

/// Recover structure field-name metadata for single-constructor structures /
/// classes from their already-loaded PROJECTION FUNCTIONS.
///
/// Real Mathlib `.olean`s do not carry Lean's `structureExt` in a form Clean
/// decodes, so an imported structure/class (`Monoid`, `MulOneClass`,
/// `Semigroup`, …) lands in the kernel with NO field-name table
/// ([`Environment::get_structure_field_names`] → `None`). The consumer of that
/// table — clean-auto's typeclass-projection law lane
/// (`collect_instance_projection_laws`, guarded on `field_names.is_some()`) —
/// then skips every imported class, so its projection laws (`mul_one`,
/// `mul_assoc`, …) never surface for real Mathlib.
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
        let Some(field) = c.name.last_component() else {
            continue;
        };
        let field = Name::from_string(&field);
        // Keep only the CANONICAL projection `S.<field>` (prefix == projected
        // structure). This is exactly Lean's projection naming and rules out an
        // unrelated `Foo.bar := fun s => s.i` that happens to project `S`.
        if Name::append(&struct_name, &field.to_string()) != c.name {
            continue;
        }
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

    // Final pass: register. `register_structure_fields` re-validates count ==
    // constructor field count and uniqueness; on mismatch it errors and we skip.
    for (struct_name, fields) in to_register {
        let _ = env.register_structure_fields(struct_name, fields);
    }
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
pub fn load_parsed_module(
    env: &mut Environment,
    module: &ParsedModule,
    module_name: Option<String>,
) -> Result<LoadSummary, ImportError> {
    load_parsed_module_with_import_policy(env, module, module_name, OleanImportPolicy::default())
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

/// Internal: load a parsed module using an externally-owned intern cache.
///
/// When the cache already contains entries from prior modules, expressions
/// shared across modules (e.g. `Nat`, `Prop`, `BVar(0)`) are deduplicated
/// across the entire dependency graph, not just within a single module (#2383).
pub(super) fn load_parsed_module_with_cache(
    env: &mut Environment,
    module: &ParsedModule,
    module_name: Option<String>,
    intern_cache: &mut ExprInternCache,
) -> Result<LoadSummary, ImportError> {
    load_parsed_module_with_cache_and_policy(
        env,
        module,
        module_name,
        intern_cache,
        OleanImportPolicy::default(),
    )
}

pub(super) fn load_parsed_module_with_cache_and_policy(
    env: &mut Environment,
    module: &ParsedModule,
    module_name: Option<String>,
    intern_cache: &mut ExprInternCache,
    policy: OleanImportPolicy,
) -> Result<LoadSummary, ImportError> {
    policy.check_parsed_module(module, module_name.as_deref())?;
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
            &mut summary.added_names,
            policy.import_kinds(),
        );
        summary.added_constants += added;
        summary.duplicate_constants += duplicates;
        summary.skipped_constants.extend(rejected);
    }

    let mut duplicate_filtered = 0usize;
    let mut cstage_skipped: Vec<SkippedConstant> = Vec::new();
    let mut upgrade_indices: Vec<usize> = Vec::new();
    let mut discharge_stub_names: Vec<Name> = Vec::new();
    let constants: Vec<_> = module
        .constants
        .iter()
        .enumerate()
        .filter(|(_i, c)| !c.name.is_empty() || c.type_.is_some())
        .filter(|(_i, c)| {
            // SOUNDNESS: skip code-generator artifacts — see is_compiler_ir_name.
            if is_compiler_ir_name(&c.name) {
                cstage_skipped.push(SkippedConstant {
                    name: c.name.clone(),
                    reason: "compiler/code-generator artifact (not kernel-checkable)".to_string(),
                });
                return false;
            }
            true
        })
        .filter(|(i, c)| {
            let name = Name::interned(&c.name);
            let exists_as_const = env.get_const(&name);
            let exists_other = env.get_inductive(&name).is_some()
                || env.get_constructor(&name).is_some()
                || env.get_recursor(&name).is_some();
            if exists_other {
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
                    && is_axiom_carrier_stub(existing)
                {
                    discharge_stub_names.push(name);
                    return true;
                }
                // Axiom upgrade: .olean.private provides value for base .olean's
                // axiom stub (Lean 4.29+ module system). Part of #3134.
                if existing.value.is_none() && c.value.is_some() {
                    upgrade_indices.push(*i);
                    return false;
                }
                duplicate_filtered += 1;
                return false;
            }
            true
        })
        .map(|(_i, c)| c)
        .collect();

    summary.duplicate_constants += duplicate_filtered;
    summary.skipped_constants.extend(cstage_skipped);

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
    let converted: Vec<ConvertedConstant> = constants
        .into_iter()
        // HYBRID (Phase-1 zero-copy): under `InductiveFamiliesOnly` the definitional
        // kinds are served by the lazy `ShardConstantSource`; never build their owned
        // `Arc<Expr>` (the memory win). `convert_parsed_constant` only ever maps these
        // to the `Other` bucket, which `register_converted_constants` already drops, so
        // filtering here removes pure waste — the registered SET is unchanged.
        .filter(|c| !inductive_families_only || is_inductive_family_kind(&c.kind))
        .map(|c| convert_parsed_constant(c, intern_cache, policy.proof_elision()))
        .collect();

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
    );

    // Upgrade axiom stubs with definitions from .olean.private (#3134).
    // HYBRID (Phase-1 zero-copy): the axiom-stub upgrade restores `Definition`
    // VALUES (a definitional kind). Under `InductiveFamiliesOnly` the definitional
    // kinds are served lazily, so eagerly upgrading them here would defeat the
    // memory win and double-register a name the lazy source already covers — skip.
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
                    if info.value.is_some() && policy.proof_elision().elides(info.kind) {
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
        let upgraded = env.upgrade_axiom_stubs(upgrade_others.into_iter());
        summary.added_constants += upgraded;
    }

    if !module.entries.is_empty() {
        summary.extension_undecoded_entries =
            module.entries.iter().map(|ext| ext.undecoded_entries).sum();
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
        // priorities BEFORE the heuristic bridges below, so real instances win
        // first-writer registration and outrank heuristic backfill
        // (#olean-env-ext-restore).
        register_real_instance_entries(env, &module.entries);
        // Recover structure/class field-name tables from the loaded projection
        // functions so the typeclass-projection law lane fires on real Mathlib
        // classes (raw `.olean`s carry no Clean-decodable `structureExt`)
        // (#olean-structure-field-names).
        register_structure_fields_from_projections(env);
        // Re-register imported typeclass instances into the kernel registry so
        // the elaborator's instance synthesis can see them (#instance-import).
        register_instances_from_extension(env);
        // Re-register imported `@[simp]` lemmas into the kernel registry so the
        // simp tactic can use them (#simp-import).
        register_simp_lemmas_from_extension(env);
        // Materialize imported reducibility attributes (`@[reducible]`,
        // `@[irreducible]`, `@[semireducible]`) into the kernel's per-constant
        // reducibility state so delta-reduction transparency is faithful
        // (#attr-import).
        register_attributes_from_extension(env);
    }

    Ok(summary)
}

/// Load a `LoadModule` into the environment using direct binary-to-Expr conversion (#2428).
///
/// This is the fast path: expressions are converted directly from binary data
/// to kernel `Expr` without materializing intermediate `ParsedExpr` trees.
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
    policy.check_load_module(module, module_name.as_deref())?;
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
            &mut summary.added_names,
            policy.import_kinds(),
        );
        summary.added_constants += added;
        summary.duplicate_constants += duplicates;
        summary.skipped_constants.extend(rejected);
    }

    let mut duplicate_filtered = 0usize;
    let mut cstage_skipped: Vec<SkippedConstant> = Vec::new();
    let mut upgrade_indices: Vec<usize> = Vec::new();
    let mut discharge_stub_names: Vec<Name> = Vec::new();
    let constants: Vec<_> = module
        .constants
        .iter()
        .enumerate()
        .filter(|(_i, c)| !c.name.is_empty() || c.type_ptr != 0)
        .filter(|(_i, c)| {
            // SOUNDNESS: skip code-generator artifacts — see is_compiler_ir_name.
            if is_compiler_ir_name(&c.name) {
                cstage_skipped.push(SkippedConstant {
                    name: c.name.clone(),
                    reason: "compiler/code-generator artifact (not kernel-checkable)".to_string(),
                });
                return false;
            }
            true
        })
        .filter(|(i, c)| {
            let name = Name::interned(&c.name);
            // Check if this constant already exists in any registration table
            let exists_as_const = env.get_const(&name);
            let exists_other = env.get_inductive(&name).is_some()
                || env.get_constructor(&name).is_some()
                || env.get_recursor(&name).is_some();
            if exists_other {
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
                    && is_axiom_carrier_stub(existing)
                {
                    discharge_stub_names.push(name);
                    return true;
                }
                // Axiom upgrade: .olean.private provides value for base .olean's
                // axiom stub (Lean 4.29+ module system). Part of #3134.
                if existing.value.is_none() && c.value_ptr != 0 {
                    upgrade_indices.push(*i);
                    return false; // handle separately via upgrade path
                }
                duplicate_filtered += 1;
                return false;
            }
            true
        })
        .map(|(_i, c)| c)
        .collect();

    summary.duplicate_constants += duplicate_filtered;
    summary.skipped_constants.extend(cstage_skipped);

    // Discharge the opaque prelude carrier stubs whose genuine inductive is about
    // to register (collected above), after the immutable borrow of `env` ends.
    discharge_carrier_stubs(env, &discharge_stub_names);

    // Reconstruct the compacted region from the owned bytes
    let region = module.region();

    // Convert constants using direct binary-to-Expr path
    let cache_size_before: u64 = intern_cache.total_entries;
    let inductive_families_only = policy.inductive_families_only();
    let converted: Vec<ConvertedConstant> = constants
        .into_iter()
        // HYBRID (Phase-1 zero-copy): under `InductiveFamiliesOnly` the definitional
        // kinds are served by the lazy `ShardConstantSource`; never build their owned
        // `Arc<Expr>` (the memory win). See the ParsedModule path for the soundness note.
        .filter(|c| !inductive_families_only || is_inductive_family_kind(&c.kind))
        .map(|c| convert_load_constant(c, &region, intern_cache, policy.proof_elision()))
        .collect();

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
    );

    // Record Lean's `DefinitionSafety::Unsafe` flag for every `unsafe def` in
    // the module (trusted eager import). Lean's kernel structurally bars safe
    // decls from referencing unsafe ones upstream, and Clean's default checker
    // keeps `allow_unsafe = true`, so this is pure bookkeeping here — it lets
    // strict checkers (`TypeChecker::set_allow_unsafe(false)`) and trust
    // reporting see the flag instead of silently upgrading `unsafe` to safe.
    for c in &module.constants {
        if c.definition_safety == Some(DefinitionSafety::Unsafe) {
            env.mark_unsafe(Name::interned(&c.name));
        }
    }

    // Upgrade axiom stubs with definitions from .olean.private (#3134).
    // When Lean 4.29+ exports definitions as axiom stubs in the base .olean,
    // the full definitions (with values) are in .olean.private. Replace the
    // stubs so the type checker can unfold these definitions.
    // HYBRID (Phase-1 zero-copy): the upgrade restores `Definition` VALUES, a
    // definitional kind served lazily under `InductiveFamiliesOnly`; skip it then
    // so the lazy source remains the single owner of the definitional kinds.
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
                convert_load_constant(
                    &module.constants[i],
                    &region,
                    intern_cache,
                    ProofValueElision::None,
                )
            })
            .collect();
        let mut upgrade_others = Vec::new();
        for cc in upgrade_converted {
            match cc {
                ConvertedConstant::Other(_name, Ok((decl, hints)), _stats) => {
                    let mut info = decl_to_constant_info(decl, hints);
                    if info.value.is_some() && policy.proof_elision().elides(info.kind) {
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
        let upgraded = env.upgrade_axiom_stubs(upgrade_others.into_iter());
        summary.added_constants += upgraded;
    }

    if !module.entries.is_empty() {
        summary.extension_undecoded_entries =
            module.entries.iter().map(|ext| ext.undecoded_entries).sum();
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
        // priorities BEFORE the heuristic bridges below, so real instances win
        // first-writer registration and outrank heuristic backfill
        // (#olean-env-ext-restore).
        register_real_instance_entries(env, &module.entries);
        // Recover structure/class field-name tables from the loaded projection
        // functions so the typeclass-projection law lane fires on real Mathlib
        // classes (raw `.olean`s carry no Clean-decodable `structureExt`)
        // (#olean-structure-field-names).
        register_structure_fields_from_projections(env);
        // Re-register imported typeclass instances into the kernel registry so
        // the elaborator's instance synthesis can see them (#instance-import).
        register_instances_from_extension(env);
        // Re-register imported `@[simp]` lemmas into the kernel registry so the
        // simp tactic can use them (#simp-import).
        register_simp_lemmas_from_extension(env);
        // Materialize imported reducibility attributes (`@[reducible]`,
        // `@[irreducible]`, `@[semireducible]`) into the kernel's per-constant
        // reducibility state so delta-reduction transparency is faithful
        // (#attr-import).
        register_attributes_from_extension(env);
    }

    Ok(summary)
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

    // Fixup: recompute is_large_elim
    {
        let mut ctor_map: HashMap<Name, Vec<Constructor>> = HashMap::new();
        for ctor in &ok_constructors {
            ctor_map
                .entry(ctor.inductive_name.clone())
                .or_default()
                .push(Constructor {
                    name: ctor.name.clone(),
                    type_: ctor.type_.clone(),
                });
        }
        for ind in &mut ok_inductives {
            let ctors = ctor_map.get(&ind.name).map(|v| v.as_slice()).unwrap_or(&[]);
            let num_types = ind.all_names.len();
            ind.is_large_elim =
                allows_large_elim(env, &ind.type_, ctors, ind.num_params, num_types);
        }
    }

    // Pass 1: Bulk register inductives
    let inductive_origin_names: Vec<_> = ok_inductives.iter().map(|ind| ind.name.clone()).collect();
    summary.added_constants += ok_inductives.len();
    env.extend_inductives_unchecked(ok_inductives.into_iter());
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
    summary.added_constants += ok_constructors.len();
    env.extend_constructors_unchecked(ok_constructors.into_iter());
    tag_inserted_constants(
        env,
        origin,
        constructor_origin_names,
        &mut summary.added_names,
    );

    // Pass 3: Bulk register recursors
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
        summary.added_constants += ok_recursors.len();
        env.extend_recursors_unchecked(ok_recursors.into_iter());
        tag_inserted_constants(env, origin, recursor_origin_names, &mut summary.added_names);
    }

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
    if inductive_families_only {
        return;
    }
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
        let rejected_names: HashSet<_> = rejected.iter().map(|(name, _)| name.clone()).collect();
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
    use super::{projection_fn_target, register_structure_fields_from_projections};
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
        let ctor_name = Name::append(name, "mk");
        env.extend_inductives_unchecked(std::iter::once(InductiveVal {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::type_(),
            num_params: 1,
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
            type_: Expr::type_(),
            num_params: 1,
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

    #[test]
    fn test_projection_fn_target_recovers_struct_and_index() {
        let s = Name::from_string("TestMonoid");
        let body = projection_value(&s, 2);
        assert_eq!(projection_fn_target(&body), Some((s, 2)));
        // A non-projection body yields None.
        assert_eq!(projection_fn_target(&Expr::type_()), None);
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
}
