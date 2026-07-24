// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coq kernel-declaration shard writers: route `TranslatedGlobalDecl` objects
//! from the clean-kernel Coq translator into `.mathverse` shard files.
//!
//! Two lanes with DIFFERENT trust semantics:
//!
//! 1. **Checked lane** — [`write_coq_decls_to_shard_checked`] (COQ-4). Every
//!    declaration is replayed through the Clean kernel
//!    ([`recheck_and_classify`] for constants, `Environment::add_inductive`
//!    for inductive families) and the shard header's `import_confidence` is
//!    stamped FROM THE VERDICT, never from the import route. Expressions flow
//!    through [`KernelShardBuilder`]'s faithful flattening (declaration-level
//!    universe params AND per-`Const` universe-level lists preserved).
//!
//!    **Trust encoding (pinned, COQ-4/COQ-5):**
//!    - `KernelVerified` **strictly ⇔** the declaration's value type-checked
//!      through the kernel's `add_decl` AND its transitive axiom closure is
//!      foundational-only (`⊆ FOUNDATIONAL_AXIOMS`) — the graduation-gate
//!      semantics, matching the repo's "prove" rules. Checked inductive
//!      families earn it through the checked `add_inductive` replay.
//!    - Type-checked but axiom-dependent ⇒ `Translated` + the named
//!      per-axiom [`AxiomProfile`] bits from
//!      [`crate::coq::axiom_map::coq_axiom_profile_bits`], with the sorted
//!      domain-axiom closure recorded in the metadata.
//!    - Univalence-dependent declarations are NEVER `KernelVerified`
//!      (COQ-5): a univalence taint implies a non-empty domain closure, so
//!      they land on the `Translated` lane carrying
//!      `AxiomProfile::UNIVALENCE`.
//!    - Kernel-rejected value-bearing declarations are written STATEMENT-ONLY
//!      (`Axiomatized` + `AxiomProfile::AXIOMATIZED`, value dropped) and are
//!      COUNTED in [`CoqShardMetadata::kernel_rejected`] — never silent.
//!
//! 2. **Legacy unchecked lane** — [`write_coq_decls_to_shard`]. Labels are
//!    import-route confidence ONLY (`Translated`/`Axiomatized` hardcoded by
//!    declaration kind); nothing is kernel-replayed and no axiom closure is
//!    computed. Kept for existing callers/tests; new pipelines must use the
//!    checked lane.
//!
//! [`opentheory_shard`]: crate::hol::opentheory_shard

use clean_kernel::coq_import::{ImportStats, TranslatedGlobalDecl};
use clean_kernel::inductive::InductiveDecl as KernelInductiveDecl;
use clean_kernel::{Declaration, Environment, Expr, Name};

use crate::coq::axiom_map::{coq_axiom_profile_bits, is_univalence_tainted};
use crate::error::{MathverseError, MathverseResult};
use crate::export::kernel_export::{InductiveFamilyMemberExport, KernelShardBuilder};
use crate::graduate::recheck::recheck_and_classify;
use crate::hol::opentheory_shard::lower_kernel_expr;
use crate::shard::{ShardReader, ShardWriter};
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
    NO_VALUE,
};

/// Metadata returned after writing Coq declarations to a shard.
#[derive(Clone, Debug, Default)]
pub struct CoqShardMetadata {
    /// Number of constant declarations (axioms, definitions, theorems, opaques)
    /// written.
    pub constants_written: usize,
    /// Number of inductive types written (each type within a mutual block
    /// counts separately).
    pub inductives_written: usize,
    /// Names of all written declarations.
    pub names: Vec<String>,
    /// Import statistics from the batch importer (optional context).
    pub import_stats: Option<ImportStats>,

    // --- Checked-lane verdict counts (COQ-4; always 0 on the legacy lane) ---
    /// Headers stamped `KernelVerified`: value type-checked with a
    /// foundational-only closure, or a checked inductive-family member
    /// (root/constructor/recursor re-earned through `add_inductive`).
    pub kernel_verified: usize,
    /// Value-bearing declarations that type-checked but whose transitive
    /// closure contains domain axioms: stamped `Translated` with named
    /// per-axiom profile bits.
    pub translated_axiom_dependent: usize,
    /// Genuine value-less axioms, stamped `Axiomatized`.
    pub axiomatized: usize,
    /// Declarations the kernel REJECTED (value failed `add_decl`, or an
    /// inductive family failed `add_inductive` / the single-type fence):
    /// written statement-only as `Axiomatized` + `AXIOMATIZED` and counted
    /// here as `(name, reason)` — the fail-closed, never-silent lane.
    pub kernel_rejected: Vec<(String, String)>,
    /// Per-declaration sorted transitive domain-axiom closure, for every
    /// declaration on the `Translated` (axiom-dependent) lane.
    pub domain_axioms: std::collections::BTreeMap<String, Vec<String>>,
}

impl CoqShardMetadata {
    /// Total declarations written.
    #[must_use]
    pub fn total(&self) -> usize {
        self.constants_written + self.inductives_written
    }
}

/// A checked Coq shard: the serialized shard bytes plus the verdict metadata.
///
/// The bytes are final (verdict-derived confidence bytes and closed axiom
/// profiles already applied); persist with `std::fs::write` or reopen with
/// [`ShardReader::from_bytes`].
#[derive(Clone, Debug)]
pub struct CheckedCoqShard {
    /// Serialized `.mathverse` shard bytes.
    pub shard_bytes: Vec<u8>,
    /// Verdict counts and per-declaration audit data.
    pub metadata: CoqShardMetadata,
}

// ---------------------------------------------------------------------------
// Checked lane (COQ-4)
// ---------------------------------------------------------------------------

/// Kernel-checked Coq shard writer: replay every declaration through the
/// Clean kernel and stamp `import_confidence` from the VERDICT (see the
/// module docs for the pinned trust encoding).
///
/// `decls` MUST be in dependency order (each declaration after everything it
/// references) — the natural emission order of the sertop extraction lane.
/// This is fail-closed, not trust-critical: an out-of-order declaration
/// simply fails its kernel re-check (missing dependency) and is written
/// statement-only + counted in [`CoqShardMetadata::kernel_rejected`].
///
/// On success every checked declaration REMAINS in `env` (the
/// [`recheck_and_classify`] contract), so callers can thread one environment
/// through multiple batches. A kernel-rejected declaration is NOT seeded into
/// `env` — its dependents fail closed too, rather than inheriting a silently
/// axiomatized dependency.
///
/// Mutual inductive blocks (`types.len() > 1`) are fail-closed
/// statement-only: the shard family format is single-type (graduation v3
/// fence), so a mutual block cannot be represented in a way the verify-side
/// checked replay could re-earn.
///
/// Returns an error only for infrastructure failures (expression flattening,
/// serialization); per-declaration kernel rejections are counted, never
/// silent and never fatal to the batch.
pub fn write_coq_decls_to_shard_checked(
    decls: &[TranslatedGlobalDecl],
    env: &mut Environment,
) -> MathverseResult<CheckedCoqShard> {
    let mut builder = KernelShardBuilder::new().with_source_system(SourceSystem::Coq);
    let mut metadata = CoqShardMetadata::default();
    // Verdict-derived per-constant stamps, applied after all adds:
    // `set_constant_axiom_profile` REPLACES the builder's name-heuristic bits
    // (zero-then-set), then `finalize_axiom_profiles` closes them in-shard.
    let mut profile_overrides: Vec<(u32, AxiomProfile)> = Vec::new();
    // `KernelShardBuilder` mints `KernelVerified` from `has_value` alone;
    // axiom-dependent value-bearing decls must be DOWNGRADED to `Translated`
    // in a post-pass over the serialized headers (the builder exposes no
    // per-index confidence setter).
    let mut confidence_overrides: Vec<(u32, ImportConfidence)> = Vec::new();

    for decl in decls {
        match decl {
            TranslatedGlobalDecl::Constant(d) => {
                write_constant_checked(
                    d,
                    env,
                    &mut builder,
                    &mut metadata,
                    &mut profile_overrides,
                    &mut confidence_overrides,
                )?;
            }
            TranslatedGlobalDecl::Inductive(ind) => {
                write_inductive_checked(
                    ind,
                    env,
                    &mut builder,
                    &mut metadata,
                    &mut profile_overrides,
                )?;
            }
        }
    }

    // Zero the heuristic bits, install the verdict bits, then close the
    // profiles over the in-shard dependency graph exactly once (the
    // graduation intake shard-write discipline).
    for (idx, profile) in &profile_overrides {
        if !builder
            .shard_writer_mut()
            .set_constant_axiom_profile(*idx, *profile)
        {
            return Err(MathverseError::Kernel(format!(
                "coq checked writer: axiom-profile override index {idx} out of range"
            )));
        }
    }
    builder.shard_writer_mut().finalize_axiom_profiles();

    let bytes = builder.write_to_bytes()?;
    let shard_bytes = if confidence_overrides.is_empty() {
        bytes
    } else {
        // Byte-faithful confidence stamp pass (the documented
        // `ShardWriter::from_reader` copy-flip-rewrite pattern): flip ONLY the
        // `import_confidence` byte of the downgraded headers.
        let mut reader = ShardReader::from_bytes(&bytes)?;
        for (idx, confidence) in &confidence_overrides {
            let header = reader.constants.get_mut(*idx as usize).ok_or_else(|| {
                MathverseError::Kernel(format!(
                    "coq checked writer: confidence override index {idx} out of range"
                ))
            })?;
            header.import_confidence = *confidence as u8;
        }
        let writer = ShardWriter::from_reader(&reader);
        let mut buf = Vec::new();
        writer.write(&mut buf)?;
        buf
    };

    Ok(CheckedCoqShard {
        shard_bytes,
        metadata,
    })
}

/// The name / level-params / type triple shared by all `Declaration` variants.
fn declaration_signature(decl: &Declaration) -> (&Name, &[Name], &Expr) {
    match decl {
        Declaration::Definition {
            name,
            level_params,
            type_,
            ..
        }
        | Declaration::Theorem {
            name,
            level_params,
            type_,
            ..
        }
        | Declaration::Opaque {
            name,
            level_params,
            type_,
            ..
        }
        | Declaration::Axiom {
            name,
            level_params,
            type_,
        } => (name, level_params, type_),
    }
}

/// Checked-lane constant: recheck through the kernel, stamp from the verdict.
fn write_constant_checked(
    decl: &Declaration,
    env: &mut Environment,
    builder: &mut KernelShardBuilder,
    metadata: &mut CoqShardMetadata,
    profile_overrides: &mut Vec<(u32, AxiomProfile)>,
    confidence_overrides: &mut Vec<(u32, ImportConfidence)>,
) -> MathverseResult<()> {
    let (name, _, _) = declaration_signature(decl);
    let name_str = name.to_string();
    let is_axiom_decl = matches!(decl, Declaration::Axiom { .. });

    match recheck_and_classify(env, decl.clone()) {
        Ok(verdict) => {
            if is_axiom_decl {
                // A genuine value-less axiom: the header is `Axiomatized`
                // (the builder's value-less classification is already
                // honest here) carrying its OWN named axiom bit plus the
                // trust-gating `AXIOMATIZED` bit.
                let idx = builder.add_declaration(decl, &[])?;
                profile_overrides.push((
                    idx,
                    coq_axiom_profile_bits(std::slice::from_ref(&name_str))
                        | AxiomProfile::AXIOMATIZED,
                ));
                metadata.axiomatized += 1;
            } else if verdict.is_foundational() && !is_univalence_tainted(&verdict.domain_axioms) {
                // KernelVerified strictly ⇔ value-typechecked AND
                // foundational-only closure. (`is_foundational` already
                // implies an empty domain closure — the explicit univalence
                // guard states the COQ-5 invariant in code: a
                // univalence-tainted closure can never reach this arm.)
                let idx = builder.add_declaration(decl, &[])?;
                profile_overrides.push((idx, AxiomProfile::NONE));
                metadata.kernel_verified += 1;
            } else {
                // Type-checked, but axiom-relative: `Translated` + the named
                // per-axiom bits, domain closure recorded for audit.
                let idx = builder.add_declaration(decl, &[])?;
                confidence_overrides.push((idx, ImportConfidence::Translated));
                profile_overrides.push((idx, coq_axiom_profile_bits(&verdict.domain_axioms)));
                metadata
                    .domain_axioms
                    .insert(name_str.clone(), verdict.domain_axioms.clone());
                metadata.translated_axiom_dependent += 1;
            }
        }
        Err(err) => {
            // Fail closed, never silent: statement-only `Axiomatized` entry
            // (value dropped) + counted with the kernel's reason.
            let idx = add_statement_only_axiomatized(builder, decl)?;
            profile_overrides.push((idx, AxiomProfile::AXIOMATIZED));
            metadata
                .kernel_rejected
                .push((name_str.clone(), err.reject_reason()));
        }
    }

    metadata.names.push(name_str);
    metadata.constants_written += 1;
    Ok(())
}

/// Write a declaration's STATEMENT ONLY (name + universe params + type, value
/// dropped) as an `Axiomatized` axiom-kind entry. The fail-closed spelling
/// for anything the kernel rejected.
fn add_statement_only_axiomatized(
    builder: &mut KernelShardBuilder,
    decl: &Declaration,
) -> MathverseResult<u32> {
    let (name, level_params, type_) = declaration_signature(decl);
    let stub = Declaration::Axiom {
        name: name.clone(),
        level_params: level_params.to_vec(),
        type_: type_.clone(),
    };
    builder.add_declaration(&stub, &[])
}

/// Checked-lane inductive family: replay through the kernel's checked
/// `add_inductive` (Generate policy semantics), then export the family via
/// [`KernelShardBuilder::add_inductive_family`] — which stamps the typed
/// `InductiveDecl.num_params` on the root and `KernelVerified` on every
/// member, exactly what the verify-side checked replay
/// (`build_inductive_replay_metadata`) requires to re-earn the family.
fn write_inductive_checked(
    ind: &KernelInductiveDecl,
    env: &mut Environment,
    builder: &mut KernelShardBuilder,
    metadata: &mut CoqShardMetadata,
    profile_overrides: &mut Vec<(u32, AxiomProfile)>,
) -> MathverseResult<()> {
    // Shard family export is single-type (graduation v3 fence): a mutual
    // block cannot be represented replayably, so it must fail closed rather
    // than be stamped with a claim the verify side can never re-earn.
    if ind.types.len() != 1 {
        return fail_closed_inductive(
            ind,
            builder,
            metadata,
            profile_overrides,
            "mutual inductive block not representable by the checked shard family format \
             (single-type fence)"
                .to_string(),
        );
    }

    if let Err(err) = env.add_inductive(ind.clone()) {
        return fail_closed_inductive(
            ind,
            builder,
            metadata,
            profile_overrides,
            format!("kernel-rejected: {err}"),
        );
    }

    // Members: the family root, its constructors, and the kernel-generated
    // primary recursor `<root>.rec` (so downstream replay and dependency
    // resolution see the eliminator). `casesOn`/`recOn` are NOT written: the
    // verify-side family match treats them as regenerable auxiliary
    // eliminators, and the family export carries members value-less.
    let root = &ind.types[0];
    let mut member_names: Vec<(String, DeclKind)> =
        vec![(root.name.to_string(), DeclKind::Inductive)];
    for ctor in &root.constructors {
        member_names.push((ctor.name.to_string(), DeclKind::Constructor));
    }
    let rec_name = format!("{}.rec", root.name);
    if env.get_const(&Name::from_string(&rec_name)).is_some() {
        member_names.push((rec_name, DeclKind::Recursor));
    }

    let mut member_infos = Vec::with_capacity(member_names.len());
    for (member_name, decl_kind) in &member_names {
        let info = env
            .get_const(&Name::from_string(member_name))
            .ok_or_else(|| {
                MathverseError::Kernel(format!(
                    "coq checked writer: family member `{member_name}` missing from the \
                 environment after a successful add_inductive"
                ))
            })?;
        member_infos.push((member_name.as_str(), *decl_kind, info));
    }
    let exports: Vec<InductiveFamilyMemberExport<'_>> = member_infos
        .iter()
        .map(
            |(member_name, decl_kind, info)| InductiveFamilyMemberExport {
                name: member_name,
                decl_kind: *decl_kind,
                level_params: &info.level_params,
                type_: &info.type_,
            },
        )
        .collect();
    builder.add_inductive_family(ind.num_params, &exports)?;

    metadata.kernel_verified += member_names.len();
    metadata.inductives_written += 1;
    for (member_name, _) in &member_names {
        metadata.names.push(member_name.clone());
    }
    Ok(())
}

/// Fail-closed inductive lane: statement-only `Axiomatized` entries for every
/// type and constructor in the block, counted per type in `kernel_rejected`.
/// The family is NOT seeded into the environment, so dependents fail closed
/// too.
fn fail_closed_inductive(
    ind: &KernelInductiveDecl,
    builder: &mut KernelShardBuilder,
    metadata: &mut CoqShardMetadata,
    profile_overrides: &mut Vec<(u32, AxiomProfile)>,
    reason: String,
) -> MathverseResult<()> {
    for ind_type in &ind.types {
        let type_stub = Declaration::Axiom {
            name: ind_type.name.clone(),
            level_params: ind.level_params.clone(),
            type_: ind_type.type_.clone(),
        };
        let idx = builder.add_declaration(&type_stub, &[])?;
        profile_overrides.push((idx, AxiomProfile::AXIOMATIZED));
        metadata.names.push(ind_type.name.to_string());
        metadata
            .kernel_rejected
            .push((ind_type.name.to_string(), reason.clone()));
        for ctor in &ind_type.constructors {
            let ctor_stub = Declaration::Axiom {
                name: ctor.name.clone(),
                level_params: ind.level_params.clone(),
                type_: ctor.type_.clone(),
            };
            let idx = builder.add_declaration(&ctor_stub, &[])?;
            profile_overrides.push((idx, AxiomProfile::AXIOMATIZED));
            metadata.names.push(ctor.name.to_string());
        }
        metadata.inductives_written += 1;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Legacy unchecked lane
// ---------------------------------------------------------------------------

/// Write a batch of [`TranslatedGlobalDecl`] values to a [`ShardWriter`].
///
/// **UNCHECKED LANE — labels are import-route confidence only.** Nothing here
/// is kernel-replayed: `Translated` on a value-bearing declaration means "the
/// translator produced it", NOT "the Clean kernel checked it", and the axiom
/// profile is left `NONE` (no closure is computed). New pipelines must use
/// [`write_coq_decls_to_shard_checked`], whose headers are stamped from a
/// real kernel verdict. Known fidelity limits of this lane: expression
/// lowering goes through [`lower_kernel_expr`], which drops per-`Const`
/// universe-level lists; declaration-level universe params ARE recorded
/// (see [`intern_level_params_legacy`]).
///
/// For each `Constant(Declaration)`, lowers the type and optional value
/// expression to `FlatExpr` and writes one `MathverseConstantHeader`.
///
/// For each `Inductive(InductiveDecl)`, writes one header per inductive type
/// in the mutual block, plus one header per constructor.
pub fn write_coq_decls_to_shard(
    decls: &[TranslatedGlobalDecl],
    writer: &mut ShardWriter,
) -> CoqShardMetadata {
    let mut metadata = CoqShardMetadata::default();

    for decl in decls {
        match decl {
            TranslatedGlobalDecl::Constant(d) => {
                write_constant(d, writer, &mut metadata);
            }
            TranslatedGlobalDecl::Inductive(ind) => {
                write_inductive(ind, writer, &mut metadata);
            }
        }
    }

    metadata
}

/// Write a batch of declarations with import stats context (unchecked lane —
/// see [`write_coq_decls_to_shard`]).
pub fn write_coq_decls_to_shard_with_stats(
    decls: &[TranslatedGlobalDecl],
    import_stats: ImportStats,
    writer: &mut ShardWriter,
) -> CoqShardMetadata {
    let mut metadata = write_coq_decls_to_shard(decls, writer);
    metadata.import_stats = Some(import_stats);
    metadata
}

/// Intern declaration-level universe parameter names as a CONTIGUOUS string
/// block (the shard reader reconstructs `count` consecutive slots from
/// `start`, so per-name deduplicating `add_string` would corrupt the run —
/// see `KernelShardBuilder::intern_level_params` for the full rationale).
///
/// Returns `(0, 0)` for empty lists and for the absurd >`u16::MAX` case
/// (leaving the params unrecorded rather than truncated).
fn intern_level_params_legacy(level_params: &[Name], writer: &mut ShardWriter) -> (u32, u16) {
    if level_params.is_empty() {
        return (0, 0);
    }
    let Ok(count) = u16::try_from(level_params.len()) else {
        return (0, 0);
    };
    let owned: Vec<String> = level_params.iter().map(ToString::to_string).collect();
    let refs: Vec<&str> = owned.iter().map(String::as_str).collect();
    (writer.add_string_block(&refs), count)
}

/// Write a single constant declaration to the shard (unchecked lane).
fn write_constant(decl: &Declaration, writer: &mut ShardWriter, metadata: &mut CoqShardMetadata) {
    let (name, level_params, type_, opt_value, confidence, decl_kind) = match decl {
        Declaration::Definition {
            name,
            level_params,
            type_,
            value,
            ..
        } => (
            name,
            level_params,
            type_,
            Some(value),
            ImportConfidence::Translated,
            DeclKind::Definition,
        ),
        Declaration::Theorem {
            name,
            level_params,
            type_,
            value,
            ..
        } => (
            name,
            level_params,
            type_,
            Some(value),
            ImportConfidence::Translated,
            DeclKind::Theorem,
        ),
        Declaration::Opaque {
            name,
            level_params,
            type_,
            value,
            ..
        } => (
            name,
            level_params,
            type_,
            Some(value),
            ImportConfidence::Translated,
            DeclKind::Opaque,
        ),
        Declaration::Axiom {
            name,
            level_params,
            type_,
        } => (
            name,
            level_params,
            type_,
            None,
            ImportConfidence::Axiomatized,
            DeclKind::Axiom,
        ),
    };

    let name_str = name.to_string();
    let name_idx = writer.add_string(&name_str);
    let type_idx = lower_kernel_expr(type_, writer);
    let value_idx = opt_value
        .map(|v| lower_kernel_expr(v, writer))
        .unwrap_or(NO_VALUE);
    let (level_params_start, level_params_count) = intern_level_params_legacy(level_params, writer);

    let header = MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx,
        source_system: SourceSystem::Coq as u8,
        import_confidence: confidence as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: decl_kind as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start,
        level_params_count,
        _pad2: [0u8; 26],
    };

    writer.add_constant(header);
    metadata.names.push(name_str);
    metadata.constants_written += 1;
}

/// Write an inductive declaration to the shard (unchecked lane).
///
/// Writes one header per inductive type plus one per constructor, mirroring
/// the structure that the kernel produces via `add_inductive`. NOTE: this
/// lane does NOT stamp the typed `InductiveDecl.num_params` metadata and
/// writes no recursors, so the verify-side checked family replay cannot
/// rebuild these families — use the checked lane for replayable shards.
fn write_inductive(
    ind: &KernelInductiveDecl,
    writer: &mut ShardWriter,
    metadata: &mut CoqShardMetadata,
) {
    for ind_type in &ind.types {
        // Write the inductive type itself.
        let name_str = ind_type.name.to_string();
        let name_idx = writer.add_string(&name_str);
        let type_idx = lower_kernel_expr(&ind_type.type_, writer);
        let (level_params_start, level_params_count) =
            intern_level_params_legacy(&ind.level_params, writer);

        let header = MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Coq as u8,
            import_confidence: ImportConfidence::Translated as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Inductive as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start,
            level_params_count,
            _pad2: [0u8; 26],
        };

        writer.add_constant(header);
        metadata.names.push(name_str);
        metadata.inductives_written += 1;

        // Write each constructor.
        for ctor in &ind_type.constructors {
            write_constructor(&ctor.name, &ctor.type_, &ind.level_params, writer, metadata);
        }
    }
}

/// Write a single constructor to the shard (counted under inductives).
fn write_constructor(
    name: &Name,
    type_: &Expr,
    level_params: &[Name],
    writer: &mut ShardWriter,
    metadata: &mut CoqShardMetadata,
) {
    let name_str = name.to_string();
    let name_idx = writer.add_string(&name_str);
    let type_idx = lower_kernel_expr(type_, writer);
    let (level_params_start, level_params_count) = intern_level_params_legacy(level_params, writer);

    let header = MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx: NO_VALUE,
        source_system: SourceSystem::Coq as u8,
        import_confidence: ImportConfidence::Translated as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: DeclKind::Constructor as u8,
        axiom_profile: AxiomProfile::NONE,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start,
        level_params_count,
        _pad2: [0u8; 26],
    };

    writer.add_constant(header);
    metadata.names.push(name_str);
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::inductive::{Constructor, InductiveType};
    use clean_kernel::level::Level;
    use clean_kernel::BinderInfo;

    use crate::shard::ShardReader;

    /// Build an axiom declaration for testing.
    fn test_axiom(name: &str) -> TranslatedGlobalDecl {
        TranslatedGlobalDecl::Constant(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::prop(),
        })
    }

    /// Build a definition declaration for testing.
    fn test_definition(name: &str) -> TranslatedGlobalDecl {
        TranslatedGlobalDecl::Constant(Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::prop(),
            value: Expr::const_str("True.intro"),
            is_reducible: false,
        })
    }

    /// Build a minimal inductive declaration for testing.
    fn test_inductive(type_name: &str, ctor_name: &str) -> TranslatedGlobalDecl {
        TranslatedGlobalDecl::Inductive(KernelInductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string(type_name),
                type_: Expr::sort(Level::succ(Level::zero())),
                constructors: vec![Constructor {
                    name: Name::from_string(ctor_name),
                    type_: Expr::const_(Name::from_string(type_name), vec![]),
                }],
            }],
        })
    }

    #[test]
    fn test_write_coq_decls_axiom() {
        let decls = vec![test_axiom("Coq.ax1")];
        let mut writer = ShardWriter::new();
        let metadata = write_coq_decls_to_shard(&decls, &mut writer);

        assert_eq!(metadata.constants_written, 1);
        assert_eq!(metadata.inductives_written, 0);
        assert_eq!(metadata.total(), 1);
        assert_eq!(metadata.names, vec!["Coq.ax1"]);

        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write should succeed");
        let reader = ShardReader::from_bytes(&buf).expect("shard read should succeed");
        assert!(reader.lookup_name("Coq.ax1").is_some());
    }

    #[test]
    fn test_write_coq_decls_definition_with_value() {
        let decls = vec![test_definition("Coq.mydef")];
        let mut writer = ShardWriter::new();
        let metadata = write_coq_decls_to_shard(&decls, &mut writer);

        assert_eq!(metadata.constants_written, 1);
        assert_eq!(metadata.names, vec!["Coq.mydef"]);

        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write should succeed");
        let reader = ShardReader::from_bytes(&buf).expect("shard read should succeed");

        let (_, hdr) = reader.lookup_name("Coq.mydef").unwrap();
        // Definitions have a value, so value_idx should not be NO_VALUE.
        assert_ne!(hdr.value_idx, NO_VALUE);
        assert_eq!(hdr.import_confidence, ImportConfidence::Translated as u8);
    }

    #[test]
    fn test_write_coq_decls_inductive() {
        let decls = vec![test_inductive("CoqUnit", "CoqUnit.star")];
        let mut writer = ShardWriter::new();
        let metadata = write_coq_decls_to_shard(&decls, &mut writer);

        // One inductive type + one constructor name in the names list.
        assert_eq!(metadata.inductives_written, 1);
        assert_eq!(metadata.constants_written, 0);
        assert!(metadata.names.contains(&"CoqUnit".to_string()));
        assert!(metadata.names.contains(&"CoqUnit.star".to_string()));

        let mut buf = Vec::new();
        writer.write(&mut buf).expect("shard write should succeed");
        let reader = ShardReader::from_bytes(&buf).expect("shard read should succeed");
        assert!(reader.lookup_name("CoqUnit").is_some());
        assert!(reader.lookup_name("CoqUnit.star").is_some());
    }

    #[test]
    fn test_write_coq_decls_mixed() {
        let decls = vec![
            test_axiom("Coq.a1"),
            test_definition("Coq.d1"),
            test_inductive("CoqBool", "CoqBool.true"),
        ];
        let mut writer = ShardWriter::new();
        let metadata = write_coq_decls_to_shard(&decls, &mut writer);

        assert_eq!(metadata.constants_written, 2);
        assert_eq!(metadata.inductives_written, 1);
        assert_eq!(metadata.total(), 3);
    }

    #[test]
    fn test_write_coq_decls_empty() {
        let mut writer = ShardWriter::new();
        let metadata = write_coq_decls_to_shard(&[], &mut writer);

        assert_eq!(metadata.total(), 0);
        assert!(metadata.names.is_empty());
        assert!(metadata.import_stats.is_none());
    }

    #[test]
    fn test_write_coq_decls_with_stats() {
        let decls = vec![test_axiom("Coq.with_stats")];
        let stats = ImportStats {
            successes: 5,
            failures: 1,
            skipped: 2,
        };
        let mut writer = ShardWriter::new();
        let metadata = write_coq_decls_to_shard_with_stats(&decls, stats, &mut writer);

        assert_eq!(metadata.constants_written, 1);
        let stored_stats = metadata.import_stats.unwrap();
        assert_eq!(stored_stats.successes, 5);
        assert_eq!(stored_stats.failures, 1);
    }

    #[test]
    fn test_write_coq_decls_source_system_is_coq() {
        let decls = vec![test_axiom("Coq.src_check")];
        let mut writer = ShardWriter::new();
        write_coq_decls_to_shard(&decls, &mut writer);

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();

        let (_, hdr) = reader.lookup_name("Coq.src_check").unwrap();
        assert_eq!(hdr.source_system, SourceSystem::Coq as u8);
    }

    #[test]
    fn test_write_coq_decls_axiom_confidence_is_axiomatized() {
        let decls = vec![test_axiom("Coq.ax_conf")];
        let mut writer = ShardWriter::new();
        write_coq_decls_to_shard(&decls, &mut writer);

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();

        let (_, hdr) = reader.lookup_name("Coq.ax_conf").unwrap();
        assert_eq!(hdr.import_confidence, ImportConfidence::Axiomatized as u8);
    }

    #[test]
    fn test_write_coq_decls_legacy_level_params_round_trip() {
        // The legacy lane must record declaration-level universe params.
        let decls = vec![TranslatedGlobalDecl::Constant(Declaration::Axiom {
            name: Name::from_string("Coq.poly_ax"),
            level_params: vec![Name::from_string("u"), Name::from_string("v")],
            type_: Expr::sort(Level::param(Name::from_string("u"))),
        })];
        let mut writer = ShardWriter::new();
        write_coq_decls_to_shard(&decls, &mut writer);

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = ShardReader::from_bytes(&buf).unwrap();
        let (_, hdr) = reader.lookup_name("Coq.poly_ax").unwrap();
        assert_eq!(hdr.level_params_count, 2, "two level params recorded");
        let start = hdr.level_params_start as usize;
        assert_eq!(reader.strings[start], "u");
        assert_eq!(reader.strings[start + 1], "v");
    }

    // -----------------------------------------------------------------------
    // Checked lane (COQ-4/COQ-5)
    // -----------------------------------------------------------------------

    /// `∀ (p : Prop), p → p` — a closed foundational statement.
    fn imp_self_type() -> Expr {
        Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
        )
    }

    /// `fun (p : Prop) (h : p) => h` — the foundational proof of `imp_self_type`.
    fn imp_self_value() -> Expr {
        Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
        )
    }

    /// `∀ (p q : Prop), p → p` — a distinct statement reserved for seeded axioms.
    fn seeded_axiom_type() -> Expr {
        Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(2)),
            ),
        )
    }

    fn theorem(name: &str, type_: Expr, value: Expr) -> TranslatedGlobalDecl {
        TranslatedGlobalDecl::Constant(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
            value,
        })
    }

    fn axiom(name: &str, type_: Expr) -> TranslatedGlobalDecl {
        TranslatedGlobalDecl::Constant(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        })
    }

    #[test]
    fn test_checked_writer_foundational_theorem_is_kernel_verified() {
        let decls = vec![theorem(
            "Coq.Init.Logic.imp_self",
            imp_self_type(),
            imp_self_value(),
        )];
        let mut env = Environment::new();
        let out = write_coq_decls_to_shard_checked(&decls, &mut env)
            .expect("checked write should succeed");

        assert_eq!(out.metadata.kernel_verified, 1);
        assert_eq!(out.metadata.translated_axiom_dependent, 0);
        assert!(out.metadata.kernel_rejected.is_empty());

        let reader = ShardReader::from_bytes(&out.shard_bytes).expect("shard read");
        let (_, hdr) = reader.lookup_name("Coq.Init.Logic.imp_self").unwrap();
        assert_eq!(
            hdr.import_confidence,
            ImportConfidence::KernelVerified as u8,
            "foundational-only theorem must be KernelVerified"
        );
        assert_eq!(hdr.axiom_profile, AxiomProfile::NONE);
        assert_eq!(hdr.source_system, SourceSystem::Coq as u8);
        assert_ne!(hdr.value_idx, NO_VALUE, "proof value must be stored");
    }

    #[test]
    fn test_checked_writer_classical_dependent_theorem_is_translated_with_lem_bit() {
        let decls = vec![
            axiom("Coq.Logic.Classical_Prop.classic", seeded_axiom_type()),
            theorem(
                "Coq.Test.uses_classic",
                seeded_axiom_type(),
                Expr::const_str("Coq.Logic.Classical_Prop.classic"),
            ),
        ];
        let mut env = Environment::new();
        let out = write_coq_decls_to_shard_checked(&decls, &mut env)
            .expect("checked write should succeed");

        assert_eq!(out.metadata.kernel_verified, 0);
        assert_eq!(out.metadata.translated_axiom_dependent, 1);
        assert_eq!(out.metadata.axiomatized, 1);
        assert_eq!(
            out.metadata.domain_axioms.get("Coq.Test.uses_classic"),
            Some(&vec!["Coq.Logic.Classical_Prop.classic".to_string()]),
            "sorted domain closure must be recorded"
        );

        let reader = ShardReader::from_bytes(&out.shard_bytes).expect("shard read");
        let (_, hdr) = reader.lookup_name("Coq.Test.uses_classic").unwrap();
        assert_eq!(
            hdr.import_confidence,
            ImportConfidence::Translated as u8,
            "axiom-dependent theorem must NOT be KernelVerified"
        );
        assert!(
            hdr.axiom_profile.has(AxiomProfile::LEM),
            "classic dependency must stamp the LEM bit, got 0x{:x}",
            hdr.axiom_profile.0
        );

        // The seeded axiom itself: Axiomatized + LEM + trust-gating bit.
        let (_, ax_hdr) = reader
            .lookup_name("Coq.Logic.Classical_Prop.classic")
            .unwrap();
        assert_eq!(
            ax_hdr.import_confidence,
            ImportConfidence::Axiomatized as u8
        );
        assert!(ax_hdr.axiom_profile.has(AxiomProfile::LEM));
        assert!(ax_hdr.axiom_profile.has(AxiomProfile::AXIOMATIZED));
    }

    #[test]
    fn test_checked_writer_kernel_rejected_value_is_counted_and_axiomatized() {
        // Proof value cites a constant that does not exist: kernel rejects.
        let decls = vec![theorem(
            "Coq.Test.broken",
            imp_self_type(),
            Expr::const_str("Missing.dependency"),
        )];
        let mut env = Environment::new();
        let out = write_coq_decls_to_shard_checked(&decls, &mut env)
            .expect("checked write should still succeed (fail-closed, not fatal)");

        assert_eq!(out.metadata.kernel_verified, 0);
        assert_eq!(
            out.metadata.kernel_rejected.len(),
            1,
            "rejection must be COUNTED, never silent"
        );
        let (name, reason) = &out.metadata.kernel_rejected[0];
        assert_eq!(name, "Coq.Test.broken");
        assert!(
            reason.starts_with("kernel-rejected:"),
            "reason must carry the kernel's message: {reason}"
        );

        let reader = ShardReader::from_bytes(&out.shard_bytes).expect("shard read");
        let (_, hdr) = reader.lookup_name("Coq.Test.broken").unwrap();
        assert_eq!(hdr.import_confidence, ImportConfidence::Axiomatized as u8);
        assert!(hdr.axiom_profile.has(AxiomProfile::AXIOMATIZED));
        assert_eq!(hdr.decl_kind, DeclKind::Axiom as u8, "statement-only entry");
        assert_eq!(hdr.value_idx, NO_VALUE, "rejected value must be dropped");
    }

    #[test]
    fn test_checked_writer_inductive_family_reverifies_incrementally() {
        use crate::verify::incremental::verify_shard_incremental_with_env;

        let decls = vec![test_inductive("CoqUnit", "CoqUnit.star")];
        let mut env = Environment::new();
        let out = write_coq_decls_to_shard_checked(&decls, &mut env)
            .expect("checked write should succeed");
        assert!(out.metadata.kernel_rejected.is_empty());
        assert!(
            out.metadata.kernel_verified >= 2,
            "family root + constructor must be KernelVerified"
        );

        let reader = ShardReader::from_bytes(&out.shard_bytes).expect("shard read");
        let report = verify_shard_incremental_with_env(&reader, Environment::new());
        assert_eq!(report.failed, 0, "checked family must replay cleanly");
        assert!(
            report.kernel_verified > 0,
            "family replay must re-earn KernelVerified"
        );
        assert!(
            report
                .kernel_verified_names
                .iter()
                .any(|n| n == "CoqUnit.star"),
            "constructor must be among the kernel-verified names: {:?}",
            report.kernel_verified_names
        );
    }

    #[test]
    fn test_checked_writer_mutual_inductive_fails_closed() {
        let mutual = TranslatedGlobalDecl::Inductive(KernelInductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![
                InductiveType {
                    name: Name::from_string("CoqEven"),
                    type_: Expr::sort(Level::succ(Level::zero())),
                    constructors: vec![],
                },
                InductiveType {
                    name: Name::from_string("CoqOdd"),
                    type_: Expr::sort(Level::succ(Level::zero())),
                    constructors: vec![],
                },
            ],
        });
        let mut env = Environment::new();
        let out = write_coq_decls_to_shard_checked(&[mutual], &mut env)
            .expect("checked write should succeed");

        assert_eq!(out.metadata.kernel_verified, 0);
        assert_eq!(out.metadata.kernel_rejected.len(), 2, "one count per type");
        let reader = ShardReader::from_bytes(&out.shard_bytes).expect("shard read");
        for name in ["CoqEven", "CoqOdd"] {
            let (_, hdr) = reader.lookup_name(name).unwrap();
            assert_eq!(hdr.import_confidence, ImportConfidence::Axiomatized as u8);
            assert!(hdr.axiom_profile.has(AxiomProfile::AXIOMATIZED));
        }
    }

    #[test]
    fn test_checked_writer_univalence_dependent_never_kernel_verified() {
        let decls = vec![
            axiom(
                "UniMath.Foundations.UnivalenceAxiom.univalenceAxiom",
                seeded_axiom_type(),
            ),
            theorem(
                "UniMath.Test.uses_univalence",
                seeded_axiom_type(),
                Expr::const_str("UniMath.Foundations.UnivalenceAxiom.univalenceAxiom"),
            ),
        ];
        let mut env = Environment::new();
        let out = write_coq_decls_to_shard_checked(&decls, &mut env)
            .expect("checked write should succeed");

        assert_eq!(
            out.metadata.kernel_verified, 0,
            "univalence-dependent content must never be KernelVerified"
        );
        let reader = ShardReader::from_bytes(&out.shard_bytes).expect("shard read");
        let (_, hdr) = reader.lookup_name("UniMath.Test.uses_univalence").unwrap();
        assert_ne!(
            hdr.import_confidence,
            ImportConfidence::KernelVerified as u8
        );
        assert_eq!(hdr.import_confidence, ImportConfidence::Translated as u8);
        assert!(
            hdr.axiom_profile.has(AxiomProfile::UNIVALENCE),
            "univalence taint must be stamped, got 0x{:x}",
            hdr.axiom_profile.0
        );
    }

    #[test]
    fn test_checked_writer_dependency_order_violation_fails_closed_not_silent() {
        // Theorem arrives BEFORE the axiom it cites: kernel re-check fails,
        // entry is statement-only + counted.
        let decls = vec![
            theorem(
                "Coq.Test.early_user",
                seeded_axiom_type(),
                Expr::const_str("Coq.Logic.Classical_Prop.classic"),
            ),
            axiom("Coq.Logic.Classical_Prop.classic", seeded_axiom_type()),
        ];
        let mut env = Environment::new();
        let out = write_coq_decls_to_shard_checked(&decls, &mut env)
            .expect("checked write should succeed");
        assert_eq!(out.metadata.kernel_rejected.len(), 1);
        assert_eq!(out.metadata.kernel_rejected[0].0, "Coq.Test.early_user");
        assert_eq!(out.metadata.axiomatized, 1);
    }
}
