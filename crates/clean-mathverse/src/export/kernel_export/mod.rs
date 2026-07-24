// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel Declaration to `.mathverse` shard export pipeline.
//!
//! Converts clean kernel `Declaration` objects directly into mathverse shard
//! entries, bypassing the `.olean` intermediate format. This enables newly
//! proved theorems (e.g., gamma-crown C001-C012) to be published as
//! searchable mathverse shards immediately after kernel verification.
//!
//! # Usage
//!
//! ```text
//! use clean_mathverse::export::kernel_export::KernelShardBuilder;
//! use clean_kernel::Declaration;
//!
//! let mut builder = KernelShardBuilder::new();
//! builder.add_declaration(&decl, &[])?;
//! builder.write_to_file("output.mathverse")?;
//! ```

use std::collections::HashMap;
use std::path::Path;

use clean_kernel::flat::{FlatBuilder, FlatDb};
use clean_kernel::Declaration;

use crate::error::{MathverseError, MathverseResult};
use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
    NO_VALUE,
};

// ---------------------------------------------------------------------------
// KernelExportEntry
// ---------------------------------------------------------------------------

/// Metadata for a single declaration being exported.
#[derive(Clone, Debug)]
pub struct KernelExportEntry {
    /// Fully qualified name (dot-separated).
    pub name: String,
    /// Whether the declaration has a proof/value term.
    pub has_value: bool,
    /// Axiom profile bits for this declaration.
    pub axiom_profile: AxiomProfile,
    /// Content domain classification.
    pub content_domain: ContentDomain,
    /// Keyword tags for search (stored in provenance sidecar).
    pub tags: Vec<String>,
}

// ---------------------------------------------------------------------------
// KernelShardBuilder
// ---------------------------------------------------------------------------

/// Builder that converts kernel `Declaration` objects into `.mathverse` shard entries.
///
/// Flattens each declaration's type and value expressions via `FlatBuilder`,
/// then writes them into a `ShardWriter` with appropriate trust metadata.
///
/// By default, exported constants are tagged with `SourceSystem::CleanNative`.
/// Callers exporting a derived library (e.g. gamma-crown) can override the
/// tag via [`KernelShardBuilder::with_source_system`].
#[must_use]
pub struct KernelShardBuilder {
    writer: ShardWriter,
    entries: Vec<KernelExportEntry>,
    source_system: SourceSystem,
    value_less_kernel_verified: bool,
}

impl KernelShardBuilder {
    /// Create a new builder with `SourceSystem::CleanNative`.
    pub fn new() -> Self {
        Self {
            writer: ShardWriter::new(),
            entries: Vec::new(),
            source_system: SourceSystem::CleanNative,
            value_less_kernel_verified: false,
        }
    }

    /// Override the [`SourceSystem`] tag stamped on every exported constant.
    ///
    /// Downstream kernel-flattening logic is identical — only the header
    /// `source_system` byte changes. Used by derived library builders such
    /// as `gamma_crown_shard` that reuse the native export pipeline.
    pub fn with_source_system(mut self, source_system: SourceSystem) -> Self {
        self.source_system = source_system;
        self
    }

    /// Trust value-LESS declarations as [`ImportConfidence::KernelVerified`]
    /// rather than the default `Axiomatized`.
    ///
    /// OPT-IN, CALLER-ASSERTED: only sound when EVERY value-less declaration the
    /// caller feeds was already kernel-verified and its proof value deliberately
    /// dropped — e.g. a `--type-only` Metamath export that stores name+type after
    /// the kernel checked the proof via `add_decl`. With this set, such an entry
    /// is classified exactly as if it still carried its value (KernelVerified,
    /// same axiom profile), so the dropped-value shard makes the SAME trust claim
    /// as the values-kept shard. Do NOT enable for paths that feed genuine
    /// (unproven) axioms.
    pub fn with_value_less_kernel_verified(mut self, yes: bool) -> Self {
        self.value_less_kernel_verified = yes;
        self
    }

    /// Add a kernel `Declaration` to the shard.
    ///
    /// The `tags` parameter provides keyword tags for search indexing.
    /// Tags are stored as part of the export entry metadata.
    ///
    /// Trust mapping:
    /// - Definitions/Theorems/Opaques (have value) -> `KernelVerified`
    /// - Axioms (no value) -> `AxiomDependent` with `AXIOMATIZED` profile bit
    pub fn add_declaration(&mut self, decl: &Declaration, tags: &[&str]) -> MathverseResult<u32> {
        self.add_declaration_with_extra_profile(decl, tags, AxiomProfile::NONE)
    }

    /// Add a kernel `Declaration`, unioning `extra_profile` into the computed
    /// axiom profile of the resulting shard header.
    ///
    /// This is the honest path for kernel-verified imports that remain
    /// *axiom-relative*: the Clean kernel genuinely re-checked the derivation
    /// (so `import_confidence` is `KernelVerified`), but the theorem's axiom
    /// closure is NOT `⊆ FOUNDATIONAL_AXIOMS`. For example, Metamath `set.mm`
    /// theorems are kernel-verified *relative to* Metamath's `$a` postulates
    /// (classical logic + ZFC); their entries must carry
    /// [`AxiomProfile::AXIOMATIZED`] so the trust gate treats them as
    /// trust-gated rather than as foundational-only proofs. Without this, the
    /// `has_value`-only heuristic in [`classify_trust_and_domain`] would stamp
    /// `KernelVerified` with `AxiomProfile::NONE`, falsely claiming the closure
    /// is foundational.
    pub fn add_declaration_with_extra_profile(
        &mut self,
        decl: &Declaration,
        tags: &[&str],
        extra_profile: AxiomProfile,
    ) -> MathverseResult<u32> {
        let parts = extract_declaration_parts(decl);
        let (level_params_start, level_params_count) =
            self.intern_level_params(&parts.name, parts.level_params)?;
        let (type_shard_idx, value_shard_idx) =
            self.flatten_and_transfer(&parts.name, parts.type_expr, parts.value_expr)?;

        let has_value = parts.value_expr.is_some();
        // A value-less entry is normally trust-classified `Axiomatized`. When the
        // caller opted in (every value-less entry it feeds was already kernel-
        // verified, value dropped afterwards — e.g. a `--type-only` Metamath
        // export), classify it as if it still carried its value so the trust claim
        // matches the values-kept shard. `decl_kind`/`value_idx` still reflect the
        // genuinely-absent value below.
        let trust_has_value = has_value || self.value_less_kernel_verified;
        let (mut axiom_profile, content_domain, import_confidence) =
            classify_trust_and_domain(&parts.name, trust_has_value);
        axiom_profile |= extra_profile;
        let name_idx = self.writer.add_string(&parts.name);

        let header = MathverseConstantHeader {
            name_idx,
            type_idx: type_shard_idx,
            value_idx: value_shard_idx.unwrap_or(NO_VALUE),
            source_system: self.source_system as u8,
            import_confidence: import_confidence as u8,
            content_domain: content_domain as u8,
            decl_kind: parts.decl_kind as u8,
            axiom_profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start,
            level_params_count,
            _pad2: [0u8; 26],
        };
        let const_idx = self.writer.add_constant(header);

        self.entries.push(KernelExportEntry {
            name: parts.name,
            has_value,
            axiom_profile,
            content_domain,
            tags: tags.iter().map(|s| s.to_string()).collect(),
        });

        Ok(const_idx)
    }

    /// Intern the declaration's universe-level parameter names contiguously.
    ///
    /// The shard format stores level params as `count` consecutive strings
    /// starting at `start`, and the reader (`reconstruct_level_params`)
    /// rebuilds them by reading `count` consecutive string slots from `start`.
    /// That invariant REQUIRES a contiguous run, so we must route through
    /// `add_string_block` (which appends without consulting the dedup cache),
    /// NOT per-name `add_string`.
    ///
    /// Per-name `add_string` deduplicates: by the time a multi-decl export
    /// reaches the Nth declaration, names like `u`/`v`/`w` are typically
    /// already in the string table (as another declaration's level params, or
    /// as binder names flattened from earlier types). `add_string` then returns
    /// those earlier, NON-CONSECUTIVE indices, so `start..start+count` reads the
    /// wrong slots — the reader reconstructs a level-param list that omits the
    /// scattered names, and the checked `add_inductive` replay rejects the
    /// family with "Undefined universe level parameter 'v'". Because the table's
    /// contents depend on env iteration order, the corruption is intermittent
    /// (a given shard either gets lucky with contiguous names or does not).
    fn intern_level_params(
        &mut self,
        name: &str,
        level_params: &[clean_kernel::Name],
    ) -> MathverseResult<(u32, u16)> {
        if level_params.is_empty() {
            return Ok((0u32, 0u16));
        }
        let count = u16::try_from(level_params.len()).map_err(|_| {
            MathverseError::Kernel(format!(
                "too many level params for {name}: {}",
                level_params.len()
            ))
        })?;
        let owned: Vec<String> = level_params.iter().map(ToString::to_string).collect();
        let refs: Vec<&str> = owned.iter().map(String::as_str).collect();
        let first = self.writer.add_string_block(&refs);
        Ok((first, count))
    }

    /// Flatten the type and optional value into a local arena, then transfer
    /// into the shard writer. Returns the shard-writer indices.
    fn flatten_and_transfer(
        &mut self,
        name: &str,
        type_expr: &clean_kernel::Expr,
        value_expr: Option<&clean_kernel::Expr>,
    ) -> MathverseResult<(u32, Option<u32>)> {
        let mut flat_builder = FlatBuilder::new();
        let type_flat_idx = flat_builder.add_kernel_expr(type_expr).map_err(|e| {
            MathverseError::Kernel(format!("failed to flatten type for {name}: {e}"))
        })?;
        let value_flat_idx = match value_expr {
            Some(val) => {
                let idx = flat_builder.add_kernel_expr(val).map_err(|e| {
                    MathverseError::Kernel(format!("failed to flatten value for {name}: {e}"))
                })?;
                Some(idx)
            }
            None => None,
        };
        self.transfer_flat_to_shard(&flat_builder, type_flat_idx, value_flat_idx)
    }

    /// Transfer expressions from a `FlatBuilder` into the shard's `ShardWriter`.
    ///
    /// Returns the remapped (type_idx, Option<value_idx>) in the shard arena.
    fn transfer_flat_to_shard(
        &mut self,
        flat_builder: &FlatBuilder,
        type_flat_idx: u32,
        value_flat_idx: Option<u32>,
    ) -> MathverseResult<(u32, Option<u32>)> {
        // Transfer all names from FlatBuilder into the shard string table.
        let name_remap: Vec<u32> = flat_builder
            .names()
            .iter()
            .map(|n| self.writer.add_string(n))
            .collect();

        // Transfer all STRING LITERALS from the FlatBuilder's SEPARATE literal
        // table into the shard string table, building a distinct remap.
        //
        // SOUNDNESS / faithfulness: `clean_kernel::flat::FlatBuilder` keeps two
        // disjoint index spaces — `names()` (Const/Proj names, level params) and
        // `strings()` (`Lit::String` payloads). A `LitStr` FlatExpr's `string_idx`
        // points into `strings()`, NOT `names()`. Before this transfer, the
        // literal table was never carried into the shard and the `LitStr` index
        // was remapped through `name_remap`, so every reconstructed string
        // literal resolved to an unrelated NAME (e.g. `Lit("")` -> `"Inhabited"`,
        // `Lit("PANIC at ")` -> `"String"`), corrupting the round-trip oracle for
        // any decl carrying string literals (String.instInhabited,
        // mkPanicMessageWithDecl, List.get!Internal._f, ...). Carrying the literal
        // table and remapping `LitStr` through it makes the serializer FAITHFUL;
        // the verify-side oracle/comparison is unchanged.
        let string_remap: Vec<u32> = flat_builder
            .strings()
            .iter()
            .map(|s| self.writer.add_string(s))
            .collect();

        // Transfer all levels from FlatBuilder into the shard level pool.
        //
        // Levels are built in order so each Succ/Max/IMax can reference the
        // already-transferred inner indices. Without this incremental remap,
        // shard-reader reconstruction fails with "level index N referenced
        // before it was reconstructed" because the shard writer's dedup
        // reorders what the flat builder produced.
        let mut level_remap: Vec<u32> = Vec::with_capacity(flat_builder.levels().len());
        for level in flat_builder.levels() {
            let remapped = remap_flat_level(level, &name_remap, &level_remap);
            level_remap.push(self.writer.add_level(remapped));
        }

        let mut flat_bytes = Vec::new();
        flat_builder.write_to(&mut flat_bytes).map_err(|error| {
            MathverseError::Kernel(format!(
                "failed to serialize flat expression arena: {error}"
            ))
        })?;
        let flat_db = FlatDb::from_bytes(&flat_bytes).map_err(|error| {
            MathverseError::Kernel(format!("failed to read flat expression arena: {error}"))
        })?;
        let mut level_list_remap = HashMap::new();

        // Transfer all expressions from FlatBuilder into the shard expr arena.
        //
        // Expressions are built incrementally so each App/Lam/Pi/Let/Proj can
        // reference the already-transferred inner indices. Without this, the
        // shard writer's expression dedup reorders indices and the reader
        // fails with "expression index N referenced before it was reconstructed".
        let mut expr_remap: Vec<u32> = Vec::with_capacity(flat_builder.exprs().len());
        for expr in flat_builder.exprs() {
            let remapped = remap_flat_expr(
                expr,
                &name_remap,
                &string_remap,
                &level_remap,
                &expr_remap,
                &mut |levels_idx| {
                    remap_flat_level_list(
                        levels_idx,
                        &flat_db,
                        &level_remap,
                        &mut self.writer,
                        &mut level_list_remap,
                    )
                },
            )?;
            expr_remap.push(self.writer.add_expr(remapped));
        }

        // Look up remapped indices.
        let type_idx =
            *expr_remap
                .get(type_flat_idx as usize)
                .ok_or(MathverseError::ExprOutOfRange {
                    idx: type_flat_idx,
                    count: expr_remap.len() as u32,
                })?;

        let value_idx = if let Some(vi) = value_flat_idx {
            Some(
                *expr_remap
                    .get(vi as usize)
                    .ok_or(MathverseError::ExprOutOfRange {
                        idx: vi,
                        count: expr_remap.len() as u32,
                    })?,
            )
        } else {
            None
        };

        Ok((type_idx, value_idx))
    }

    /// Add a kernel-checked inductive family's members to the shard
    /// (graduation v3 carried inductive families).
    ///
    /// The first member MUST be the family root (`DeclKind::Inductive`);
    /// remaining members are its constructors and any referenced generated
    /// recursors. Every member is written value-less (`NO_VALUE`) with its
    /// regenerated type and the family's level params; the root header is
    /// stamped with the typed `InductiveDecl.num_params` metadata so the
    /// verify-side replay (`build_inductive_replay_metadata`) can rebuild the
    /// checked declaration. Under the v3.0 single-type fence no `all_names`
    /// block is written.
    ///
    /// Returns one shard constant index per member, in input order.
    pub(crate) fn add_inductive_family(
        &mut self,
        num_params: u32,
        members: &[InductiveFamilyMemberExport<'_>],
    ) -> MathverseResult<Vec<u32>> {
        let mut indices = Vec::with_capacity(members.len());
        for (position, member) in members.iter().enumerate() {
            let (level_params_start, level_params_count) =
                self.intern_level_params(member.name, member.level_params)?;
            let (type_shard_idx, _) = self.flatten_and_transfer(member.name, member.type_, None)?;
            let (_, content_domain, _) = classify_trust_and_domain(member.name, false);
            let name_idx = self.writer.add_string(member.name);

            let mut header = MathverseConstantHeader {
                name_idx,
                type_idx: type_shard_idx,
                value_idx: NO_VALUE,
                source_system: self.source_system as u8,
                // The family re-earned KernelVerified through the checked
                // `add_inductive` replay (family_checked), not a value check.
                import_confidence: ImportConfidence::KernelVerified as u8,
                content_domain: content_domain as u8,
                decl_kind: member.decl_kind as u8,
                axiom_profile: AxiomProfile::NONE,
                sidecar_digest: 0,
                provenance_idx: 0,
                level_params_start,
                level_params_count,
                _pad2: [0u8; 26],
            };
            if position == 0 {
                header.set_inductive_decl_num_params(num_params);
            }
            indices.push(self.writer.add_constant(header));

            self.entries.push(KernelExportEntry {
                name: member.name.to_string(),
                has_value: false,
                axiom_profile: AxiomProfile::NONE,
                content_domain,
                tags: Vec::new(),
            });
        }
        Ok(indices)
    }

    /// Number of declarations added so far.
    #[inline]
    pub fn entry_count(&self) -> usize {
        self.entries.len()
    }

    /// Access the export entries (for provenance/metadata).
    pub fn entries(&self) -> &[KernelExportEntry] {
        &self.entries
    }

    /// Write the shard to a file.
    pub fn write_to_file(&self, path: impl AsRef<Path>) -> MathverseResult<()> {
        self.writer.write_to_file(path)
    }

    /// Write the shard to a byte buffer (useful for tests).
    pub fn write_to_bytes(&self) -> MathverseResult<Vec<u8>> {
        let mut buf = Vec::new();
        self.writer.write(&mut buf)?;
        Ok(buf)
    }

    /// Access the underlying `ShardWriter` (for advanced use cases).
    pub fn shard_writer(&self) -> &ShardWriter {
        &self.writer
    }

    /// Mutable access to the underlying `ShardWriter`.
    ///
    /// Needed by post-add passes that close axiom profiles
    /// (`ShardWriter::finalize_axiom_profiles`) or attach per-constant
    /// provenance (`ShardWriter::set_constant_provenance` /
    /// `ShardWriter::set_provenance`) before the shard is written — the
    /// graduation intake gate uses all three.
    pub fn shard_writer_mut(&mut self) -> &mut ShardWriter {
        &mut self.writer
    }
}

impl Default for KernelShardBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// One value-less member of a carried inductive family bound for the shard
/// (graduation v3): the family root, a constructor, or a generated recursor,
/// carrying the type the checked `add_inductive` replay regenerated.
pub(crate) struct InductiveFamilyMemberExport<'a> {
    pub(crate) name: &'a str,
    /// `DeclKind::Inductive`, `DeclKind::Constructor`, or `DeclKind::Recursor`.
    pub(crate) decl_kind: DeclKind,
    pub(crate) level_params: &'a [clean_kernel::Name],
    pub(crate) type_: &'a clean_kernel::Expr,
}

/// Extracted declaration fields shared across all four `Declaration` variants.
struct DeclarationParts<'a> {
    name: String,
    level_params: &'a [clean_kernel::Name],
    type_expr: &'a clean_kernel::Expr,
    value_expr: Option<&'a clean_kernel::Expr>,
    decl_kind: DeclKind,
}

fn extract_declaration_parts(decl: &Declaration) -> DeclarationParts<'_> {
    match decl {
        Declaration::Definition {
            name,
            level_params,
            type_,
            value,
            ..
        } => DeclarationParts {
            name: name.to_string(),
            level_params,
            type_expr: type_,
            value_expr: Some(value),
            decl_kind: DeclKind::Definition,
        },
        Declaration::Theorem {
            name,
            level_params,
            type_,
            value,
            ..
        } => DeclarationParts {
            name: name.to_string(),
            level_params,
            type_expr: type_,
            value_expr: Some(value),
            decl_kind: DeclKind::Theorem,
        },
        Declaration::Opaque {
            name,
            level_params,
            type_,
            value,
            ..
        } => DeclarationParts {
            name: name.to_string(),
            level_params,
            type_expr: type_,
            value_expr: Some(value),
            decl_kind: DeclKind::Opaque,
        },
        Declaration::Axiom {
            name,
            level_params,
            type_,
        } => DeclarationParts {
            name: name.to_string(),
            level_params,
            type_expr: type_,
            value_expr: None,
            decl_kind: DeclKind::Axiom,
        },
    }
}

/// Classify a declaration's trust level, content domain, and axiom-profile
/// flags from its name and whether it has a proof value.
fn classify_trust_and_domain(
    name: &str,
    has_value: bool,
) -> (AxiomProfile, ContentDomain, ImportConfidence) {
    let mut axiom_profile = AxiomProfile::NONE;
    let import_confidence = if has_value {
        ImportConfidence::KernelVerified
    } else {
        axiom_profile |= AxiomProfile::AXIOMATIZED;
        ImportConfidence::Axiomatized
    };
    let content_profile = name_content_profile(name);
    axiom_profile |= content_profile;
    let content_domain = if content_profile != AxiomProfile::NONE {
        ContentDomain::NnVerification
    } else {
        ContentDomain::PureMath
    };
    (axiom_profile, content_domain, import_confidence)
}

/// Name-heuristic content-domain axiom-profile bits.
///
/// NN-verification topics (`nn_verify.` / `GammaCrown.` / `NNVerify.`) carry
/// `FLOAT_APPROX | NN_ABSTRACTION`; everything else is `NONE`. This is the
/// single source of truth for the heuristic so the native-shard producer
/// ([`crate::build_library_native`]) and [`classify_trust_and_domain`] cannot
/// drift. The bits are a *content tag* derived from the name, not a
/// proof-derived axiom dependency.
pub(crate) fn name_content_profile(name: &str) -> AxiomProfile {
    if name.starts_with("nn_verify.")
        || name.starts_with("GammaCrown.")
        || name.starts_with("NNVerify.")
    {
        AxiomProfile::FLOAT_APPROX | AxiomProfile::NN_ABSTRACTION
    } else {
        AxiomProfile::NONE
    }
}

// ---------------------------------------------------------------------------
// Remapping helpers
// ---------------------------------------------------------------------------

use clean_kernel::flat::{FlatExpr, FlatLevel};

/// Remap a FlatLevel's name and inner-level references.
///
/// `level_remap[i]` must contain the shard-writer index of the flat-builder
/// level at index `i`. Because levels are built in order (each Succ/Max/IMax
/// depends only on smaller indices), this table is populated incrementally
/// by the caller before each `remap_flat_level` call.
fn remap_flat_level(level: &FlatLevel, name_remap: &[u32], level_remap: &[u32]) -> FlatLevel {
    let remap_level = |idx: u32| -> u32 { level_remap.get(idx as usize).copied().unwrap_or(idx) };

    match level.tag {
        FlatLevel::TAG_ZERO => FlatLevel::zero(),
        FlatLevel::TAG_SUCC => {
            let inner =
                u32::from_le_bytes([level.data[0], level.data[1], level.data[2], level.data[3]]);
            FlatLevel::succ(remap_level(inner))
        }
        FlatLevel::TAG_MAX | FlatLevel::TAG_IMAX => {
            let left =
                u32::from_le_bytes([level.data[0], level.data[1], level.data[2], level.data[3]]);
            let right =
                u32::from_le_bytes([level.data[4], level.data[5], level.data[6], level.data[7]]);
            let mut result = FlatLevel::max(remap_level(left), remap_level(right));
            result.tag = level.tag; // preserve IMAX
            result
        }
        FlatLevel::TAG_PARAM => {
            let name_idx =
                u32::from_le_bytes([level.data[0], level.data[1], level.data[2], level.data[3]]);
            let remapped = name_remap
                .get(name_idx as usize)
                .copied()
                .unwrap_or(name_idx);
            FlatLevel::param(remapped)
        }
        _ => FlatLevel::zero(),
    }
}

/// Remap a FlatExpr's name, level, and inner-expression references.
///
/// Each inner-expr reference (App/Lam/Pi/Let/Proj) is remapped via `expr_remap`.
/// The caller builds `expr_remap` incrementally so an expression at flat-builder
/// index `i` sees the shard-writer indices for all strictly-smaller flat
/// indices. Const level-list offsets are remapped through the shard writer's
/// own level-list table so universe-polymorphic constants survive replay.
fn remap_flat_expr(
    expr: &FlatExpr,
    name_remap: &[u32],
    string_remap: &[u32],
    level_remap: &[u32],
    expr_remap: &[u32],
    remap_level_list: &mut impl FnMut(u32) -> MathverseResult<u32>,
) -> MathverseResult<FlatExpr> {
    let d = &expr.data;
    let read_u32 =
        |off: usize| -> u32 { u32::from_le_bytes([d[off], d[off + 1], d[off + 2], d[off + 3]]) };

    let remap_name = |idx: u32| -> u32 { name_remap.get(idx as usize).copied().unwrap_or(idx) };
    // `LitStr` indexes the FlatBuilder's literal-string table, a DIFFERENT index
    // space from names — remap it through `string_remap`, never `name_remap`.
    let remap_string = |idx: u32| -> u32 { string_remap.get(idx as usize).copied().unwrap_or(idx) };
    let remap_level = |idx: u32| -> u32 { level_remap.get(idx as usize).copied().unwrap_or(idx) };
    let remap_expr = |idx: u32| -> u32 { expr_remap.get(idx as usize).copied().unwrap_or(idx) };

    let mut result = match expr.tag {
        0 => FlatExpr::bvar(read_u32(0)),              // BVar
        1 => FlatExpr::sort(remap_level(read_u32(0))), // Sort
        2 => {
            // Const
            let name_idx = read_u32(0);
            let levels_idx = read_u32(4);
            FlatExpr::const_ref(remap_name(name_idx), remap_level_list(levels_idx)?)
        }
        3 => FlatExpr::app(remap_expr(read_u32(0)), remap_expr(read_u32(4))),
        4 => FlatExpr::lam(d[0], remap_expr(read_u32(1)), remap_expr(read_u32(5))),
        5 => FlatExpr::pi(d[0], remap_expr(read_u32(1)), remap_expr(read_u32(5))),
        6 => FlatExpr::let_expr(
            remap_expr(read_u32(0)),
            remap_expr(read_u32(4)),
            remap_expr(read_u32(8)),
        ),
        7 => {
            // LitNat. A NAT_BIG literal stores a STRING-table index (the decimal
            // limb string) in data[0..4]; remap it through string_remap like
            // LitStr. A plain literal stores the inline u64 — copy verbatim.
            if expr
                .flags()
                .contains(clean_kernel::flat::FlatFlags::NAT_BIG)
            {
                let mut e = FlatExpr::lit_nat(0);
                e.data[0..4].copy_from_slice(&remap_string(read_u32(0)).to_le_bytes());
                e
            } else {
                let val = u64::from_le_bytes([d[0], d[1], d[2], d[3], d[4], d[5], d[6], d[7]]);
                FlatExpr::lit_nat(val)
            }
        }
        8 => FlatExpr::lit_str(remap_string(read_u32(0))), // LitStr
        9 => {
            // Proj
            let name_idx = read_u32(0);
            let field = u16::from_le_bytes([d[4], d[5]]);
            let expr_idx = read_u32(6);
            FlatExpr::proj(remap_name(name_idx), field, remap_expr(expr_idx))
        }
        10 => {
            // FVar
            let val = u64::from_le_bytes([d[0], d[1], d[2], d[3], d[4], d[5], d[6], d[7]]);
            FlatExpr::fvar(val)
        }
        _ => FlatExpr::bvar(0),
    };
    result.flags = expr.flags;
    Ok(result)
}

fn remap_flat_level_list(
    levels_idx: u32,
    flat_db: &FlatDb<'_>,
    level_remap: &[u32],
    writer: &mut ShardWriter,
    cache: &mut HashMap<u32, u32>,
) -> MathverseResult<u32> {
    if levels_idx == u32::MAX {
        return Ok(u32::MAX);
    }
    if let Some(&remapped) = cache.get(&levels_idx) {
        return Ok(remapped);
    }

    let old_levels = flat_db.get_level_list(levels_idx).map_err(|error| {
        MathverseError::Kernel(format!(
            "failed to read flat level list {levels_idx}: {error}"
        ))
    })?;
    let mut remapped_levels = Vec::with_capacity(old_levels.len());
    for old_idx in old_levels {
        let remapped = level_remap.get(old_idx as usize).copied().ok_or_else(|| {
            MathverseError::Kernel(format!(
                "flat level list {levels_idx} references missing level {old_idx}"
            ))
        })?;
        remapped_levels.push(remapped);
    }

    let remapped = writer.add_level_list(&remapped_levels);
    cache.insert(levels_idx, remapped);
    Ok(remapped)
}

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_gamma_crown;
