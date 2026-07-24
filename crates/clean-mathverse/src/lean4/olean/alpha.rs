// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4 `.olean` to `.mathverse` shard importer.
//!
//! Adapts `clean-olean`'s parsed module data into `MathverseConstantHeader`s
//! and feeds them to a `ShardWriter` for `.mathverse` shard emission.
//!
//! Includes a `LoweringCtx` that translates `ParsedExpr` / `ParsedLevel`
//! trees into the flat arena format (`FlatExpr` / `FlatLevel`) used by
//! `clean-kernel`.

use std::collections::{HashMap, HashSet};

use clean_kernel::flat::{FlatExpr, FlatLevel, FlatTag};
use clean_olean::expr::{ParsedBinderInfo, ParsedExpr, ParsedLiteral};
use clean_olean::level::ParsedLevel;
use clean_olean::module::{ConstantKind, ParsedConstant, ParsedModule};

use crate::types::ExprIdx;

use crate::error::MathverseResult;
use crate::provenance::{ProvenanceBuilder, ProvenanceRecord};
use crate::shard::ShardWriter;
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
    NO_VALUE,
};

// ---------------------------------------------------------------------------
// ImportStats
// ---------------------------------------------------------------------------

/// Statistics from a Lean 4 module import.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ImportStats {
    /// Total number of constants processed.
    pub total: u32,
    /// Constants with proof terms (source-verified or kernel-verified confidence).
    pub kernel_verified: u32,
    /// Constants upgraded to kernel-verified due to actual OUR type-checker verification.
    pub kernel_verified_from_tc: u32,
    /// Constants without proof terms (axiomatized confidence).
    pub axiomatized: u32,
    /// Constants that were skipped (e.g., unsupported kinds).
    pub skipped: u32,
}

// ---------------------------------------------------------------------------
// Lean4Importer
// ---------------------------------------------------------------------------

/// Imports Lean 4 parsed module data into Mathverse shard format.
///
/// Holds a reference to the source module and provides methods for
/// converting constants into `MathverseConstantHeader`s.
pub struct Lean4Importer<'a> {
    module: &'a ParsedModule,
}

impl<'a> Lean4Importer<'a> {
    /// Create a new importer for the given parsed module.
    pub fn new(module: &'a ParsedModule) -> Self {
        Self { module }
    }

    /// Import all constants from the module into the shard writer.
    ///
    /// Returns statistics about the import.
    pub fn import(&self, writer: &mut ShardWriter) -> MathverseResult<ImportStats> {
        import_module(self.module, writer)
    }

    /// Access the underlying parsed module.
    pub fn module(&self) -> &ParsedModule {
        self.module
    }
}

// ---------------------------------------------------------------------------
// Axiom profile computation
// ---------------------------------------------------------------------------

/// Map a Lean 4 constant's axiom usage to an `AxiomProfile` bitvector.
///
/// Well-known Lean 4 axioms are recognized by name:
/// - `Classical.choice` -> CHOICE bit
/// - `propext` -> PROP_EXT bit
/// - `Quot.*` (`Quot`, `Quot.mk`, `Quot.ind`, `Quot.lift`) -> QUOT bit
///
/// Any `Axiom` or `Opaque` constant also gets the AXIOMATIZED bit set.
pub fn compute_axiom_profile(constant: &ParsedConstant) -> AxiomProfile {
    let mut profile = AxiomProfile::NONE;

    // Check for well-known axiom names
    match constant.name.as_str() {
        "Classical.choice" => {
            profile |= AxiomProfile::CHOICE;
            profile |= AxiomProfile::CLASSICAL;
        }
        "propext" => {
            profile |= AxiomProfile::PROP_EXT;
        }
        "Quot" | "Quot.mk" | "Quot.ind" | "Quot.lift" => {
            profile |= AxiomProfile::QUOT;
        }
        _ => {}
    }

    // Axioms and opaques get the AXIOMATIZED bit
    match constant.kind {
        ConstantKind::Axiom | ConstantKind::Opaque => {
            profile |= AxiomProfile::AXIOMATIZED;
        }
        _ => {}
    }

    profile
}

/// Determine the `ImportConfidence` for a Lean 4 constant.
///
/// Returns `SourceVerified` (not `KernelVerified`) for constants that passed
/// Lean 4's own type checker. `KernelVerified` is reserved for constants
/// verified by OUR clean kernel (e.g., via `verify_shard_incremental()`).
fn confidence_for(constant: &ParsedConstant) -> ImportConfidence {
    match constant.kind {
        ConstantKind::Axiom | ConstantKind::Opaque => ImportConfidence::Axiomatized,
        ConstantKind::Theorem | ConstantKind::Definition => {
            if constant.value.is_some() {
                ImportConfidence::SourceVerified
            } else {
                ImportConfidence::Axiomatized
            }
        }
        ConstantKind::Inductive | ConstantKind::Constructor | ConstantKind::Recursor => {
            ImportConfidence::SourceVerified
        }
        ConstantKind::Quot => ImportConfidence::SourceVerified,
        _ => ImportConfidence::Unverified,
    }
}

/// Map a `ConstantKind` to a `DeclKind` for the mathverse shard header.
///
/// Delegates to the shared [`crate::lean4::olean::decl_kind::decl_kind_from_olean`].
fn decl_kind_for(kind: &ConstantKind) -> DeclKind {
    crate::lean4::olean::decl_kind::decl_kind_from_olean(kind)
}

/// Attach typed inductive-family metadata parsed from `.olean` to the shard header.
pub(crate) fn apply_inductive_header_metadata(
    header: &mut MathverseConstantHeader,
    constant: &ParsedConstant,
    writer: &mut ShardWriter,
) {
    if !matches!(constant.kind, ConstantKind::Inductive) {
        return;
    }
    if let Some(inductive_val) = &constant.inductive_val {
        header.set_inductive_decl_num_params(inductive_val.num_params);
        if !inductive_val.all.is_empty() && inductive_val.all.len() <= u16::MAX as usize {
            let all_names: Vec<&str> = inductive_val.all.iter().map(String::as_str).collect();
            let start = writer.add_string_block(&all_names);
            header.set_inductive_decl_all_names(start, all_names.len() as u16);
        }
    }
}

/// Determine whether a constant has a meaningful value (proof term).
///
/// Inductive types, constructors, and recursors do NOT have explicit proof
/// terms in the .olean format. Their type expressions are real and present,
/// but there is no "value" expression to store. We now use `NO_VALUE` for
/// these instead of emitting a placeholder Sort(0).
fn has_value(constant: &ParsedConstant) -> bool {
    match constant.kind {
        ConstantKind::Theorem | ConstantKind::Definition => constant.value.is_some(),
        // Inductives/constructors/recursors have types but NOT values.
        // The old code returned true and then fell through to a Sort(0)
        // placeholder. Now we honestly report no value.
        ConstantKind::Inductive | ConstantKind::Constructor => false,
        // Recursors may have recursor rules stored as value; check.
        ConstantKind::Recursor => constant.value.is_some(),
        ConstantKind::Quot => constant.value.is_some(),
        ConstantKind::Axiom | ConstantKind::Opaque => false,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// ParsedBinderInfo -> u8
// ---------------------------------------------------------------------------

/// Convert a `ParsedBinderInfo` into the u8 tag expected by `FlatExpr`.
fn binder_info_to_u8(bi: &ParsedBinderInfo) -> u8 {
    match bi {
        ParsedBinderInfo::Default => 0,
        ParsedBinderInfo::Implicit => 1,
        ParsedBinderInfo::StrictImplicit => 2,
        ParsedBinderInfo::InstImplicit => 3,
        ParsedBinderInfo::Unknown(n) => *n,
        _ => 0,
    }
}

// ---------------------------------------------------------------------------
// LoweringCtx
// ---------------------------------------------------------------------------

/// Context for lowering `ParsedExpr`/`ParsedLevel` trees into flat arena
/// format.
///
/// Holds a mutable reference to a `ShardWriter` and caches string table
/// entries to deduplicate names during lowering.
pub(crate) struct LoweringCtx<'a> {
    pub(crate) writer: &'a mut ShardWriter,
    /// Cache: string value -> string table index (dedup).
    string_cache: HashMap<String, u32>,
}

impl<'a> LoweringCtx<'a> {
    /// Create a new lowering context wrapping the given shard writer.
    pub(crate) fn new(writer: &'a mut ShardWriter) -> Self {
        Self {
            writer,
            string_cache: HashMap::new(),
        }
    }

    /// Add a string to the string table, deduplicating via cache.
    pub(crate) fn intern_string(&mut self, s: &str) -> u32 {
        if let Some(&idx) = self.string_cache.get(s) {
            return idx;
        }
        let idx = self.writer.add_string(s);
        self.string_cache.insert(s.to_string(), idx);
        idx
    }

    /// Append a constant's universe-parameter names as a CONTIGUOUS block and
    /// return `(start, count)` for its `level_params_start`/`level_params_count`
    /// header window.
    ///
    /// The shard format reads level params as the half-open string-table window
    /// `[start .. start + count)`, so the names MUST occupy consecutive slots.
    /// Interning them one-by-one via [`Self::intern_string`] does NOT guarantee
    /// this: a param name already present in the table (e.g. because the
    /// declaration's type or value already referenced `Sort u_1`) dedups to its
    /// earlier index, leaving the remaining params interned at scattered
    /// positions. The window then reads neighbouring strings (other names) as if
    /// they were universe parameters, which the kernel rejects as
    /// `UndefinedLevelParam` even though the declaration is well-formed.
    ///
    /// Routing through [`ShardWriter::add_string_block`] guarantees contiguity
    /// (it appends without deduplicating). The `string_cache` is left untouched
    /// so subsequent [`Self::intern_string`] calls keep returning the original
    /// (possibly earlier) index — matching `add_string_block`'s own contract.
    pub(crate) fn add_level_param_block(&mut self, params: &[String]) -> (u32, u16) {
        if params.is_empty() {
            return (0, 0);
        }
        let names: Vec<&str> = params.iter().map(String::as_str).collect();
        let start = self.writer.add_string_block(&names);
        (start, names.len() as u16)
    }

    /// Lower a `ParsedLevel` tree into flat levels, returning the level
    /// index in the shard's level pool.
    pub(crate) fn lower_level(&mut self, level: &ParsedLevel) -> u32 {
        match level {
            ParsedLevel::Zero => {
                let flat = FlatLevel::zero();
                self.writer.add_level(flat)
            }
            ParsedLevel::Succ(inner) => {
                let inner_idx = self.lower_level(inner);
                let flat = FlatLevel::succ(inner_idx);
                self.writer.add_level(flat)
            }
            ParsedLevel::Max(left, right) => {
                let left_idx = self.lower_level(left);
                let right_idx = self.lower_level(right);
                let flat = FlatLevel::max(left_idx, right_idx);
                self.writer.add_level(flat)
            }
            ParsedLevel::IMax(left, right) => {
                let left_idx = self.lower_level(left);
                let right_idx = self.lower_level(right);
                let mut flat = FlatLevel::max(left_idx, right_idx);
                flat.tag = FlatLevel::TAG_IMAX;
                self.writer.add_level(flat)
            }
            ParsedLevel::Param(name) => {
                let name_idx = self.intern_string(name);
                let flat = FlatLevel::param(name_idx);
                self.writer.add_level(flat)
            }
            ParsedLevel::MVar(name) => {
                // Metavariables should not appear in elaborated .olean
                // output. Treat as a parameter for graceful degradation.
                let name_idx = self.intern_string(name);
                let flat = FlatLevel::param(name_idx);
                self.writer.add_level(flat)
            }
            _ => {
                // Forward-compatible: unknown variants become zero.
                let flat = FlatLevel::zero();
                self.writer.add_level(flat)
            }
        }
    }

    /// Lower a `ParsedExpr` tree into flat expressions, returning the expr
    /// index in the shard's expression arena.
    pub(crate) fn lower_expr(&mut self, expr: &ParsedExpr) -> u32 {
        match expr {
            ParsedExpr::BVar(n) => {
                let flat = FlatExpr::bvar(*n as u32);
                self.writer.add_expr(flat)
            }
            ParsedExpr::FVar(name) => {
                // VERDICT PARITY: hash the fvar NAME with the SAME fixed-seed
                // ahash the eager olean import uses (`convert_expr_direct` ->
                // `clean_olean::import::hash_str`). The name string here is the
                // identical `resolve_name_ptr` output as eager, so an identical
                // hasher yields an identical `FVarId` and a byte-identical
                // reconstructed `Expr`. A different hasher (the old std
                // `DefaultHasher`) gave a different id for the same name,
                // diverging FVar identity and breaking eager-vs-lazy verdict
                // parity on FVar-bearing closure constants.
                let id = clean_olean::import::hash_str(name);
                let flat = FlatExpr::fvar(id);
                self.writer.add_expr(flat)
            }
            ParsedExpr::MVar(name) => {
                // Metavariables are opaque; treat as fvar with hashed name —
                // same fixed-seed ahash as the eager path (see FVar above).
                let id = clean_olean::import::hash_str(name);
                let flat = FlatExpr::fvar(id);
                self.writer.add_expr(flat)
            }
            ParsedExpr::Sort(level) => {
                let level_idx = self.lower_level(level);
                let flat = FlatExpr::sort(level_idx);
                self.writer.add_expr(flat)
            }
            ParsedExpr::Const(name, levels) => {
                let name_idx = self.intern_string(name);
                // Lower each universe level and collect indices for the level list.
                let level_indices: Vec<u32> =
                    levels.iter().map(|lvl| self.lower_level(lvl)).collect();
                let levels_list_idx = self.writer.add_level_list(&level_indices);
                let flat = FlatExpr::const_ref(name_idx, levels_list_idx);
                self.writer.add_expr(flat)
            }
            ParsedExpr::App(func, arg) => {
                let fn_idx = self.lower_expr(func);
                let arg_idx = self.lower_expr(arg);
                let flat = FlatExpr::app(fn_idx, arg_idx);
                self.writer.add_expr(flat)
            }
            ParsedExpr::Lam(_name, ty, body, bi) => {
                let ty_idx = self.lower_expr(ty);
                let body_idx = self.lower_expr(body);
                let flat = FlatExpr::lam(binder_info_to_u8(bi), ty_idx, body_idx);
                self.writer.add_expr(flat)
            }
            ParsedExpr::ForallE(_name, ty, body, bi) => {
                let ty_idx = self.lower_expr(ty);
                let body_idx = self.lower_expr(body);
                let flat = FlatExpr::pi(binder_info_to_u8(bi), ty_idx, body_idx);
                self.writer.add_expr(flat)
            }
            ParsedExpr::LetE(_name, ty, val, body, _nondep) => {
                let ty_idx = self.lower_expr(ty);
                let val_idx = self.lower_expr(val);
                let body_idx = self.lower_expr(body);
                let flat = FlatExpr::let_expr(ty_idx, val_idx, body_idx);
                self.writer.add_expr(flat)
            }
            ParsedExpr::Lit(ParsedLiteral::Nat(bignat)) => {
                // PARITY: the FlatExpr Nat literal holds only a u64. A Nat literal
                // exceeding u64::MAX (e.g. USize.size = 2^64) cannot fit inline.
                // The OLD code silently truncated to u64::MAX, producing a WRONG
                // value the eager olean import (which keeps the real BigNat) never
                // equals. Match `clean_kernel::flat::convert` EXACTLY: store the
                // little-endian u64 limbs as a comma-separated decimal string in
                // the string table and flag the LitNat NAT_BIG, so the value
                // round-trips losslessly (BigNat::from_limbs on read).
                match bignat.to_u64() {
                    Some(value) => {
                        let flat = FlatExpr::lit_nat(value);
                        self.writer.add_expr(flat)
                    }
                    None => {
                        let limbs = bignat
                            .limbs()
                            .iter()
                            .map(|l| l.to_string())
                            .collect::<Vec<_>>()
                            .join(",");
                        let str_idx = self.intern_string(&limbs);
                        let mut flat = FlatExpr::lit_nat(0);
                        flat.data[0..4].copy_from_slice(&str_idx.to_le_bytes());
                        flat.flags |= clean_kernel::flat::FlatFlags::NAT_BIG.bits();
                        self.writer.add_expr(flat)
                    }
                }
            }
            ParsedExpr::Lit(ParsedLiteral::String(s)) => {
                let string_idx = self.intern_string(s);
                let flat = FlatExpr::lit_str(string_idx);
                self.writer.add_expr(flat)
            }
            ParsedExpr::MData(inner) => {
                // MData is a metadata wrapper; lower the inner expression
                // directly (transparent).
                self.lower_expr(inner)
            }
            ParsedExpr::Proj(struct_name, field_idx, inner) => {
                let name_idx = self.intern_string(struct_name);
                let inner_idx = self.lower_expr(inner);
                let flat = FlatExpr::proj(name_idx, *field_idx as u16, inner_idx);
                self.writer.add_expr(flat)
            }
            _ => {
                // Forward-compatible: unknown expression variants become
                // BVar(0).
                let flat = FlatExpr::bvar(0);
                self.writer.add_expr(flat)
            }
        }
    }
}

// FVar/MVar ids are hashed via `clean_olean::import::hash_str` (fixed-seed
// ahash) for byte-identical parity with the eager olean import; the former
// local std `DefaultHasher` helper was removed because a different hasher
// diverges FVar identity (see `lower_expr`'s FVar arm).

// ---------------------------------------------------------------------------
// Module import
// ---------------------------------------------------------------------------

/// Convert all constants from a `ParsedModule` into `MathverseConstantHeader`s
/// and add them to a `ShardWriter`.
///
/// Each constant gets:
/// - A string table entry for its name
/// - Lowered type and value expression indices (via `LoweringCtx`)
/// - Source system set to `Lean4`
/// - Content domain set to `PureMath` (heuristic default)
/// - Axiom profile computed from the constant's name and kind
pub fn import_module(
    module: &ParsedModule,
    writer: &mut ShardWriter,
) -> MathverseResult<ImportStats> {
    import_module_verified(module, writer, None)
}

/// Convert all constants from a `ParsedModule` into `MathverseConstantHeader`s
/// and add them to a `ShardWriter`, upgrading any constant in
/// `verified_names` to `KernelVerified`.
pub fn import_module_verified(
    module: &ParsedModule,
    writer: &mut ShardWriter,
    verified_names: Option<&HashSet<String>>,
) -> MathverseResult<ImportStats> {
    let mut stats = ImportStats::default();
    let mut ctx = LoweringCtx::new(writer);

    for constant in &module.constants {
        // SOUNDNESS: skip Lean compiler/code-generator artifacts (`._cstage*`,
        // `_elambda*`/`_lambda*`, `_rarg`, `_spec*`, `_unsafe_rec`). They are not
        // kernel-checkable (types reference the undeclared `_obj`/`_neutral`
        // pseudo-types or carry empty level-params) and must not enter the shard.
        // See `clean_olean::import::is_compiler_ir_name`.
        if clean_olean::import::is_compiler_ir_name(&constant.name) {
            stats.total += 1;
            stats.skipped += 1;
            continue;
        }
        let name_idx = ctx.intern_string(&constant.name);

        // Determine confidence: TC verification overrides heuristic.
        let heuristic = confidence_for(constant);
        let verified_by_tc = verified_names.is_some_and(|names| names.contains(&constant.name));
        let confidence = if verified_by_tc {
            ImportConfidence::KernelVerified
        } else {
            heuristic
        };
        let profile = compute_axiom_profile(constant);

        // Lower the type expression if present.
        let type_idx: u32 = match &constant.type_ {
            Some(type_expr) => ctx.lower_expr(type_expr),
            None => {
                // No type expression; emit a placeholder Sort(0).
                let l0 = ctx.writer.add_level(FlatLevel::zero());
                ctx.writer.add_expr(FlatExpr::sort(l0))
            }
        };

        // Lower the value expression if present and the constant kind
        // has a value.
        let value_idx: u32 = if has_value(constant) {
            match &constant.value {
                Some(val_expr) => ctx.lower_expr(val_expr),
                None => {
                    // Definitional constant without explicit value
                    // (e.g., Inductive). Emit a placeholder Sort(0).
                    let l0 = ctx.writer.add_level(FlatLevel::zero());
                    ctx.writer.add_expr(FlatExpr::sort(l0))
                }
            }
        } else {
            NO_VALUE
        };

        // Store declaration-level universe parameter names in the string table
        // as a CONTIGUOUS block — see `add_level_param_block` for why a plain
        // intern loop corrupts the `[start..start+count)` window.
        let (lp_start, lp_count) = ctx.add_level_param_block(&constant.level_params);

        let mut header = MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: confidence as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: decl_kind_for(&constant.kind) as u8,
            axiom_profile: profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: lp_start,
            level_params_count: lp_count,
            _pad2: [0u8; 26],
        };
        apply_inductive_header_metadata(&mut header, constant, ctx.writer);

        ctx.writer.add_constant(header);

        stats.total += 1;
        if verified_by_tc
            && heuristic != ImportConfidence::KernelVerified
            && heuristic != ImportConfidence::SourceVerified
        {
            stats.kernel_verified_from_tc += 1;
        }
        match confidence {
            ImportConfidence::KernelVerified | ImportConfidence::SourceVerified => {
                stats.kernel_verified += 1;
            }
            ImportConfidence::Axiomatized => stats.axiomatized += 1,
            _ => stats.skipped += 1,
        }
    }

    Ok(stats)
}

// ---------------------------------------------------------------------------
// Dependency extraction
// ---------------------------------------------------------------------------

/// Extract all constant references from a `FlatExpr` arena starting at the
/// given root index.
///
/// Walks the expression tree recursively, collecting `name_idx` values from
/// every `Const` node reachable from `root`. Returns a sorted, deduplicated
/// `Vec<u32>` of name indices.
///
/// This is used to compute the dependency graph: for a constant with type
/// expression rooted at `type_idx`, `extract_deps(&exprs, type_idx)` returns
/// the name indices of all constants referenced in that type.
pub fn extract_deps(exprs: &[FlatExpr], root: ExprIdx) -> Vec<u32> {
    let mut deps = Vec::new();
    let mut visited = hashbrown::HashSet::new();
    extract_deps_recursive(exprs, root, &mut deps, &mut visited);
    deps.sort_unstable();
    deps.dedup();
    deps
}

fn extract_deps_recursive(
    exprs: &[FlatExpr],
    idx: ExprIdx,
    deps: &mut Vec<u32>,
    visited: &mut hashbrown::HashSet<u32>,
) {
    if !visited.insert(idx) {
        return;
    }
    let i = idx as usize;
    if i >= exprs.len() {
        return;
    }
    let expr = &exprs[i];
    match expr.tag() {
        Ok(FlatTag::Const) => {
            // data[0..4] = name_idx
            if let Ok(name_idx) = expr.read_u32(0) {
                deps.push(name_idx);
            }
        }
        Ok(FlatTag::App) => {
            // data[0..4] = fn_idx, data[4..8] = arg_idx
            if let Ok(fn_idx) = expr.read_u32(0) {
                extract_deps_recursive(exprs, fn_idx, deps, visited);
            }
            if let Ok(arg_idx) = expr.read_u32(4) {
                extract_deps_recursive(exprs, arg_idx, deps, visited);
            }
        }
        Ok(FlatTag::Pi) | Ok(FlatTag::Lam) => {
            // data[0] = binder_info, data[1..5] = ty_idx, data[5..9] = body_idx
            if let Ok(ty_idx) = expr.read_u32(1) {
                extract_deps_recursive(exprs, ty_idx, deps, visited);
            }
            if let Ok(body_idx) = expr.read_u32(5) {
                extract_deps_recursive(exprs, body_idx, deps, visited);
            }
        }
        Ok(FlatTag::Let) => {
            // data[0..4] = ty_idx, data[4..8] = val_idx, data[8..12] = body_idx
            if let Ok(ty_idx) = expr.read_u32(0) {
                extract_deps_recursive(exprs, ty_idx, deps, visited);
            }
            if let Ok(val_idx) = expr.read_u32(4) {
                extract_deps_recursive(exprs, val_idx, deps, visited);
            }
            if let Ok(body_idx) = expr.read_u32(8) {
                extract_deps_recursive(exprs, body_idx, deps, visited);
            }
        }
        Ok(FlatTag::Proj) => {
            // data[0..4] = name_idx, data[4..6] = field, data[6..10] = expr_idx
            if let Ok(inner) = expr.read_u32(6) {
                extract_deps_recursive(exprs, inner, deps, visited);
            }
        }
        _ => {
            // BVar, Sort, FVar, LitNat, LitStr — no sub-expressions with
            // constant references.
        }
    }
}

// ---------------------------------------------------------------------------
// ProofInfo
// ---------------------------------------------------------------------------

/// Summary of proof-related properties for a parsed constant.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ProofInfo {
    /// The constant is declared as a theorem.
    pub is_theorem: bool,
    /// The constant is declared as opaque.
    pub is_opaque: bool,
    /// The proof term contains `sorryAx` (incomplete proof).
    pub has_sorry: bool,
    /// Approximate size of the proof term (node count).
    pub proof_size: usize,
    /// The proof references `Classical.choice`.
    pub uses_classical: bool,
    /// The proof references `Quot.lift` or `Quot.mk` (quotient choice).
    pub uses_choice: bool,
}

/// Extract proof-related metadata from a `ParsedConstant`.
///
/// Walks the value expression (if present) to detect sorry, classical
/// usage, choice, and compute an approximate node count.
pub fn extract_proof_info(constant: &ParsedConstant) -> ProofInfo {
    let mut info = ProofInfo {
        is_theorem: constant.kind == ConstantKind::Theorem,
        is_opaque: constant.kind == ConstantKind::Opaque,
        ..Default::default()
    };
    if let Some(val) = &constant.value {
        walk_expr_for_proof_info(val, &mut info);
    }
    info
}

fn walk_expr_for_proof_info(expr: &ParsedExpr, info: &mut ProofInfo) {
    info.proof_size += 1;
    match expr {
        ParsedExpr::Const(name, _levels) => {
            if name == "sorryAx" {
                info.has_sorry = true;
            }
            if name == "Classical.choice" {
                info.uses_classical = true;
                info.uses_choice = true;
            }
            if name == "Quot.lift" || name == "Quot.mk" {
                info.uses_choice = true;
            }
        }
        ParsedExpr::App(func, arg) => {
            walk_expr_for_proof_info(func, info);
            walk_expr_for_proof_info(arg, info);
        }
        ParsedExpr::Lam(_name, ty, body, _bi) => {
            walk_expr_for_proof_info(ty, info);
            walk_expr_for_proof_info(body, info);
        }
        ParsedExpr::ForallE(_name, ty, body, _bi) => {
            walk_expr_for_proof_info(ty, info);
            walk_expr_for_proof_info(body, info);
        }
        ParsedExpr::LetE(_name, ty, val, body, _) => {
            walk_expr_for_proof_info(ty, info);
            walk_expr_for_proof_info(val, info);
            walk_expr_for_proof_info(body, info);
        }
        ParsedExpr::MData(inner) => {
            walk_expr_for_proof_info(inner, info);
        }
        ParsedExpr::Proj(_name, _field, inner) => {
            walk_expr_for_proof_info(inner, info);
        }
        // BVar, FVar, MVar, Sort, Lit — leaf nodes.
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Expression depth
// ---------------------------------------------------------------------------

/// Compute the depth of a `ParsedExpr` tree.
fn expr_depth(expr: &ParsedExpr) -> usize {
    match expr {
        ParsedExpr::App(func, arg) => 1 + expr_depth(func).max(expr_depth(arg)),
        ParsedExpr::Lam(_, ty, body, _) | ParsedExpr::ForallE(_, ty, body, _) => {
            1 + expr_depth(ty).max(expr_depth(body))
        }
        ParsedExpr::LetE(_, ty, val, body, _) => {
            1 + expr_depth(ty).max(expr_depth(val)).max(expr_depth(body))
        }
        ParsedExpr::MData(inner) | ParsedExpr::Proj(_, _, inner) => 1 + expr_depth(inner),
        // Leaf nodes (BVar, FVar, MVar, Sort, Const, Lit).
        _ => 1,
    }
}

/// Compute the maximum expression depth of a constant (type + value).
fn constant_expr_depth(constant: &ParsedConstant) -> usize {
    let type_depth = constant.type_.as_ref().map_or(0, expr_depth);
    let value_depth = constant.value.as_ref().map_or(0, expr_depth);
    type_depth.max(value_depth)
}

// ---------------------------------------------------------------------------
// Lean4ImportConfig
// ---------------------------------------------------------------------------

/// Configuration for Lean 4 module import with filtering and trust options.
#[derive(Clone, Debug, Default)]
pub struct Lean4ImportConfig {
    /// Skip constants whose proof term contains `sorryAx`.
    pub skip_sorry: bool,
    /// Include private/protected constants (those with `_private` prefix).
    pub include_private: bool,
    /// Skip constants whose expression tree exceeds this depth.
    /// 0 means no limit.
    pub max_expr_depth: usize,
    /// Modules whose constants automatically get `SourceVerified` confidence.
    pub trusted_modules: Vec<String>,
}

impl Lean4ImportConfig {
    /// Create a new config builder with default settings.
    pub fn builder() -> Lean4ImportConfigBuilder {
        Lean4ImportConfigBuilder(Self::default())
    }
}

/// Builder for `Lean4ImportConfig`.
pub struct Lean4ImportConfigBuilder(Lean4ImportConfig);

impl Lean4ImportConfigBuilder {
    /// When `true`, constants containing `sorryAx` are skipped.
    #[must_use]
    pub fn skip_sorry(mut self, skip: bool) -> Self {
        self.0.skip_sorry = skip;
        self
    }

    /// When `true`, private/protected constants are included.
    #[must_use]
    pub fn include_private(mut self, include: bool) -> Self {
        self.0.include_private = include;
        self
    }

    /// Set the maximum expression depth; constants exceeding it are skipped.
    /// Pass 0 for no limit.
    #[must_use]
    pub fn max_expr_depth(mut self, depth: usize) -> Self {
        self.0.max_expr_depth = depth;
        self
    }

    /// Add a trusted module name. Constants from trusted modules get
    /// `SourceVerified` confidence regardless of their kind.
    #[must_use]
    pub fn trusted_module(mut self, module: &str) -> Self {
        self.0.trusted_modules.push(module.to_string());
        self
    }

    /// Consume the builder and return the config.
    pub fn build(self) -> Lean4ImportConfig {
        self.0
    }
}

// ---------------------------------------------------------------------------
// Batch axiom profile
// ---------------------------------------------------------------------------

/// Compute axiom profiles for a batch of constants.
///
/// Equivalent to calling `compute_axiom_profile` on each constant, but
/// structured for batch pipelines that process pre-collected constant lists.
pub fn batch_compute_axiom_profiles(constants: &[(String, &ParsedConstant)]) -> Vec<AxiomProfile> {
    constants
        .iter()
        .map(|(_name, c)| compute_axiom_profile(c))
        .collect()
}

// ---------------------------------------------------------------------------
// Import with provenance
// ---------------------------------------------------------------------------

/// Enhanced import that generates a `ProvenanceRecord` for every constant.
///
/// Returns `(ImportStats, Vec<ProvenanceRecord>)` — the records are ordered
/// to match the constants in `module.constants` (skipped constants still
/// produce a record tagged with a "skipped" note).
pub fn import_with_provenance(
    module: &ParsedModule,
    writer: &mut ShardWriter,
    config: &Lean4ImportConfig,
) -> MathverseResult<(ImportStats, Vec<ProvenanceRecord>)> {
    let mut stats = ImportStats::default();
    let mut records = Vec::with_capacity(module.constants.len());
    let mut ctx = LoweringCtx::new(writer);

    for constant in &module.constants {
        // SOUNDNESS: skip Lean compiler/code-generator artifacts — not
        // kernel-checkable; they must not enter the shard. See
        // `clean_olean::import::is_compiler_ir_name`.
        if clean_olean::import::is_compiler_ir_name(&constant.name) {
            stats.total += 1;
            stats.skipped += 1;
            records.push(
                ProvenanceBuilder::new(&constant.name)
                    .note("skipped: compiler/code-generator artifact (not kernel-checkable)")
                    .build(),
            );
            continue;
        }
        // Apply skip_sorry filter.
        if config.skip_sorry {
            let pi = extract_proof_info(constant);
            if pi.has_sorry {
                stats.total += 1;
                stats.skipped += 1;
                records.push(
                    ProvenanceBuilder::new(&constant.name)
                        .note("skipped: sorry in proof")
                        .build(),
                );
                continue;
            }
        }

        // Apply include_private filter.
        if !config.include_private && constant.name.contains("._private") {
            stats.total += 1;
            stats.skipped += 1;
            records.push(
                ProvenanceBuilder::new(&constant.name)
                    .note("skipped: private constant")
                    .build(),
            );
            continue;
        }

        // Apply max_expr_depth filter.
        if config.max_expr_depth > 0 {
            let depth = constant_expr_depth(constant);
            if depth > config.max_expr_depth {
                stats.total += 1;
                stats.skipped += 1;
                records.push(
                    ProvenanceBuilder::new(&constant.name)
                        .note(&format!(
                            "skipped: depth {depth} > limit {}",
                            config.max_expr_depth
                        ))
                        .build(),
                );
                continue;
            }
        }

        let name_idx = ctx.intern_string(&constant.name);

        // Determine confidence: trusted modules override to SourceVerified
        // (not KernelVerified — the source system checked these, not our kernel).
        let confidence = if config
            .trusted_modules
            .iter()
            .any(|m| constant.name.starts_with(m))
        {
            ImportConfidence::SourceVerified
        } else {
            confidence_for(constant)
        };

        let profile = compute_axiom_profile(constant);

        let type_idx: u32 = match &constant.type_ {
            Some(type_expr) => ctx.lower_expr(type_expr),
            None => {
                let l0 = ctx.writer.add_level(FlatLevel::zero());
                ctx.writer.add_expr(FlatExpr::sort(l0))
            }
        };

        let value_idx: u32 = if has_value(constant) {
            match &constant.value {
                Some(val_expr) => ctx.lower_expr(val_expr),
                None => {
                    let l0 = ctx.writer.add_level(FlatLevel::zero());
                    ctx.writer.add_expr(FlatExpr::sort(l0))
                }
            }
        } else {
            NO_VALUE
        };

        // Store declaration-level universe parameter names in the string table
        // as a CONTIGUOUS block — see `add_level_param_block` for why a plain
        // intern loop corrupts the `[start..start+count)` window.
        let (lp_start, lp_count) = ctx.add_level_param_block(&constant.level_params);

        let mut header = MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: confidence as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: decl_kind_for(&constant.kind) as u8,
            axiom_profile: profile,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: lp_start,
            level_params_count: lp_count,
            _pad2: [0u8; 26],
        };
        apply_inductive_header_metadata(&mut header, constant, ctx.writer);

        ctx.writer.add_constant(header);

        stats.total += 1;
        match confidence {
            ImportConfidence::KernelVerified | ImportConfidence::SourceVerified => {
                stats.kernel_verified += 1;
            }
            ImportConfidence::Axiomatized => stats.axiomatized += 1,
            _ => stats.skipped += 1,
        }

        let record = ProvenanceBuilder::new(&constant.name)
            .note(&format!("kind: {:?}", constant.kind))
            .build();
        records.push(record);
    }

    Ok((stats, records))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use clean_olean::expr::BigNat;
    use clean_olean::module::{ConstantKind, ParsedConstant, ParsedModule};

    /// Build a minimal `ParsedModule` with the given constants.
    fn mock_module(constants: Vec<ParsedConstant>) -> ParsedModule {
        ParsedModule {
            const_names: constants.iter().map(|c| c.name.clone()).collect(),
            constants,
            extra_const_names: Vec::new(),
            imports: Vec::new(),
            entries: Vec::new(),
            clean_payload: None,
        }
    }

    /// Build a minimal `ParsedConstant` with the given name and kind.
    fn mock_constant(name: &str, kind: ConstantKind, has_val: bool) -> ParsedConstant {
        ParsedConstant {
            definition_safety: None,
            quot_kind: None,
            name: name.to_string(),
            kind,
            level_params: Vec::new(),
            type_: None,
            value: if has_val { Some(mock_expr()) } else { None },
            inductive_val: None,
            constructor_val: None,
            recursor_val: None,
            hints: None,
        }
    }

    /// Build a trivial ParsedExpr (Sort 0 / Prop) as a placeholder.
    fn mock_expr() -> ParsedExpr {
        ParsedExpr::Sort(ParsedLevel::Zero)
    }

    // -----------------------------------------------------------------------
    // Axiom profile tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_choice_axiom_profile() {
        let c = mock_constant("Classical.choice", ConstantKind::Axiom, false);
        let profile = compute_axiom_profile(&c);
        assert!(profile.has(AxiomProfile::CHOICE));
        assert!(profile.has(AxiomProfile::CLASSICAL));
        assert!(profile.has(AxiomProfile::AXIOMATIZED));
    }

    #[test]
    fn test_propext_axiom_profile() {
        let c = mock_constant("propext", ConstantKind::Axiom, false);
        let profile = compute_axiom_profile(&c);
        assert!(profile.has(AxiomProfile::PROP_EXT));
        assert!(profile.has(AxiomProfile::AXIOMATIZED));
        assert!(!profile.has(AxiomProfile::CHOICE));
    }

    #[test]
    fn test_quot_axiom_profile() {
        for name in &["Quot", "Quot.mk", "Quot.ind", "Quot.lift"] {
            let c = mock_constant(name, ConstantKind::Quot, false);
            let profile = compute_axiom_profile(&c);
            assert!(
                profile.has(AxiomProfile::QUOT),
                "{name} should have QUOT bit"
            );
            assert!(
                !profile.has(AxiomProfile::AXIOMATIZED),
                "{name} (Quot kind) should not have AXIOMATIZED bit"
            );
        }
    }

    #[test]
    fn test_theorem_no_axiom_bits() {
        let c = mock_constant("Nat.add_comm", ConstantKind::Theorem, true);
        let profile = compute_axiom_profile(&c);
        assert!(profile.is_pure());
    }

    #[test]
    fn test_import_module_verified_skips_compiler_ir() {
        // SOUNDNESS regression guard: the production shard-write path must drop
        // compiler/code-generator artifacts and keep genuine declarations
        // (including the match-equation compiler's `match_N`, which is real).
        let module = mock_module(vec![
            mock_constant("Nat.add_comm", ConstantKind::Theorem, true), // kept
            mock_constant("Nat.bitwise._cstage2", ConstantKind::Definition, true), // skip
            mock_constant("Equiv.Set.rangeInl._elambda_1", ConstantKind::Axiom, false), // skip
            mock_constant("List.foldr._rarg", ConstantKind::Definition, true), // skip
            mock_constant("Foo.match_1", ConstantKind::Definition, true), // kept (genuine)
        ]);
        let mut writer = ShardWriter::new();
        let stats = import_module_verified(&module, &mut writer, None)
            .expect("import_module_verified should succeed");
        assert_eq!(stats.total, 5, "all 5 constants processed");
        assert_eq!(stats.skipped, 3, "the 3 code-gen artifacts skipped");
        assert_eq!(
            writer.constant_count(),
            2,
            "only the 2 genuine declarations (Nat.add_comm, Foo.match_1) reach the shard"
        );
    }

    #[test]
    fn test_opaque_gets_axiomatized() {
        let c = mock_constant("SomeOpaque", ConstantKind::Opaque, false);
        let profile = compute_axiom_profile(&c);
        assert!(profile.has(AxiomProfile::AXIOMATIZED));
        assert!(profile.is_trust_gated());
    }

    // -----------------------------------------------------------------------
    // Confidence tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_axiom_confidence() {
        let c = mock_constant("ax1", ConstantKind::Axiom, false);
        assert_eq!(confidence_for(&c), ImportConfidence::Axiomatized);
    }

    #[test]
    fn test_theorem_with_proof_confidence() {
        let c = mock_constant("thm1", ConstantKind::Theorem, true);
        assert_eq!(confidence_for(&c), ImportConfidence::SourceVerified);
    }

    #[test]
    fn test_definition_with_value_confidence() {
        let c = mock_constant("def1", ConstantKind::Definition, true);
        assert_eq!(confidence_for(&c), ImportConfidence::SourceVerified);
    }

    #[test]
    fn test_definition_without_value_confidence() {
        let c = mock_constant("def_no_val", ConstantKind::Definition, false);
        assert_eq!(confidence_for(&c), ImportConfidence::Axiomatized);
    }

    #[test]
    fn test_inductive_confidence() {
        let c = mock_constant("Nat", ConstantKind::Inductive, false);
        assert_eq!(confidence_for(&c), ImportConfidence::SourceVerified);
    }

    // -----------------------------------------------------------------------
    // Module import tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_import_empty_module() {
        let module = mock_module(Vec::new());
        let mut writer = ShardWriter::new();
        let stats = import_module(&module, &mut writer).unwrap();
        assert_eq!(stats.total, 0);
        assert_eq!(stats.kernel_verified, 0);
        assert_eq!(stats.axiomatized, 0);
    }

    #[test]
    fn test_import_mixed_constants() {
        let constants = vec![
            mock_constant("Nat.add", ConstantKind::Definition, true),
            mock_constant("Nat.add_comm", ConstantKind::Theorem, true),
            mock_constant("Classical.choice", ConstantKind::Axiom, false),
            mock_constant("Nat", ConstantKind::Inductive, false),
            mock_constant("Nat.zero", ConstantKind::Constructor, false),
            mock_constant("Nat.rec", ConstantKind::Recursor, false),
            mock_constant("SomeOpaque", ConstantKind::Opaque, false),
        ];
        let module = mock_module(constants);
        let mut writer = ShardWriter::new();
        let stats = import_module(&module, &mut writer).unwrap();

        assert_eq!(stats.total, 7);
        assert_eq!(stats.kernel_verified, 5);
        assert_eq!(stats.axiomatized, 2);
        assert_eq!(stats.skipped, 0);
    }

    #[test]
    fn test_import_produces_correct_headers() {
        let constants = vec![
            mock_constant("propext", ConstantKind::Axiom, false),
            mock_constant("Nat.add", ConstantKind::Definition, true),
        ];
        let module = mock_module(constants);
        let mut writer = ShardWriter::new();
        import_module(&module, &mut writer).unwrap();

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        assert_eq!(reader.header.constant_count, 2);

        let c0 = &reader.constants[0];
        assert_eq!(reader.strings[c0.name_idx as usize], "propext");
        assert_eq!(c0.source_system, SourceSystem::Lean4 as u8);
        assert_eq!(c0.import_confidence, ImportConfidence::Axiomatized as u8);
        assert!(!c0.has_value());
        let profile0 = c0.profile();
        assert!(profile0.has(AxiomProfile::PROP_EXT));
        assert!(profile0.has(AxiomProfile::AXIOMATIZED));

        let c1 = &reader.constants[1];
        assert_eq!(reader.strings[c1.name_idx as usize], "Nat.add");
        assert_eq!(c1.import_confidence, ImportConfidence::SourceVerified as u8);
        assert!(c1.profile().is_pure());
    }

    #[test]
    fn test_import_module_verified_promotes_tc_verified_axiom() {
        let module = mock_module(vec![mock_constant(
            "verified_axiom",
            ConstantKind::Axiom,
            false,
        )]);
        let verified_names = std::collections::HashSet::from([String::from("verified_axiom")]);
        let mut writer = ShardWriter::new();

        let stats = import_module_verified(&module, &mut writer, Some(&verified_names)).unwrap();

        assert_eq!(stats.total, 1);
        assert_eq!(stats.kernel_verified, 1);
        assert_eq!(stats.axiomatized, 0);
        // Axiom heuristic is Axiomatized, so TC promotion counts.
        assert_eq!(stats.kernel_verified_from_tc, 1);

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        assert_eq!(
            reader.constants[0].import_confidence,
            ImportConfidence::KernelVerified as u8
        );
    }

    #[test]
    fn test_import_module_verified_keeps_heuristic_for_unverified_constant() {
        let module = mock_module(vec![mock_constant(
            "unverified_axiom",
            ConstantKind::Axiom,
            false,
        )]);
        let verified_names = std::collections::HashSet::from([String::from("other_constant")]);
        let mut writer = ShardWriter::new();

        let stats = import_module_verified(&module, &mut writer, Some(&verified_names)).unwrap();

        assert_eq!(stats.total, 1);
        assert_eq!(stats.kernel_verified, 0);
        assert_eq!(stats.axiomatized, 1);
        // Not in the verified set, so no TC promotion.
        assert_eq!(stats.kernel_verified_from_tc, 0);

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        assert_eq!(
            reader.constants[0].import_confidence,
            ImportConfidence::Axiomatized as u8
        );
    }

    #[test]
    fn test_import_module_verified_none_preserves_existing_behavior() {
        let module = mock_module(vec![
            mock_constant("axiom1", ConstantKind::Axiom, false),
            mock_constant("thm1", ConstantKind::Theorem, true),
        ]);
        let mut heuristic_writer = ShardWriter::new();
        let mut verified_writer = ShardWriter::new();

        let heuristic_stats = import_module(&module, &mut heuristic_writer).unwrap();
        let verified_stats = import_module_verified(&module, &mut verified_writer, None).unwrap();

        assert_eq!(verified_stats, heuristic_stats);

        let mut heuristic_buf = Vec::new();
        heuristic_writer.write(&mut heuristic_buf).unwrap();
        let heuristic_reader = crate::shard::ShardReader::from_bytes(&heuristic_buf).unwrap();

        let mut verified_buf = Vec::new();
        verified_writer.write(&mut verified_buf).unwrap();
        let verified_reader = crate::shard::ShardReader::from_bytes(&verified_buf).unwrap();

        let heuristic_confidences: Vec<u8> = heuristic_reader
            .constants
            .iter()
            .map(|constant| constant.import_confidence)
            .collect();
        let verified_confidences: Vec<u8> = verified_reader
            .constants
            .iter()
            .map(|constant| constant.import_confidence)
            .collect();
        assert_eq!(verified_confidences, heuristic_confidences);
    }

    #[test]
    fn test_import_module_verified_theorem_no_tc_promotion_count() {
        // A theorem-with-value already gets KernelVerified heuristically,
        // so TC verification should NOT increment kernel_verified_from_tc.
        let module = mock_module(vec![mock_constant(
            "my_theorem",
            ConstantKind::Theorem,
            true,
        )]);
        let verified_names = std::collections::HashSet::from([String::from("my_theorem")]);
        let mut writer = ShardWriter::new();

        let stats = import_module_verified(&module, &mut writer, Some(&verified_names)).unwrap();

        assert_eq!(stats.total, 1);
        assert_eq!(stats.kernel_verified, 1);
        // Heuristic already gives KernelVerified, so this is not a TC promotion.
        assert_eq!(stats.kernel_verified_from_tc, 0);
    }

    #[test]
    fn test_import_module_verified_mixed_constants_tc_tracking() {
        // Mix of axiom (TC-verified -> promotion) and theorem (TC-verified -> no promotion).
        let module = mock_module(vec![
            mock_constant("ax1", ConstantKind::Axiom, false),
            mock_constant("thm1", ConstantKind::Theorem, true),
            mock_constant("ax2", ConstantKind::Axiom, false),
        ]);
        let verified_names =
            std::collections::HashSet::from([String::from("ax1"), String::from("thm1")]);
        let mut writer = ShardWriter::new();

        let stats = import_module_verified(&module, &mut writer, Some(&verified_names)).unwrap();

        assert_eq!(stats.total, 3);
        // ax1 (TC->KV) + thm1 (heuristic KV) = 2 kernel_verified
        assert_eq!(stats.kernel_verified, 2);
        // ax2 not in verified set -> stays axiomatized
        assert_eq!(stats.axiomatized, 1);
        // Only ax1 is a TRUE promotion (heuristic was Axiomatized, TC overrode to KV)
        assert_eq!(stats.kernel_verified_from_tc, 1);
    }

    #[test]
    fn test_lean4_importer_struct() {
        let module = mock_module(vec![mock_constant("x", ConstantKind::Theorem, true)]);
        let importer = Lean4Importer::new(&module);
        assert_eq!(importer.module().constants.len(), 1);

        let mut writer = ShardWriter::new();
        let stats = importer.import(&mut writer).unwrap();
        assert_eq!(stats.total, 1);
        assert_eq!(stats.kernel_verified, 1);
    }

    // -----------------------------------------------------------------------
    // Binder info conversion tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_binder_info_to_u8() {
        assert_eq!(binder_info_to_u8(&ParsedBinderInfo::Default), 0);
        assert_eq!(binder_info_to_u8(&ParsedBinderInfo::Implicit), 1);
        assert_eq!(binder_info_to_u8(&ParsedBinderInfo::StrictImplicit), 2);
        assert_eq!(binder_info_to_u8(&ParsedBinderInfo::InstImplicit), 3);
        assert_eq!(binder_info_to_u8(&ParsedBinderInfo::Unknown(7)), 7);
    }

    // -----------------------------------------------------------------------
    // Level lowering tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_lower_level_zero() {
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let idx = ctx.lower_level(&ParsedLevel::Zero);
        assert_eq!(idx, 0);
    }

    #[test]
    fn test_lower_level_succ() {
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let level = ParsedLevel::Succ(Box::new(ParsedLevel::Zero));
        let idx = ctx.lower_level(&level);
        assert_eq!(idx, 1);
    }

    #[test]
    fn test_lower_level_max() {
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let level = ParsedLevel::Max(
            Box::new(ParsedLevel::Zero),
            Box::new(ParsedLevel::Succ(Box::new(ParsedLevel::Zero))),
        );
        let idx = ctx.lower_level(&level);
        // zero=0 (deduped for both occurrences), succ(0)=1, max(0,1)=2
        assert_eq!(idx, 2);
    }

    #[test]
    fn test_lower_level_imax() {
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let level = ParsedLevel::IMax(Box::new(ParsedLevel::Zero), Box::new(ParsedLevel::Zero));
        let idx = ctx.lower_level(&level);
        // zero=0 (deduped), imax(0,0)=1
        assert_eq!(idx, 1);
    }

    #[test]
    fn test_lower_level_param() {
        // The writer pre-seeds FlatLevel::zero at index 0, so the new
        // Param level lands at index 1, not 0.
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let level = ParsedLevel::Param("u".to_string());
        let idx = ctx.lower_level(&level);
        assert_eq!(idx, 1);
    }

    #[test]
    fn test_lower_level_mvar() {
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let level = ParsedLevel::MVar("?u".to_string());
        let idx = ctx.lower_level(&level);
        assert_eq!(idx, 1);
    }

    // -----------------------------------------------------------------------
    // Expression lowering tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_lower_expr_bvar() {
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let idx = ctx.lower_expr(&ParsedExpr::BVar(3));
        assert_eq!(idx, 0);
    }

    #[test]
    fn test_lower_expr_sort_roundtrip() {
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let expr = ParsedExpr::Sort(ParsedLevel::Zero);
        let idx = ctx.lower_expr(&expr);

        let mut buf = Vec::new();
        ctx.writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        assert_eq!(reader.header.level_count, 1);
        assert_eq!(reader.header.expr_count, 1);
        let e = &reader.exprs[idx as usize];
        assert_eq!(e.tag().unwrap(), FlatTag::Sort);
    }

    #[test]
    fn test_lower_expr_const_no_levels() {
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let expr = ParsedExpr::Const("Nat".to_string(), vec![]);
        let idx = ctx.lower_expr(&expr);

        let mut buf = Vec::new();
        ctx.writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        let e = &reader.exprs[idx as usize];
        assert_eq!(e.tag().unwrap(), FlatTag::Const);
        let name_idx = e.read_u32(0).unwrap();
        assert_eq!(reader.strings[name_idx as usize], "Nat");
        let levels_idx = e.read_u32(4).unwrap();
        assert_eq!(levels_idx, u32::MAX);
    }

    #[test]
    fn test_lower_expr_const_with_levels() {
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let expr = ParsedExpr::Const(
            "List".to_string(),
            vec![ParsedLevel::Param("u".to_string())],
        );
        let idx = ctx.lower_expr(&expr);

        let mut buf = Vec::new();
        ctx.writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        assert!(reader.header.level_count >= 1);
        let e = &reader.exprs[idx as usize];
        assert_eq!(e.tag, FlatTag::Const as u8);
    }

    #[test]
    fn test_lower_expr_app() {
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let expr = ParsedExpr::App(
            Box::new(ParsedExpr::Const("f".to_string(), vec![])),
            Box::new(ParsedExpr::BVar(0)),
        );
        let idx = ctx.lower_expr(&expr);

        let mut buf = Vec::new();
        ctx.writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        assert_eq!(reader.header.expr_count, 3);
        let e = &reader.exprs[idx as usize];
        assert_eq!(e.tag().unwrap(), FlatTag::App);
        assert_eq!(e.read_u32(0).unwrap(), 0); // fn_idx
        assert_eq!(e.read_u32(4).unwrap(), 1); // arg_idx
    }

    #[test]
    fn test_lower_expr_pi() {
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let expr = ParsedExpr::ForallE(
            "x".to_string(),
            Box::new(ParsedExpr::Const("Nat".to_string(), vec![])),
            Box::new(ParsedExpr::BVar(0)),
            ParsedBinderInfo::Default,
        );
        let idx = ctx.lower_expr(&expr);

        let mut buf = Vec::new();
        ctx.writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        let e = &reader.exprs[idx as usize];
        assert_eq!(e.tag().unwrap(), FlatTag::Pi);
        assert_eq!(e.data[0], 0); // binder_info = Default
    }

    #[test]
    fn test_lower_expr_lam() {
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let expr = ParsedExpr::Lam(
            "x".to_string(),
            Box::new(ParsedExpr::Const("Nat".to_string(), vec![])),
            Box::new(ParsedExpr::BVar(0)),
            ParsedBinderInfo::Implicit,
        );
        let idx = ctx.lower_expr(&expr);

        let mut buf = Vec::new();
        ctx.writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        let e = &reader.exprs[idx as usize];
        assert_eq!(e.tag().unwrap(), FlatTag::Lam);
        assert_eq!(e.data[0], 1); // binder_info = Implicit
    }

    #[test]
    fn test_lower_expr_let() {
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let nat = ParsedExpr::Const("Nat".to_string(), vec![]);
        let val = ParsedExpr::Lit(ParsedLiteral::Nat(BigNat::from_u64(42)));
        let body = ParsedExpr::BVar(0);
        let expr = ParsedExpr::LetE(
            "x".to_string(),
            Box::new(nat),
            Box::new(val),
            Box::new(body),
            false,
        );
        let idx = ctx.lower_expr(&expr);

        let mut buf = Vec::new();
        ctx.writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        let e = &reader.exprs[idx as usize];
        assert_eq!(e.tag().unwrap(), FlatTag::Let);
        assert_eq!(reader.header.expr_count, 4);
    }

    #[test]
    fn test_lower_expr_lit_nat() {
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let expr = ParsedExpr::Lit(ParsedLiteral::Nat(BigNat::from_u64(999)));
        let idx = ctx.lower_expr(&expr);

        let mut buf = Vec::new();
        ctx.writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        let e = &reader.exprs[idx as usize];
        assert_eq!(e.tag().unwrap(), FlatTag::LitNat);
        assert_eq!(e.read_u64(0).unwrap(), 999);
    }

    #[test]
    fn test_lower_expr_lit_nat_big() {
        // A Nat literal exceeding u64::MAX is now stored FAITHFULLY via the
        // NAT_BIG flag (decimal limbs in the string table), not silently
        // truncated to u64::MAX. Reconstructing it must reproduce the exact value.
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let big = BigNat::from_limbs(vec![u64::MAX, 1]); // = 2^64 + (2^64 - 1)
        let expr = ParsedExpr::Lit(ParsedLiteral::Nat(big));
        let idx = ctx.lower_expr(&expr);

        let mut buf = Vec::new();
        ctx.writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        let e = &reader.exprs[idx as usize];
        // Tag stays LitNat, but the NAT_BIG flag is set and the inline u64 is 0;
        // data[0..4] indexes the limb string.
        assert_eq!(e.tag().unwrap(), FlatTag::LitNat);
        assert!(e.flags().contains(clean_kernel::flat::FlatFlags::NAT_BIG));
        // Full reconstruct must yield the exact BigNat (not a truncation).
        let recon = crate::shard_reconstruct::reconstruct_from_shard(
            &reader.exprs,
            &reader.levels,
            &reader.strings,
            idx,
        )
        .expect("reconstruct NAT_BIG literal");
        use clean_kernel::expr::{BigNat as KBigNat, ExprKind, Literal};
        match recon.kind() {
            ExprKind::Lit(Literal::Nat(n)) => {
                assert_eq!(*n, KBigNat::from_limbs(vec![u64::MAX, 1]));
            }
            other => panic!("expected Nat literal, got {other:?}"),
        }
    }

    #[test]
    fn test_lower_expr_lit_string() {
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let expr = ParsedExpr::Lit(ParsedLiteral::String("hello".to_string()));
        let idx = ctx.lower_expr(&expr);

        let mut buf = Vec::new();
        ctx.writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        let e = &reader.exprs[idx as usize];
        assert_eq!(e.tag().unwrap(), FlatTag::LitStr);
        let str_idx = e.read_u32(0).unwrap();
        assert_eq!(reader.strings[str_idx as usize], "hello");
    }

    #[test]
    fn test_lower_expr_proj() {
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let expr = ParsedExpr::Proj("Prod".to_string(), 1, Box::new(ParsedExpr::BVar(0)));
        let idx = ctx.lower_expr(&expr);

        let mut buf = Vec::new();
        ctx.writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        let e = &reader.exprs[idx as usize];
        assert_eq!(e.tag().unwrap(), FlatTag::Proj);
        let name_idx = e.read_u32(0).unwrap();
        assert_eq!(reader.strings[name_idx as usize], "Prod");
        assert_eq!(e.read_u16(4).unwrap(), 1);
    }

    #[test]
    fn test_lower_expr_fvar() {
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let expr = ParsedExpr::FVar("x".to_string());
        let idx = ctx.lower_expr(&expr);

        let mut buf = Vec::new();
        ctx.writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        let e = &reader.exprs[idx as usize];
        assert_eq!(e.tag().unwrap(), FlatTag::FVar);
        let fvar_id = e.read_u64(0).unwrap();
        assert_ne!(fvar_id, 0);
    }

    #[test]
    fn test_lower_expr_mdata_transparent() {
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let inner = ParsedExpr::BVar(5);
        let expr = ParsedExpr::MData(Box::new(inner));
        let idx = ctx.lower_expr(&expr);

        let mut buf = Vec::new();
        ctx.writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        assert_eq!(reader.header.expr_count, 1);
        let e = &reader.exprs[idx as usize];
        assert_eq!(e.tag, FlatTag::BVar as u8);
    }

    // -----------------------------------------------------------------------
    // String dedup test
    // -----------------------------------------------------------------------

    #[test]
    fn test_intern_string_dedup() {
        let mut writer = ShardWriter::new();
        let mut ctx = LoweringCtx::new(&mut writer);
        let idx1 = ctx.intern_string("Nat");
        let idx2 = ctx.intern_string("Nat");
        let idx3 = ctx.intern_string("Bool");
        assert_eq!(idx1, idx2, "Same string should return same index");
        assert_ne!(
            idx1, idx3,
            "Different strings should return different indices"
        );
    }

    // -----------------------------------------------------------------------
    // Round-trip: lower -> shard write -> shard read -> verify structure
    // -----------------------------------------------------------------------

    #[test]
    fn test_lowering_round_trip_shard() {
        let type_expr = ParsedExpr::ForallE(
            "n".to_string(),
            Box::new(ParsedExpr::Const("Nat".to_string(), vec![])),
            Box::new(ParsedExpr::Const("Nat".to_string(), vec![])),
            ParsedBinderInfo::Default,
        );
        let val_expr = ParsedExpr::Lam(
            "n".to_string(),
            Box::new(ParsedExpr::Const("Nat".to_string(), vec![])),
            Box::new(ParsedExpr::BVar(0)),
            ParsedBinderInfo::Default,
        );
        let constant = ParsedConstant {
            definition_safety: None,
            quot_kind: None,
            name: "Nat.id".to_string(),
            kind: ConstantKind::Definition,
            level_params: Vec::new(),
            type_: Some(type_expr),
            value: Some(val_expr),
            inductive_val: None,
            constructor_val: None,
            recursor_val: None,
            hints: None,
        };
        let module = mock_module(vec![constant]);

        let mut writer = ShardWriter::new();
        let stats = import_module(&module, &mut writer).unwrap();
        assert_eq!(stats.total, 1);
        assert_eq!(stats.kernel_verified, 1);

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        assert_eq!(reader.header.constant_count, 1);
        let c = &reader.constants[0];
        assert_eq!(reader.strings[c.name_idx as usize], "Nat.id");
        assert!(c.has_value());

        let type_e = &reader.exprs[c.type_idx as usize];
        assert_eq!(type_e.tag().unwrap(), FlatTag::Pi);

        let val_e = &reader.exprs[c.value_idx as usize];
        assert_eq!(val_e.tag().unwrap(), FlatTag::Lam);

        assert!(reader.strings.contains(&"Nat".to_string()));
        assert!(reader.strings.contains(&"Nat.id".to_string()));
    }

    #[test]
    fn test_lowering_sort_round_trip() {
        let type_expr = ParsedExpr::Sort(ParsedLevel::Succ(Box::new(ParsedLevel::Zero)));
        let constant = ParsedConstant {
            definition_safety: None,
            quot_kind: None,
            name: "MySort".to_string(),
            kind: ConstantKind::Definition,
            level_params: Vec::new(),
            type_: Some(type_expr),
            value: Some(ParsedExpr::Sort(ParsedLevel::Zero)),
            inductive_val: None,
            constructor_val: None,
            recursor_val: None,
            hints: None,
        };
        let module = mock_module(vec![constant]);

        let mut writer = ShardWriter::new();
        import_module(&module, &mut writer).unwrap();

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        let c = &reader.constants[0];
        let type_e = &reader.exprs[c.type_idx as usize];
        assert_eq!(type_e.tag().unwrap(), FlatTag::Sort);
        assert!(reader.header.level_count >= 2);
    }

    // -----------------------------------------------------------------------
    // Dependency extraction tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_extract_deps_single_const() {
        // Arena: [Const(name_idx=7)]
        let exprs = vec![FlatExpr::const_ref(7, u32::MAX)];
        let deps = extract_deps(&exprs, 0);
        assert_eq!(deps, vec![7]);
    }

    #[test]
    fn test_extract_deps_app_two_consts() {
        // Arena: [Const(3), Const(5), App(0, 1)]
        let exprs = vec![
            FlatExpr::const_ref(3, u32::MAX),
            FlatExpr::const_ref(5, u32::MAX),
            FlatExpr::app(0, 1),
        ];
        let deps = extract_deps(&exprs, 2);
        assert_eq!(deps, vec![3, 5]);
    }

    #[test]
    fn test_extract_deps_pi_two_consts() {
        // Arena: [Const(10), Const(20), Pi(binder=0, ty=0, body=1)]
        let exprs = vec![
            FlatExpr::const_ref(10, u32::MAX),
            FlatExpr::const_ref(20, u32::MAX),
            FlatExpr::pi(0, 0, 1),
        ];
        let deps = extract_deps(&exprs, 2);
        assert_eq!(deps, vec![10, 20]);
    }

    #[test]
    fn test_extract_deps_lam_two_consts() {
        // Arena: [Const(10), Const(20), Lam(binder=1, ty=0, body=1)]
        let exprs = vec![
            FlatExpr::const_ref(10, u32::MAX),
            FlatExpr::const_ref(20, u32::MAX),
            FlatExpr::lam(1, 0, 1),
        ];
        let deps = extract_deps(&exprs, 2);
        assert_eq!(deps, vec![10, 20]);
    }

    #[test]
    fn test_extract_deps_let_three_consts() {
        // Arena: [Const(1), Const(2), Const(3), Let(ty=0, val=1, body=2)]
        let exprs = vec![
            FlatExpr::const_ref(1, u32::MAX),
            FlatExpr::const_ref(2, u32::MAX),
            FlatExpr::const_ref(3, u32::MAX),
            FlatExpr::let_expr(0, 1, 2),
        ];
        let deps = extract_deps(&exprs, 3);
        assert_eq!(deps, vec![1, 2, 3]);
    }

    #[test]
    fn test_extract_deps_proj() {
        // Arena: [Const(42), Proj(name=0, field=1, expr=0)]
        let exprs = vec![FlatExpr::const_ref(42, u32::MAX), FlatExpr::proj(0, 1, 0)];
        let deps = extract_deps(&exprs, 1);
        assert_eq!(deps, vec![42]);
    }

    #[test]
    fn test_extract_deps_nested() {
        // Pi(Const(A), App(Const(B), Const(C)))
        // Arena: [Const(A=1), Const(B=2), Const(C=3), App(1, 2), Pi(bi=0, ty=0, body=3)]
        let exprs = vec![
            FlatExpr::const_ref(1, u32::MAX), // idx 0
            FlatExpr::const_ref(2, u32::MAX), // idx 1
            FlatExpr::const_ref(3, u32::MAX), // idx 2
            FlatExpr::app(1, 2),              // idx 3
            FlatExpr::pi(0, 0, 3),            // idx 4
        ];
        let deps = extract_deps(&exprs, 4);
        assert_eq!(deps, vec![1, 2, 3]);
    }

    #[test]
    fn test_extract_deps_no_consts() {
        // Arena: [BVar(0), Sort(level=0)]
        // No FlatLevel pool needed since we're only inspecting tags.
        let exprs = vec![FlatExpr::bvar(0), FlatExpr::sort(0)];
        let deps = extract_deps(&exprs, 0);
        assert!(deps.is_empty());
        let deps = extract_deps(&exprs, 1);
        assert!(deps.is_empty());
    }

    #[test]
    fn test_extract_deps_dedup() {
        // Same constant referenced twice: App(Const(5), Const(5))
        // Arena: [Const(5), App(0, 0)]
        let exprs = vec![FlatExpr::const_ref(5, u32::MAX), FlatExpr::app(0, 0)];
        let deps = extract_deps(&exprs, 1);
        assert_eq!(
            deps,
            vec![5],
            "Duplicate const references should be deduped"
        );
    }

    #[test]
    fn test_extract_deps_empty_arena() {
        let exprs: Vec<FlatExpr> = vec![];
        let deps = extract_deps(&exprs, 0);
        assert!(deps.is_empty());
    }

    #[test]
    fn test_extract_deps_out_of_bounds_root() {
        let exprs = vec![FlatExpr::bvar(0)];
        let deps = extract_deps(&exprs, 99);
        assert!(deps.is_empty());
    }

    #[test]
    fn test_extract_deps_cycle_safe() {
        // If we somehow have a cycle (App(1, 0), App(0, 0)), the visited
        // set should prevent infinite recursion.
        let exprs = vec![
            FlatExpr::app(1, 0), // idx 0 -> fn=1, arg=0
            FlatExpr::app(0, 0), // idx 1 -> fn=0, arg=0
        ];
        let deps = extract_deps(&exprs, 0);
        // No Const nodes in the cycle, so no deps.
        assert!(deps.is_empty());
    }

    // -----------------------------------------------------------------------
    // Full pipeline integration test
    // -----------------------------------------------------------------------

    /// Helper: build a ParsedConstant with a type expression and optional
    /// value expression, using all constructor parameters.
    fn rich_constant(
        name: &str,
        kind: ConstantKind,
        type_expr: ParsedExpr,
        value_expr: Option<ParsedExpr>,
    ) -> ParsedConstant {
        ParsedConstant {
            definition_safety: None,
            quot_kind: None,
            name: name.to_string(),
            kind,
            level_params: Vec::new(),
            type_: Some(type_expr),
            value: value_expr,
            inductive_val: None,
            constructor_val: None,
            recursor_val: None,
            hints: None,
        }
    }

    #[test]
    fn test_full_pipeline_integration() {
        // Build a module with ~10 constants spanning all constant kinds.
        // Use non-trivial type expressions to exercise the full lowering
        // pipeline and dependency extraction.

        let nat_const = || ParsedExpr::Const("Nat".to_string(), vec![]);
        let bool_const = || ParsedExpr::Const("Bool".to_string(), vec![]);
        let prop = || ParsedExpr::Sort(ParsedLevel::Zero);
        let type0 = || ParsedExpr::Sort(ParsedLevel::Succ(Box::new(ParsedLevel::Zero)));

        // Pi (n : Nat) -> Nat
        let nat_to_nat = || {
            ParsedExpr::ForallE(
                "n".to_string(),
                Box::new(nat_const()),
                Box::new(nat_const()),
                ParsedBinderInfo::Default,
            )
        };

        // Pi (n : Nat) -> Prop
        let nat_to_prop = || {
            ParsedExpr::ForallE(
                "n".to_string(),
                Box::new(nat_const()),
                Box::new(prop()),
                ParsedBinderInfo::Default,
            )
        };

        // App(Const("List"), Const("Nat")) — simulating List Nat
        let list_nat = || {
            ParsedExpr::App(
                Box::new(ParsedExpr::Const(
                    "List".to_string(),
                    vec![ParsedLevel::Param("u".to_string())],
                )),
                Box::new(nat_const()),
            )
        };

        // Lam (x : Nat) => x — identity function
        let nat_id = || {
            ParsedExpr::Lam(
                "x".to_string(),
                Box::new(nat_const()),
                Box::new(ParsedExpr::BVar(0)),
                ParsedBinderInfo::Default,
            )
        };

        let constants = vec![
            // 0: Theorem with proof (Nat.add_comm : Pi Nat -> Nat -> Prop)
            rich_constant(
                "Nat.add_comm",
                ConstantKind::Theorem,
                nat_to_prop(),
                Some(nat_id()),
            ),
            // 1: Definition with value (Nat.id : Nat -> Nat)
            rich_constant(
                "Nat.id",
                ConstantKind::Definition,
                nat_to_nat(),
                Some(nat_id()),
            ),
            // 2: Axiom — no value
            rich_constant("Classical.choice", ConstantKind::Axiom, type0(), None),
            // 3: Inductive (Nat : Type)
            rich_constant("Nat", ConstantKind::Inductive, type0(), None),
            // 4: Constructor (Nat.zero : Nat)
            rich_constant("Nat.zero", ConstantKind::Constructor, nat_const(), None),
            // 5: Constructor (Nat.succ : Nat -> Nat)
            rich_constant("Nat.succ", ConstantKind::Constructor, nat_to_nat(), None),
            // 6: Recursor
            rich_constant("Nat.rec", ConstantKind::Recursor, nat_to_nat(), None),
            // 7: Opaque — trust-gated
            rich_constant("SomeOpaque", ConstantKind::Opaque, type0(), None),
            // 8: Quot
            rich_constant("Quot", ConstantKind::Quot, type0(), None),
            // 9: Definition with complex type (uses List, Nat, Bool)
            rich_constant(
                "List.head",
                ConstantKind::Definition,
                ParsedExpr::ForallE(
                    "xs".to_string(),
                    Box::new(list_nat()),
                    Box::new(bool_const()),
                    ParsedBinderInfo::Default,
                ),
                Some(nat_id()),
            ),
        ];

        let module = mock_module(constants);

        // 1. Import into shard writer
        let mut writer = ShardWriter::new();
        let stats = import_module(&module, &mut writer).unwrap();

        // Verify stats
        assert_eq!(stats.total, 10);
        // Theorem(proof=yes), Definition(val=yes), Inductive, Constructor x2,
        // Recursor, Quot, Definition(val=yes) = 8 kernel verified
        assert_eq!(stats.kernel_verified, 8);
        // Axiom(Classical.choice), Opaque(SomeOpaque) = 2 axiomatized
        assert_eq!(stats.axiomatized, 2);
        assert_eq!(stats.skipped, 0);

        // 2. Write to shard and read back
        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        // 3. Verify constant count
        assert_eq!(reader.header.constant_count, 10);
        assert_eq!(reader.constants.len(), 10);

        // 4. Verify names match
        let names: Vec<&str> = reader
            .constants
            .iter()
            .map(|c| reader.strings[c.name_idx as usize].as_str())
            .collect();
        assert_eq!(names[0], "Nat.add_comm");
        assert_eq!(names[1], "Nat.id");
        assert_eq!(names[2], "Classical.choice");
        assert_eq!(names[3], "Nat");
        assert_eq!(names[4], "Nat.zero");
        assert_eq!(names[5], "Nat.succ");
        assert_eq!(names[6], "Nat.rec");
        assert_eq!(names[7], "SomeOpaque");
        assert_eq!(names[8], "Quot");
        assert_eq!(names[9], "List.head");

        // 5. Verify axiom profiles
        let c2 = &reader.constants[2]; // Classical.choice
        let prof2 = c2.profile();
        assert!(prof2.has(AxiomProfile::CHOICE));
        assert!(prof2.has(AxiomProfile::CLASSICAL));
        assert!(prof2.has(AxiomProfile::AXIOMATIZED));
        assert!(prof2.is_trust_gated());

        let c7 = &reader.constants[7]; // SomeOpaque
        let prof7 = c7.profile();
        assert!(prof7.has(AxiomProfile::AXIOMATIZED));
        assert!(prof7.is_trust_gated());

        let c8 = &reader.constants[8]; // Quot
        let prof8 = c8.profile();
        assert!(prof8.has(AxiomProfile::QUOT));
        assert!(!prof8.is_trust_gated());

        let c0 = &reader.constants[0]; // Nat.add_comm (Theorem)
        assert!(c0.profile().is_pure());
        assert!(!c0.is_trust_gated());

        // 6. Verify has_value correct
        assert!(reader.constants[0].has_value()); // Theorem with proof
        assert!(reader.constants[1].has_value()); // Definition with value
        assert!(!reader.constants[2].has_value()); // Axiom
        assert!(!reader.constants[3].has_value()); // Inductive (no value, real type)
        assert!(!reader.constants[4].has_value()); // Constructor (no value, real type)
        assert!(!reader.constants[5].has_value()); // Constructor (no value, real type)
        assert!(!reader.constants[6].has_value()); // Recursor (no value expr provided)
        assert!(!reader.constants[7].has_value()); // Opaque
        assert!(!reader.constants[8].has_value()); // Quot (no value expr provided)
        assert!(reader.constants[9].has_value()); // Definition with value

        // 7. Verify expression indices are in bounds
        let expr_count = reader.header.expr_count;
        for (i, c) in reader.constants.iter().enumerate() {
            assert!(
                c.type_idx < expr_count,
                "constant {i} type_idx {} out of bounds (expr_count={})",
                c.type_idx,
                expr_count
            );
            if c.has_value() {
                assert!(
                    c.value_idx < expr_count,
                    "constant {i} value_idx {} out of bounds (expr_count={})",
                    c.value_idx,
                    expr_count
                );
            }
        }

        // 8. Verify expression tag structure for key constants
        let type_expr_0 = &reader.exprs[reader.constants[0].type_idx as usize];
        assert_eq!(type_expr_0.tag().unwrap(), FlatTag::Pi);

        let type_expr_3 = &reader.exprs[reader.constants[3].type_idx as usize];
        assert_eq!(type_expr_3.tag().unwrap(), FlatTag::Sort);

        let type_expr_4 = &reader.exprs[reader.constants[4].type_idx as usize];
        assert_eq!(type_expr_4.tag().unwrap(), FlatTag::Const);

        let type_expr_9 = &reader.exprs[reader.constants[9].type_idx as usize];
        assert_eq!(type_expr_9.tag().unwrap(), FlatTag::Pi);

        // 9. Verify dependency extraction works on the type expressions.
        // Nat.add_comm has type Pi(Nat, Prop) — should reference "Nat" name
        let deps_0 = extract_deps(&reader.exprs, reader.constants[0].type_idx);
        assert!(
            !deps_0.is_empty(),
            "Nat.add_comm type should reference at least one constant"
        );
        // The Nat name_idx should be in the deps
        let nat_name_idx = reader
            .strings
            .iter()
            .position(|s| s == "Nat")
            .expect("Nat should be in string table") as u32;
        assert!(
            deps_0.contains(&nat_name_idx),
            "Nat.add_comm type should reference Nat, deps={deps_0:?}"
        );

        // List.head has type Pi(App(List, Nat), Bool) — should reference
        // List, Nat, Bool
        let deps_9 = extract_deps(&reader.exprs, reader.constants[9].type_idx);
        let list_name_idx = reader
            .strings
            .iter()
            .position(|s| s == "List")
            .expect("List should be in string table") as u32;
        let bool_name_idx = reader
            .strings
            .iter()
            .position(|s| s == "Bool")
            .expect("Bool should be in string table") as u32;
        assert!(
            deps_9.contains(&list_name_idx),
            "List.head type should reference List"
        );
        assert!(
            deps_9.contains(&nat_name_idx),
            "List.head type should reference Nat"
        );
        assert!(
            deps_9.contains(&bool_name_idx),
            "List.head type should reference Bool"
        );

        // 10. Verify trust filtering: trust-gated constants should be
        //     precisely the axiom and opaque ones.
        let trust_gated: Vec<&str> = reader
            .constants
            .iter()
            .filter(|c| c.is_trust_gated())
            .map(|c| reader.strings[c.name_idx as usize].as_str())
            .collect();
        assert_eq!(
            trust_gated,
            vec!["Classical.choice", "SomeOpaque"],
            "Only Axiom and Opaque constants should be trust-gated"
        );

        // 11. Verify source system is Lean4 for all constants.
        for c in &reader.constants {
            assert_eq!(c.source_system, SourceSystem::Lean4 as u8);
        }

        // 12. Verify string table contains expected names.
        assert!(reader.strings.contains(&"Nat".to_string()));
        assert!(reader.strings.contains(&"Bool".to_string()));
        assert!(reader.strings.contains(&"List".to_string()));
        assert!(reader.strings.contains(&"Nat.add_comm".to_string()));
        assert!(reader.strings.contains(&"List.head".to_string()));
    }

    /// Verify decl_kind and is_inductive_family for all constant kinds
    /// through the full pipeline (companion to test_full_pipeline_integration).
    #[test]
    fn test_pipeline_decl_kind_and_inductive_family() {
        use crate::types::DeclKind;
        let nat_const = || ParsedExpr::Const("Nat".to_string(), vec![]);
        let prop = || ParsedExpr::Sort(ParsedLevel::Zero);
        let type0 = || ParsedExpr::Sort(ParsedLevel::Succ(Box::new(ParsedLevel::Zero)));
        let nat_to_nat = || {
            ParsedExpr::ForallE(
                "n".to_string(),
                Box::new(nat_const()),
                Box::new(nat_const()),
                ParsedBinderInfo::Default,
            )
        };
        let nat_id = || {
            ParsedExpr::Lam(
                "x".to_string(),
                Box::new(nat_const()),
                Box::new(ParsedExpr::BVar(0)),
                ParsedBinderInfo::Default,
            )
        };
        let nat_to_prop = || {
            ParsedExpr::ForallE(
                "n".to_string(),
                Box::new(nat_const()),
                Box::new(prop()),
                ParsedBinderInfo::Default,
            )
        };
        let constants = vec![
            rich_constant(
                "Nat.add_comm",
                ConstantKind::Theorem,
                nat_to_prop(),
                Some(nat_id()),
            ),
            rich_constant(
                "Nat.id",
                ConstantKind::Definition,
                nat_to_nat(),
                Some(nat_id()),
            ),
            rich_constant("Classical.choice", ConstantKind::Axiom, type0(), None),
            rich_constant("Nat", ConstantKind::Inductive, type0(), None),
            rich_constant("Nat.zero", ConstantKind::Constructor, nat_const(), None),
            rich_constant("Nat.succ", ConstantKind::Constructor, nat_to_nat(), None),
            rich_constant("Nat.rec", ConstantKind::Recursor, nat_to_nat(), None),
            rich_constant("SomeOpaque", ConstantKind::Opaque, type0(), None),
            rich_constant("Quot", ConstantKind::Quot, type0(), None),
            rich_constant(
                "List.head",
                ConstantKind::Definition,
                type0(),
                Some(nat_id()),
            ),
        ];
        let module = mock_module(constants);
        let mut writer = ShardWriter::new();
        import_module(&module, &mut writer).unwrap();
        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        // decl_kind
        let expected_kinds: &[u8] = &[
            DeclKind::Theorem as u8,
            DeclKind::Definition as u8,
            DeclKind::Axiom as u8,
            DeclKind::Inductive as u8,
            DeclKind::Constructor as u8,
            DeclKind::Constructor as u8,
            DeclKind::Recursor as u8,
            DeclKind::Opaque as u8,
            DeclKind::Quot as u8,
            DeclKind::Definition as u8,
        ];
        for (i, &expected) in expected_kinds.iter().enumerate() {
            assert_eq!(
                reader.constants[i].decl_kind, expected,
                "constant {i} decl_kind"
            );
        }
        // is_inductive_family: true for indices 3,4,5,6 (Inductive/Constructor/Recursor)
        let inductive_family_expected = [
            false, false, false, true, true, true, true, false, false, false,
        ];
        for (i, &expected) in inductive_family_expected.iter().enumerate() {
            assert_eq!(
                reader.constants[i].is_inductive_family(),
                expected,
                "constant {i} is_inductive_family"
            );
        }
    }

    // -----------------------------------------------------------------------
    // Inductive type reconstruction test
    // -----------------------------------------------------------------------

    #[test]
    fn test_inductive_uses_real_type_not_placeholder() {
        // Verify inductives get real type expressions, not Sort(0) placeholders.
        let type0 = || ParsedExpr::Sort(ParsedLevel::Succ(Box::new(ParsedLevel::Zero)));
        let nat_const = || ParsedExpr::Const("Nat".to_string(), vec![]);
        let nat_to_nat = || {
            ParsedExpr::ForallE(
                "n".to_string(),
                Box::new(nat_const()),
                Box::new(nat_const()),
                ParsedBinderInfo::Default,
            )
        };
        let constants = vec![
            rich_constant("Nat", ConstantKind::Inductive, type0(), None),
            rich_constant("Nat.zero", ConstantKind::Constructor, nat_const(), None),
            rich_constant("Nat.succ", ConstantKind::Constructor, nat_to_nat(), None),
            rich_constant("Nat.rec", ConstantKind::Recursor, nat_to_nat(), None),
        ];
        let module = mock_module(constants);
        let mut writer = ShardWriter::new();
        let stats = import_module(&module, &mut writer).unwrap();
        assert_eq!(stats.total, 4);
        assert_eq!(stats.kernel_verified, 4);
        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        // Nat: type should be Sort (Sort 1 = Type), not placeholder
        let nat_h = &reader.constants[0];
        assert_eq!(nat_h.decl_kind, DeclKind::Inductive as u8);
        assert!(!nat_h.has_value());
        assert_eq!(
            reader.exprs[nat_h.type_idx as usize].tag().unwrap(),
            FlatTag::Sort,
            "Nat type"
        );
        // Nat.zero: type should be Const (referencing Nat)
        let zero_h = &reader.constants[1];
        assert_eq!(zero_h.decl_kind, DeclKind::Constructor as u8);
        assert!(!zero_h.has_value());
        assert_eq!(
            reader.exprs[zero_h.type_idx as usize].tag().unwrap(),
            FlatTag::Const,
            "Nat.zero type"
        );
        // Nat.succ: type should be Pi (Nat -> Nat)
        let succ_h = &reader.constants[2];
        assert_eq!(succ_h.decl_kind, DeclKind::Constructor as u8);
        assert!(!succ_h.has_value());
        assert_eq!(
            reader.exprs[succ_h.type_idx as usize].tag().unwrap(),
            FlatTag::Pi,
            "Nat.succ type"
        );
        // Nat.rec: type should be Pi (Nat -> Nat)
        let rec_h = &reader.constants[3];
        assert_eq!(rec_h.decl_kind, DeclKind::Recursor as u8);
        assert!(!rec_h.has_value());
        assert_eq!(
            reader.exprs[rec_h.type_idx as usize].tag().unwrap(),
            FlatTag::Pi,
            "Nat.rec type"
        );
    }

    #[test]
    fn test_decl_kind_round_trip_through_shard() {
        use crate::types::DeclKind;

        // Create constants of each kind and verify decl_kind survives
        // write/read round-trip through the shard format.
        let prop = || ParsedExpr::Sort(ParsedLevel::Zero);
        let constants = vec![
            rich_constant("thm", ConstantKind::Theorem, prop(), Some(prop())),
            rich_constant("def1", ConstantKind::Definition, prop(), Some(prop())),
            rich_constant("ax1", ConstantKind::Axiom, prop(), None),
            rich_constant("opq", ConstantKind::Opaque, prop(), None),
            rich_constant("ind", ConstantKind::Inductive, prop(), None),
            rich_constant("ctor", ConstantKind::Constructor, prop(), None),
            rich_constant("rec", ConstantKind::Recursor, prop(), None),
            rich_constant("quot", ConstantKind::Quot, prop(), None),
        ];
        let module = mock_module(constants);

        let mut writer = ShardWriter::new();
        import_module(&module, &mut writer).unwrap();

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        assert_eq!(reader.constants[0].decl_kind, DeclKind::Theorem as u8);
        assert_eq!(reader.constants[1].decl_kind, DeclKind::Definition as u8);
        assert_eq!(reader.constants[2].decl_kind, DeclKind::Axiom as u8);
        assert_eq!(reader.constants[3].decl_kind, DeclKind::Opaque as u8);
        assert_eq!(reader.constants[4].decl_kind, DeclKind::Inductive as u8);
        assert_eq!(reader.constants[5].decl_kind, DeclKind::Constructor as u8);
        assert_eq!(reader.constants[6].decl_kind, DeclKind::Recursor as u8);
        assert_eq!(reader.constants[7].decl_kind, DeclKind::Quot as u8);
    }

    // -----------------------------------------------------------------------
    // Level-parameter contiguity (WS11 regression)
    // -----------------------------------------------------------------------

    /// WS11 REGRESSION: the level-parameter `[start..start+count)` string-table
    /// window must reconstruct to the EXACT declared parameter names even when a
    /// parameter name was already interned while lowering the constant's type or
    /// value.
    ///
    /// Before the fix, level params were interned one-by-one: a name already in
    /// the table (here `u`, referenced by `Sort u` in the type) deduped to its
    /// earlier index, so `lp_start` pointed at that scattered slot and the window
    /// read `[u, <whatever string follows u>]` instead of `[u, v]`. On real
    /// Mathlib decls this surfaced as a spurious `UndefinedLevelParam`
    /// rejection (e.g. `Prod.map_injective` "undefined u_3").
    #[test]
    fn test_level_params_contiguous_when_name_already_interned() {
        use crate::shard_reconstruct::reconstruct_level_params;

        // type = Sort u  (forces `u` into the string table BEFORE the param block)
        // params = [u, v]   (`v` appears nowhere else)
        let type_expr = ParsedExpr::Sort(ParsedLevel::Param("u".to_string()));
        let mut constant = rich_constant(
            "Test.levelParamScatter",
            ConstantKind::Definition,
            type_expr,
            Some(ParsedExpr::Sort(ParsedLevel::Param("u".to_string()))),
        );
        constant.level_params = vec!["u".to_string(), "v".to_string()];

        let module = mock_module(vec![constant]);
        let mut writer = ShardWriter::new();
        import_module(&module, &mut writer).unwrap();

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        let c = &reader.constants[0];
        assert_eq!(c.level_params_count, 2, "count must survive the round-trip");

        let params =
            reconstruct_level_params(&reader.strings, c.level_params_start, c.level_params_count)
                .expect("level params reconstruct");
        let names: Vec<String> = params.iter().map(ToString::to_string).collect();
        assert_eq!(
            names,
            vec!["u".to_string(), "v".to_string()],
            "the param window must read EXACTLY the declared params, not scattered neighbours"
        );
    }

    /// WS11 SOUNDNESS: the contiguous-block fix must not let a constant that
    /// genuinely references an UNDECLARED universe parameter slip through. Its
    /// type references `v` but only `u` is declared, so the reconstructed param
    /// list must NOT contain `v` — the downstream kernel `add_decl`
    /// `find_undef_level_param` check then still rejects it (`UndefinedLevelParam`).
    #[test]
    fn test_level_params_undeclared_param_not_smuggled_in() {
        use crate::shard_reconstruct::reconstruct_level_params;

        // type references BOTH u and v, but only u is declared.
        let type_expr = ParsedExpr::ForallE(
            "x".to_string(),
            Box::new(ParsedExpr::Sort(ParsedLevel::Param("u".to_string()))),
            Box::new(ParsedExpr::Sort(ParsedLevel::Param("v".to_string()))),
            ParsedBinderInfo::Default,
        );
        let mut constant =
            rich_constant("Test.undeclaredParam", ConstantKind::Axiom, type_expr, None);
        constant.level_params = vec!["u".to_string()];

        let module = mock_module(vec![constant]);
        let mut writer = ShardWriter::new();
        import_module(&module, &mut writer).unwrap();

        let mut buf = Vec::new();
        writer.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();

        let c = &reader.constants[0];
        assert_eq!(c.level_params_count, 1);
        let params =
            reconstruct_level_params(&reader.strings, c.level_params_start, c.level_params_count)
                .expect("level params reconstruct");
        let names: Vec<String> = params.iter().map(ToString::to_string).collect();
        assert_eq!(
            names,
            vec!["u".to_string()],
            "only the genuinely-declared param may appear; the undeclared `v` must stay out"
        );
        assert!(
            !names.contains(&"v".to_string()),
            "the contiguity fix must NOT smuggle an undeclared param into the declared list"
        );
    }

    // -----------------------------------------------------------------------
    // ProofInfo tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_info_theorem_with_proof() {
        let c = mock_constant("thm", ConstantKind::Theorem, true);
        let info = extract_proof_info(&c);
        assert!(info.is_theorem);
        assert!(!info.is_opaque);
        assert!(!info.has_sorry);
        // Sort(Zero) is a single node.
        assert_eq!(info.proof_size, 1);
    }

    #[test]
    fn test_proof_info_opaque() {
        let c = mock_constant("op", ConstantKind::Opaque, false);
        let info = extract_proof_info(&c);
        assert!(!info.is_theorem);
        assert!(info.is_opaque);
        assert_eq!(info.proof_size, 0);
    }

    #[test]
    fn test_proof_info_detects_sorry() {
        let sorry_expr = ParsedExpr::App(
            Box::new(ParsedExpr::Const("sorryAx".to_string(), vec![])),
            Box::new(ParsedExpr::BVar(0)),
        );
        let c = ParsedConstant {
            definition_safety: None,
            quot_kind: None,
            name: "bad_thm".to_string(),
            kind: ConstantKind::Theorem,
            level_params: Vec::new(),
            type_: None,
            value: Some(sorry_expr),
            inductive_val: None,
            constructor_val: None,
            recursor_val: None,
            hints: None,
        };
        let info = extract_proof_info(&c);
        assert!(info.has_sorry);
        assert!(info.is_theorem);
        assert_eq!(info.proof_size, 3); // App + Const + BVar
    }

    #[test]
    fn test_proof_info_detects_classical() {
        let classical_expr = ParsedExpr::Const("Classical.choice".to_string(), vec![]);
        let c = ParsedConstant {
            definition_safety: None,
            quot_kind: None,
            name: "classical_thm".to_string(),
            kind: ConstantKind::Theorem,
            level_params: Vec::new(),
            type_: None,
            value: Some(classical_expr),
            inductive_val: None,
            constructor_val: None,
            recursor_val: None,
            hints: None,
        };
        let info = extract_proof_info(&c);
        assert!(info.uses_classical);
        assert!(info.uses_choice);
    }

    #[test]
    fn test_proof_info_detects_quot_lift() {
        let quot_expr = ParsedExpr::Const("Quot.lift".to_string(), vec![]);
        let c = ParsedConstant {
            definition_safety: None,
            quot_kind: None,
            name: "quot_thm".to_string(),
            kind: ConstantKind::Theorem,
            level_params: Vec::new(),
            type_: None,
            value: Some(quot_expr),
            inductive_val: None,
            constructor_val: None,
            recursor_val: None,
            hints: None,
        };
        let info = extract_proof_info(&c);
        assert!(info.uses_choice);
        assert!(!info.uses_classical);
    }

    #[test]
    fn test_proof_info_nested_expr() {
        // Lam(Nat, App(Const("f"), BVar(0)))
        let nested = ParsedExpr::Lam(
            "x".to_string(),
            Box::new(ParsedExpr::Const("Nat".to_string(), vec![])),
            Box::new(ParsedExpr::App(
                Box::new(ParsedExpr::Const("f".to_string(), vec![])),
                Box::new(ParsedExpr::BVar(0)),
            )),
            ParsedBinderInfo::Default,
        );
        let c = ParsedConstant {
            definition_safety: None,
            quot_kind: None,
            name: "nested".to_string(),
            kind: ConstantKind::Definition,
            level_params: Vec::new(),
            type_: None,
            value: Some(nested),
            inductive_val: None,
            constructor_val: None,
            recursor_val: None,
            hints: None,
        };
        let info = extract_proof_info(&c);
        // Lam + Const(Nat) + App + Const(f) + BVar = 5
        assert_eq!(info.proof_size, 5);
        assert!(!info.has_sorry);
    }

    // -----------------------------------------------------------------------
    // Expression depth tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_expr_depth_leaf() {
        assert_eq!(expr_depth(&ParsedExpr::BVar(0)), 1);
        assert_eq!(expr_depth(&ParsedExpr::Sort(ParsedLevel::Zero)), 1);
        assert_eq!(expr_depth(&ParsedExpr::Const("x".to_string(), vec![])), 1);
    }

    #[test]
    fn test_expr_depth_nested() {
        let deep = ParsedExpr::App(
            Box::new(ParsedExpr::App(
                Box::new(ParsedExpr::Const("f".to_string(), vec![])),
                Box::new(ParsedExpr::BVar(0)),
            )),
            Box::new(ParsedExpr::BVar(1)),
        );
        // App(App(Const, BVar), BVar) -> depth 3
        assert_eq!(expr_depth(&deep), 3);
    }

    // -----------------------------------------------------------------------
    // Lean4ImportConfig builder tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_config_defaults() {
        let config = Lean4ImportConfig::default();
        assert!(!config.skip_sorry);
        assert!(!config.include_private);
        assert_eq!(config.max_expr_depth, 0);
        assert!(config.trusted_modules.is_empty());
    }

    #[test]
    fn test_config_builder() {
        let config = Lean4ImportConfig::builder()
            .skip_sorry(true)
            .include_private(true)
            .max_expr_depth(128)
            .trusted_module("Init")
            .trusted_module("Mathlib")
            .build();
        assert!(config.skip_sorry);
        assert!(config.include_private);
        assert_eq!(config.max_expr_depth, 128);
        assert_eq!(config.trusted_modules, vec!["Init", "Mathlib"]);
    }

    // -----------------------------------------------------------------------
    // Batch axiom profile tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_batch_compute_axiom_profiles_empty() {
        let profiles = batch_compute_axiom_profiles(&[]);
        assert!(profiles.is_empty());
    }

    #[test]
    fn test_batch_compute_axiom_profiles() {
        let c1 = mock_constant("Classical.choice", ConstantKind::Axiom, false);
        let c2 = mock_constant("Nat.add", ConstantKind::Definition, true);
        let c3 = mock_constant("propext", ConstantKind::Axiom, false);
        let batch: Vec<(String, &ParsedConstant)> = vec![
            ("Classical.choice".to_string(), &c1),
            ("Nat.add".to_string(), &c2),
            ("propext".to_string(), &c3),
        ];
        let profiles = batch_compute_axiom_profiles(&batch);
        assert_eq!(profiles.len(), 3);
        assert!(profiles[0].has(AxiomProfile::CHOICE));
        assert!(profiles[1].is_pure());
        assert!(profiles[2].has(AxiomProfile::PROP_EXT));
    }

    // -----------------------------------------------------------------------
    // import_with_provenance tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_import_with_provenance_basic() {
        let constants = vec![
            mock_constant("Nat.add", ConstantKind::Definition, true),
            mock_constant("ax1", ConstantKind::Axiom, false),
        ];
        let module = mock_module(constants);
        let mut writer = ShardWriter::new();
        let config = Lean4ImportConfig::default();
        let (stats, records) = import_with_provenance(&module, &mut writer, &config).unwrap();
        assert_eq!(stats.total, 2);
        assert_eq!(stats.kernel_verified, 1);
        assert_eq!(stats.axiomatized, 1);
        assert_eq!(records.len(), 2);
        assert_eq!(records[0].original_name, "Nat.add");
        assert_eq!(records[1].original_name, "ax1");
    }

    #[test]
    fn test_import_with_provenance_skip_sorry() {
        let sorry_expr = ParsedExpr::Const("sorryAx".to_string(), vec![]);
        let constants = vec![
            ParsedConstant {
                definition_safety: None,
                quot_kind: None,
                name: "bad".to_string(),
                kind: ConstantKind::Theorem,
                level_params: Vec::new(),
                type_: None,
                value: Some(sorry_expr),
                inductive_val: None,
                constructor_val: None,
                recursor_val: None,
                hints: None,
            },
            mock_constant("good", ConstantKind::Theorem, true),
        ];
        let module = mock_module(constants);
        let mut writer = ShardWriter::new();
        let config = Lean4ImportConfig::builder().skip_sorry(true).build();
        let (stats, records) = import_with_provenance(&module, &mut writer, &config).unwrap();
        assert_eq!(stats.total, 2);
        assert_eq!(stats.skipped, 1);
        assert_eq!(stats.kernel_verified, 1);
        assert_eq!(records.len(), 2);
        assert!(records[0].notes[0].contains("sorry"));
    }

    #[test]
    fn test_import_with_provenance_skip_private() {
        let constants = vec![
            mock_constant("Foo._private.bar", ConstantKind::Definition, true),
            mock_constant("Foo.pub", ConstantKind::Definition, true),
        ];
        let module = mock_module(constants);
        let mut writer = ShardWriter::new();
        let config = Lean4ImportConfig::default(); // include_private=false
        let (stats, records) = import_with_provenance(&module, &mut writer, &config).unwrap();
        assert_eq!(stats.total, 2);
        assert_eq!(stats.skipped, 1);
        assert_eq!(stats.kernel_verified, 1);
        assert!(records[0].notes[0].contains("private"));
    }

    #[test]
    fn test_import_with_provenance_depth_limit() {
        // Build a deeply nested expression.
        let mut deep = ParsedExpr::BVar(0);
        for _ in 0..10 {
            deep = ParsedExpr::App(
                Box::new(ParsedExpr::Const("f".to_string(), vec![])),
                Box::new(deep),
            );
        }
        let constants = vec![ParsedConstant {
            definition_safety: None,
            quot_kind: None,
            name: "deep_const".to_string(),
            kind: ConstantKind::Definition,
            level_params: Vec::new(),
            type_: Some(deep),
            value: Some(mock_expr()),
            inductive_val: None,
            constructor_val: None,
            recursor_val: None,
            hints: None,
        }];
        let module = mock_module(constants);
        let mut writer = ShardWriter::new();
        let config = Lean4ImportConfig::builder().max_expr_depth(3).build();
        let (stats, records) = import_with_provenance(&module, &mut writer, &config).unwrap();
        assert_eq!(stats.total, 1);
        assert_eq!(stats.skipped, 1);
        assert!(records[0].notes[0].contains("depth"));
    }

    #[test]
    fn test_import_with_provenance_trusted_module() {
        let constants = vec![mock_constant("Init.Core.id", ConstantKind::Axiom, false)];
        let module = mock_module(constants);
        let mut writer = ShardWriter::new();
        let config = Lean4ImportConfig::builder().trusted_module("Init").build();
        let (stats, _records) = import_with_provenance(&module, &mut writer, &config).unwrap();
        // Axiom in trusted module -> SourceVerified (counted in kernel_verified stats)
        assert_eq!(stats.kernel_verified, 1);
        assert_eq!(stats.axiomatized, 0);
    }

    #[test]
    fn test_import_with_provenance_empty_module() {
        let module = mock_module(Vec::new());
        let mut writer = ShardWriter::new();
        let config = Lean4ImportConfig::default();
        let (stats, records) = import_with_provenance(&module, &mut writer, &config).unwrap();
        assert_eq!(stats.total, 0);
        assert!(records.is_empty());
    }
}
